//===-- LocalOpts.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/LocalOpts.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"
// L'include seguente va in LocalOpts.h
#include <llvm/IR/Constants.h>
#include <cmath>

using namespace llvm;

// svolto a lezione ma migliorato in runOnBasicBlockAdv
bool runOnBasicBlock(BasicBlock &B)
{
    for (auto &I : B)
    {
        if (Instruction::Mul == I.getOpcode())
        {
            outs() << "Operazione: " << I << "\n";

            bool swp = false;
            ConstantInt *power2 = nullptr;

            if (ConstantInt *secOp = dyn_cast<ConstantInt>(I.getOperand(1)))
            {
                if (secOp->getValue().isPowerOf2())
                    power2 = secOp;
            }

            if (power2 == nullptr)
            {
                if (ConstantInt *firOp = dyn_cast<ConstantInt>(I.getOperand(0)))
                {
                    if (firOp->getValue().isPowerOf2())
                    {
                        power2 = firOp;
                        swp = true;
                    }
                }
            }

            if (power2 != nullptr)
            {
                ConstantInt *shiftOp = ConstantInt::get(power2->getType(), power2->getValue().exactLogBase2());
                outs() << "Operando: " << power2->getValue() << "\n";

                Instruction *NewI;

                if (swp)
                    NewI = BinaryOperator::Create(Instruction::Shl, I.getOperand(1), shiftOp);
                else
                    NewI = BinaryOperator::Create(Instruction::Shl, I.getOperand(0), shiftOp);

                NewI->insertAfter(&I);
                I.replaceAllUsesWith(NewI);
            }
            else
                outs() << "Nessuna potenza di 2\n";
        }
    }
    return true;
}

/**
 * ALGEBRAIC IDENTITIES FUNCTION
 *
 * Un'identità algebrica è possibile nei seguenti casi:
 *  1. x+0 = 0+x => x
 *  2. x*1 = 1*x => x
 *
 * La funzione esegue un controllo cercando di capire, prima di tutto, se l'opcode corrisponde
 * a una moltiplicazione o a un'addizione.
 * In tal caso, procede a definire una variabile 'imm' null e a controllare che il secondo operatore
 * sia un valore costante. Se è costante, controlla che sia 0 in caso di addizione o 1 in caso di moltiplicazione.
 * Potrbbe però anche essere che l'operatore costante sia il primo. Pertanto, se imm è null vuol dire che il
 * secondo operando NON è una costante e vale la pena controllare il primo. Si ripetono quindi i controlli,
 * stavolta però sul primo operatore.
 * Il flag 'status' serve solamente a capire se c'è stata o meno un'azione.
 */
bool runOnAlgebraicIdentity(BasicBlock &B)
{
    bool status = false;

    // Iteratore su tutte le istruzioni del BasicBlock
    for (auto &I : B)
    {
        // Controllo che l'operazione sia commutativa
        if (Instruction::Add == I.getOpcode() || Instruction::Mul == I.getOpcode())
        {
            ConstantInt *imm = nullptr;

            // Controllo se il secondo operando è una costante e quale operazione sto eseguendo
            if (ConstantInt *secOp = dyn_cast<ConstantInt>(I.getOperand(1)))
            {
                if (secOp->getValue().isZero() && Instruction::Add == I.getOpcode())
                {
                    imm = secOp;
                    outs() << "[AlgebraicIdentity]: " << I.getOpcodeName() << " ->" << I << "\n";
                    outs() << "Identità risolta su " << I.getOpcodeName() << " con x in prima posizione" << "\n";
                    I.replaceAllUsesWith(I.getOperand(0));
                    status = true;
                }
                else if (secOp->getValue().isOne() && Instruction::Mul == I.getOpcode())
                {
                    imm = secOp;
                    outs() << "[AlgebraicIdentity]: " << I.getOpcodeName() << " ->" << I << "\n";
                    outs() << "Identità risolta su " << I.getOpcodeName() << " con x in prima posizione" << "\n";
                    I.replaceAllUsesWith(I.getOperand(0));
                    status = true;
                }
            }

            // Controllo se il primo operando è una costante e quale operazione sto eseguendo
            if (imm == nullptr)
            {
                if (ConstantInt *firOp = dyn_cast<ConstantInt>(I.getOperand(0)))
                {
                    if (firOp->getValue().isZero() && Instruction::Add == I.getOpcode())
                    {
                        imm = firOp;
                        outs() << "[AlgebraicIdentity]: " << I.getOpcodeName() << " ->" << I << "\n";
                        outs() << "Identità risolta su " << I.getOpcodeName() << " con x in seconda posizione" << "\n";
                        I.replaceAllUsesWith(I.getOperand(1));
                        status = true;
                    }
                    else if (firOp->getValue().isOne() && Instruction::Mul == I.getOpcode())
                    {
                        imm = firOp;
                        outs() << "[AlgebraicIdentity]: " << I.getOpcodeName() << " ->" << I << "\n";
                        outs() << "Identità risolta su " << I.getOpcodeName() << " con x in seconda posizione" << "\n";
                        I.replaceAllUsesWith(I.getOperand(1));
                        status = true;
                    }
                }
            }
        }
    }
    // Flag falso, trovato nulla
    if (!status)
        outs() << "Nessuna identità trovata \n";
    outs() << "[AlgebraicIdentity] terminata \n\n";
    return status;
}

/**
 * STRENGTH REDUCTION (ADVANCED)
 *
 * La Strength Reduction consiste nel trasformare delle moltiplicazioni o delle divisioni in delle
 * operazioni svolte tramite shifting left o right:
 *  1. 15*x = x*15 => (x<<4) - x
 *  2. x/8 => x>>3
 *
 * Un vincolo da rispettare è che le costanti devono, ovviamente, essere potenze di 2 o un numero che si avvicina
 * alle potenze di 2 di ±1 (come nell'esempio di prima con 15).
 * Dapprima si controlla che l'opcode sia o una moltiplicazione o una divisione, casi che andranno trattati a
 * parte per via della proprietà commutativa della moltiplicazione (non presente nella divisione).
 *
 * CASO MUL :
 * Successivamente, si controlla quale dei due operandi è quello costante. Nel caso del primo operando costante,
 * il flag 'swp' sarà true. Se quindi il valore di 'imm' non è null (ergo, uno dei due operatori è costante) e
 * il valore della moltiplicazione non è 1 (altrimenti si avrebbe una algebraic identity), si procede col calcolo.
 * Si controlla che 'imm' sia una potenza di 2, affinché si possa semplificare con una semplice istruzione di shifting.
 * In altro caso, si controlla che o 'val+1' o 'val-1' siano potenze di 2. In questo caso, sono due le istruzioni da
 * creare, una per lo shifting, l'altra per l'addizione/sottrazione di val.
 *
 * CASO DIV :
 * Uguale a prima, con la differenza che qua ci dev'essere una potenza esatta di 2 per funzionare.
 * Inoltre, lo swap non si può fare perché la proprietà commutativa non è presente per le divisioni.
 */
bool runOnBasicBlockAdv(BasicBlock &B)
{
    for (auto &I : B)
    {
        if (Instruction::Mul == I.getOpcode())
        {
            bool swp = false;
            ConstantInt *imm = nullptr;

            if (ConstantInt *secOp = dyn_cast<ConstantInt>(I.getOperand(1)))
                imm = secOp;
            else if (ConstantInt *firOp = dyn_cast<ConstantInt>(I.getOperand(0)))
            {
                imm = firOp;
                swp = true;
            }

            if (imm != nullptr && !imm->getValue().isOne())
            {
                APInt val = imm->getValue();
                if (val.isPowerOf2())
                {
                    ConstantInt *shiftOp = ConstantInt::get(imm->getType(), imm->getValue().exactLogBase2());
                    outs() << "[StrengthReduction]: " << I.getOpcodeName() << " ->" << I << "\n";
                    outs() << "Immediato potenza di 2 -> shift x<<" << shiftOp->getValue() << "\n";

                    Instruction *NewI_1;

                    if (swp)
                        NewI_1 = BinaryOperator::Create(Instruction::Shl, I.getOperand(1), shiftOp);
                    else
                        NewI_1 = BinaryOperator::Create(Instruction::Shl, I.getOperand(0), shiftOp);

                    NewI_1->insertAfter(&I);
                    I.replaceAllUsesWith(NewI_1);
                }
                else if ((val + 1).isPowerOf2())
                {
                    ConstantInt *shiftOp = ConstantInt::get(imm->getType(), imm->getValue().nearestLogBase2());
                    outs() << "[StrengthReduction]: " << I.getOpcodeName() << " ->" << I << "\n";
                    outs() << "(immediato+1) potenza di 2 -> shift x<<" << shiftOp->getValue() << " e aggiunta una sub \n";

                    Instruction *NewI_1;
                    Instruction *NewI_2;

                    if (swp)
                    {
                        NewI_1 = BinaryOperator::Create(Instruction::Shl, I.getOperand(1), shiftOp);
                        NewI_2 = BinaryOperator::Create(Instruction::Sub, NewI_1, I.getOperand(1));
                    }
                    else
                    {
                        NewI_1 = BinaryOperator::Create(Instruction::Shl, I.getOperand(0), shiftOp);
                        NewI_2 = BinaryOperator::Create(Instruction::Sub, NewI_1, I.getOperand(0));
                    }

                    NewI_1->insertAfter(&I);
                    NewI_2->insertAfter(NewI_1);
                    I.replaceAllUsesWith(NewI_2);
                }
                else if ((val - 1).isPowerOf2())
                {
                    ConstantInt *shiftOp = ConstantInt::get(imm->getType(), imm->getValue().nearestLogBase2());
                    outs() << "[StrengthReduction]: " << I.getOpcodeName() << " ->" << I << "\n";
                    outs() << "(immediato-1) potenza di 2 -> shift x<<" << shiftOp->getValue() << " e aggiunta una add \n";

                    Instruction *NewI_1;
                    Instruction *NewI_2;

                    if (swp)
                    {
                        NewI_1 = BinaryOperator::Create(Instruction::Shl, I.getOperand(1), shiftOp);
                        NewI_2 = BinaryOperator::Create(Instruction::Add, NewI_1, I.getOperand(1));
                    }
                    else
                    {
                        NewI_1 = BinaryOperator::Create(Instruction::Shl, I.getOperand(0), shiftOp);
                        NewI_2 = BinaryOperator::Create(Instruction::Add, NewI_1, I.getOperand(0));
                    }

                    NewI_1->insertAfter(&I);
                    NewI_2->insertAfter(NewI_1);
                    I.replaceAllUsesWith(NewI_2);
                }
            }
        }
        else if (Instruction::SDiv == I.getOpcode())
        {
            ConstantInt *imm = nullptr;

            if (ConstantInt *secOp = dyn_cast<ConstantInt>(I.getOperand(1)))
                imm = secOp;

            if (imm != nullptr)
            {
                if (imm->getValue().isPowerOf2())
                {
                    ConstantInt *shiftOp = ConstantInt::get(imm->getType(), imm->getValue().nearestLogBase2());
                    outs() << "[StrengthReduction]: " << I.getOpcodeName() << " ->" << I << "\n";
                    outs() << "Immediato potenza di 2 -> shift x>>" << shiftOp->getValue() << "\n";

                    Instruction *NewI_1;

                    NewI_1 = BinaryOperator::Create(Instruction::LShr, I.getOperand(0), shiftOp);

                    NewI_1->insertAfter(&I);
                    I.replaceAllUsesWith(NewI_1);
                }
            }
        }
    }
    outs() << "[StrengthReduction] terminata \n\n";
    return true;
}

/**
 * MULTI-INSTRUCTION OPTIMIZATION
 *
 * Un'ottimizzazione multi-istruzione consiste nel snellire alcune istruzioni nel caso in cui contengano valori
 * uguali. Un esempio:
 *  - a = b+1, c = a-1 => a = b+1, c=b
 *
 * Dapprima avviene un controllo che verifica la validità dell'opcode, che dev'essere un'addizione o una sottrazione.
 * Anche qua è presente 'swp' per controllare che l'operando costante sia in prima o in seconda posizione.
 * Si va poi a iterare su tutti gli usi di quella specifica istruzione e si fa lo stesso controllo, compreso lo swap.
 * Se le posizioni sono le stesse e i due immediates sono uguali, allora l'ultimo controllo da fare riguarda proprio
 * la discordanza di opcode. Infatti, se i due opcode saranno differenti, significa che uno è un'addizione e l'altro
 * una sottrazione. In pratica, si annullano a vicenda!
 */
bool runOnMultiInstruction(BasicBlock &B)
{
    for (auto &I : B)
    {
        if (Instruction::Add == I.getOpcode() || Instruction::Sub == I.getOpcode())
        {
            bool swp = false;
            ConstantInt *imm1 = nullptr;

            // Controllo swap della prima istruzione
            if (ConstantInt *secOp = dyn_cast<ConstantInt>(I.getOperand(1)))
                imm1 = secOp;
            else if (ConstantInt *firOp = dyn_cast<ConstantInt>(I.getOperand(0)))
            {
                imm1 = firOp;
                swp = true;
            }

            if (imm1 != nullptr)
            {
                // Itero su tutti gli user della prima istruzione
                for (auto iter_U = I.user_begin(); iter_U != I.user_end(); ++iter_U)
                {
                    Instruction *U = dyn_cast<Instruction>(*iter_U);
                    if (Instruction::Add == U->getOpcode() || Instruction::Sub == U->getOpcode())
                    {
                        ConstantInt *imm2 = nullptr;

                        // Determinato che la seconda istruzione è una add o una sub, ne controllo lo swap
                        if (ConstantInt *secOp = dyn_cast<ConstantInt>(U->getOperand(1)))
                            imm2 = secOp;
                        else if (ConstantInt *firOp = dyn_cast<ConstantInt>(U->getOperand(0)))
                            imm2 = firOp;

                        if (imm2)
                        {
                            // Se lo swap combacia con la prima e gli opcode discordano, abbiamo una multi-instr
                            if (imm1 == imm2 && I.getOpcode() != U->getOpcode())
                            {
                                outs() << "[MultiInstruction]: " << I.getOpcodeName() << " ->" << I << "\n";
                                outs() << "[MultiInstruction]: " << U->getOpcodeName() << " ->" << I << "\n";
                                if (swp)
                                    U->replaceAllUsesWith(I.getOperand(1));
                                else
                                    U->replaceAllUsesWith(I.getOperand(0));
                                outs() << "Multi Instruction trovata" << "\n";
                            }
                        }
                        else
                            outs() << "Multi Instruction non trovata" << "\n";
                    }
                }
            }
        }
    }
    outs() << "[MultiInstruction] terminata \n\n";
    return true;
}

bool runOnFunction(Function &F)
{
    bool Transformed = false;

    for (auto Iter = F.begin(); Iter != F.end(); ++Iter)
    {
        if (runOnAlgebraicIdentity(*Iter))
            Transformed = true;
        if (runOnBasicBlockAdv(*Iter))
        {
            Transformed = true;
        }
        if (runOnMultiInstruction(*Iter))
        {
            Transformed = true;
        }
        /*if (runOnBasicBlock(*Iter)) {
          Transformed = true;
        }*/
    }
    return Transformed;
}

PreservedAnalyses LocalOpts::run(Module &M, ModuleAnalysisManager &AM)
{
    for (auto Fiter = M.begin(); Fiter != M.end(); ++Fiter)
        if (runOnFunction(*Fiter))
            return PreservedAnalyses::none();

    return PreservedAnalyses::all();
}