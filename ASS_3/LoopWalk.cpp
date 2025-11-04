#include "llvm/Transforms/Utils/LoopWalk.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"
#include <cmath>

using namespace llvm;

std::vector<Instruction *> ToMove;
std::set<Instruction *> Invariants;

/**
 * Funzione per il controllo della Loop Invariance di un operando, cioè
 * se tale operando cambia durante l'esecuzione del loop.
 *
 * Controlla che l'operando non sia o una costante o un argomento di funzione, poiché
 * essi saranno sempre Loop Invariant.
 * Nel caso in cui invece l'operando sia il risultato di un'altra istruzione, bisogna
 * accertarsi che tale istruzione non sia all'interno del loop o che sia a sua volta
 * Loop Invariant. Si controlla quindi:
 *  - !loop.contains(inst->getParent())
 *  - Invariants.count(inst)
 */
bool isOperandInvariant(Value *operand, Loop &loop)
{
    if (isa<Constant>(operand) || isa<Argument>(operand))
        return true;
    if (Instruction *inst = dyn_cast<Instruction>(operand))
    {
        if (!loop.contains(inst->getParent()) || Invariants.count(inst))
            return true;
    }

    return false;
}

/**
 * Funzione per il controllo della Loop Invariance di un'istruzione, cioè
 * se il suo valore cambia durante l'esecuzione del loop.
 *
 * Il primo controllo viene fatto sulla sicurezza (Speculation). In pratica,
 * se ho istruzioni che toccano la memoria, come 'store' o 'call', o lavoro sui
 * thread, non posso spostare tale istruzione al di fuori, poiché potrebbe
 * rompere il programma.
 * Successivamente, si esegue un banale controllo con la funzione isOperandInvariant()
 * su tutti gli operandi dell'istruzione. Se tutti gli operandi sono Loop Invariant,
 * anche l'istruzione è da considerasi tale.
 */
bool isInstrInvariant(Instruction *I, Loop &loop)
{
    if (!isSafeToSpeculativelyExecute(I))
    {
        errs() << "[" << *I << "] Security: Check speculativo negativo!\n";
        return false;
    }

    for (auto operand = I->op_begin(); operand != I->op_end(); ++operand)
    {
        if (!isOperandInvariant(*operand, loop))
            return false;
    }

    outs() << "[" << *I << "] Istruzione Loop Invariant!\n";

    return true;
}

/**
 * Funzione di popolamento dei vettori ToMove e Invariants.
 * ToMove colleziona tutte le istruzioni per le quali è possibile eseguire
 * la Code Motion, mentre Invariants semplicemente viene usato per il
 * controllo dell'invarianza degli operandi.
 */
void findInvariantsInstr(BasicBlock &block, Loop &loop)
{
    for (auto &I : block)
    {
        if (isInstrInvariant(&I, loop))
        {
            ToMove.push_back(&I);
            Invariants.insert(&I);
        }
    }
}

/**
 * Funzione principale che esegue su tutto il loop e verifica la possibilità
 * o meno di eseguire la Code Motion.
 *
 * Dapprima, viene controllata l'esistenza di un preheader dove poter eseguire
 * la Code Motion. Se non è presente, si ritorna false.
 * Successivamente, si utilizzano alcune strutture dati utili per:
 *  - il DominatorTree (DT).
 *  - vec che contiene tutti i blocchi di uscita del loop.
 *
 * Si scorre il loop e per ogni blocco si controlla che esso domini tutte
 * le uscite. Se le domina, si passa al controllo della Loop Invariance
 * tramite i metodi precedenti. Sennò, si scarta.
 * Infine, viene eseguita la Code Motion per tutte le istruzioni disponibili.
 */
bool runOnLoop(Loop &loop, LoopAnalysisManager &LAM, LoopStandardAnalysisResults &LAR,
               LPMUpdater &LU)
{
    BasicBlock *preHeader = loop.getLoopPreheader();
    if (!preHeader)
        return false;

    // Strutture dati per uscite/domtree
    SmallVector<BasicBlock *> vec{};
    loop.getExitBlocks(vec);
    DominatorTree &DT = LAR.DT;

    // Scorro i BB del Loop
    auto loopBlocks = loop.getBlocks();
    for (auto &block : loopBlocks)
    {
        bool dominateExits = true;

        // Controllo che il blocco attuale domini tutte le uscite
        for (auto exitBB = vec.begin(); exitBB != vec.end(); ++exitBB)
        {
            if (!DT.dominates(block, *exitBB))
                dominateExits = false;
        }

        // Se non presente, setto un nome univoco al blocco.
        // Necessario in LLVM per gestione unicità.
        if (!block->hasName())
            block->setName("BB");

        outs() << "[" << block->getName() << "] Domina l'uscita?: " << dominateExits << "\n";

        if (dominateExits)
            findInvariantsInstr(*block, loop);
    }

    // Code Motion
    for (auto &I : ToMove)
    {
        outs() << "Istruzione disponibile a CM: " << *I << "\n";
        I->moveBefore(preHeader->getTerminator());
    }

    preHeader->print(outs());

    return true;
}

// RUN FUNCTION
PreservedAnalyses LoopWalk::run(Loop &L, LoopAnalysisManager &LAM, LoopStandardAnalysisResults &LAR,
                                LPMUpdater &LU)
{
    if (!runOnLoop(L, LAM, LAR, LU))
        return PreservedAnalyses::none();

    return PreservedAnalyses::all();
}