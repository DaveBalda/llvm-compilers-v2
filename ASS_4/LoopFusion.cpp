#include "llvm/Transforms/Utils/LoopFusion.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/IR/TypedPointerType.h"

// Memorizzazione coppie di loop adiacenti
void pair(llvm::Loop *&L1, llvm::Loop *&L2, std::set<std::pair<llvm::Loop *, llvm::Loop *>> &set)
{
    set.insert(std::make_pair(L1, L2));
}

// Trova loop adiacenti
void adjLoops(std::set<std::pair<llvm::Loop *, llvm::Loop *>> &adjacentLoops, llvm::LoopInfo &LI)
{
    bool adjFound = false;

    for (auto *L1 : LI)
    {
        for (auto *L2 : LI)
        {
            // Caso 1: entrambi guarded
            if (L1->isGuarded() && L2->isGuarded())
            {
                // Blocco d'uscita (spesso con solo 1 istr di branch)
                auto *exitBlock = L1->getExitBlock();

                // Usiamo getParent() per ottenere un BasicBlock datatype
                auto *guard2 = L2->getLoopGuardBranch()->getParent();

                /**
                 * In pratica, si controlla che exitBlock sia vuoto, come vuole
                 * la norma (singola istruzione di branch presente). Inoltre, va
                 * prima verificato che il successore di exitBlock sia proprio la
                 * guardia di L2.
                 *
                 * Se tutto va bene, aggiungiamo una coppia di loop adiacenti come pair.
                 */
                if (exitBlock && guard2 && exitBlock->getSingleSuccessor() == guard2)
                {
                    bool extraInstr = false;
                    for (auto &I : *exitBlock)
                    {
                        if (&I != exitBlock->getTerminator())
                        {
                            llvm::outs() << "[Guarded Loops] Non adiacenti! Istruzione extra → " << I << "\n";
                            extraInstr = true;
                            break;
                        }
                    }
                    if (!extraInstr)
                    {
                        llvm::outs() << "[Guarded Loops] Adiacenza trovata!\n";
                        adjFound = true;
                        pair(L1, L2, adjacentLoops);
                    }
                }
            }

            // Caso 2: entrambi unguarded
            else if (!L1->isGuarded() && !L2->isGuarded())
            {
                auto *exitBlock = L1->getExitBlock();
                auto *preheader2 = L2->getLoopPreheader();

                /**
                 * In questo caso, il controllo viene fatto semplicemente
                 * sui due bocchi. Se exitBlock è uguale al preheader del
                 * successivo, allora sono adiacenti.
                 */
                if (exitBlock && preheader2 && exitBlock == preheader2)
                {
                    llvm::outs() << "[Unguarded Loops] Adiacenza trovata!\n";
                    adjFound = true;
                    pair(L1, L2, adjacentLoops);
                }
            }
        }
    }

    if (!adjFound)
        llvm::outs() << "[adjLoops] Nessuna coppia trovata!\n";
}

// Verifica i loop dal punto di vista del control flow
bool checkEquivalence(std::pair<llvm::Loop *, llvm::Loop *> loop, llvm::DominatorTree &DT, llvm::PostDominatorTree &PDT)
{

    // Verifica che i loop guarded abbiano la stessa condizione
    if (loop.first->isGuarded())
        if (auto FC0CmpInst = llvm::dyn_cast<llvm::Instruction>(loop.first->getLoopGuardBranch()->getCondition()))
            if (auto FC1CmpInst = llvm::dyn_cast<llvm::Instruction>(loop.second->getLoopGuardBranch()->getCondition()))
                if (!FC0CmpInst->isIdenticalTo(FC1CmpInst))
                    return 0;

    /**
     * Se i loop hanno la guardia, si effettua un controllo sul parent
     * della guardia (cioè sul basic block che la contiene) sia di dominanza che
     * di post-dominanza.
     */
    if (loop.first->isGuarded())
    {
        if (DT.dominates(loop.first->getLoopGuardBranch()->getParent(),
                         loop.second->getLoopGuardBranch()->getParent()) &&
            PDT.dominates(loop.second->getLoopGuardBranch()->getParent(),
                          loop.first->getLoopGuardBranch()->getParent()))
        {
            llvm::outs() << "\n[checkEquivalence] Control Flow equivalente!\n";
            return 1;
        }
    }
    /**
     * Se i loop non hanno la guardia, si effettua un controllo sull'header
     * sia di dominanza che di post-dominanza.
     */
    else
    {
        if (DT.dominates(loop.first->getHeader(), loop.second->getHeader()) && PDT.dominates(loop.second->getHeader(), loop.first->getHeader()))
        {
            llvm::outs() << "\n[checkEquivalence] Control Flow equivalente!\n";
            return 1;
        }
    }
    return 0;
}

// Verifica del trip count
bool TripCount(std::pair<llvm::Loop *, llvm::Loop *> loop, llvm::ScalarEvolution &SE)
{

    auto l1Backedges = SE.getBackedgeTakenCount(loop.first);
    auto l2Backedges = SE.getBackedgeTakenCount(loop.second);

    /**
     * Controlla che sia calcolabile a priori in numero di backedges di
     * entrambi i loop.
     */
    if (l1Backedges->getSCEVType() == llvm::SCEVCouldNotCompute().getSCEVType() ||
        l2Backedges->getSCEVType() == llvm::SCEVCouldNotCompute().getSCEVType())
    {
        llvm::outs() << "\n[TripCount] Impossibile calcolare il TripCount!\n";
        return 0;
    }

    if (l1Backedges == l2Backedges)
    {
        llvm::outs() << "\n[TripCount] Stesso numero di backedge\n";
        return 1;
    }
    return 0;
}

// Controllo delle negative dependecies
bool negDependencies(std::pair<llvm::Loop *, llvm::Loop *> loop)
{
    // set con istruzioni dipedenti tra di loro
    std::set<llvm::Instruction *> depInst{};

    for (auto &BB : loop.first->getBlocks())
    {
        for (llvm::Instruction &I : *BB)
        {
            // Se l'istruzione accede alla memoria (tipo a[i]) allora esegui...
            if (I.getOpcode() == llvm::Instruction::GetElementPtr)
            {
                // Stiamo parlando di tutti gli usi di %a
                for (auto &use : I.getOperand(0)->uses())
                {
                    // Controlla che gli user di %a siano istruzioni.
                    if (auto inst = llvm::dyn_cast<llvm::Instruction>(use.getUser()))
                    {
                        if (loop.second->contains(inst))
                        {
                            // Indice di %a nel secondo loop.
                            // Controllo che sia un'istruzione.
                            if (auto inst2 = llvm::dyn_cast<llvm::Instruction>(inst->getOperand(1)))
                            {
                                /**
                                 * Se è una PHI instruction, significa che il valore non è alterato.
                                 * Supponiamo a[i]:
                                 *  - Caso 1: i è quello del preheader (es: i=0)
                                 *  - Caso 2: i è quello del latch (es: i++)
                                 * Quindi, siamo davanti a un'istruzione PHI.
                                 * Se invece l'istruzione non è una PHI (es: i+1), allora qualcos'altro
                                 * sta alterando l'offset. Questo perché nella forma single SSA vai
                                 * a ridefinire l'operazione (es: %j = sub %i, 1).
                                 */
                                if (auto PHIinst = llvm::dyn_cast<llvm::Instruction>(inst2->getOperand(0)))
                                {
                                    switch (PHIinst->getOpcode())
                                    {
                                    case llvm::Instruction::PHI:
                                    case llvm::Instruction::Sub: // se l'istruzione è una sub, l'offset è negativo e si riesce ad unire i loop
                                        break;
                                    default:
                                        depInst.insert(PHIinst); // l'offset verrà modificato da un'altra istruzione --> i loop non possono essere uniti
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // visualizzazione, se presenti, delle istruzioni che violano la dipendenza negativa
    if (!depInst.empty())
    {
        llvm::outs() << "\n\n[negDep] Trovate dipendenze negative! Loop non fondibili:\n";
        for (auto inst : depInst)
        {
            llvm::outs() << "Istruzione: " << *inst << "\n";
        }
        return 0;
    }
    return 1;
}

// Fusione dei loop
void loopFusion(llvm::Loop *&L1, llvm::Loop *&L2)
{
    /**
     * Sostituzione delle induction variables di L2 con quelle di L1.
     * Le IV sono i contatori (es: i, j...)
     */
    auto firstLoopIV = L1->getCanonicalInductionVariable();
    auto secondLoopIV = L2->getCanonicalInductionVariable();

    secondLoopIV->replaceAllUsesWith(firstLoopIV);

    auto header1 = L1->getHeader();
    auto header2 = L2->getHeader();
    auto latch1 = L1->getLoopLatch();
    auto latch2 = L2->getLoopLatch();
    auto exit = L2->getUniqueExitBlock();

    if (!L1->isGuarded())
    {
        /**
         * Modifiche al Control Flow Graph (unguarded):
         * 1. Header L1 --> Exit L2
         * 2. Body L1 --> Body L2
         * 3. Body L2 --> Latch L1
         * 4. Header L2 --> Latch L2
         */

        // dropBack(1) mi toglie il latch dalla lista, back() mi prende il body
        llvm::BasicBlock *lastL1BB = L1->getBlocks().drop_back(1).back();

        // collegamento body loop2 al body loop1 (tolgo sia latch che header)
        lastL1BB->getTerminator()->setSuccessor(0, L2->getBlocks().drop_front(1).drop_back(1).front());

        // collegamento body loop2 latch loop1
        L2->getBlocks().drop_front(1).drop_back(1).back()->getTerminator()->setSuccessor(0, latch1);

        // collegamento header loop2 al latch loop2
        llvm::BranchInst::Create(latch2, header2->getTerminator());
        header2->getTerminator()->eraseFromParent();

        // collegamento header loop1 all'L2 exit
        llvm::BranchInst::Create(L1->getBlocks().drop_front(1).front(), exit, header1->back().getOperand(0), header1->getTerminator());
        header1->getTerminator()->eraseFromParent();
    }
    else
    {
        // modifiche al control flow graph eseguite:
        // guard1 --> L2 exit
        // latch1 --> L2 exit
        // header1 --> header2
        // header2 --> latch1

        auto guard1 = L1->getLoopGuardBranch()->getParent();

        // collegamento guard loop1 all' L2 exit
        llvm::BranchInst::Create(L1->getLoopPreheader(), exit, guard1->back().getOperand(0), guard1->getTerminator());
        guard1->getTerminator()->eraseFromParent();

        // collegamento latch loop1 all'L2 exit
        llvm::BranchInst::Create(L1->getBlocks().front(), exit, latch1->back().getOperand(0), latch1->getTerminator());
        latch1->getTerminator()->eraseFromParent();

        // collegamento header loop1 all'header loop2
        L1->getBlocks().drop_back(1).back()->getTerminator()->setSuccessor(0, L2->getBlocks().front());

        // collegamento header loop2 al latch loop1
        L2->getBlocks().drop_back(1).back()->getTerminator()->setSuccessor(0, latch1);

        // rimozione header loop2 - PHI node
        header2->front().eraseFromParent();
    }
}

llvm::PreservedAnalyses llvm::LoopFusion::run(Function &F, FunctionAnalysisManager &AM)
{

    llvm::LoopInfo &LI = AM.getResult<llvm::LoopAnalysis>(F);
    llvm::DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
    llvm::PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);
    llvm::ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);

    // Set con coppie di loop adiacenti
    std::set<std::pair<llvm::Loop *, llvm::Loop *>> adjacentLoops{};

    adjLoops(adjacentLoops, LI);

    bool modified = 0;

    for (std::pair<llvm::Loop *, llvm::Loop *> loop : adjacentLoops)
    {
        if (!checkEquivalence(loop, DT, PDT))
            continue;
        if (!TripCount(loop, SE))
            continue;
        if (!negDependencies(loop))
            continue;

        llvm::outs() << "\nI loop possono essere fusi\n";
        loopFusion(loop.first, loop.second);

        modified = 1;
    }

    if (modified)
        return llvm::PreservedAnalyses::none();
    else
        return llvm::PreservedAnalyses::all();
}