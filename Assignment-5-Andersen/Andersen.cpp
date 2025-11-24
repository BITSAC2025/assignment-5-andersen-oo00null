/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A5Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    (void)consg;

    Andersen andersen(consg);

    // TODO: complete the following method
    andersen.runPointerAnalysis();

    andersen.dumpResult();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    auto pag = SVF::PAG::getPAG();

    // -----------------------------------------------------------
    // Phase 1: Initialize Points-to Sets (Initial Constraints)
    // -----------------------------------------------------------
    // Handle Addr: y = &x
    // Constraint: {x} subset of pts(y)
    // Propagation: pts[y] <- pts[y] U {x}
    for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Addr))
    {
        // Addr edge: SrcID (x, the address) -> DstID (y, the pointer)
        // SrcID is the address node (Addr node), DstID is the pointer variable.
        // PAG::getPAG()->getIDWithLLVMInst() can map LLVM values to node IDs,
        // but here we just use the IDs from the edge.
        unsigned address = edge->getSrcID(); // x (the memory location)
        unsigned pointer = edge->getDstID(); // y (the variable holding the address)
        
        // pts[pointer] <- pts[pointer] U {address}
        pts[pointer].insert(address); 
    }

    // -----------------------------------------------------------
    // Phase 2: Iteratively Propagate Constraints (Fixed-Point Iteration)
    // -----------------------------------------------------------
    bool changed = true;
    while (changed)
    {
        changed = false;

        // --- Basic Propagation Rules (Subset Constraints: pts[src] subset of pts[dst]) ---

        // Phi: res = Phi(op1, op2, ...)
        // Constraint: pts(op_i) subset of pts(res)
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Phi))
        {
            const SVF::PhiStmt *phi = SVF::SVFUtil::cast<SVF::PhiStmt>(edge);
            unsigned res = phi->getResID(); // Result (dst)
            for (const auto opVar : phi->getOpndVars()) // All operands (src)
            {
                unsigned op = opVar->getId();
                for (auto p : pts[op])
                {
                    if (pts[res].insert(p).second)
                        changed = true;
                }
            }
        }
        
        // Select: res = Select(cond, op1, op2)
        // Constraint: pts(op_i) subset of pts(res) (Similar to Phi)
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Select))
        {
            const SVF::SelectStmt *sel = SVF::SVFUtil::cast<SVF::SelectStmt>(edge);
            unsigned res = sel->getResID(); // Result (dst)
            for (const auto opVar : sel->getOpndVars()) // All operands (src)
            {
                unsigned op = opVar->getId();
                for (auto p : pts[op])
                {
                    if (pts[res].insert(p).second)
                        changed = true;
                }
            }
        }
        
        // Copy: y = x (Simple assignment)
        // Constraint: pts(src) subset of pts(dst)
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Copy))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }

        // Call (Argument Passing) and Ret (Return Value Passing) are also Copy-like constraints
        // Call: DstID is the formal parameter/return value, SrcID is the actual argument/returned value.
        // Constraint: pts(actual) subset of pts(formal)
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Call))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }
        
        // Ret: DstID is the receiver of return value, SrcID is the return value.
        // Constraint: pts(return\_value) subset of pts(receiver)
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Ret))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }
        
        // ThreadFork/ThreadJoin: Similar to Copy for cross-thread data flow
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::ThreadFork))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::ThreadJoin))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }

        // --- Indirect Memory Access Rules (The Core of Andersen Analysis) ---

        // Load: y = *x
        // Constraint: If a in pts(x), then pts(a) subset of pts(y)
        // Load edge: SrcID is the pointer x, DstID is the result y.
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Load))
        {
            unsigned x = edge->getSrcID(); // x: pointer (operand)
            unsigned y = edge->getDstID(); // y: variable receiving the value (*x)

            // For every address 'a' that 'x' points to:
            for (auto a : pts[x]) 
            {
                // Propagate contents of pts[a] to pts[y]
                for (auto v : pts[a])
                {
                    if (pts[y].insert(v).second) 
                        changed = true;
                }
            }
        }

        // Store: *x = y
        // Constraint: If a in pts(x), then pts(y) subset of pts(a)
        // Store edge: SrcID is the value y, DstID is the pointer x.
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Store))
        {
            unsigned y = edge->getSrcID(); // y: value (operand)
            unsigned x = edge->getDstID(); // x: pointer to memory location (operand)

            // For every address 'a' that 'x' points to:
            for (auto a : pts[x]) 
            {
                // Propagate contents of pts[y] to pts[a]
                for (auto v : pts[y]) 
                {
                    if (pts[a].insert(v).second) 
                        changed = true;
                }
            }
        }
    } // End while (changed)
}