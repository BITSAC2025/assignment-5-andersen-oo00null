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
    consg->dump();
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
    for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Addr))
    {
        pts[edge->getSrcID()].insert(edge->getDstID());
    }
    bool changed = true;
    while (changed)
    {
        changed = false;
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Phi))
        {
            const SVF::PhiStmt *phi = SVF::SVFUtil::cast<SVF::PhiStmt>(edge);
            unsigned res = phi->getResID();
            for (const auto opVar : phi->getOpndVars())
            {
                unsigned op = opVar->getId();
                for (auto p : pts[op])
                {
                    if (pts[res].insert(p).second)
                        changed = true;
                }
            }
        }
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Select))
        {
            const SVF::SelectStmt *sel = SVF::SVFUtil::cast<SVF::SelectStmt>(edge);
            unsigned res = sel->getResID();
            for (const auto opVar : sel->getOpndVars())
            {
                unsigned op = opVar->getId();
                for (auto p : pts[op])
                {
                    if (pts[res].insert(p).second)
                        changed = true;
                }
            }
        }
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
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Load))
        {
            unsigned y = edge->getSrcID();
            unsigned x = edge->getDstID();
            for (auto p : pts[y])
            {
                for (auto v : pts[p])
                {
                    if (pts[x].insert(v).second)
                        changed = true;
                }
            }
        }
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Store))
        {
            unsigned y = edge->getSrcID();
            unsigned x = edge->getDstID();
            for (auto p : pts[x])
            {
                for (auto v : pts[y])
                {
                    if (pts[p].insert(v).second)
                        changed = true;
                }
            }
        }
    }
}