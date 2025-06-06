package tip.analysis

import tip.ast.{AAssignStmt, AIdentifier, AVarStmt, NoPointers, NoRecords}
import tip.ast.AstNodeData.DeclarationData
import tip.cfg.{CfgFunExitNode, CfgNode, CfgStmtNode, IntraproceduralProgramCfg}
import tip.lattices.{MapLattice, PowersetLattice}
import tip.solvers.{SimpleMapLatticeFixpointSolver, SimpleWorklistFixpointSolver}

/**
 * Base class for reaching definitions analysis.
 */
/*
IMPORTANT: Opposite to LiveVarsAnalysis we need to work with Predecessors => true arg to FlowSensitiveAnalysis
 */
abstract class ReachingDefAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(true) {

  val lattice: MapLattice[CfgNode, PowersetLattice[AAssignStmt]] = new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case _: CfgFunExitNode => lattice.sublattice.bottom
      case r: CfgStmtNode =>
        r.data match {
          case as: AAssignStmt =>
            as.left match {
              case id: AIdentifier =>
                lattice.sublattice.lub(
                  Set(as),
                  s.filter(as => as.left match {
                    case innerId: AIdentifier => !innerId.name.equals(id.name)
                    case _ => true
                  })
                )
              case _ => s
            }
          case _: AVarStmt => // [[var x]] = {var x}
            s
          case _ => s // [[n]] = JOIN(n)
        }
      case _ => s // [[n]] = JOIN(n)
    }
}

/**
 * Live variables analysis that uses the simple fixpoint solver.
 */
class ReachingDefAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
  extends ReachingDefAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with BackwardDependencies

/**
 * Live variables analysis that uses the worklist solver.
 */
class ReachingDefAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
  extends ReachingDefAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with BackwardDependencies
