package tip.analysis

import tip.cfg._
import tip.ast.AstNodeData.DeclarationData
import tip.lattices.{LiftLattice, VariableSizeLattice}
import tip.solvers._

/**
 * Trait implementing variable size analysis with widening for intraprocedural CFG.
 */
trait VariableSizeAnalysisWidening extends ValueAnalysisMisc with Dependencies[CfgNode] {

  /** The control-flow graph */
  val cfg: ProgramCfg

  /** Underlying stepped-interval lattice */
  val valuelattice: VariableSizeLattice.type

  /** Lifted state lattice */
  val liftedstatelattice: LiftLattice[statelattice.type]

  /** Identify loop heads to apply widening */
  def loophead(n: CfgNode): Boolean = indep(n).exists(cfg.rank(_) > cfg.rank(n))

  /** Widening for single lattice element */
  def widenInterval(x: valuelattice.Element, y: valuelattice.Element): valuelattice.Element =
    valuelattice.widen(x, y)

  /** Widening for lifted state across variables */
  def widen(x: liftedstatelattice.Element, y: liftedstatelattice.Element): liftedstatelattice.Element = (x, y) match {
    case (liftedstatelattice.Bottom, rhs) => rhs
    case (lhs, liftedstatelattice.Bottom) => lhs
    case (liftedstatelattice.Lift(xm), liftedstatelattice.Lift(ym)) =>
      liftedstatelattice.Lift(
        declaredVars.map(v => v -> widenInterval(xm(v), ym(v))).toMap
      )
  }
}

object VariableSizeAnalysis {

  object Intraprocedural {

    /**
     * Variables size analysis, using the worklist solver with init and widening.
     */
    class WorklistSolverWithWidening(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
      extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, VariableSizeLattice)
        with WorklistFixpointSolverWithReachabilityAndWidening[CfgNode]
        with VariableSizeAnalysisWidening

    /**
     * Variables size analysis, using the worklist solver with init, widening, and narrowing.
     */
    class WorklistSolverWithWideningAndNarrowing(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
      extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, VariableSizeLattice)
        with WorklistFixpointSolverWithReachabilityAndWideningAndNarrowing[CfgNode]
        with VariableSizeAnalysisWidening {

      val narrowingSteps = 5
    }

  }
}

