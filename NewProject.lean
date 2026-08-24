-- `ForMathlib/` holds results of general mathematical interest (partial trace, positive
-- semidefiniteness, spectral/singular-value decomposition, majorization, unitarily invariant
-- norms, ...) that are, in the author's judgment, reasonable candidates for upstreaming to
-- Mathlib. The remaining imports below are specific to this project's own goal (bounding the
-- overlap of a projector with a Kronecker product).
import NewProject.ForMathlib.Majorization
import NewProject.ForMathlib.PartialTrace
import NewProject.ForMathlib.PosSemidef
import NewProject.ForMathlib.Projector
import NewProject.ForMathlib.EigenvalueMonotonicity
import NewProject.ForMathlib.SpectralDecomposition
import NewProject.ForMathlib.TraceInequality
import NewProject.ForMathlib.SingularValue
import NewProject.ForMathlib.SingularValueDecomposition
import NewProject.ForMathlib.KyFanNorm
import NewProject.ForMathlib.UnitarilyInvariantNorm
import NewProject.BilinearPositivity
import NewProject.OverlapBound
import NewProject.SumKroneckerMajorization
import NewProject.SumKroneckerWeakMajorization
