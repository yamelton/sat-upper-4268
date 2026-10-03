import SatUpper.NumericalMoments
import SatUpper.NumericalLogs
import SatUpper.VarianceControl

/-! Kernel-checked enclosure of the complete finite analytic expression. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SatUpper.Formalization

theorem vertex_and_edge_le :
    VertexEnclosures.vertexUpper Witness.cutoff NumericalMoments.lower NumericalMoments.upper +
      NumericalLogs.edgeUpper ≤ Witness.roundedUpper := by
  decide +kernel

theorem numericalEnclosure : NumericalEnclosure := by
  have hv := VertexEnclosures.vertexUpper_correct NumericalMoments.enclosures
  have hc := NumericalLogs.edgeCorrection_le
  have hn :
      (VertexEnclosures.vertexUpper Witness.cutoff NumericalMoments.lower NumericalMoments.upper : ℝ) +
        (NumericalLogs.edgeUpper : ℝ) ≤ (Witness.roundedUpper : ℝ) := by
    exact_mod_cast vertex_and_edge_le
  unfold NumericalEnclosure finiteAnalyticBound
  linarith

/-- Assemble the numerical certificate with an asymptotic interpolation comparison. -/
theorem upperBound_of_comparison (hcomparison : AsymptoticComparison) :
    CandidateUpperBound :=
  upperBound_of_comparison_and_enclosure hcomparison numericalEnclosure

end SatUpper.Formalization
