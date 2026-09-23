import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import RhLean.Quadruple

open Complex Set Filter Asymptotics MeasureTheory Topology

noncomputable section

/-- g(x) = {x} (fractional part) for x ≥ 1, and 0 for x < 1. -/
def fracTail : ℝ → ℂ := (Ici (1:ℝ)).indicator (fun y => ((Int.fract y : ℝ) : ℂ))

/-- g is bounded by 1. -/
lemma fracTail_norm_le (x : ℝ) : ‖fracTail x‖ ≤ 1 := by
  unfold fracTail Set.indicator
  split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  · simp

/-- g is measurable. -/
lemma fracTail_measurable : Measurable fracTail :=
  (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ici

/-- T1: g is locally integrable on (0, ∞): bounded and measurable,
    hence integrable on every compact set. -/
lemma fracTail_locallyIntegrableOn : LocallyIntegrableOn fracTail (Ioi 0) := by
  refine LocallyIntegrable.locallyIntegrableOn ?_ _
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact Integrable.of_bound fracTail_measurable.aestronglyMeasurable 1
    (Eventually.of_forall fracTail_norm_le)

/-- g = O(1) at infinity (a = 0). -/
lemma fracTail_isBigO_top : fracTail =O[atTop] (fun x : ℝ => x ^ (-(0:ℝ))) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact fracTail_norm_le x

/-- g vanishes near 0, so it is O(x^(-b)) for every b. -/
lemma fracTail_isBigO_bot (b : ℝ) : fracTail =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  have hlt : ∀ᶠ x in 𝓝[>] (0:ℝ), x < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  filter_upwards [hlt] with x hx
  have h0 : fracTail x = 0 := by
    simp [fracTail, Set.indicator, not_le.mpr hx]
  simp [h0]

/-- The Mellin transform of g is complex-differentiable for Re z < 0. -/
theorem fracTail_mellin_differentiableAt {z : ℂ} (hz : z.re < 0) :
    DifferentiableAt ℂ (mellin fracTail) z :=
  mellin_differentiableAt_of_isBigO_rpow fracTail_locallyIntegrableOn
    fracTail_isBigO_top hz (fracTail_isBigO_bot (z.re - 1)) (by linarith)

/-- F(s) = ∫₁^∞ {x} x^(-s-1) dx is analytic on the half-plane Re s > 0. -/
theorem F_differentiableOn :
    DifferentiableOn ℂ (fun s => mellin fracTail (-s)) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  have hneg : (-s).re < 0 := by rw [neg_re]; linarith
  exact ((fracTail_mellin_differentiableAt hneg).comp s
    differentiableAt_id.neg).differentiableWithinAt

end

#print axioms F_differentiableOn
