import RhLean.ZetaFormula
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex Set Filter Topology

noncomputable section

/-- G(s) = s/(s-1) - s·F(s), the candidate formula for ζ. -/
def zetaG (s : ℂ) : ℂ := s / (s - 1) - s * mellin fracTail (-s)

/-- V = strip ∪ upper bridge ∪ right half-plane. Avoids s = 1. -/
def domV : Set ℂ :=
  ({s : ℂ | 0 < s.re} ∩ {s | s.re < 1}) ∪ ({s : ℂ | 0 < s.re} ∩ {s | 0 < s.im})
    ∪ {s : ℂ | 1 < s.re}

lemma domV_subset_re_pos : domV ⊆ {s : ℂ | 0 < s.re} := by
  intro s hs
  rcases hs with (h | h) | h
  · exact h.1
  · exact h.1
  · have h' : 1 < s.re := h
    show 0 < s.re
    linarith

lemma domV_subset_ne_one : domV ⊆ {1}ᶜ := by
  intro s hs heq
  rw [mem_singleton_iff] at heq
  subst heq
  rcases hs with (h | h) | h
  · exact absurd h.2 (by norm_num)
  · exact absurd h.2 (by norm_num)
  · exact absurd h (by norm_num)

lemma domV_isOpen : IsOpen domV := by
  unfold domV
  exact (((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).union
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_const continuous_im))).union
    (isOpen_lt continuous_const continuous_re)

lemma domV_isPreconnected : IsPreconnected domV := by
  unfold domV
  have hA : Convex ℝ ({s : ℂ | 0 < s.re} ∩ {s | s.re < 1}) :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have hB : Convex ℝ ({s : ℂ | 0 < s.re} ∩ {s | 0 < s.im}) :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  have hC : Convex ℝ {s : ℂ | 1 < s.re} := convex_halfSpace_re_gt 1
  have hAB : IsPreconnected (({s : ℂ | 0 < s.re} ∩ {s | s.re < 1}) ∪
      ({s : ℂ | 0 < s.re} ∩ {s | 0 < s.im})) :=
    IsPreconnected.union (⟨1/2, 1⟩ : ℂ) (by norm_num) (by norm_num)
      hA.isPreconnected hB.isPreconnected
  exact IsPreconnected.union (⟨2, 1⟩ : ℂ) (by norm_num) (by norm_num)
    hAB hC.isPreconnected

lemma two_mem_domV : (2 : ℂ) ∈ domV := by
  unfold domV
  norm_num

lemma zetaG_differentiableOn : DifferentiableOn ℂ zetaG domV := by
  intro s hs
  have hre : 0 < s.re := domV_subset_re_pos hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr (domV_subset_ne_one hs)
  have hF : DifferentiableAt ℂ (fun z : ℂ => mellin fracTail (-z)) s :=
    (F_differentiableOn s hre).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hre)
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z / (z - 1)) s :=
    differentiableAt_id.div (differentiableAt_id.sub_const 1) hne
  exact (h1.sub (differentiableAt_id.mul hF)).differentiableWithinAt

/-- ζ = G frequently near 2, using equality on real s > 1. -/
lemma zeta_eq_zetaG_frequently : ∃ᶠ z in 𝓝[≠] (2 : ℂ), riemannZeta z = zetaG z := by
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (2:ℝ)) (𝓝[≠] (2:ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := (continuous_ofReal.tendsto (2:ℝ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (2:ℝ) ≤ 𝓝 2)
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
      exact_mod_cast hx
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (2:ℝ), riemannZeta ((x:ℝ):ℂ) = zetaG ((x:ℝ):ℂ) := by
    have h12 : ∀ᶠ x : ℝ in 𝓝 (2:ℝ), 1 < x := lt_mem_nhds (by norm_num)
    exact (h12.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (2:ℝ) ≤ 𝓝 2)).mono
      fun x hx => zeta_eq_F_of_lt hx
  exact ht.frequently hev.frequently

/-- Step 3: identity theorem. ζ = G on all of V. -/
theorem zeta_eq_zetaG_on_domV : EqOn riemannZeta zetaG domV :=
  AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (analyticOn_riemannZeta.mono domV_subset_ne_one)
    (zetaG_differentiableOn.analyticOnNhd domV_isOpen)
    domV_isPreconnected two_mem_domV zeta_eq_zetaG_frequently

/-- Special case for step 4: real σ in (0, 1). -/
theorem zeta_eq_F_of_mem_strip {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta σ = (σ:ℂ) / ((σ:ℂ) - 1) - (σ:ℂ) * mellin fracTail (-(σ:ℂ)) :=
  zeta_eq_zetaG_on_domV (Or.inl (Or.inl ⟨by simpa using h0, by simpa using h1⟩))

end

#print axioms zeta_eq_F_of_mem_strip
