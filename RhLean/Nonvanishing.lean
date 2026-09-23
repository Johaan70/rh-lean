import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open Complex Real

theorem zeta_zero_symmetric (s : ℂ)
    (hs : ∀ n : ℕ, s ≠ -↑n) (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub hs hs1, hzero, mul_zero]

theorem zeta_eq_functional (s : ℂ)
    (hs : ∀ n : ℕ, (1 - s) ≠ -↑n) (hs1 : s ≠ 0) :
    riemannZeta s =
      2 * (2 * ↑π) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
      cos (↑π * (1 - s) / 2) * riemannZeta (1 - s) := by
  have h := riemannZeta_one_sub hs (by
    intro heq; apply hs1
    have hre := congr_arg Complex.re heq
    have him := congr_arg Complex.im heq
    simp only [sub_re, one_re, sub_im, one_im] at hre him
    apply Complex.ext <;> simp <;> linarith)
  simp only [sub_sub_cancel] at h; exact h

/-- Every nontrivial zero lies in the critical strip 0 < Re(s) < 1. -/
theorem nontrivial_zero_in_strip (s : ℂ) (hzero : riemannZeta s = 0)
    (hntriv : ¬∃ n : ℕ, s = -2 * (↑n + 1)) (hne1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hle'
    have hle : s.re ≤ 0 := not_lt.mp hle'
    have hre : 1 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
    have hne_zero := riemannZeta_ne_zero_of_one_le_re hre
    by_cases hs0 : s = 0
    · rw [hs0] at hzero; norm_num [riemannZeta_zero] at hzero
    rw [zeta_eq_functional s
      (fun n heq => by
        have hren := congr_arg Complex.re heq
        simp only [sub_re, one_re, neg_re, natCast_re] at hren
        linarith [Nat.cast_nonneg (α := ℝ) n]) hs0] at hzero
    have hne_gamma : Complex.Gamma (1 - s) ≠ 0 := by
      apply Complex.Gamma_ne_zero; intro n heq
      apply hntriv ⟨n, by
        have hre2 := congr_arg Complex.re heq
        have him2 := congr_arg Complex.im heq
        simp only [sub_re, one_re, neg_re, natCast_re,
                   sub_im, one_im, neg_im, natCast_im] at hre2 him2
        apply Complex.ext <;> simp <;> linarith⟩
    have hne_exp : (2 : ℂ) * (2 * ↑π) ^ (-(1 - s)) ≠ 0 :=
      mul_ne_zero two_ne_zero
        (cpow_ne_zero_iff.mpr (Or.inl (by norm_num [pi_ne_zero])))
    have hcos : cos (↑π * (1 - s) / 2) = 0 := by
      rcases mul_eq_zero.mp hzero with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · rcases mul_eq_zero.mp h2 with h3 | h3
          · exact absurd h3 hne_exp
          · exact absurd h3 hne_gamma
        · exact h2
      · exact absurd h1 hne_zero
    rw [Complex.cos_eq_zero_iff] at hcos
    obtain ⟨k, hk⟩ := hcos
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
    have hone_sub_s : (1 : ℂ) - s = 2 * k + 1 := by
      have key : ↑π * (1 - s) = ↑π * (2 * ↑k + 1) := by
        linear_combination 2 * hk
      exact mul_left_cancel₀ hpi key
    have hre1 := congr_arg Complex.re hone_sub_s
    have him1 := congr_arg Complex.im hone_sub_s
    simp at hre1 him1
    have hk_re : s.re = -2 * k := by linarith
    have hk_im : s.im = 0 := by linarith
    have hknn : 0 ≤ k := by exact_mod_cast (show (0:ℝ) ≤ k by linarith)
    have hkne : k ≠ 0 := fun heq => hs0 (by
      apply Complex.ext
      · simp only [zero_re]; push_cast [heq] at hk_re; linarith
      · simp only [zero_im]; linarith)
    have hkpos : 0 < k := lt_of_le_of_ne hknn (Ne.symm hkne)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    have hkR : (k : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hn
    exact hntriv ⟨n, by apply Complex.ext <;> simp <;> linarith⟩
  · by_contra hge'
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge') hzero

/-- RH follows from RH restricted to the critical strip. -/
theorem rh_reduces_to_strip :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) →
    RiemannHypothesis := by
  intro h s hzero hntriv hne1
  obtain ⟨h0, h1⟩ := nontrivial_zero_in_strip s hzero hntriv hne1
  exact h s hzero h0 h1

#print axioms nontrivial_zero_in_strip
#print axioms rh_reduces_to_strip
