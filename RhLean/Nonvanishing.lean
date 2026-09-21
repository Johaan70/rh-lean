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

theorem rh_reduces_to_strip :
    (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) →
    RiemannHypothesis := by
  intro h s hzero hntriv hne1
  by_cases hge : 1 ≤ s.re
  · exact absurd hzero (riemannZeta_ne_zero_of_one_le_re hge)
  · by_cases hle : s.re ≤ 0
    · exfalso
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
      -- Extract 1 - s = 2k + 1
      have hone_sub_s : (1 : ℂ) - s = 2 * k + 1 := by
        have : (π : ℂ) * ((1 - s) - (2 * k + 1)) = 0 := by
          have hk2 : ↑π * (1 - s) / 2 = (2 * ↑k + 1) * ↑π / 2 := hk
          field_simp [hpi] at hk2
          linear_combination hk2
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 hpi
        · linarith [h1]
      -- Real part: simp fully
      have hk_re : (1 : ℝ) - s.re = 2 * (k : ℝ) + 1 := by
        have := congr_arg Complex.re hone_sub_s
        simp only [sub_re, one_re, add_re, mul_re, intCast_re, intCast_im,
                   ofReal_re, ofReal_im, mul_zero, sub_zero, one_re] at this
        linarith
      -- Imag part
      have hk_im : s.im = 0 := by
        have := congr_arg Complex.im hone_sub_s
        simp only [sub_im, one_im, add_im, mul_im, intCast_re, intCast_im,
                   ofReal_re, ofReal_im, mul_zero, add_zero, one_im] at this
        linarith
      have hse_re : s.re = -2 * (k : ℝ) := by linarith
      have hknn : 0 ≤ k := by exact_mod_cast (show (0 : ℝ) ≤ k by linarith)
      have hkne : k ≠ 0 := by
        intro heq; apply hs0; apply Complex.ext
        · simp only [zero_re]; push_cast [heq] at hse_re; linarith
        · simp only [zero_im]; linarith
      have hkpos : 0 < k := lt_of_le_of_ne hknn (Ne.symm hkne)
      -- s = -2k
      have hs_eq : s = -2 * (k : ℂ) := by
        apply Complex.ext
        · simp only [neg_mul, neg_re, mul_re, ofReal_re, intCast_re,
                     ofReal_im, intCast_im, mul_zero, sub_zero]; push_cast; linarith
        · simp only [neg_mul, neg_im, mul_im, ofReal_re, intCast_re,
                     ofReal_im, intCast_im, mul_zero, add_zero]; push_cast; linarith
      -- Apply hntriv: s = -2*(k-1+1) = -2*(n+1) where n = k-1
      apply hntriv ⟨(k - 1).toNat, by
        rw [hs_eq]
        apply Complex.ext
        · simp only [neg_mul, neg_re, mul_re, ofReal_re, intCast_re,
                     ofReal_im, intCast_im, mul_zero, sub_zero, add_re, one_re, natCast_re]
          have hk1 : (0 : ℤ) ≤ k - 1 := by omega
          have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg hk1
          push_cast [this]; push_cast; ring
        · simp only [neg_mul, neg_im, mul_im, ofReal_re, intCast_re,
                     ofReal_im, intCast_im, mul_zero, add_zero, add_im, one_im, natCast_im]
          push_cast; linarith⟩
    · exact h s hzero (lt_of_not_ge hle) (lt_of_not_ge hge)
