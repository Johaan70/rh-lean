import RhLean.ZetaBridge

open Complex

noncomputable section

/-- 2b-i: for real s > 1, ζ(s) equals the real Dirichlet series, cast to ℂ. -/
lemma zeta_ofReal_tsum {s : ℝ} (hs : 1 < s) :
    riemannZeta s = ((∑' n : ℕ, 1 / ((n:ℝ) + 1) ^ s : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [ofReal_re]; exact hs), ofReal_tsum]
  congr 1
  ext n
  rw [ofReal_div, ofReal_one, ofReal_cpow (by positivity)]
  push_cast
  norm_cast

/-- Step 2b: ζ(s) = s/(s-1) - s·F(s) for real s > 1. -/
theorem zeta_eq_F_of_lt {s : ℝ} (hs : 1 < s) :
    riemannZeta s = (s:ℂ) / ((s:ℂ) - 1) - (s:ℂ) * mellin fracTail (-(s:ℂ)) := by
  rw [F_eq_termTSum hs, ZetaAsymptotics.termTSum_of_lt hs, zeta_ofReal_tsum hs]
  generalize (∑' n : ℕ, 1 / ((n:ℝ) + 1) ^ s) = T
  have h0 : (s:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : s > 0))
  have h1 : (s:ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (ne_of_gt hs)
  push_cast
  field_simp
  ring

end

#print axioms zeta_eq_F_of_lt
