import RhLean.ZetaExtend

open Complex Set MeasureTheory

noncomputable section

/-- Step 4a: F = termTSum for all s > 0. Same proof as `F_eq_termTSum`;
    the hypothesis s > 1 was only ever used as 0 < s. -/
theorem F_eq_termTSum_of_pos {s : ℝ} (hs : 0 < s) :
    mellin fracTail (-(s : ℂ)) = ((ZetaAsymptotics.termTSum s : ℝ) : ℂ) := by
  have hint : IntegrableOn (Fint s) (⋃ n : ℕ, Ico ((n:ℝ) + 1) ((n:ℝ) + 2)) := by
    rw [iUnion_Ico_eq_Ici]
    refine (fracTail_mellinConvergent hs).mono_set ?_
    intro t ht
    rw [mem_Ici] at ht
    rw [mem_Ioi]
    linarith
  have hsum := hasSum_integral_iUnion (fun _ => measurableSet_Ico)
    Ico_pairwise_disjoint hint
  simp_rw [integral_piece hs, iUnion_Ico_eq_Ici] at hsum
  rw [mellin_eq_integral_Ici, ← hsum.tsum_eq]
  unfold ZetaAsymptotics.termTSum
  rw [ofReal_tsum]

/-- Step 4b: termTSum is a sum of nonnegative terms. -/
lemma termTSum_nonneg (s : ℝ) : 0 ≤ ZetaAsymptotics.termTSum s :=
  tsum_nonneg fun n => ZetaAsymptotics.term_nonneg (n + 1) s

/-- Step 4c: for real 0 < σ < 1, ζ(σ) is a negative real number. -/
theorem riemannZeta_ofReal_neg_of_mem_strip {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ r : ℝ, r < 0 ∧ riemannZeta σ = r := by
  refine ⟨σ / (σ - 1) - σ * ZetaAsymptotics.termTSum σ, ?_, ?_⟩
  · have hdiv : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg h0 (by linarith)
    have hmul : 0 ≤ σ * ZetaAsymptotics.termTSum σ :=
      mul_nonneg h0.le (termTSum_nonneg σ)
    linarith
  · rw [zeta_eq_F_of_mem_strip h0 h1, F_eq_termTSum_of_pos h0]
    push_cast
    ring

/-- Step 4d: ζ has no zeros on the real interval (0, 1). -/
theorem riemannZeta_ne_zero_of_mem_strip {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta σ ≠ 0 := by
  obtain ⟨r, hr, heq⟩ := riemannZeta_ofReal_neg_of_mem_strip h0 h1
  rw [heq]
  exact_mod_cast hr.ne

/-- Every nontrivial zero of ζ has nonzero imaginary part. -/
theorem nontrivial_zero_im_ne_zero (s : ℂ) (hzero : riemannZeta s = 0)
    (hntriv : ¬∃ n : ℕ, s = -2 * (↑n + 1)) : s.im ≠ 0 := by
  intro him
  obtain ⟨h0, h1⟩ := nontrivial_zero_in_strip s hzero hntriv
  have hs : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hs] at hzero
  exact riemannZeta_ne_zero_of_mem_strip h0 h1 hzero

end

#print axioms riemannZeta_ne_zero_of_mem_strip
#print axioms nontrivial_zero_im_ne_zero
