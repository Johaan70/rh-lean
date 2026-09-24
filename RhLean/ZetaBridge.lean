import RhLean.ZetaStrip
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open Complex Set Filter MeasureTheory

noncomputable section

/-- Integrand of F at real exponent s: t^(-s-1) · g(t). -/
def Fint (s : ℝ) (t : ℝ) : ℂ := (t : ℂ) ^ (-(s : ℂ) - 1) • fracTail t

/-- The Mellin integral converges for s > 0 (reuses step 1 bounds). -/
lemma fracTail_mellinConvergent {s : ℝ} (hs : 0 < s) :
    MellinConvergent fracTail (-(s : ℂ)) :=
  mellinConvergent_of_isBigO_rpow fracTail_locallyIntegrableOn fracTail_isBigO_top
    (by rw [neg_re, ofReal_re]; linarith) (fracTail_isBigO_bot (-s - 1))
    (by rw [neg_re, ofReal_re]; linarith)

/-- 2a-i: the intervals [n+1, n+2) cover [1, ∞). -/
lemma iUnion_Ico_eq_Ici :
    (⋃ n : ℕ, Ico ((n:ℝ) + 1) ((n:ℝ) + 2)) = Ici (1:ℝ) := by
  ext x
  simp only [mem_iUnion, mem_Ico, mem_Ici]
  constructor
  · rintro ⟨n, h1, _⟩
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro hx
    refine ⟨⌊x - 1⌋₊, ?_, ?_⟩
    · have := Nat.floor_le (show (0:ℝ) ≤ x - 1 by linarith)
      linarith
    · have := Nat.lt_floor_add_one (x - 1)
      linarith

/-- 2a-ii: the intervals are pairwise disjoint. -/
lemma Ico_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint (fun n : ℕ => Ico ((n:ℝ) + 1) ((n:ℝ) + 2))) := by
  intro i j hij
  unfold Function.onFun
  rw [Set.disjoint_left]
  intro x hx hy
  rw [mem_Ico] at hx hy
  have h1 : (i:ℝ) < (j:ℝ) + 1 := by linarith [hx.1, hy.2]
  have h2 : (j:ℝ) < (i:ℝ) + 1 := by linarith [hy.1, hx.2]
  have h1' : i < j + 1 := by exact_mod_cast h1
  have h2' : j < i + 1 := by exact_mod_cast h2
  exact hij (by omega)

/-- 2a-iii: g = 0 on (0,1), so the Mellin integral lives on [1, ∞). -/
lemma mellin_eq_integral_Ici (s : ℝ) :
    mellin fracTail (-(s : ℂ)) = ∫ t in Ici (1:ℝ), Fint s t := by
  sorry

/-- 2a-iv: each piece equals Mathlib's `term`. -/
lemma integral_piece {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∫ t in Ico ((n:ℝ) + 1) ((n:ℝ) + 2), Fint s t =
      ((ZetaAsymptotics.term (n + 1) s : ℝ) : ℂ) := by
  sorry

/-- Step 2a: our Mellin F equals Mathlib's termTSum for real s > 1. -/
theorem F_eq_termTSum {s : ℝ} (hs : 1 < s) :
    mellin fracTail (-(s : ℂ)) = ((ZetaAsymptotics.termTSum s : ℝ) : ℂ) := by
  have hint : IntegrableOn (Fint s) (⋃ n : ℕ, Ico ((n:ℝ) + 1) ((n:ℝ) + 2)) := by
    rw [iUnion_Ico_eq_Ici]
    refine (fracTail_mellinConvergent (by linarith)).mono_set ?_
    intro t ht
    rw [mem_Ici] at ht
    rw [mem_Ioi]
    linarith
  have hsum := hasSum_integral_iUnion (fun _ => measurableSet_Ico)
    Ico_pairwise_disjoint hint
  simp_rw [integral_piece (by linarith : (0:ℝ) < s), iUnion_Ico_eq_Ici] at hsum
  rw [mellin_eq_integral_Ici, ← hsum.tsum_eq]
  unfold ZetaAsymptotics.termTSum
  rw [ofReal_tsum]

end

#print axioms F_eq_termTSum
