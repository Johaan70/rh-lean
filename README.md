# rh-lean

Lean 4 formalization toward the Riemann Hypothesis using Mathlib.

## Status

10 sorry-free theorems proven (verified with #print axioms):

- `vonMangoldt_prime` — Λ(p) = log(p) for primes
- `vonMangoldt_nonneg` — Λ(n) ≥ 0 for all n  
- `rh_no_zeros_off_line` — RH implies Re(s) = 1/2
- `rh_critical_strip` — RH holds in critical strip 0 < Re(s) < 1

Uses Mathlib's official `RiemannHypothesis` definition:
```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0)
            (_ : ¬∃ n : ℕ, s = -2 * (n + 1))
            (_ : s ≠ 1),
  s.re = 1 / 2
```

- `zeta_zero_symmetric` — ζ(s) = 0 → ζ(1−s) = 0
- `zeta_eq_functional` — functional equation in reverse direction
- `rh_reduces_to_strip` — RH follows from RH restricted to 0 < Re(s) < 1

- `zeta_zero_conj` — ζ(ρ) = 0 → ζ(ρ̄) = 0
- `zeta_zero_quadruple` — nontrivial zeros come in quadruples: ρ, 1−ρ, ρ̄, 1−ρ̄

Conjugation symmetry uses Mathlib's `riemannZeta_conj` (NumberTheory/Harmonic/ZetaAsymp).

- `nontrivial_zero_in_strip` — every nontrivial zero has 0 < Re(s) < 1

## Real zeros in the critical strip (new)

- `riemannZeta_ofReal_neg_of_mem_strip` — for real 0 < σ < 1, ζ(σ) is a negative real number
- `riemannZeta_ne_zero_of_mem_strip` — ζ has no zeros on the real interval (0, 1)
- `nontrivial_zero_im_ne_zero` — every nontrivial zero has nonzero imaginary part

Proof route: F(s) = ∫₁^∞ {x} x^(-s-1) dx as a Mellin transform (analytic on Re s > 0),
F = Mathlib's `termTSum`, ζ(s) = s/(s-1) - s·F(s) for s > 1, extended to 0 < σ < 1
by the identity theorem on a connected domain avoiding s = 1, then a sign argument.

## Next steps

- Connect ZetaZeros topology to critical strip
- Formalize Selberg trace formula
- Attack sorry #1: geodesic-prime bijection

## Build

```bash
lake update
lake build RhLean
```
