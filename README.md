# rh-lean

Lean 4 formalization toward the Riemann Hypothesis using Mathlib.

## Status

4 sorry-free theorems proven:

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

## Next steps

- Connect ZetaZeros topology to critical strip
- Formalize Selberg trace formula
- Attack sorry #1: geodesic-prime bijection

## Build

```bash
lake update
lake build RhLean
```
