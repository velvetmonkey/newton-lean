# newton-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](NewtonLean)

NewtonLean is a Lean 4 / Mathlib formalization of one-dimensional Newton's
method near a minimiser. The development works with a real-valued objective
`f : ℝ → ℝ`, a strictly positive second derivative, a Lipschitz second
derivative, and a critical point `xStar`. Under the stated curvature hypotheses,
the formalized Newton iteration satisfies a quadratic error recurrence and a
local doubly exponential convergence bound.

The source is generated from an Aristotle proof run and contains no `sorry` or
`admit`. It uses the standard Lean axioms only.

## Mathematical Setting

The main structure is `NewtonSetup`, bundling:

- an objective `f : ℝ → ℝ`;
- a nonnegative Lipschitz constant `L : ℝ≥0` for the second derivative;
- a minimiser or critical point `xStar : ℝ`;
- differentiability of `f` and `deriv f`;
- strict positive curvature `deriv (deriv f) x > 0`;
- criticality `deriv f xStar = 0`;
- positivity of `L`;
- a lower-bound condition saying `f''(xStar) ≤ f''(x)` for all `x`.

The Newton step is

```lean
newtonStep x = x - f' x / f'' x
```

and the Newton sequence is the iteration of this step from an initial point
`x₀`.

## Theorem Inventory

| Module | Name | Statement |
| --- | --- | --- |
| `NewtonLean.Defs` | `NewtonSetup.m_pos` | `0 < ns.m` |
| `NewtonLean.Defs` | `NewtonSetup.f''_pos` | `0 < ns.f'' x` |
| `NewtonLean.Defs` | `NewtonSetup.f''_ne_zero` | `ns.f'' x ≠ 0` |
| `NewtonLean.Defs` | `NewtonSetup.m_le_f''` | `ns.m ≤ ns.f'' x` |
| `NewtonLean.Descent` | `NewtonSetup.newton_step_well_defined` | `0 < deriv (deriv ns.f) x` |
| `NewtonLean.Descent` | `NewtonSetup.key_bound` | `|deriv ns.f x - deriv (deriv ns.f) x * (x - ns.xStar)| ≤ ↑ns.L / 2 * (x - ns.xStar) ^ 2` |
| `NewtonLean.Descent` | `NewtonSetup.newton_step_error` | `ns.newtonStep x - ns.xStar = -(deriv ns.f x - deriv (deriv ns.f) x * (x - ns.xStar)) / deriv (deriv ns.f) x` |
| `NewtonLean.Descent` | `NewtonSetup.newton_error_bound` | `|ns.newtonStep x - ns.xStar| ≤ ↑ns.L / (2 * ns.m) * (x - ns.xStar) ^ 2` |
| `NewtonLean.Convergence` | `NewtonSetup.newton_seq_contraction` | `↑ns.L / (2 * ns.m) * |ns.newtonSeq x₀ k - ns.xStar| ≤ (↑ns.L / (2 * ns.m) * |x₀ - ns.xStar|) ^ 2 ^ k` |
| `NewtonLean.Convergence` | `NewtonSetup.newton_convergence_rate` | `|ns.newtonSeq x₀ k - ns.xStar| ≤ 2 * ns.m / ↑ns.L * (↑ns.L / (2 * ns.m) * |x₀ - ns.xStar|) ^ 2 ^ k` |
| `NewtonLean.Convergence` | `NewtonSetup.newton_local_convergence` | `∃ δ > 0, ∀ x₀ : ℝ, |x₀ - ns.xStar| < δ → ∀ k : ℕ, |ns.newtonSeq x₀ k - ns.xStar| ≤ 2 * δ * (1 / 2 : ℝ) ^ 2 ^ k` |

## Modules

- `NewtonLean.Defs`: setup, derivatives, Newton step, and Newton sequence.
- `NewtonLean.Descent`: well-definedness and the quadratic one-step error bound.
- `NewtonLean.Convergence`: contraction, explicit convergence rate, and local
  quadratic convergence.

## Build

```bash
lake build
rg "sorry|admit" NewtonLean/
```

The library targets Lean 4.28.0 and Mathlib v4.28.0.

## Author

Ben Cassie
