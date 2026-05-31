import Mathlib

/-!
# Newton's Method — Definitions

This file defines the setup for Newton's method in one dimension (f : ℝ → ℝ),
along with the Newton step and Newton sequence.
-/

open scoped NNReal

noncomputable section

/-- Configuration for Newton's method in one dimension. -/
structure NewtonSetup where
  /-- The objective function. -/
  f : ℝ → ℝ
  /-- Lipschitz constant for the second derivative. -/
  L : ℝ≥0
  /-- The unique minimiser. -/
  xStar : ℝ
  /-- `f` is differentiable. -/
  hDiff : Differentiable ℝ f
  /-- `f'` is differentiable (so `f''` exists everywhere). -/
  hDiff' : Differentiable ℝ (deriv f)
  /-- Strict convexity: `f'' > 0` everywhere. -/
  hf''_pos : ∀ x, 0 < deriv (deriv f) x
  /-- The Hessian (second derivative) is `L`-Lipschitz. -/
  hLip : LipschitzWith L (deriv (deriv f))
  /-- `xStar` is a critical point (`f'(xStar) = 0`). -/
  hCrit : deriv f xStar = 0
  /-- The Lipschitz constant is positive. -/
  hL_pos : (0 : ℝ) < L
  /-- `f''(xStar)` is a global lower bound for `f''`.
      This holds e.g. when `f''` is convex and minimised at `xStar`. -/
  hf''_min : ∀ x, deriv (deriv f) xStar ≤ deriv (deriv f) x

namespace NewtonSetup

/-- The first derivative of `f`. -/
def f' (ns : NewtonSetup) : ℝ → ℝ := deriv ns.f

/-- The second derivative of `f`. -/
def f'' (ns : NewtonSetup) : ℝ → ℝ := deriv (deriv ns.f)

/-- `m = f''(xStar)`, the curvature at the minimiser. -/
def m (ns : NewtonSetup) : ℝ := deriv (deriv ns.f) ns.xStar

/-- One step of Newton's method: `x ↦ x - f'(x) / f''(x)`. -/
def newtonStep (ns : NewtonSetup) (x : ℝ) : ℝ :=
  x - deriv ns.f x / deriv (deriv ns.f) x

/-- The Newton sequence starting from `x₀`. -/
def newtonSeq (ns : NewtonSetup) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => ns.newtonStep (ns.newtonSeq x₀ n)

/-! ### Basic properties -/

variable (ns : NewtonSetup)

lemma m_pos : 0 < ns.m := ns.hf''_pos ns.xStar

lemma f''_pos (x : ℝ) : 0 < ns.f'' x := ns.hf''_pos x

lemma f''_ne_zero (x : ℝ) : ns.f'' x ≠ 0 := ne_of_gt (ns.f''_pos x)

lemma m_le_f'' (x : ℝ) : ns.m ≤ ns.f'' x := ns.hf''_min x

lemma f'_eq : ns.f' = deriv ns.f := rfl

lemma f''_eq : ns.f'' = deriv (deriv ns.f) := rfl

lemma m_eq : ns.m = deriv (deriv ns.f) ns.xStar := rfl

lemma newtonStep_def (x : ℝ) :
    ns.newtonStep x = x - ns.f' x / ns.f'' x := rfl

lemma newtonSeq_zero (x₀ : ℝ) : ns.newtonSeq x₀ 0 = x₀ := rfl

lemma newtonSeq_succ (x₀ : ℝ) (n : ℕ) :
    ns.newtonSeq x₀ (n + 1) = ns.newtonStep (ns.newtonSeq x₀ n) := rfl

end NewtonSetup

end
