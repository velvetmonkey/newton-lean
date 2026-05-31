# newton-lean: Formal Proofs of One-Dimensional Newton Convergence in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
2026-05-31

## Abstract

`newton-lean` is a Lean 4 / Mathlib library formalising a one-dimensional Newton method convergence argument near a minimiser. The setup packages a real objective, differentiability of the first derivative, positive second derivative, Lipschitz second derivative, criticality at `xStar`, and a lower-bound condition on curvature. It proves a key Taylor-style remainder estimate, the quadratic one-step error bound, an explicit doubly exponential convergence rate, and a local quadratic convergence theorem. The development is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

Newton's method is one of the central algorithms of numerical optimisation. In one dimension, the method updates

```text
x_{k+1} = x_k - f'(x_k) / f''(x_k).
```

Near a nondegenerate minimiser, the method converges quadratically: the next error is bounded by a constant times the square of the current error. This gives the characteristic rapid local convergence of Newton iteration.

The Lean library formalises a deterministic one-dimensional version of this theorem. The proof avoids an integral Taylor theorem and instead uses a monotonicity argument to establish the key remainder bound from Lipschitz continuity of the second derivative.

## 2. Mathematical Setting

`NewtonLean/Defs.lean` defines `NewtonSetup`. It contains `f : Real -> Real`, a nonnegative Lipschitz constant `L`, a point `xStar`, differentiability assumptions for `f` and `deriv f`, strict positivity of `f''`, Lipschitz continuity of `f''`, the criticality condition `f'(xStar) = 0`, positivity of `L`, and the condition that `f''(xStar)` is a global lower bound for `f''`.

The definitions include

```text
f' x = deriv f x
f'' x = deriv (deriv f) x
m = f'' xStar
newtonStep x = x - f' x / f'' x.
```

The sequence `newtonSeq x0 k` iterates this step.

## 3. Main Theorems

The basic setup proves `m_pos`, `f''_pos`, `f''_ne_zero`, and `m_le_f''`. `Descent.lean` proves `newton_step_well_defined` and the key estimate

```text
key_bound:
  |f'(x) - f''(x) * (x - xStar)|
    <= L / 2 * (x - xStar)^2.
```

It also proves the exact error identity `newton_step_error` and the main one-step theorem

```text
newton_error_bound:
  |newtonStep x - xStar|
    <= L / (2 * m) * (x - xStar)^2.
```

`Convergence.lean` proves `newton_seq_contraction`, `newton_convergence_rate`,

```text
|x_k - xStar|
  <= 2 * m / L * ((L / (2 * m)) * |x_0 - xStar|)^(2^k),
```

and `newton_local_convergence`, which gives a radius `delta > 0` such that initial points inside that radius satisfy

```text
|x_k - xStar| <= 2 * delta * (1 / 2)^(2^k).
```

## 4. Proof Sketch

The technical heart is `key_bound`. The proof defines auxiliary functions comparing `f'` to the affine approximation with slope `f''(x)`. Lipschitz continuity of `f''` controls the derivative of these auxiliary functions on the interval between `x` and `xStar`, yielding the Taylor-style remainder inequality.

The Newton step error can then be written as the negative remainder divided by `f''(x)`. Since `f''(x) >= m > 0`, the remainder bound implies the quadratic recurrence. The convergence module iterates the recurrence after scaling the error by `L / (2m)`. The local theorem chooses a radius that makes the scaled initial error at most one half, producing the doubly exponential decay.

## 5. Relation to Sibling Libraries

`newton-lean` complements the first-order optimisation libraries. `gradient-descent-lean`, DOI `10.5281/zenodo.20472996`, proves smooth convex descent for first-order updates. `nesterov-lean`, DOI `10.5281/zenodo.20474481`, studies acceleration. `heavy-ball-lean` formalises a momentum method with geometric decay. Newton's method is second-order and local: its proof is driven by curvature and a quadratic error recurrence rather than a global first-order descent sum.

## 6. Conclusion

`newton-lean` gives a concise Lean 4 proof of one-dimensional local Newton convergence. It records the curvature hypotheses, proves the key remainder estimate, derives the one-step quadratic error bound, and solves the resulting recurrence. Future work could extend this formalisation to multidimensional Newton methods, self-concordant functions, or damped globalised variants.

## References

Kantorovich, L. V. and Akilov, G. P. (1982). *Functional Analysis*. Pergamon Press.

Nocedal, J. and Wright, S. J. (2006). *Numerical Optimization*. Springer.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *gradient-descent-lean: Formal Proofs of Gradient Descent Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20472996>

Cassie, B. (2026). *nesterov-lean: Formal Proofs of Nesterov Accelerated Gradient Descent in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20474481>
