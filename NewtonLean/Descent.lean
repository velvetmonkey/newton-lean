import NewtonLean.Defs

/-!
# Newton's Method — Descent Lemmas

We prove that Newton's step is well-defined (since `f'' > 0` everywhere) and
establish the local quadratic error bound:

  `|x_{k+1} - x*| ≤ (L / (2 m)) · |x_k - x*|²`

where `m = f''(x*)`.

The proof avoids integrals entirely by using a **monotonicity argument**:
define the auxiliary function `U(y) = f'(y) - f''(x)(y - x*) + (L/2)(x - y)²`
and show `U' ≤ 0` (resp. `U' ≥ 0`) on the relevant interval, so that
`U(x) ≤ U(x*)`, yielding `f'(x) - f''(x)(x - x*) ≤ (L/2)(x - x*)²`.
-/

open scoped NNReal

noncomputable section

namespace NewtonSetup

variable (ns : NewtonSetup)

/-! ### Well-definedness -/

/-- `f'' > 0` everywhere, so the Newton step denominator is never zero. -/
theorem newton_step_well_defined (x : ℝ) : 0 < deriv (deriv ns.f) x :=
  ns.hf''_pos x

/-! ### Key technical bound -/

/-
**Key bound (upper, x ≥ x*).**
`f'(x) - f''(x)(x - x*) ≤ (L/2)(x - x*)²` when `x* ≤ x`.

Proof: let `U(y) = f'(y) - f''(x)(y - x*) + (L/2)(x - y)²`. Then `U(x*) = (L/2)(x - x*)²`,
`U(x) = f'(x) - f''(x)(x - x*)`, and `U'(y) = f''(y) - f''(x) + L(y - x) ≤ 0`
for `y ∈ [x*, x]` (using `f''(y) - f''(x) ≤ L(x - y)`). So `U` is antitone,
giving `U(x) ≤ U(x*)`.
-/
lemma key_upper_bound_ge (x : ℝ) (hge : ns.xStar ≤ x) :
    deriv ns.f x - deriv (deriv ns.f) x * (x - ns.xStar) ≤
      ↑ns.L / 2 * (x - ns.xStar) ^ 2 := by
  by_contra! h_contra;
  -- Define U(y) = f'(y) - f''(x)*(y - xStar) + (L/2)*(x - y)^2.
  set U : ℝ → ℝ := fun y => deriv ns.f y - deriv (deriv ns.f) x * (y - ns.xStar) + (ns.L / 2) * (x - y)^2;
  -- By definition of $U$, we know that $U'(y) = f''(y) - f''(x) + L(y - x)$.
  have hU_deriv : ∀ y, deriv U y = deriv (deriv ns.f) y - deriv (deriv ns.f) x + ns.L * (y - x) := by
    intro y; norm_num [ U, mul_comm, sub_sq, mul_assoc, mul_left_comm, ns.hDiff.differentiableAt, ns.hDiff'.differentiableAt ] ; ring;
  -- Since $U$ is differentiable and $U'(y) \leq 0$ for $y \in [x*, x]$, we can apply the Mean Value Theorem to $U$ on this interval.
  have hU_mvt : ∀ y ∈ Set.Icc ns.xStar x, y < x → ∃ c ∈ Set.Ioo y x, deriv U c = (U x - U y) / (x - y) := by
    intros y hy hyx; apply_rules [ exists_deriv_eq_slope _, hyx ];
    · exact ContinuousOn.add ( ContinuousOn.sub ( ns.hDiff'.continuous.continuousOn ) ( ContinuousOn.mul continuousOn_const ( continuousOn_id.sub continuousOn_const ) ) ) ( ContinuousOn.mul continuousOn_const ( ContinuousOn.pow ( continuousOn_const.sub continuousOn_id ) 2 ) );
    · exact DifferentiableOn.add ( DifferentiableOn.sub ( ns.hDiff'.differentiableOn ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( differentiableOn_id.sub_const _ ) ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.pow ( differentiableOn_id.const_sub _ ) _ ) );
  -- Since $U'(y) \leq 0$ for $y \in [x*, x]$, we have $U(x) \leq U(y)$ for all $y \in [x*, x]$.
  have hU_le : ∀ y ∈ Set.Icc ns.xStar x, y < x → U x ≤ U y := by
    intros y hy hyx
    obtain ⟨c, hc⟩ := hU_mvt y hy hyx
    have h_deriv_nonpos : deriv U c ≤ 0 := by
      have h_deriv_nonpos : |deriv (deriv ns.f) c - deriv (deriv ns.f) x| ≤ ns.L * |c - x| := by
        exact ns.hLip.dist_le_mul c x;
      cases abs_cases ( deriv ( deriv ns.f ) c - deriv ( deriv ns.f ) x ) <;> cases abs_cases ( c - x ) <;> nlinarith [ hU_deriv c, hc.1.1, hc.1.2 ];
    rw [ hc.2, div_le_iff₀ ] at h_deriv_nonpos <;> linarith;
  grind +suggestions

/-
**Key bound (upper, x ≤ x*).**
Same bound when `x ≤ x*`, using monotonicity of `U` on `[x, x*]`.
-/
lemma key_upper_bound_le (x : ℝ) (hle : x ≤ ns.xStar) :
    deriv ns.f x - deriv (deriv ns.f) x * (x - ns.xStar) ≤
      ↑ns.L / 2 * (x - ns.xStar) ^ 2 := by
  -- Define U(y) = f'(y) - f''(x)*(y - xStar) + (L/2)*(x - y)^2.
  set U : ℝ → ℝ := fun y => deriv ns.f y - deriv (deriv ns.f) x * (y - ns.xStar) + (↑ns.L / 2) * (x - y)^2;
  -- Since $U$ is monotone on $[x, x*]$, we have $U(x) \leq U(x*)$.
  have hU_le_UxStar : U x ≤ U ns.xStar := by
    have hU_mono : ∀ y ∈ Set.Ioo x ns.xStar, deriv U y ≥ 0 := by
      intro y hy; erw [ deriv_add, deriv_sub ] <;> norm_num [ ns.hDiff.differentiableAt, ns.hDiff'.differentiableAt ] ; ring_nf ; (
      norm_num [ mul_assoc, mul_comm x ];
      have := ns.hLip.dist_le_mul x y;
      rw [ Real.dist_eq, Real.dist_eq ] at this ; cases abs_cases ( deriv ( deriv ns.f ) x - deriv ( deriv ns.f ) y ) <;> cases abs_cases ( x - y ) <;> nlinarith [ hy.1, hy.2 ]);
      fun_prop;
    by_contra h_contra;
    have := exists_deriv_eq_slope U ( show x < ns.xStar from lt_of_le_of_ne hle <| by aesop_cat );
    exact absurd ( this ( by exact ContinuousOn.add ( ContinuousOn.sub ( ns.hDiff'.continuous.continuousOn ) ( ContinuousOn.mul continuousOn_const ( continuousOn_id.sub continuousOn_const ) ) ) ( ContinuousOn.mul continuousOn_const ( ContinuousOn.pow ( continuousOn_const.sub continuousOn_id ) 2 ) ) ) ( by exact fun y hy => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( DifferentiableAt.sub ( ns.hDiff'.differentiableAt ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( differentiableAt_id.sub ( differentiableAt_const _ ) ) ) ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.pow ( differentiableAt_id.const_sub _ ) 2 ) ) ) ) ) ( by rintro ⟨ c, hc₁, hc₂ ⟩ ; rw [ eq_div_iff ] at hc₂ <;> nlinarith [ hU_mono c hc₁, hc₁.1, hc₁.2 ] );
  simp +zetaDelta at *;
  linarith [ ns.hCrit ]

/-
**Key bound (lower, x ≥ x*).**
`-(f'(x) - f''(x)(x - x*)) ≤ (L/2)(x - x*)²`, analogous to the upper bound.
-/
lemma key_lower_bound_ge (x : ℝ) (hge : ns.xStar ≤ x) :
    -(deriv ns.f x - deriv (deriv ns.f) x * (x - ns.xStar)) ≤
      ↑ns.L / 2 * (x - ns.xStar) ^ 2 := by
  -- Let $V(y) = -f'(y) + f''(x)(y - x*) + \frac{L}{2}(x - y)^2$.
  set V : ℝ → ℝ := fun y => -deriv ns.f y + deriv (deriv ns.f) x * (y - ns.xStar) + (ns.L / 2) * (x - y)^2;
  -- We need to show that $V$ is non-increasing on $[x^*, x]$.
  have hV_noninc : ∀ y ∈ Set.Icc ns.xStar x, ∀ z ∈ Set.Icc ns.xStar x, y ≤ z → V z ≤ V y := by
    -- We need to show that $V'(y) \leq 0$ for all $y \in [x^*, x]$.
    have hV_deriv_nonpos : ∀ y ∈ Set.Icc ns.xStar x, deriv V y ≤ 0 := by
      intro y hy;
      -- By definition of $V$, we know that its derivative is $-f''(y) + f''(x) + L(y - x)$.
      have hV_deriv : deriv V y = -deriv (deriv ns.f) y + deriv (deriv ns.f) x + ns.L * (y - x) := by
        norm_num +zetaDelta at *;
        norm_num [ sub_sq, mul_comm, ns.hDiff.differentiableAt, ns.hDiff'.differentiableAt ] ; ring;
      have := ns.hLip.dist_le_mul y x;
      norm_num [ Real.dist_eq ] at *;
      cases abs_cases ( deriv ( deriv ns.f ) y - deriv ( deriv ns.f ) x ) <;> cases abs_cases ( y - x ) <;> nlinarith [ show ( ns.L : ℝ ) ≥ 0 by positivity ];
    apply_rules [ antitoneOn_of_deriv_nonpos ];
    · exact convex_Icc _ _;
    · exact ContinuousOn.add ( ContinuousOn.add ( ContinuousOn.neg ( ns.hDiff'.continuous.continuousOn ) ) ( ContinuousOn.mul continuousOn_const ( continuousOn_id.sub continuousOn_const ) ) ) ( ContinuousOn.mul continuousOn_const ( ContinuousOn.pow ( continuousOn_const.sub continuousOn_id ) 2 ) );
    · exact DifferentiableOn.add ( DifferentiableOn.add ( DifferentiableOn.neg ( ns.hDiff'.differentiableOn ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( differentiableOn_id.sub_const _ ) ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.pow ( differentiableOn_id.const_sub _ ) _ ) );
    · exact fun y hy => hV_deriv_nonpos y <| interior_subset hy;
  simp +zetaDelta at *;
  have := hV_noninc ns.xStar le_rfl hge x hge le_rfl hge; norm_num at this; linarith [ ns.hCrit ] ;

/-
**Key bound (lower, x ≤ x*).**
-/
lemma key_lower_bound_le (x : ℝ) (hle : x ≤ ns.xStar) :
    -(deriv ns.f x - deriv (deriv ns.f) x * (x - ns.xStar)) ≤
      ↑ns.L / 2 * (x - ns.xStar) ^ 2 := by
  by_contra! h_contra;
  -- Apply the mean value theorem to the interval $[x, x^*]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x ns.xStar, deriv (fun y => -deriv ns.f y + deriv (deriv ns.f) x * (y - ns.xStar) + (ns.L / 2) * (x - y) ^ 2) c = ( (-deriv ns.f ns.xStar + deriv (deriv ns.f) x * (ns.xStar - ns.xStar) + (ns.L / 2) * (x - ns.xStar) ^ 2) - (-deriv ns.f x + deriv (deriv ns.f) x * (x - ns.xStar) + (ns.L / 2) * (x - x) ^ 2) ) / (ns.xStar - x) := by
    apply_rules [ exists_deriv_eq_slope ];
    · cases lt_or_eq_of_le hle <;> simp_all +decide;
      linarith [ ns.hCrit ];
    · exact ContinuousOn.add ( ContinuousOn.add ( ContinuousOn.neg ( ns.hDiff'.continuous.continuousOn ) ) ( ContinuousOn.mul continuousOn_const ( continuousOn_id.sub continuousOn_const ) ) ) ( ContinuousOn.mul continuousOn_const ( ContinuousOn.pow ( continuousOn_const.sub continuousOn_id ) 2 ) );
    · exact DifferentiableOn.add ( DifferentiableOn.add ( DifferentiableOn.neg ( ns.hDiff'.differentiableOn ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( differentiableOn_id.sub_const _ ) ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.pow ( differentiableOn_id.const_sub _ ) _ ) );
  -- By definition of $V$, we know that its derivative is $V'(y) = -f''(y) + f''(x) + L(y - x)$.
  have hV_deriv : deriv (fun y => -deriv ns.f y + deriv (deriv ns.f) x * (y - ns.xStar) + (ns.L / 2) * (x - y) ^ 2) c = -deriv (deriv ns.f) c + deriv (deriv ns.f) x + ns.L * (c - x) := by
    norm_num [ sub_sq, mul_comm, ns.hDiff.differentiableAt, ns.hDiff'.differentiableAt ] ; ring;
  -- Since $c \in (x, x^*)$, we have $f''(c) - f''(x) \leq L(c - x)$ by the Lipschitz condition.
  have h_lip : deriv (deriv ns.f) c - deriv (deriv ns.f) x ≤ ns.L * (c - x) := by
    have := ns.hLip.dist_le_mul c x;
    rw [ dist_eq_norm, dist_eq_norm ] at this;
    rw [ Real.norm_eq_abs, Real.norm_eq_abs ] at this ; rw [ abs_of_nonneg ( sub_nonneg.mpr hc.1.1.le ) ] at this ; linarith [ abs_le.mp this ];
  rw [ eq_div_iff ] at hc <;> nlinarith [ hc.1.1, hc.1.2, ns.hCrit ]

/-
**Key bound (combined).**
`|f'(x) - f''(x)(x - x*)| ≤ (L/2)(x - x*)²` for all `x`.
-/
theorem key_bound (x : ℝ) :
    |deriv ns.f x - deriv (deriv ns.f) x * (x - ns.xStar)| ≤
      ↑ns.L / 2 * (x - ns.xStar) ^ 2 := by
  by_cases hge : ns.xStar ≤ x;
  · exact abs_le.mpr ⟨ by linarith [ key_lower_bound_ge ns x hge ], by linarith [ key_upper_bound_ge ns x hge ] ⟩;
  · exact abs_le.mpr ⟨ by linarith [ key_lower_bound_le ns x ( le_of_not_ge hge ) ], by linarith [ key_upper_bound_le ns x ( le_of_not_ge hge ) ] ⟩

/-! ### Newton step error formula -/

/-
The Newton step error can be written as
`newtonStep x - x* = -(f'(x) - f''(x)(x - x*)) / f''(x)`.
-/
lemma newton_step_error (x : ℝ) :
    ns.newtonStep x - ns.xStar =
      -(deriv ns.f x - deriv (deriv ns.f) x * (x - ns.xStar)) /
        deriv (deriv ns.f) x := by
  rw [ eq_div_iff ] <;> norm_num [ NewtonSetup.newtonStep_def ] ; ring_nf;
  · unfold NewtonSetup.f' NewtonSetup.f''; ring_nf;
    linarith [ mul_inv_cancel_left₀ ( ne_of_gt ( ns.newton_step_well_defined x ) ) ( deriv ns.f x ) ];
  · exact ne_of_gt ( ns.f''_pos x )

/-! ### Main error bound -/

/-
**Quadratic error bound for Newton's method.**
`|x_{k+1} - x*| ≤ (L / (2 m)) · |x_k - x*|²`
where `m = f''(x*)`.
-/
theorem newton_error_bound (x : ℝ) :
    |ns.newtonStep x - ns.xStar| ≤
      ↑ns.L / (2 * ns.m) * (x - ns.xStar) ^ 2 := by
  rw [ newton_step_error, abs_div ];
  convert div_le_div_of_nonneg_right ( ns.key_bound x ) ( abs_nonneg _ ) |> ( fun h => h.trans _ ) using 1;
  rw [ abs_neg ];
  convert div_le_div_of_nonneg_left _ _ ( show |deriv ( deriv ns.f ) x| ≥ ns.m from _ ) using 1;
  · ring;
  · positivity;
  · exact ns.hf''_pos ns.xStar;
  · exact le_trans ( ns.m_le_f'' x ) ( le_abs_self _ )

end NewtonSetup

end
