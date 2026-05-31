import NewtonLean.Descent

/-!
# Newton's Method — Convergence

We prove local quadratic (superlinear) convergence of Newton's method.

## Main results

* `newton_convergence_rate`: the precise convergence rate
  `|x_k - x*| ≤ (2m/L) · ((L/(2m)) · |x₀ - x*|)^(2^k)`
* `newton_local_convergence`: there exists `δ > 0` such that if `|x₀ - x*| < δ`
  then `|x_k - x*| ≤ 2δ · (1/2)^(2^k)` (doubly exponential decay)
-/

open scoped NNReal

noncomputable section

namespace NewtonSetup

variable (ns : NewtonSetup)

/-! ### Inductive error bound -/

/-
The error of the Newton sequence satisfies
`C · |e_k| ≤ (C · |e₀|)^(2^k)` where `C = L/(2m)`.
Equivalently, `|e_k| ≤ (1/C) · (C · |e₀|)^(2^k)`.
-/
lemma newton_seq_contraction (x₀ : ℝ) (k : ℕ) :
    ↑ns.L / (2 * ns.m) * |ns.newtonSeq x₀ k - ns.xStar| ≤
      (↑ns.L / (2 * ns.m) * |x₀ - ns.xStar|) ^ 2 ^ k := by
  induction' k with k ih;
  · norm_num [ NewtonSetup.newtonSeq ];
  · have h_step : |ns.newtonSeq x₀ (k + 1) - ns.xStar| ≤ ns.L / (2 * ns.m) * |ns.newtonSeq x₀ k - ns.xStar|^2 := by
      convert ns.newton_error_bound ( ns.newtonSeq x₀ k ) using 1 ; norm_num [ sq_abs ];
    refine le_trans ( mul_le_mul_of_nonneg_left h_step <| by exact div_nonneg ( NNReal.coe_nonneg _ ) <| mul_nonneg zero_le_two <| le_of_lt <| ns.m_pos ) ?_;
    convert pow_le_pow_left₀ ( by exact mul_nonneg ( div_nonneg ( NNReal.coe_nonneg _ ) ( mul_nonneg zero_le_two ( le_of_lt ( ns.m_pos ) ) ) ) ( abs_nonneg _ ) ) ih 2 using 1 ; ring;
    ring

/-! ### Convergence rate -/

/-
**Convergence rate.** For any starting point `x₀`,
`|x_k - x*| ≤ (2m/L) · ((L/(2m)) · |x₀ - x*|)^(2^k)`.
-/
theorem newton_convergence_rate (x₀ : ℝ) (k : ℕ) :
    |ns.newtonSeq x₀ k - ns.xStar| ≤
      2 * ns.m / ↑ns.L * (↑ns.L / (2 * ns.m) * |x₀ - ns.xStar|) ^ 2 ^ k := by
  have := ns.newton_seq_contraction x₀ k;
  convert mul_le_mul_of_nonneg_left this ( show 0 ≤ ( 2 * ns.m / ns.L : ℝ ) by exact div_nonneg ( mul_nonneg zero_le_two ( le_of_lt ( ns.m_pos ) ) ) ( le_of_lt ( ns.hL_pos ) ) ) using 1 ; ring_nf;
  simp +decide [ ns.hL_pos.ne', ns.m_pos.ne' ]

/-! ### Local convergence -/

/-
**Local quadratic convergence.** There exists `δ > 0` such that if
`|x₀ - x*| < δ` then `|x_k - x*| ≤ 2δ · (1/2)^(2^k)` for all `k`.
This gives doubly-exponential decay of the error.
-/
theorem newton_local_convergence :
    ∃ δ > 0, ∀ x₀ : ℝ, |x₀ - ns.xStar| < δ →
      ∀ k : ℕ, |ns.newtonSeq x₀ k - ns.xStar| ≤
        2 * δ * (1 / 2 : ℝ) ^ 2 ^ k := by
  refine' ⟨ ns.m / ns.L, _, _ ⟩;
  · exact div_pos ( ns.hf''_pos _ ) ( mod_cast ns.hL_pos );
  · intro x₀ hx₀ k
    have h_bound : (ns.L / (2 * ns.m)) * |x₀ - ns.xStar| < 1 / 2 := by
      convert mul_lt_mul_of_pos_left hx₀ ( show 0 < ( ns.L : ℝ ) / ( 2 * ns.m ) by exact div_pos ( mod_cast ns.hL_pos ) ( mul_pos zero_lt_two ( m_pos ns ) ) ) using 1 ; ring_nf;
      norm_num [ ne_of_gt ( m_pos ns ), ne_of_gt ( show 0 < ( ns.L : ℝ ) from mod_cast ns.hL_pos ) ];
    have := newton_convergence_rate ns x₀ k;
    refine' le_trans this _;
    gcongr;
    · exact pow_nonneg ( mul_nonneg ( div_nonneg ( NNReal.coe_nonneg _ ) ( mul_nonneg zero_le_two ( le_of_lt ( ns.m_pos ) ) ) ) ( abs_nonneg _ ) ) _;
    · exact mul_nonneg zero_le_two ( div_nonneg ( le_of_lt ( ns.m_pos ) ) ( NNReal.coe_nonneg _ ) );
    · rw [ mul_div ];
    · exact mul_nonneg ( div_nonneg ( NNReal.coe_nonneg _ ) ( mul_nonneg zero_le_two ( le_of_lt ( ns.m_pos ) ) ) ) ( abs_nonneg _ )

end NewtonSetup

end
