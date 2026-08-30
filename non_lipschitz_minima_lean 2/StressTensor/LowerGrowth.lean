import StressTensor.EndpointRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Section 4: integrated lower growth

This module turns the pointwise estimate from `StressBounds` into the power
growth estimate used in (4.10).  The hypotheses are stated on the punctured
vertical segment, exactly where the singular stress formula is meaningful.
-/

namespace StressTensor

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

/-- The model singular kernel is integrable because `2 / p < 1`. -/
theorem intervalIntegrable_singularKernel
    (P : Params) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => τ ^ (-singularExponent P)) volume a b := by
  apply intervalIntegral.intervalIntegrable_rpow'
  linarith [singularExponent_lt_one P]

/-- The singular denominator on the positive half-line is the reciprocal of
the power kernel after inversion. -/
theorem one_div_singularDenominator_eq_rpow_neg
    (P : Params) {τ : ℝ} (hτ : 0 < τ) :
    1 / singularDenominator P τ = τ ^ (-singularExponent P) := by
  rw [singularDenominator, abs_of_pos hτ]
  rw [Real.rpow_neg hτ.le]
  simp [singularExponent, one_div]

/-- Closed form for the primitive of the model singularity. -/
theorem integral_singularKernel_zero_to
    (P : Params) {y : ℝ} (_hy : 0 ≤ y) :
    (∫ τ : ℝ in (0 : ℝ)..y, τ ^ (-singularExponent P)) =
      y ^ holderExponent P / holderExponent P := by
  have hexp : -1 < -singularExponent P := by
    linarith [singularExponent_lt_one P]
  rw [integral_rpow (Or.inl hexp)]
  have hholder : -singularExponent P + 1 = holderExponent P := by
    simp [holderExponent]
    ring
  rw [hholder]
  have hpos := holderExponent_pos P
  simp [Real.zero_rpow hpos.ne']

/-- Integrating the estimate `S ≥ 1/8`, `Γ₁ ≥ 1/2` gives the exact
one-dimensional lower growth used to detect the cusp. -/
theorem candidateV_lower_growth
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hy : 0 < y)
    (hint : IntervalIntegrable
      (fun τ => singularStressX P γ x τ) volume 0 y)
    (hU : ∀ τ ∈ Ioo (0 : ℝ) y, InU P x τ (jetOf γ x τ))
    (hscalar : ∀ τ ∈ Ioo (0 : ℝ) y,
      (1 : ℝ) / 8 ≤ scalarField P γ x τ) :
    ((1 : ℝ) / 16) *
        (y ^ holderExponent P / holderExponent P) ≤
      candidateV P γ x y := by
  have hkernel := intervalIntegrable_singularKernel P 0 y
  have hmodel : IntervalIntegrable
      (fun τ : ℝ => ((1 : ℝ) / 16) * τ ^ (-singularExponent P))
      volume 0 y := hkernel.const_mul _
  have hmono :
      (∫ τ : ℝ in (0 : ℝ)..y,
          ((1 : ℝ) / 16) * τ ^ (-singularExponent P)) ≤
        ∫ τ : ℝ in (0 : ℝ)..y, singularStressX P γ x τ := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hy.le hmodel hint
    intro τ hτ
    have hpoint := one_div_sixteen_singularDenominator_le_stressX
      (P := P) (γ := γ) (x := x) (y := τ) hτ.1.ne'
      (hU τ hτ) (hscalar τ hτ)
    rw [div_eq_mul_inv, ← one_div] at hpoint
    rw [one_div_singularDenominator_eq_rpow_neg P hτ.1] at hpoint
    exact hpoint
  rw [intervalIntegral.integral_const_mul,
    integral_singularKernel_zero_to P hy.le] at hmono
  exact hmono

/-- The power lower bound has a super-linear quotient at the origin, so the
candidate cannot be Lipschitz near a point of the light line.  This is a
direct integral proof of the last assertion in (4.10); no pointwise
differentiability of `candidateV` is needed.

The three segment hypotheses are precisely the localized Section 3 bounds
needed to invoke `candidateV_lower_growth` on every sufficiently short
positive vertical segment. -/
theorem candidateV_not_lipschitzNearAt_of_segment_bounds
    {P : Params} {γ : ℝ → ℝ → ℝ} {x₀ ε : ℝ}
    (hε : 0 < ε)
    (hint : ∀ y, 0 < y → y < ε →
      IntervalIntegrable (fun τ => singularStressX P γ x₀ τ) volume 0 y)
    (hU : ∀ y, 0 < y → y < ε → ∀ τ ∈ Ioo (0 : ℝ) y,
      InU P x₀ τ (jetOf γ x₀ τ))
    (hscalar : ∀ y, 0 < y → y < ε → ∀ τ ∈ Ioo (0 : ℝ) y,
      (1 : ℝ) / 8 ≤ scalarField P γ x₀ τ) :
    ¬ LipschitzNearAt (candidateVUncurried P γ) (x₀, 0) := by
  rintro ⟨C, s, hs, hlip⟩
  rcases Metric.mem_nhds_iff.1 hs with ⟨r, hr, hball⟩
  let δ : ℝ := min ε r
  have hδ : 0 < δ := by
    exact lt_min hε hr
  have hexp : holderExponent P - 1 < 0 := by
    linarith [holderExponent_lt_one P]
  have hlarge : ∀ᶠ y in 𝓝[>] (0 : ℝ),
      16 * holderExponent P * (C : ℝ) <
        y ^ (holderExponent P - 1) :=
    (tendsto_rpow_neg_nhdsGT_zero hexp).eventually
      (Ioi_mem_atTop (16 * holderExponent P * (C : ℝ)))
  have hsmall : Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hδ
  rcases (hlarge.and hsmall).exists with ⟨y, hylarge, hy⟩
  have hyε : y < ε := hy.2.trans_le (min_le_left _ _)
  have hyr : y < r := hy.2.trans_le (min_le_right _ _)
  have hzmem : (x₀, y) ∈ s := by
    apply hball
    simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, abs_of_pos hy.1]
      using And.intro hr hyr
  have hz₀mem : (x₀, (0 : ℝ)) ∈ s := by
    exact hball (Metric.mem_ball_self hr)
  have hlipbound := hlip.dist_le_mul (x₀, y) hzmem (x₀, (0 : ℝ)) hz₀mem
  simp [candidateVUncurried, candidateV_zero, Prod.dist_eq,
    abs_of_pos hy.1, max_eq_right hy.1.le] at hlipbound
  have hlower := candidateV_lower_growth
    (P := P) (γ := γ) (x := x₀) hy.1
    (hint y hy.1 hyε) (hU y hy.1 hyε) (hscalar y hy.1 hyε)
  have hα : 0 < holderExponent P := holderExponent_pos P
  have hrpow :
      y ^ holderExponent P = y ^ (holderExponent P - 1) * y := by
    calc
      y ^ holderExponent P = y ^ ((holderExponent P - 1) + 1) := by ring_nf
      _ = y ^ (holderExponent P - 1) * y ^ (1 : ℝ) := by
        rw [Real.rpow_add hy.1]
      _ = y ^ (holderExponent P - 1) * y := by simp
  have hquotient :
      (C : ℝ) * y <
        ((1 : ℝ) / 16) *
          (y ^ holderExponent P / holderExponent P) := by
    have hden : 0 < 16 * holderExponent P := mul_pos (by norm_num) hα
    have heq : ((1 : ℝ) / 16) *
        (y ^ holderExponent P / holderExponent P) =
        y ^ holderExponent P / (16 * holderExponent P) := by
      field_simp [hα.ne']
    rw [heq]
    apply (lt_div_iff₀ hden).2
    calc
      (C : ℝ) * y * (16 * holderExponent P) =
          (16 * holderExponent P * (C : ℝ)) * y := by ring
      _ < y ^ (holderExponent P - 1) * y :=
        mul_lt_mul_of_pos_right hylarge hy.1
      _ = y ^ holderExponent P := hrpow.symm
  have hvstrict : (C : ℝ) * y < candidateV P γ x₀ y :=
    hquotient.trans_le hlower
  have hvupper : candidateV P γ x₀ y ≤ (C : ℝ) * y :=
    (le_abs_self _).trans hlipbound
  exact (not_lt_of_ge hvupper) hvstrict

end

end StressTensor
