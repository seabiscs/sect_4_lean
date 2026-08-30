import StressTensor.StressPotential

/-!
# Section 4: component bounds near the light line

The original Section 3 project already proves `Γ₁ ≥ 1/2` on `U_q`.  Combining
that fact with a positive lower bound for the scalar factor `S` yields a
pointwise lower bound for the first stress component.  This is the cleanest
kernel-checked source of the blow-up used in Section 4.2.
-/

namespace StressTensor

noncomputable section

/-- The singular denominator is positive off the light line. -/
theorem singularDenominator_pos (P : Params) {y : ℝ} (hy : y ≠ 0) :
    0 < singularDenominator P y := by
  exact Real.rpow_pos_of_pos (abs_pos.mpr hy) _

@[simp] theorem singularDenominator_zero (P : Params) :
    singularDenominator P 0 = 0 := by
  have hexp : (2 / P.p) ≠ 0 := by
    exact (singularExponent_pos P).ne'
  simp [singularDenominator, Real.zero_rpow hexp]

/-- A modular lower estimate for the singular tangential component. -/
theorem singularStressX_ge_of_inU
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y s : ℝ}
    (hy : y ≠ 0)
    (hU : InU P x y (jetOf γ x y))
    (hs : 0 ≤ s)
    (hscalar : s ≤ scalarField P γ x y) :
    (s / 2) / singularDenominator P y ≤ singularStressX P γ x y := by
  have hdenom := singularDenominator_pos P hy
  have hgamma : (1 : ℝ) / 2 ≤ gamma1Field γ x y := by
    simpa only [gamma1Field] using gamma1_ge_one_half hU
  have hscalar_nonneg : 0 ≤ scalarField P γ x y := hs.trans hscalar
  have hgamma_nonneg : 0 ≤ gamma1Field γ x y := by linarith
  rw [singularStressX]
  apply (div_le_div_iff_of_pos_right hdenom).2
  nlinarith [mul_nonneg hscalar_nonneg hgamma_nonneg]

/-- With the numerical bound `S ≥ 1/8` from (3.19), the first component is at
least `1 / (16 |y|^(2/p))`. -/
theorem one_div_sixteen_singularDenominator_le_stressX
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hy : y ≠ 0)
    (hU : InU P x y (jetOf γ x y))
    (hscalar : (1 : ℝ) / 8 ≤ scalarField P γ x y) :
    ((1 : ℝ) / 16) / singularDenominator P y ≤
      singularStressX P γ x y := by
  simpa only [show ((1 : ℝ) / 8) / 2 = (1 : ℝ) / 16 by norm_num] using
    singularStressX_ge_of_inU hy hU (by norm_num : (0 : ℝ) ≤ 1 / 8) hscalar

/-- A generic upper estimate for the same component.  The localized Section 3
output supplies the two scalar bounds in applications. -/
theorem abs_singularStressX_le
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y Cs Cg : ℝ}
    (hy : y ≠ 0) (hCs : 0 ≤ Cs)
    (hscalar : |scalarField P γ x y| ≤ Cs)
    (hgamma : |gamma1Field γ x y| ≤ Cg) :
    |singularStressX P γ x y| ≤
      (Cs * Cg) / singularDenominator P y := by
  have hdenom := singularDenominator_pos P hy
  rw [singularStressX, abs_div, abs_of_pos hdenom, abs_mul]
  exact div_le_div_of_nonneg_right
    (mul_le_mul hscalar hgamma (abs_nonneg _) hCs) hdenom.le

end

end StressTensor
