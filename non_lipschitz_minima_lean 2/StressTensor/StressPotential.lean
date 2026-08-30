import StressTensor.SectionFourCore
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Section 4: the stress potential

We define the candidate from (4.1) by an oriented interval integral.  The
vertical weak derivative is obtained from the one-dimensional Lebesgue
differentiation theorem.  For the horizontal derivative we expose, and then
use, the exact dominated-parametric-integral hypotheses invoked informally in
(4.2).  The integration of the divergence relation across the deleted axis is
also proved from one-sided limits, matching the two cases in the paper.
-/

namespace StressTensor

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

/-- The prospective minimizer from (4.1). -/
def candidateV (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..y, singularStressX P γ x τ

@[simp] theorem candidateV_zero
    (P : Params) (γ : ℝ → ℝ → ℝ) (x : ℝ) :
    candidateV P γ x 0 = 0 := by
  simp [candidateV]

/-- The fundamental theorem of calculus in `y`, in the a.e. form appropriate
for the singular integrand in (4.1). -/
theorem ae_hasDerivAt_candidateV_y
    {P : Params} {γ : ℝ → ℝ → ℝ} {x a b : ℝ}
    (hzero : (0 : ℝ) ∈ uIcc a b)
    (hint : IntervalIntegrable (fun τ => singularStressX P γ x τ) volume a b) :
    ∀ᵐ y ∂volume, y ∈ uIcc a b →
      HasDerivAt (candidateV P γ x) (singularStressX P γ x y) y := by
  filter_upwards [hint.ae_hasDerivAt_integral] with y hy
  intro hyab
  change HasDerivAt
    (fun y => ∫ τ in (0 : ℝ)..y, singularStressX P γ x τ)
    (singularStressX P γ x y) y
  exact hy hyab 0 hzero

/-- The same integrability hypothesis gives the continuity across the light
line used immediately after (4.1); in fact it gives absolute continuity on
every fixed vertical slice. -/
theorem candidateV_absolutelyContinuousOnInterval
    {P : Params} {γ : ℝ → ℝ → ℝ} {x a b : ℝ}
    (hzero : (0 : ℝ) ∈ uIcc a b)
    (hint : IntervalIntegrable (fun τ => singularStressX P γ x τ) volume a b) :
    AbsolutelyContinuousOnInterval (candidateV P γ x) a b := by
  change AbsolutelyContinuousOnInterval
    (fun y => ∫ τ in (0 : ℝ)..y, singularStressX P γ x τ) a b
  exact hint.absolutelyContinuousOnInterval_intervalIntegral hzero

/-- The elementary integral estimate behind the first bound after (4.1).
The model majorant can later be specialized to `C |τ|^(-2/p)`. -/
theorem abs_candidateV_le_abs_integral_of_bound
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ} {bound : ℝ → ℝ}
    (hbound : ∀ᵐ τ ∂volume.restrict (Ι (0 : ℝ) y),
      ‖singularStressX P γ x τ‖ ≤ bound τ)
    (hint : IntervalIntegrable bound volume 0 y) :
    |candidateV P γ x y| ≤ |∫ τ in (0 : ℝ)..y, bound τ| := by
  simpa only [candidateV, Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_abs_of_norm_le hbound hint

/-- A direct wrapper around Mathlib's dominated differentiation theorem.  It
formalizes the step “differentiate under the integral” in (4.2), with all
measurability, neighborhood, and integrable-majorant assumptions visible. -/
theorem hasDerivAt_candidateV_x_of_dominated
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    {s : Set ℝ} {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 x)
    (hstress_meas : ∀ᶠ ξ in 𝓝 x,
      AEStronglyMeasurable (fun τ => singularStressX P γ ξ τ)
        (volume.restrict (Ι (0 : ℝ) y)))
    (hstress_int :
      IntervalIntegrable (fun τ => singularStressX P γ x τ) volume 0 y)
    (hderiv_meas : AEStronglyMeasurable
      (fun τ => deriv (fun ξ => singularStressX P γ ξ τ) x)
      (volume.restrict (Ι (0 : ℝ) y)))
    (hderiv_bound : ∀ᵐ τ ∂volume, τ ∈ Ι (0 : ℝ) y →
      ∀ ξ ∈ s, ‖deriv (fun ζ => singularStressX P γ ζ τ) ξ‖ ≤ bound τ)
    (hbound_int : IntervalIntegrable bound volume 0 y)
    (hderiv : ∀ᵐ τ ∂volume, τ ∈ Ι (0 : ℝ) y →
      ∀ ξ ∈ s, HasDerivAt (fun ζ => singularStressX P γ ζ τ)
        (deriv (fun ζ => singularStressX P γ ζ τ) ξ) ξ) :
    HasDerivAt (fun ξ => candidateV P γ ξ y)
      (∫ τ in (0 : ℝ)..y, deriv (fun ζ => singularStressX P γ ζ τ) x) x := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := y)
    hs hstress_meas hstress_int hderiv_meas hderiv_bound hbound_int hderiv
  simpa only [candidateV] using h.2

/-- A zero auxiliary residual forces the factored singular stress to have
zero classical divergence away from the light line.  This packages the use of
(3.11), (3.15), and (3.22) made before (4.3). -/
theorem singularStressDivergence_eq_zero_of_auxiliaryEquation
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ} (hy0 : y ≠ 0)
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y))
    (haux : auxiliaryEquationAt P γ x y) :
    singularStressDivergence P γ x y = 0 := by
  rw [singularStressDivergence_eq_rpow_mul_residual
    hy0 hx hxx hyx hy hxy hyy hS]
  have hres : differentialResidual P γ x y = 0 :=
    (differentialResidual_eq_zero_iff_auxiliaryEquationAt
      hx hxx hyx hy hxy hyy hS).2 haux
  rw [hres, mul_zero]

/-- Component form of zero divergence, equation (4.3). -/
theorem stress_component_derivatives_opposite
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y dx dy : ℝ}
    (hx : HasDerivAt (fun ξ => singularStressX P γ ξ y) dx x)
    (hy : HasDerivAt (fun η => singularStressY P γ x η) dy y)
    (hdiv : singularStressDivergence P γ x y = 0) :
    dx = -dy := by
  simp only [singularStressDivergence, hx.deriv, hy.deriv] at hdiv
  linarith

/-- Integration of (4.3) on the positive side of the light line. -/
theorem integral_stressXDerivative_eq_neg_stressY_of_pos
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    {dx : ℝ → ℝ} (hy : 0 < y)
    (hderiv : ∀ τ ∈ Ioo (0 : ℝ) y,
      HasDerivAt (fun η => singularStressY P γ x η) (-dx τ) τ)
    (hint : IntervalIntegrable (fun τ => -dx τ) volume 0 y)
    (hzero : Tendsto (fun η => singularStressY P γ x η) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hycont : ContinuousAt (fun η => singularStressY P γ x η) y) :
    (∫ τ in (0 : ℝ)..y, dx τ) = -singularStressY P γ x y := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hy
    hderiv hint hzero (hycont.tendsto.mono_left inf_le_left)
  rw [intervalIntegral.integral_neg] at hFTC
  linarith

/-- Integration of (4.3) on the negative side of the light line. -/
theorem integral_stressXDerivative_eq_neg_stressY_of_neg
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    {dx : ℝ → ℝ} (hy : y < 0)
    (hderiv : ∀ τ ∈ Ioo y (0 : ℝ),
      HasDerivAt (fun η => singularStressY P γ x η) (-dx τ) τ)
    (hint : IntervalIntegrable (fun τ => -dx τ) volume y 0)
    (hzero : Tendsto (fun η => singularStressY P γ x η) (𝓝[<] (0 : ℝ)) (𝓝 0))
    (hycont : ContinuousAt (fun η => singularStressY P γ x η) y) :
    (∫ τ in (0 : ℝ)..y, dx τ) = -singularStressY P γ x y := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hy
    hderiv hint (hycont.tendsto.mono_left inf_le_left) hzero
  rw [intervalIntegral.integral_neg] at hFTC
  rw [intervalIntegral.integral_symm]
  linarith

/-- Once differentiation under the integral and the integrated divergence
identity are available, the horizontal derivative in (4.4) follows exactly. -/
theorem hasDerivAt_candidateV_x_of_integral_identity
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    {dx : ℝ → ℝ}
    (hparam : HasDerivAt (fun ξ => candidateV P γ ξ y)
      (∫ τ in (0 : ℝ)..y, dx τ) x)
    (hFTC : (∫ τ in (0 : ℝ)..y, dx τ) = -singularStressY P γ x y) :
    HasDerivAt (fun ξ => candidateV P γ ξ y)
      (-singularStressY P γ x y) x := by
  exact hparam.congr_deriv hFTC

/-- Coordinate form of the gradient identity (4.4). -/
theorem candidateV_coordinate_derivatives
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun ξ => candidateV P γ ξ y)
      (-singularStressY P γ x y) x)
    (hy : HasDerivAt (candidateV P γ x)
      (singularStressX P γ x y) y) :
    HasDerivAt (fun ξ => candidateV P γ ξ y)
        (candidateGradient P γ x y).1 x ∧
      HasDerivAt (candidateV P γ x)
        (candidateGradient P γ x y).2 y := by
  simpa using And.intro hx hy

end

end StressTensor
