import StressTensor.LowerGrowth
import StressTensor.VariationalTransfer

/-!
# Section 4: assembled endpoint and duality transfer

This module gives a compact, honest top-level theorem for the parts of
Section 4 that can be assembled from the preceding kernel-checked lemmas.
The record below does not assert the missing localization theory globally:
every analytic input is a field that an eventual Cauchy--Kowalevskaya and
Sobolev development must construct.

In particular, `stress_weak` is the localized weak endpoint estimate,
`fenchel_inverse` is (2.21) almost everywhere on the set where the stress
formula represents the original field.  The segment fields are the localized
Section 3 bounds used by the direct integral proof at a light-line point.
-/

namespace StressTensor

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

/-- Explicit localized inputs from Sections 3 and 4.  This is data rather than
a global assumption, and its fields are intentionally strong enough to keep
the resulting theorem free of hidden regularity assumptions. -/
structure SectionFourEndpointData
    (P : Params) (γ : ℝ → ℝ → ℝ) (Ω : Set Point)
    (x₀ : ℝ) (gradU : Point → ℝ × ℝ) where
  stress_weak : InWeakLp (weakExponent P)
    (fun z => singularStress P γ z.1 z.2) Ω
  fenchel_inverse : ∀ᵐ z ∂volume.restrict Ω,
    areaGradient P (singularStress P γ z.1 z.2) = gradU z
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  segment_integrable : ∀ y, 0 < y → y < epsilon →
    IntervalIntegrable (fun τ => singularStressX P γ x₀ τ) volume 0 y
  segment_inU : ∀ y, 0 < y → y < epsilon → ∀ τ ∈ Ioo (0 : ℝ) y,
    InU P x₀ τ (jetOf γ x₀ τ)
  segment_scalar_lower : ∀ y, 0 < y → y < epsilon → ∀ τ ∈ Ioo (0 : ℝ) y,
    (1 : ℝ) / 8 ≤ scalarField P γ x₀ τ

/-- Conditional assembly of the weak endpoint estimate, the rotated
Fenchel-gradient identity (4.7), and failure of local Lipschitz continuity.
The hypotheses are precisely the localization obligations that remain after
the algebra and one-dimensional calculus proved in the preceding modules. -/
theorem sectionFour_endpoint_duality
    {P : Params} {γ : ℝ → ℝ → ℝ} {Ω : Set Point}
    {x₀ : ℝ} {gradU : Point → ℝ × ℝ}
    (D : SectionFourEndpointData P γ Ω x₀ gradU) :
    InWeakLp (weakExponent P)
        (fun z => candidateGradient P γ z.1 z.2) Ω ∧
      (∀ᵐ z ∂volume.restrict Ω,
        areaGradient P (candidateGradient P γ z.1 z.2) =
          candidateCalibration gradU z) ∧
      ¬ LipschitzNearAt (candidateVUncurried P γ) (x₀, 0) := by
  refine ⟨(candidateGradient_inWeakLp_iff P γ Ω).2 D.stress_weak, ?_, ?_⟩
  · exact areaGradient_candidate_field_ae P γ gradU Ω D.fenchel_inverse
  · exact candidateV_not_lipschitzNearAt_of_segment_bounds D.epsilon_pos
      D.segment_integrable D.segment_inU D.segment_scalar_lower

end

end StressTensor
