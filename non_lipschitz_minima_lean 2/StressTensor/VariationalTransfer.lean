import StressTensor.EndpointRegularity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Section 4: calibration and generalized-minimizer transfer

The paper obtains minimality from the supporting-hyperplane inequality for the
convex area density and from a divergence-free calibration.  The first theorem
below formalizes that integration argument for an arbitrary measure space.

Mathlib has no ready-made multidimensional `W₀¹¹` trace/BV-relaxation API with
which to formalize Proposition 2.3.  `RelaxationBridge` therefore records that
cited theorem as explicit data.  It is a structure, not an axiom: downstream
results must receive an implementation of the bridge before they can claim a
generalized minimizer.
-/

namespace StressTensor

noncomputable section

open MeasureTheory Set

/-- The area density `Aₚ(z) = (1 + |z|ᵖ)^(1/p)`. -/
def areaDensity (P : Params) (z : ℝ × ℝ) : ℝ :=
  Real.rpow (1 + Real.rpow (normSq z) (P.p / 2)) (1 / P.p)

theorem areaDensity_pos (P : Params) (z : ℝ × ℝ) :
    0 < areaDensity P z := by
  apply Real.rpow_pos_of_pos
  have hz : 0 ≤ Real.rpow (normSq z) (P.p / 2) :=
    Real.rpow_nonneg (normSq_nonneg z) _
  linarith

/-- The integral functional evaluated on an already supplied gradient field. -/
def areaFunctional
    {α : Type*} [MeasurableSpace α] (P : Params) (μ : Measure α)
    (gradient : α → ℝ × ℝ) : ℝ :=
  ∫ x, areaDensity P (gradient x) ∂μ

/-- A vector `calibration` supports the area density at `base`. -/
def SupportsAreaDensity
    (P : Params) (calibration base : ℝ × ℝ) : Prop :=
  ∀ competitor : ℝ × ℝ,
    areaDensity P base + dot calibration (competitor - base) ≤
      areaDensity P competitor

/-- The supporting-hyperplane/calibration proof of minimality.  This is the
precise integral argument invoked after (4.8). -/
theorem areaFunctional_le_of_calibration
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (P : Params) (base competitor calibration : α → ℝ × ℝ)
    (hbase : Integrable (fun x => areaDensity P (base x)) μ)
    (hcompetitor : Integrable (fun x => areaDensity P (competitor x)) μ)
    (hlinear : Integrable
      (fun x => dot (calibration x) (competitor x - base x)) μ)
    (hsupport : ∀ᵐ x ∂μ,
      SupportsAreaDensity P (calibration x) (base x))
    (hstationary :
      (∫ x, dot (calibration x) (competitor x - base x) ∂μ) = 0) :
    areaFunctional P μ base ≤ areaFunctional P μ competitor := by
  have hpointwise : ∀ᵐ x ∂μ,
      areaDensity P (base x) +
          dot (calibration x) (competitor x - base x) ≤
        areaDensity P (competitor x) := by
    filter_upwards [hsupport] with x hx
    exact hx (competitor x)
  have hmono := integral_mono_ae (hbase.add hlinear) hcompetitor hpointwise
  simpa only [Pi.add_apply, integral_add hbase hlinear, hstationary, add_zero,
    areaFunctional] using hmono

/-- The calibration obtained from the Section 4 duality computation. -/
def candidateCalibration
    (gradU : Point → ℝ × ℝ) : Point → ℝ × ℝ :=
  fun z => quarterTurn (gradU z)

/-- Equation (4.7), lifted to fields almost everywhere on a specified set.
The a.e. formulation is important: the stress identity in the reference is
off-axis, while the chosen Lean representative is totalized to zero on the
light line. -/
theorem areaGradient_candidate_field_ae
    (P : Params) (γ : ℝ → ℝ → ℝ) (gradU : Point → ℝ × ℝ)
    (Ω : Set Point)
    (hinverse : ∀ᵐ z ∂volume.restrict Ω,
      areaGradient P (singularStress P γ z.1 z.2) = gradU z) :
    ∀ᵐ z ∂volume.restrict Ω,
      areaGradient P (candidateGradient P γ z.1 z.2) =
        candidateCalibration gradU z := by
  filter_upwards [hinverse] with z hz
  exact areaGradient_candidateGradient P γ z.1 z.2 (gradU z) hz

/-- A mixed-partial equality makes the divergence of a rotated gradient zero,
which is the algebraic content of (4.8). -/
theorem divergence_quarterTurn_gradient_zero
    {ux_y uy_x : ℝ} (hmixed : ux_y = uy_x) :
    -uy_x + ux_y = 0 := by
  linarith

/-- Minimizer in a specified admissible class. -/
def IsMinimizer {W : Type*} (energy : W → ℝ) (admissible : Set W) (v : W) : Prop :=
  v ∈ admissible ∧ ∀ w ∈ admissible, energy v ≤ energy w

/-- Unique minimizer in a specified admissible class. -/
def IsUniqueMinimizer
    {W : Type*} (energy : W → ℝ) (admissible : Set W) (v : W) : Prop :=
  IsMinimizer energy admissible v ∧
    ∀ w ∈ admissible, energy w = energy v → w = v

/-- The one-competitor calibration comparison, quantified over an admissible
class of gradient fields.  The stationarity premise is the formal boundary
where the PDE integration-by-parts/trace argument enters. -/
theorem isMinimizer_areaFunctional_of_calibration
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (P : Params) (base calibration : α → ℝ × ℝ)
    (admissible : Set (α → ℝ × ℝ))
    (hmem : base ∈ admissible)
    (hbase : Integrable (fun x => areaDensity P (base x)) μ)
    (hsupport : ∀ᵐ x ∂μ,
      SupportsAreaDensity P (calibration x) (base x))
    (hcompetitor : ∀ competitor ∈ admissible,
      Integrable (fun x => areaDensity P (competitor x)) μ)
    (hlinear : ∀ competitor ∈ admissible,
      Integrable (fun x => dot (calibration x) (competitor x - base x)) μ)
    (hstationary : ∀ competitor ∈ admissible,
      (∫ x, dot (calibration x) (competitor x - base x) ∂μ) = 0) :
    IsMinimizer (areaFunctional P μ) admissible base := by
  refine ⟨hmem, ?_⟩
  intro competitor hcompetitor_mem
  exact areaFunctional_le_of_calibration P base competitor calibration hbase
    (hcompetitor competitor hcompetitor_mem)
    (hlinear competitor hcompetitor_mem) hsupport
    (hstationary competitor hcompetitor_mem)

/-- Strict comparison away from `v` upgrades minimality to uniqueness.  In the
paper this strict comparison follows from strict convexity plus equality of
traces. -/
theorem isUniqueMinimizer_of_strict
    {W : Type*} {energy : W → ℝ} {admissible : Set W} {v : W}
    (hv : v ∈ admissible)
    (hstrict : ∀ w ∈ admissible, w ≠ v → energy v < energy w) :
    IsUniqueMinimizer energy admissible v := by
  constructor
  · refine ⟨hv, ?_⟩
    intro w hw
    by_cases h : w = v
    · simp [h]
    · exact (hstrict w hw h).le
  · intro w hw heq
    by_contra hne
    have hlt := hstrict w hw hne
    linarith

/-- Explicit interface for Proposition 2.3 and the cited BV relaxation
theorems.  Its `transfers_unique` field is deliberately the still-unformalized
transfer statement itself, so this record is a typed placeholder/interface,
not a proof of Proposition 2.3. -/
structure RelaxationBridge (W BV : Type*) where
  embed : W → BV
  ordinaryEnergy : W → ℝ
  relaxedEnergy : BV → ℝ
  ordinaryClass : Set W
  generalizedClass : Set BV
  energy_agrees : ∀ w ∈ ordinaryClass,
    relaxedEnergy (embed w) = ordinaryEnergy w
  transfers_unique : ∀ v : W,
    IsUniqueMinimizer ordinaryEnergy ordinaryClass v →
      IsUniqueMinimizer relaxedEnergy generalizedClass (embed v)

/-- Application of the explicit relaxation bridge. -/
theorem unique_generalizedMinimizer_of_bridge
    {W BV : Type*} (B : RelaxationBridge W BV) {v : W}
    (hv : IsUniqueMinimizer B.ordinaryEnergy B.ordinaryClass v) :
    IsUniqueMinimizer B.relaxedEnergy B.generalizedClass (B.embed v) :=
  B.transfers_unique v hv

end

end StressTensor
