import StressTensor.StressBounds
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Holder

/-!
# Section 4: endpoint and non-Lipschitz regularity

Mathlib does not currently contain a Lorentz/Marcinkiewicz-space API matching
the notation in the paper.  We therefore record the weak endpoint condition
directly through distribution functions, and the finite-`t` Lorentz quantity
through its defining truncated integral.  The rotation invariance needed for
`Dv = stressᗮ` is proved exactly.

The final part gives a general, kernel-checked criterion turning unbounded
Fréchet derivatives in every neighborhood into failure of local Lipschitz
continuity.  It avoids any appeal to an unavailable Sobolev-space API.
-/

namespace StressTensor

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Interval Topology

/-- Euclidean size on the pair representation. -/
def vectorSize (z : ℝ × ℝ) : ℝ :=
  Real.sqrt (normSq z)

theorem vectorSize_nonneg (z : ℝ × ℝ) : 0 ≤ vectorSize z :=
  Real.sqrt_nonneg _

@[simp] theorem vectorSize_quarterTurn (z : ℝ × ℝ) :
    vectorSize (quarterTurn z) = vectorSize z := by
  simp [vectorSize]

/-- The distribution set `{z ∈ Ω | |f z| > level}`. -/
def distributionSet
    (f : Point → ℝ × ℝ) (Ω : Set Point) (level : ℝ) : Set Point :=
  Ω ∩ {z | vectorSize (f z) > level}

/-- Membership in weak `L^r`, expressed by the standard distribution bound
`λ^r |{|f|>λ}| ≤ C`. -/
def InWeakLp (r : ℝ) (f : Point → ℝ × ℝ) (Ω : Set Point) : Prop :=
  ∃ C : ENNReal, C ≠ ∞ ∧ ∀ level : ℝ, 0 < level →
    ENNReal.rpow (ENNReal.ofReal level) r *
      volume (distributionSet f Ω level) ≤ C

/-- A quarter-turn preserves the weak endpoint condition. -/
theorem inWeakLp_quarterTurn_iff
    (r : ℝ) (f : Point → ℝ × ℝ) (Ω : Set Point) :
    InWeakLp r (fun z => quarterTurn (f z)) Ω ↔ InWeakLp r f Ω := by
  simp only [InWeakLp, distributionSet, vectorSize_quarterTurn]

/-- Equation (4.4) transfers the weak `L^(p/2)` estimate from the stress to the
candidate gradient. -/
theorem candidateGradient_inWeakLp_iff
    (P : Params) (γ : ℝ → ℝ → ℝ) (Ω : Set Point) :
    InWeakLp (weakExponent P)
        (fun z => candidateGradient P γ z.1 z.2) Ω ↔
      InWeakLp (weakExponent P)
        (fun z => singularStress P γ z.1 z.2) Ω := by
  exact inWeakLp_quarterTurn_iff _ _ _

/-- Real-valued distribution measure used in the finite-`t` Lorentz
functional.  In applications `Ω` has finite measure. -/
def distributionMeasure
    (f : Point → ℝ × ℝ) (Ω : Set Point) (level : ℝ) : ℝ :=
  (volume (distributionSet f Ω level)).toReal

/-- The upper-tail truncation of the `t`-th power of the Lorentz seminorm
from (4.11). -/
def lorentzTruncation
    (r t : ℝ) (f : Point → ℝ × ℝ) (Ω : Set Point) (M : ℝ) : ℝ :=
  r * ∫ level in (1 : ℝ)..M,
    Real.rpow (Real.rpow level r * distributionMeasure f Ω level) (t / r) / level

/-- Finiteness of the high-level Lorentz tail.  Positivity of the exponents,
finite measure of the domain, and integrability of every truncation are part
of the definition, so neither `ENNReal.toReal ∞ = 0` nor Mathlib's convention
for a non-integrable Bochner integral can create a spurious witness.

Finiteness of the full Lorentz seminorm implies this tail condition.  The
converse also needs control of the omitted low-level interval `(0,1)`, and is
not claimed here. -/
def FiniteLorentzOn
    (r t : ℝ) (f : Point → ℝ × ℝ) (Ω : Set Point) : Prop :=
  0 < r ∧ 0 < t ∧ volume Ω ≠ ∞ ∧
    (∀ M : ℝ, 1 ≤ M → IntervalIntegrable
      (fun level =>
        Real.rpow
          (Real.rpow level r * distributionMeasure f Ω level) (t / r) /
            level)
      volume 1 M) ∧
    ∃ K : ℝ, ∀ M : ℝ, 1 ≤ M → lorentzTruncation r t f Ω M ≤ K

/-- The logarithmic lower bound in (4.11) rules out every finite-`t` Lorentz
seminorm. -/
theorem not_finiteLorentzOn_of_log_lower
    {r t c : ℝ} {f : Point → ℝ × ℝ} {Ω : Set Point}
    (hc : 0 < c)
    (hlog : ∀ M : ℝ, 1 < M →
      Real.log M / c ≤ lorentzTruncation r t f Ω M) :
    ¬ FiniteLorentzOn r t f Ω := by
  rintro ⟨_, _, _, _, K, hK⟩
  let M : ℝ := Real.exp (c * (|K| + 1))
  have harg : 0 < c * (|K| + 1) := by positivity
  have hM : 1 < M := by
    simpa only [M, Real.one_lt_exp_iff] using harg
  have hlower := hlog M hM
  have hupper := hK M hM.le
  have hlogM : Real.log M = c * (|K| + 1) := by
    simp [M]
  rw [hlogM] at hlower
  have hquot : c * (|K| + 1) / c = |K| + 1 := by
    field_simp [hc.ne']
  rw [hquot] at hlower
  have hKabs : K ≤ |K| := le_abs_self K
  linarith

/-- Local Lipschitz continuity at one specified point. -/
def LipschitzNearAt {E F : Type*} [PseudoMetricSpace E] [PseudoEMetricSpace F]
    (f : E → F) (x₀ : E) : Prop :=
  ∃ C : NNReal, ∃ s : Set E, s ∈ 𝓝 x₀ ∧ LipschitzOnWith C f s

/-- If every neighborhood contains a differentiability point whose derivative
has arbitrarily large norm, the function is not Lipschitz near `x₀`. -/
theorem not_lipschitzNearAt_of_unbounded_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x₀ : E}
    (hunbounded : ∀ (C : NNReal) (s : Set E), s ∈ 𝓝 x₀ →
      ∃ x ∈ s, ∃ f' : E →L[ℝ] F,
        HasFDerivAt f f' x ∧ (C : ℝ) < ‖f'‖) :
    ¬ LipschitzNearAt f x₀ := by
  rintro ⟨C, t, ht, hlip⟩
  rcases mem_nhds_iff.1 ht with ⟨u, hut, hu_open, hx₀u⟩
  have hu_nhds_x₀ : u ∈ 𝓝 x₀ := hu_open.mem_nhds hx₀u
  rcases hunbounded C u hu_nhds_x₀ with ⟨x, hxu, L, hL, hCL⟩
  have hu_nhds_x : u ∈ 𝓝 x := hu_open.mem_nhds hxu
  have hbound : ‖L‖ ≤ (C : ℝ) :=
    hL.le_of_lipschitzOn hu_nhds_x (hlip.mono hut)
  exact (not_lt_of_ge hbound) hCL

/-- The differential whose coefficients are a Euclidean gradient pair. -/
def gradientDifferential (g : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  g.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    g.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem gradientDifferential_apply (g h : ℝ × ℝ) :
    gradientDifferential g h = g.1 * h.1 + g.2 * h.2 := by
  simp [gradientDifferential]

/-- The operator norm controls each coordinate of the represented gradient. -/
theorem abs_snd_le_norm_gradientDifferential (g : ℝ × ℝ) :
    |g.2| ≤ ‖gradientDifferential g‖ := by
  have h := (gradientDifferential g).le_opNorm ((0 : ℝ), (1 : ℝ))
  simpa using h

/-- The candidate as a function of a point rather than two curried variables. -/
def candidateVUncurried (P : Params) (γ : ℝ → ℝ → ℝ) : Point → ℝ :=
  fun z => candidateV P γ z.1 z.2

/-- A point-selection formulation of the blow-up estimate implies failure of
local Lipschitz continuity at a light-line point.  The pointwise lower bound
in `StressBounds` is designed to discharge the size premise after the
localized Section 3 construction is supplied. -/
theorem candidateV_not_lipschitzNearAt
    {P : Params} {γ : ℝ → ℝ → ℝ} {z₀ : Point}
    (hpoints : ∀ (C : NNReal) (s : Set Point), s ∈ 𝓝 z₀ →
      ∃ z ∈ s,
        HasFDerivAt (candidateVUncurried P γ)
          (gradientDifferential (candidateGradient P γ z.1 z.2)) z ∧
        (C : ℝ) < |singularStressX P γ z.1 z.2|) :
    ¬ LipschitzNearAt (candidateVUncurried P γ) z₀ := by
  apply not_lipschitzNearAt_of_unbounded_fderiv
  intro C s hs
  rcases hpoints C s hs with ⟨z, hzs, hderiv, hlarge⟩
  refine ⟨z, hzs, gradientDifferential (candidateGradient P γ z.1 z.2), hderiv, ?_⟩
  exact hlarge.trans_le <| by
    simpa only [candidateGradient_snd] using
      abs_snd_le_norm_gradientDifferential (candidateGradient P γ z.1 z.2)

end

end StressTensor
