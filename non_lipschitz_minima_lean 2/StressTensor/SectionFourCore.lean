import StressTensor.DifferentialBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Section 4: finite-dimensional core

This module records the algebra used in Section 4 of the reference.  Vectors
are represented by pairs, as in the existing stress-tensor development, and
`normSq` is their squared Euclidean norm (rather than Mathlib's product norm).

The central operation is the quarter-turn `z ↦ zᗮ = (-z₂,z₁)`.  We prove that
it preserves the Euclidean norm and commutes with the radial gradient of the
degenerate area density.  Consequently the Fenchel-gradient inverse identity
from (2.21), when supplied at the unrotated stress, immediately yields (4.7).
-/

namespace StressTensor

noncomputable section

namespace Params

/-- Build the conjugate parameter package used throughout the development
from the single hypothesis `p > 2` in Theorem 4.1. -/
def ofP (p : ℝ) (hp : 2 < p) : Params where
  p := p
  q := p / (p - 1)
  one_lt_q := by
    have hp1 : 0 < p - 1 := by linarith
    exact (lt_div_iff₀ hp1).2 (by linarith)
  q_lt_two := by
    have hp1 : 0 < p - 1 := by linarith
    apply (div_lt_iff₀ hp1).2
    linarith
  two_lt_p := hp
  holder := by
    have hp0 : p ≠ 0 := by linarith
    have hp1 : p - 1 ≠ 0 := by linarith
    field_simp [hp0, hp1]
    ring

@[simp] theorem ofP_p (p : ℝ) (hp : 2 < p) : (ofP p hp).p = p := rfl

@[simp] theorem ofP_q (p : ℝ) (hp : 2 < p) :
    (ofP p hp).q = p / (p - 1) := rfl

end Params

/-- The singular exponent `2 / p` appearing on the light line. -/
def singularExponent (P : Params) : ℝ :=
  2 / P.p

/-- The Hölder exponent `1 - 2 / p` in Theorem 4.1. -/
def holderExponent (P : Params) : ℝ :=
  1 - singularExponent P

/-- The weak-Lebesgue exponent `p / 2`. -/
def weakExponent (P : Params) : ℝ :=
  P.p / 2

theorem singularExponent_pos (P : Params) : 0 < singularExponent P := by
  exact div_pos (by norm_num) P.p_pos

theorem singularExponent_lt_one (P : Params) : singularExponent P < 1 := by
  rw [singularExponent, div_lt_one P.p_pos]
  exact P.two_lt_p

theorem holderExponent_pos (P : Params) : 0 < holderExponent P := by
  rw [holderExponent]
  linarith [singularExponent_lt_one P]

theorem holderExponent_lt_one (P : Params) : holderExponent P < 1 := by
  rw [holderExponent]
  linarith [singularExponent_pos P]

theorem weakExponent_gt_one (P : Params) : 1 < weakExponent P := by
  rw [weakExponent]
  linarith [P.two_lt_p]

/-- The counterclockwise quarter-turn `(z₁,z₂) ↦ (-z₂,z₁)`, equation (4.6). -/
def quarterTurn (z : ℝ × ℝ) : ℝ × ℝ :=
  (-z.2, z.1)

@[simp] theorem quarterTurn_fst (z : ℝ × ℝ) : (quarterTurn z).1 = -z.2 := rfl

@[simp] theorem quarterTurn_snd (z : ℝ × ℝ) : (quarterTurn z).2 = z.1 := rfl

@[simp] theorem quarterTurn_zero : quarterTurn (0, 0) = (0, 0) := by
  simp [quarterTurn]

theorem quarterTurn_add (z w : ℝ × ℝ) :
    quarterTurn (z + w) = quarterTurn z + quarterTurn w := by
  ext <;> simp [quarterTurn, add_comm]

theorem quarterTurn_smul (a : ℝ) (z : ℝ × ℝ) :
    quarterTurn (a • z) = a • quarterTurn z := by
  ext <;> simp [quarterTurn]

@[simp] theorem quarterTurn_quarterTurn (z : ℝ × ℝ) :
    quarterTurn (quarterTurn z) = -z := by
  ext <;> simp [quarterTurn]

/-- Equation (4.6): a quarter-turn preserves the squared Euclidean norm. -/
@[simp] theorem normSq_quarterTurn (z : ℝ × ℝ) :
    normSq (quarterTurn z) = normSq z := by
  simp only [normSq, quarterTurn_fst, quarterTurn_snd]
  ring

theorem normSq_nonneg (z : ℝ × ℝ) : 0 ≤ normSq z := by
  simp only [normSq]
  positivity

/-- Euclidean inner product on the pair representation. -/
def dot (z w : ℝ × ℝ) : ℝ :=
  z.1 * w.1 + z.2 * w.2

@[simp] theorem dot_self (z : ℝ × ℝ) : dot z z = normSq z := by
  simp [dot, normSq]
  ring

@[simp] theorem dot_quarterTurn_self (z : ℝ × ℝ) :
    dot (quarterTurn z) z = 0 := by
  simp [dot, quarterTurn]
  ring

@[simp] theorem dot_quarterTurn (z w : ℝ × ℝ) :
    dot (quarterTurn z) (quarterTurn w) = dot z w := by
  simp [dot, quarterTurn]
  ring

/-- Gradient of the area density `Aₚ(z) = (1 + |z|ᵖ)^(1/p)`, written using
the squared Euclidean norm.  This formula is valid at the origin because
`p > 2`. -/
def areaGradient (P : Params) (z : ℝ × ℝ) : ℝ × ℝ :=
  let a :=
    Real.rpow (normSq z) ((P.p - 2) / 2) /
      Real.rpow (1 + Real.rpow (normSq z) (P.p / 2)) (1 - 1 / P.p)
  (a * z.1, a * z.2)

/-- Radial maps commute with the quarter-turn.  This is the algebraic content
of the first two equalities in (4.7). -/
theorem areaGradient_quarterTurn (P : Params) (z : ℝ × ℝ) :
    areaGradient P (quarterTurn z) = quarterTurn (areaGradient P z) := by
  simp only [areaGradient, normSq_quarterTurn, quarterTurn_fst, quarterTurn_snd]
  simp [quarterTurn]

/-- Equation (4.7), isolated from the prior Fenchel-duality theorem (2.21).
The only hypothesis is exactly the unrotated gradient-inverse identity. -/
theorem areaGradient_quarterTurn_of_inverse
    (P : Params) (stress gradU : ℝ × ℝ)
    (hinverse : areaGradient P stress = gradU) :
    areaGradient P (quarterTurn stress) = quarterTurn gradU := by
  rw [areaGradient_quarterTurn, hinverse]

/-- The factored stress from Section 3, bundled as a vector. -/
def singularStress
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ × ℝ :=
  (singularStressX P γ x y, singularStressY P γ x y)

/-- The gradient predicted for the Section 4 potential, equation (4.4). -/
def candidateGradient
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ × ℝ :=
  quarterTurn (singularStress P γ x y)

@[simp] theorem candidateGradient_fst
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    (candidateGradient P γ x y).1 = -singularStressY P γ x y := rfl

@[simp] theorem candidateGradient_snd
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    (candidateGradient P γ x y).2 = singularStressX P γ x y := rfl

@[simp] theorem normSq_candidateGradient
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    normSq (candidateGradient P γ x y) =
      normSq (singularStress P γ x y) := by
  exact normSq_quarterTurn _

/-- The pointwise Euler-field identity used in (4.7). -/
theorem areaGradient_candidateGradient
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) (gradU : ℝ × ℝ)
    (hinverse : areaGradient P (singularStress P γ x y) = gradU) :
    areaGradient P (candidateGradient P γ x y) = quarterTurn gradU := by
  exact areaGradient_quarterTurn_of_inverse P _ _ hinverse

end

end StressTensor
