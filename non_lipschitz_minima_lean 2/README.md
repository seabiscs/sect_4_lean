# Degenerate area functional: stress tensor and Section 4

This is a reproducible Lean 4 development of the stress-tensor construction
in Sections 3.1--3.2 and a kernel-checked partial/conditional formalization of
Section 4, “Non-Lipschitz minima of the degenerate area functional,” from the
supplied reference.

The project deliberately separates four levels of certainty:

1. identities and estimates proved by Lean;
2. analytic facts stated with every needed hypothesis visible;
3. analytic, Sobolev, trace, and BV facts represented by typed interfaces with
   all downstream assumptions visible;
4. the Cauchy--Kowalevskaya existence theorem, isolated as explicit data
   because Mathlib does not currently provide the required theorem.

There are no `sorry`, `admit`, custom axioms, or hidden oracle calls in the
formalization.

## Build

The project is pinned to Lean 4.33.0 and Mathlib 4.33.0. With `elan` installed:

```sh
lake update
lake build
```

`lake-manifest.json` records the exact dependency revisions used for the
successful local build. This deliverable was last verified on 2026-08-25 with
Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`; `lake build` completed all 2,757
jobs without errors or warnings.

See `AUDIT.md` for reproducible elaborated-environment checks covering all 606
project declarations and for the distinction between project-defined axioms
and Lean/Mathlib's standard logical principles.

## Module map

| Module | Content from the reference |
|---|---|
| `StressTensor/Definitions.lean` | Parameters, five-jet, `Γ₁`, `Γ₂`, `Γ₀`, `C̃`, `S̃`, `c₀,c₁,c₂,L₀`, `R`, `G`, and the domains `Q`, `U`, `V` |
| `StressTensor/Ansatz.lean` | Ansatz derivatives (3.2), norm identity (3.4)--(3.5), deficit factorization (3.9), and stress factorization (3.10) |
| `StressTensor/ScalarFactors.lean` | Integral definition of `C̃` (3.6) and its equality with the divided difference via the fundamental theorem of calculus |
| `StressTensor/ScalarDerivatives.lean` | `∂d C̃`, the exact logarithmic derivative formula for `S̃` in (3.20), and the derivative-at-zero consequence of evenness |
| `StressTensor/AuxiliaryEquation.lean` | Algebraic encodings of the two long expansions (3.13)--(3.14), checked regrouping into (3.15)--(3.16), axis formulas, and equivalence with CK normal form (3.23) |
| `StressTensor/AxisFormulas.lean` | Exact `y=0` formulas for `C̃`, `S̃`, its derivatives, and the specialized coefficients displayed after (3.22) |
| `StressTensor/Bounds.lean` | Elementary `U → V` estimates (3.17)--(3.18), the geometric portion of (3.19), `Γ₁ ≥ 1/2`, and the modular noncharacteristic bound `c₀ ≥ (q-1)/2¹⁰` |
| `StressTensor/Symmetry.lean` | Algebraic reflection `y ↦ -y`, parity of the jet and coefficients, and invariance of `R` and `G` |
| `StressTensor/AnalyticInterface.lean` | Actual iterated derivatives, the auxiliary PDE, the explicit CK result interface, uniqueness-implies-evenness, and localized spacelike-gradient consequences |
| `StressTensor/ReflectionBridge.lean` | Actual derivative, scalar-data, PDE, Cauchy-data, and analyticity preservation under reflection; evenness on a symmetric CK domain |
| `StressTensor/DifferentialBridge.lean` | Actual chain/product rules for (3.13)--(3.14) and the off-axis divergence identity (3.11) for the defined factored singular-stress fields, under explicit differentiability hypotheses |
| `StressTensor/CauchyDataBridge.lean` | The prescribed Cauchy data imply the exact axis jet `(0,-1,0,0,0)`, the formula `Γ₀(0,y)=-2+y²`, and hence `Γ₀(0,0)=-2` |
| `StressTensor/SectionFourCore.lean` | Construction of conjugate parameters from `p>2`, endpoint exponents, quarter-turn algebra (4.6), area-gradient rotation, and the conditional duality step (4.7) |
| `StressTensor/StressPotential.lean` | The actual interval-integral candidate (4.1), vertical a.e. FTC, dominated differentiation in `x`, and one-sided integration of the off-axis divergence relation (4.2)--(4.4) |
| `StressTensor/StressBounds.lean` | Explicit lower and upper component bounds obtained from the localized Section 3 scalar data |
| `StressTensor/EndpointRegularity.lean` | Distribution-function definition of weak `L^(p/2)`, rotation invariance, guarded finite-Lorentz tails, and a general differentiable blow-up criterion |
| `StressTensor/LowerGrowth.lean` | Exact integration of `y^(-2/p)`, the cusp lower bound, and direct failure of local Lipschitz continuity from localized segment bounds |
| `StressTensor/VariationalTransfer.lean` | Area density/functional, supporting-calibration comparison, admissible-field minimality, strict uniqueness, and an explicit placeholder for the external BV relaxation theorem |
| `StressTensor/SectionFourTransfer.lean` | An assembled a.e. endpoint/duality/non-Lipschitz transfer theorem from explicit localized data |

Import `StressTensor` to use all modules in this project.
See `FORMALIZATION_STATUS.md` for an equation-by-equation coverage table.

## What is kernel-checked

The following claims are proved without additional mathematical assumptions
beyond those displayed in their theorem signatures:

- the two first-derivative formulas for `u(x,y)=x+y²γ(x,y)`;
- `|Du|² = 1 + y²Γ₀` at the level of the recorded jet;
- the removable value, evenness, quotient identity, and exact deficit
  factorization for `C̃`;
- equality of the integral and quotient forms of `C̃` when the real-power base
  stays positive on the integration segment;
- the `d`-derivative of `C̃` and the displayed logarithmic derivative identity
  for `S̃`, under explicit positivity hypotheses;
- the real-power bookkeeping and vector stress factorization, with positivity
  and nonzero assumptions made explicit;
- the exact polynomial regrouping of the encoded expansions as
  `R = c₀γₓₓ + 2c₁γₓᵧ + c₂γᵧᵧ + L₀`;
- the actual chain/product-rule expansions and the divergence identity
  `div(factored stress)=|y|^(-2/p) R` off `y=0`, under the displayed
  derivative, mixed-partial, and joint-differential hypotheses;
- `R=0 ↔ γₓₓ=G` whenever `c₀≠0`;
- the finite-dimensional bounds sending `U_q` into `V_q`, including
  `Γ₀<-1`, `Γ₁≥1/2`, and the noncharacteristic lower bound from the stated
  scalar estimates;
- invariance of the differential expression under transverse reflection;
- preservation of the actual auxiliary equation, analyticity, and Cauchy data
  under reflection, and evenness of a unique solution on a symmetric domain;
- recovery of the exact five-component initial jet and
  `Γ₀(0,y)=-2+y²`, including `Γ₀(0,0)=-2`, from the prescribed Cauchy data;
- `ansatzGradient=(1,0)` on `y=0` and its squared norm is below `1` off the
  axis after localization to `U_q`.

For Section 4, Lean additionally checks:

- every `p>2` determines the conjugate parameter package used by the earlier
  modules, and `0 < 2/p < 1`, `0 < 1-2/p < 1`, `p/2>1`;
- the quarter-turn preserves the squared Euclidean norm and commutes with the
  defined radial area-gradient map;
- the candidate `v(x,y)=∫₀ʸ F₁(x,τ)dτ` is zero on the axis, is absolutely
  continuous on each integrable vertical slice, and has vertical derivative
  `F₁` almost everywhere;
- the dominated parameter-integral theorem and the two one-sided FTC/zero-flux
  arguments used to obtain the horizontal derivative `-F₂`;
- the lower estimate `F₁ ≥ 1/(16|y|^(2/p))` from `S≥1/8` and `Γ₁≥1/2`;
- the exact integral
  `∫₀ʸ τ^(-2/p)dτ = y^(1-2/p)/(1-2/p)` for `y≥0`, the corresponding lower
  growth of `v`, and direct non-Lipschitzness at an axis point under the stated
  localized segment hypotheses;
- invariance of the weak distribution estimate under the quarter-turn and a
  logarithmic criterion ruling out every guarded finite Lorentz tail;
- the supporting-hyperplane integration argument proving minimality for an
  explicitly supplied admissible class of gradient fields;
- transfer of weak endpoint, a.e. duality, and non-Lipschitz conclusions by
  `sectionFour_endpoint_duality` from the recorded localized hypotheses.

## Explicit formalization boundary

The reference invokes Cauchy--Kowalevskaya to obtain a locally unique analytic
solution. `CKOutcome` records the existence/uniqueness data used by this
project: an open neighborhood, an analytic solution, its Cauchy data, and
local uniqueness. It is a structure that must be constructed from an external
CK theorem; it is not postulated as an axiom. Once such a value on a
`y`-symmetric domain is supplied, Lean proves that reflection preserves the
full solution predicate and derives evenness from uniqueness.

The following parts remain outside this project's proved core:

- a full formal proof of analyticity of the piecewise continuation `C̃` and
  `S̃` near `(0,-2)`;
- automatic discharge of the explicit derivative, mixed-partial, and joint
  `S̃`-differential hypotheses in `DifferentialBridge.lean` solely from the
  still-unproved local analyticity statements;
- a function-level neighborhood theorem identifying the original
  energy-gradient stress with the factored singular-stress fields before
  taking their divergence (the pointwise vector factorization is proved);
- derivation of every numerical lower bound in (3.19)--(3.20) from those
  analytic identities (the noncharacteristic theorem accepts the final two
  scalar inequalities explicitly);
- a formal Cauchy--Kowalevskaya theorem establishing `CKOutcome`;
- the compact-neighborhood shrinking argument and the final maximally
  extended light-ray conclusion, which also uses definitions and results from
  the earlier Section 2.3 not included in the attached text;
- construction of the localized Section 3 solution and automatic discharge of
  the uniform stress bounds, `∂ₓF₁` majorant, one-sided `F₂→0`, and weak
  `L^(p/2)` estimate used by Section 4;
- promotion of the fixed-slice derivative theorems to a two-dimensional a.e.
  Fréchet-gradient identity and the complete joint `C^(0,1-2/p)` segment
  estimate (4.5);
- proof that `areaGradient` is the Fréchet derivative of `areaDensity`, plus
  convexity/strict convexity and the Fenchel inverse (2.21); these enter through
  explicit supporting and inverse hypotheses;
- the zero-trace integration-by-parts theorem for the affine `W₀¹¹` Dirichlet
  class.  The proved calibration theorem currently operates on an explicitly
  supplied admissible class of gradient fields;
- the horizontal-strip distribution estimate needed to derive the logarithmic
  Lorentz lower bound (4.11).  Lean proves the contradiction once that lower
  bound is provided;
- first-order Sobolev, trace, BV relaxation, and recession-function theory
  sufficient to formalize Proposition 2.3. `RelaxationBridge.transfers_unique`
  is the typed placeholder for that cited result, not a proof of it;
- consequently, the unconditional existential statement of Theorem 4.1.

The singular stress is represented by a total Lean function.  Division by
zero assigns it the value zero on `y=0`; all identities that originate from
the off-axis stress formula are therefore stated off-axis or almost
everywhere.  This representative choice has no effect on integral statements.

This boundary is intentional: the project does not turn a cited theorem or an
omitted earlier result into an untracked Lean axiom.

## Confidentiality

The supplied PDF and pasted source text are not included in this deliverable.
During this task, no files were published, committed, pushed, or uploaded to a
public service. The project contains public dependency URLs, and building it
may download those dependencies. Keep the delivered archive private if
confidentiality is required.
