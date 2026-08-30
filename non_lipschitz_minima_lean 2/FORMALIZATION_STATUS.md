# Equation-by-equation status

“Proved” means checked by Lean with no project-defined axiom or proof
placeholder. “Conditional” means the theorem is proved from hypotheses shown
in its Lean signature. “Interface” means the cited external existence theorem
is represented by explicit data rather than asserted globally.

| Reference | Status | Lean location |
|---|---|---|
| (3.1)--(3.3) | Proved definitions and `HasDerivAt` formulas | `Definitions`, `Ansatz` |
| (3.4)--(3.5) | Proved jet-level squared-gradient identity | `Ansatz.normSq_ansatz` |
| (3.6) | Proved integral/quotient equality under positive-base hypothesis; removable value proved | `ScalarFactors`, `Ansatz` |
| Analyticity of `C̃` | Not yet proved | Explicit project boundary |
| (3.7)--(3.8) | Definitions, positivity/evenness, and exact `d` derivative proved conditionally | `Ansatz`, `ScalarDerivatives` |
| Analyticity of `S̃` | Not yet proved | Explicit project boundary |
| (3.9) | Proved exact deficit factorization | `Ansatz.deficit_factorization` |
| (3.10) | Proved vector stress factorization under positivity and `y ≠ 0` | `Ansatz.stressVector_factorization` |
| (3.11)--(3.12) | Proved off-axis divergence identity for the defined factored stress fields under explicit differentiability/full-differential hypotheses; a neighborhood bridge from the original energy-gradient stress is not packaged | `DifferentialBridge`; explicit boundary |
| (3.13)--(3.14) | Proved actual product/chain-rule expansions under the same explicit hypotheses | `DifferentialBridge` |
| (3.15)--(3.16) | Proved polynomial regrouping and axis simplifications | `AuxiliaryEquation`, `AxisFormulas` |
| (3.17)--(3.18) | Proved `U_q → V_q` and all finite-dimensional component bounds | `Bounds` |
| (3.19) | Proved `1 < -d < 4` and `|t²d| < 4ρ_q²`; the displayed base/rpow lower bound and final uniform `C̃,S̃` numerical bounds are not derived | `Bounds`; explicit boundary |
| Derivative identity in (3.20) | Proved under positive-base/positive-`C̃` hypotheses | `ScalarDerivatives.deriv_Stilde_d_div` |
| Lower bound in (3.20) | Accepted as the explicit scalar inequality needed downstream | `Bounds` |
| (3.21) | Proved from `S̃ ≥ 1/8` and the displayed derivative lower bound | `Bounds.coeff0_ge_q_sub_one_div_1024_of_inU` |
| (3.22)--(3.23) | Auxiliary equation defined; normal-form equivalence proved when `c₀ ≠ 0` | `AnalyticInterface`, `AuxiliaryEquation` |
| Axis extension formulas | Proved exactly when `Γ₀ < 0`; analyticity of the extension is not proved | `AxisFormulas` |
| (3.24), Cauchy data | Proved to determine the exact axis jet, `Γ₀(0,y)=-2+y²`, and the origin value `Γ₀(0,0)=-2` | `CauchyDataBridge` |
| (3.24), CK existence/uniqueness | Interface, not an axiom | `AnalyticInterface.CKOutcome` |
| Reflection/evenness | Proved for a `CKOutcome` on a `y`-symmetric domain | `ReflectionBridge` |
| Localization to a compact cube | Not yet proved | Explicit project boundary |
| (3.25), strict spacelikeness | Proved for the finite-dimensional `ansatzGradient` from membership in `U_q`; a packaged actual-gradient corollary, two-sided `C` bounds, and the light-ray conclusion are not proved | `AnalyticInterface`; explicit boundary |

The maximally extended light-ray conclusion also depends on definitions and
results from the earlier Section 2.3, which was not part of the supplied text.

## Section 4 status

Here “conditional” means that Lean proves the displayed implication from the
analytic or variational hypotheses in its theorem signature.  It does not
mean that those hypotheses have been silently postulated.

| Reference | Status | Lean location |
|---|---|---|
| `p>2`, `q=p/(p-1)` | Proved construction of `Params`, including conjugacy and the required ranges | `SectionFourCore.Params.ofP` |
| Exponents in Thm. 4.1 | Proved `0<2/p<1`, `0<1-2/p<1`, and `p/2>1` | `SectionFourCore` |
| (4.1) | Proved definition by oriented interval integral and zero trace on `y=0` | `StressPotential.candidateV`, `candidateV_zero` |
| Vertical part of (4.4) | Proved a.e. on each integrable vertical slice; absolute continuity also proved | `StressPotential.ae_hasDerivAt_candidateV_y`, `candidateV_absolutelyContinuousOnInterval` |
| (4.2), differentiation in `x` | Conditional theorem using Mathlib's dominated parametric-interval-integral theorem, with measurability, derivative, and majorant hypotheses explicit | `StressPotential.hasDerivAt_candidateV_x_of_dominated` |
| (4.3) off the axis | Proved from the auxiliary equation and the Section 3 differential bridge under explicit differentiability hypotheses | `StressPotential.singularStressDivergence_eq_zero_of_auxiliaryEquation` |
| (4.3) integrated across `y=0` | Proved separately for `y>0` and `y<0` from the derivative identity, interval integrability, endpoint continuity, and one-sided `F₂→0` | `StressPotential.integral_stressXDerivative_eq_neg_stressY_of_pos`, `_of_neg` |
| (4.4), full 2D a.e. gradient | Coordinate derivative assembly proved pointwise; the Fubini/Sobolev upgrade to a 2D a.e. Fréchet derivative is not yet proved | `StressPotential.candidateV_coordinate_derivatives`; explicit boundary |
| (4.5), axis growth | Upper bound available from a generic integral majorant; exact lower power growth proved from localized `InU` and `S≥1/8` | `StressPotential.abs_candidateV_le_abs_integral_of_bound`, `LowerGrowth.candidateV_lower_growth` |
| (4.5), joint Hölder estimate | Not yet proved; requires the scalar segment estimate and horizontal component localization | Explicit boundary |
| (4.6) | Proved quarter-turn component, linearity, double-turn, inner-product, and squared-norm identities | `SectionFourCore` |
| (4.7) | Proved rotation of the defined radial area-gradient; the field statement is a.e. and conditional on the Fenchel inverse identity | `SectionFourCore.areaGradient_quarterTurn`, `VariationalTransfer.areaGradient_candidate_field_ae` |
| (4.8), calibration comparison | Generic supporting-hyperplane integration and admissible-gradient-field minimality proved | `VariationalTransfer.areaFunctional_le_of_calibration`, `isMinimizer_areaFunctional_of_calibration` |
| (4.8), Sobolev Dirichlet class | Not yet proved: convex support, zero-trace integration by parts, and equality of functions from gradients/traces are explicit boundaries | `SupportsAreaDensity`; explicit boundary |
| Strict uniqueness | Abstract strict-comparison theorem proved | `VariationalTransfer.isUniqueMinimizer_of_strict` |
| Proposition 2.3 / generalized minimizer | Typed placeholder/interface, not a proof of the cited BV relaxation theorem | `VariationalTransfer.RelaxationBridge` |
| (4.9)--(4.10), pointwise stress lower bound | Proved `F₁≥1/(16|y|^(2/p))` from `InU` and `S≥1/8` | `StressBounds.one_div_sixteen_singularDenominator_le_stressX` |
| (4.10), non-Lipschitzness | Proved directly from the integrated lower growth and localized segment hypotheses; no pointwise differentiability assumption is needed | `LowerGrowth.candidateV_not_lipschitzNearAt_of_segment_bounds` |
| Weak `L^(p/2)` transfer | Proved invariant under quarter-turn using the custom distribution-function definition | `EndpointRegularity.candidateGradient_inWeakLp_iff` |
| (4.11), finite Lorentz failure | Proved from an explicit logarithmic lower bound, with positive exponents, finite domain measure, and truncation integrability guarded in the definition; the strip-measure lower bound itself is not yet proved | `EndpointRegularity.not_finiteLorentzOn_of_log_lower` |
| Assembled endpoint result | Conditional transfer of weak endpoint, a.e. duality, and non-Lipschitzness | `SectionFourTransfer.sectionFour_endpoint_duality` |
| Theorem 4.1 as stated | Not yet proved unconditionally | Explicit project boundary |

### Source corrections reflected in Lean

- The off-axis stress representative is totalized to zero on `y=0`, so (4.7)
  is formulated almost everywhere and blow-up bounds exclude the axis.
- The lower bound corresponding to (4.10) is stated only for nonzero `y`.
- The local finite-Lorentz statement is represented through guarded
  distribution-function tails rather than treating the closed strip `S_p` as
  an open Sobolev domain.
- The variational theorem says “global minimizer in the supplied admissible
  class,” matching the displayed comparison rather than the weaker prose
  “local minimizer.”
- The generalized-minimizer transfer is described as unique, matching the
  proof preceding Theorem 4.1; it is not claimed until a `RelaxationBridge` is
  supplied.
