/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# A moving-chart formula for covariant differentiation along a curve

This file constructs a moving-chart candidate for the covariant derivative of a tangent field
along a curve.  At a parameter `t`, both the curve and the field are read in the tangent-bundle
trivialization coming from the chart centred at the current point `γ t`.  If `u` and `v` are those
coordinate readings and `Γ` is the Christoffel map of the connection in that frame, the defining
formula is

`D V / dt = v' + Γ(v, u')`.

The result is transported back to `TangentSpace I (γ t)`.  Thus the definition uses the chart at
the current point rather than a single global chart.  Derivatives are taken within a parameter
set `s`, so that the construction applies on a closed interval as well as on all of `𝕜`; the
unrestricted operator is the `s = Set.univ` case, exactly as Mathlib's `fderiv` is the
`Set.univ` case of `fderivWithin`.  This first part of the along-curve API proves the
characteristic additive and scalar Leibniz laws, locality in the field and parameter set, and
naturality under differentiable reparametrization.  For a field pulled back from an ambient vector
field, `AlongCurve/Pullback.lean` identifies the formula in an arbitrary fixed chart and with the
ambient covariant derivative.

## Main definitions and results

* `TauCeti.Manifold.sectionCoord`: the coordinate reading of a tangent field along a curve in a
  specified tangent-bundle trivialization; see `VectorBundle/SectionAlongCurve/Basic.lean`.
* `CovariantDerivative.alongCurveInChartWithin`: the model-space formula `v' + Γ(v, u')` within
  a parameter set, computed by `CovariantDerivative.alongCurveInChartWithin_apply`.
* `CovariantDerivative.alongCurveWithin`: the resulting tangent field along the curve, computed
  by `CovariantDerivative.alongCurveWithin_apply`, and its unrestricted case
  `CovariantDerivative.alongCurve`; `CovariantDerivative.alongCurveWithin_univ` relates them.
* `CovariantDerivative.alongCurveWithin_add`, `CovariantDerivative.alongCurveWithin_smul` and
  `CovariantDerivative.alongCurveWithin_const_smul`: additivity, the scalar Leibniz rule, and
  scalar homogeneity; each has an unrestricted counterpart.
* `CovariantDerivative.alongCurveWithin_zero`: the zero-field law, with
  `CovariantDerivative.alongCurve_zero` its unrestricted case.
* `CovariantDerivative.alongCurveWithin_sum` and `CovariantDerivative.alongCurve_sum`: additivity
  over finite sums of fields with differentiable coordinate readings.
* `CovariantDerivative.alongCurveWithin_const`: along a constant curve the candidate is the
  ordinary derivative of the field, with `CovariantDerivative.alongCurve_const` its unrestricted
  case; `CovariantDerivative.alongCurveWithin_const_of_hasDerivWithinAt` and
  `CovariantDerivative.alongCurve_const_of_hasDerivAt` read off a known derivative.
* `CovariantDerivative.alongCurveWithin_inter`, `CovariantDerivative.alongCurveWithin_of_mem_nhds`,
  `CovariantDerivative.alongCurveWithin_subset`, `CovariantDerivative.alongCurveWithin_congr`, and
  `CovariantDerivative.alongCurveWithin_comp`: parameter-set and field locality and
  reparametrization, with
  `CovariantDerivative.alongCurve_congr` and `CovariantDerivative.alongCurve_comp` their
  unrestricted cases.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhauser, 1992, Ch. 2, Proposition 2.2.
* The moving-chart construction was informed by
  `formalized-sources/DoCarmo/DoCarmoLib/Riemannian/Connection/CovariantDerivativeAlong.lean` and
  `formalized-sources/DoCarmo/DoCarmoLib/Riemannian/Connection/AffineCovariantDerivativeAlong.lean`
  in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture) repository
  at revision `24f32e4d600878bfaac6bc2f2f9324175571c321`; this implementation instead uses Mathlib's
  `CovariantDerivative` and Tau Ceti's `christoffelMap` directly.
-/

public section

open Bundle Filter
open scoped Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

variable (cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  (γ : 𝕜 → M) (V : ∀ t, TangentSpace I (γ t))

/-- The moving-chart coordinate formula for `V` along `γ` in the chart centred at `x`, taken
within the parameter set `s`: `v' + Γ(v, u')`, where `u = extChartAt I x ∘ γ` and
`v = sectionCoord γ V x` are the coordinate readings of the curve and the field, their
derivatives are taken within `s`, and `Γ` is the Christoffel map of `cov` in the local frame of
the fixed basis `Module.finBasis 𝕜 E`.  Its chart independence and agreement with an ambient
derivative are established for fields pulled back from ambient vector fields by
`CovariantDerivative.symmL_alongCurveInChartWithin_pullback`; they remain open here for a general
section along the curve.  When the coordinate readings are not differentiable within `s` at `t`,
`UniqueDiffWithinAt 𝕜 s t` fails,
or `γ` does not stay in `(trivializationAt E (TangentSpace I) x).baseSet` near `t` within `s`, its
components may carry their junk value `0`. -/
def alongCurveInChartWithin (s : Set 𝕜) (x : M) (t : 𝕜) : E :=
  derivWithin (sectionCoord (F := E) γ V x) s t +
    christoffelMap (Module.finBasis 𝕜 E)
      (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet)) (γ t)
        (sectionCoord (F := E) γ V x t) (derivWithin (extChartAt I x ∘ γ) s t)

/-- The defining formula for the coordinate covariant derivative within a parameter set. -/
theorem alongCurveInChartWithin_apply (s : Set 𝕜) (x : M) (t : 𝕜) :
    alongCurveInChartWithin cov γ V s x t =
      derivWithin (sectionCoord (F := E) γ V x) s t +
        christoffelMap (Module.finBasis 𝕜 E)
          (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet))
            (γ t) (sectionCoord (F := E) γ V x t) (derivWithin (extChartAt I x ∘ γ) s t) :=
  (rfl)

/-- The moving-chart candidate for the covariant derivative of `V` along `γ` within the parameter
set `s`, transported from the model space to `TangentSpace I (γ t)`.  Its identification with the
ambient covariant derivative is established for pulled-back fields by
`CovariantDerivative.alongCurveWithin_pullback`; it remains open here for a general section along
the curve.  It inherits the junk values of `alongCurveInChartWithin`.  The Christoffel map is read
in the local frame of the fixed basis `Module.finBasis 𝕜 E`. -/
def alongCurveWithin (s : Set 𝕜) (t : 𝕜) : TangentSpace I (γ t) :=
  (trivializationAt E (TangentSpace I) (γ t)).symmL 𝕜 (γ t)
    (alongCurveInChartWithin cov γ V s (γ t) t)

/-- The defining formula for the along-curve candidate within a parameter set: the coordinate
formula in the chart at the current point, transported back to the tangent space there. -/
theorem alongCurveWithin_apply (s : Set 𝕜) (t : 𝕜) :
    alongCurveWithin cov γ V s t =
      (trivializationAt E (TangentSpace I) (γ t)).symmL 𝕜 (γ t)
        (alongCurveInChartWithin cov γ V s (γ t) t) :=
  (rfl)

variable {γ} in
/-- In the trivialization `C` at `γ t`, the covariant derivative along `γ` of `Q` is the ordinary
derivative of its coordinate reading plus the Christoffel term. -/
theorem continuousLinearMapAt_alongCurveWithin
    {s : Set 𝕜} {t : 𝕜} {C : TangentSpace I (γ t) →L[𝕜] E}
    (hC : C = (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt 𝕜 (γ t))
    (Q : ∀ r, TangentSpace I (γ r)) :
    C (alongCurveWithin cov γ Q s t) =
      derivWithin (sectionCoord (F := E) γ Q (γ t)) s t +
        christoffelMap (Module.finBasis 𝕜 E)
          (cov.isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t)
          (C (Q t)) (derivWithin (extChartAt I (γ t) ∘ γ) s t) := by
  subst hC
  rw [alongCurveWithin_apply, Trivialization.continuousLinearMapAt_symmL
      _ (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)),
    alongCurveInChartWithin_apply, sectionCoord_apply]

/-- The junk value of the along-curve candidate: it vanishes where the parameter set does not have
unique derivatives, because `derivWithin` is then `0`. -/
theorem alongCurveWithin_of_not_uniqueDiffWithinAt {s : Set 𝕜} {t : 𝕜}
    (hu : ¬UniqueDiffWithinAt 𝕜 s t) : alongCurveWithin cov γ V s t = 0 := by
  simp [alongCurveWithin_apply, alongCurveInChartWithin_apply,
    derivWithin_zero_of_not_uniqueDiffWithinAt hu]
  rfl

/-- At a zero of a field, its covariant derivative is its ordinary coordinate derivative
in the canonical tangent trivialization at that point. -/
theorem alongCurveWithin_eq_derivWithin_sectionCoord_of_eq_zero {s : Set 𝕜} {t : 𝕜}
    (hV : V t = 0) :
    alongCurveWithin cov γ V s t = derivWithin (sectionCoord (F := E) γ V (γ t)) s t := by
  simp [alongCurveWithin_apply, alongCurveInChartWithin_apply, sectionCoord_apply, hV, map_zero]
  rfl

/-- The moving-chart candidate for the covariant derivative of `V` along `γ`, with unrestricted
derivatives.  This is the `s = Set.univ` case of `alongCurveWithin`, and carries the same junk
values and the same fixed local frame. -/
def alongCurve (t : 𝕜) : TangentSpace I (γ t) :=
  alongCurveWithin cov γ V Set.univ t

/-- Restricting the moving-chart candidate to the whole parameter space gives its unrestricted
version. -/
@[simp]
theorem alongCurveWithin_univ (t : 𝕜) :
    alongCurveWithin cov γ V Set.univ t = alongCurve cov γ V t :=
  (rfl)

/-- The defining formula for the unrestricted along-curve candidate: the coordinate formula in
the chart at the current point, transported back to the tangent space there. -/
theorem alongCurve_apply (t : 𝕜) :
    alongCurve cov γ V t =
      (trivializationAt E (TangentSpace I) (γ t)).symmL 𝕜 (γ t)
        (alongCurveInChartWithin cov γ V Set.univ (γ t) t) :=
  (rfl)

/-! ### Algebra laws -/

/-- The coordinate formula within a parameter set is additive in the field. -/
private theorem alongCurveInChartWithin_add (W : ∀ t, TangentSpace I (γ t)) (s : Set 𝕜)
    (x : M) {t : 𝕜}
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V x) s t)
    (hW : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ W x) s t) :
    alongCurveInChartWithin cov γ (fun r ↦ V r + W r) s x t =
      alongCurveInChartWithin cov γ V s x t + alongCurveInChartWithin cov γ W s x t := by
  rw [alongCurveInChartWithin_apply, alongCurveInChartWithin_apply,
    alongCurveInChartWithin_apply, sectionCoord_add, derivWithin_add hV hW]
  simp only [Pi.add_apply, map_add, add_apply]
  abel

/-- The moving-chart candidate within a parameter set is additive in the field. -/
theorem alongCurveWithin_add (W : ∀ t, TangentSpace I (γ t)) (s : Set 𝕜) {t : 𝕜}
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ W (γ t)) s t) :
    alongCurveWithin cov γ (fun r ↦ V r + W r) s t =
      alongCurveWithin cov γ V s t + alongCurveWithin cov γ W s t := by
  rw [alongCurveWithin_apply, alongCurveWithin_apply, alongCurveWithin_apply,
    alongCurveInChartWithin_add cov γ V W s (γ t) hV hW, map_add]

/-- The unrestricted moving-chart candidate is additive in the field. -/
theorem alongCurve_add (W : ∀ t, TangentSpace I (γ t)) {t : 𝕜}
    (hV : DifferentiableAt 𝕜 (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt 𝕜 (sectionCoord (F := E) γ W (γ t)) t) :
    alongCurve cov γ (fun r ↦ V r + W r) t =
      alongCurve cov γ V t + alongCurve cov γ W t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact alongCurveWithin_add cov γ V W Set.univ hV.differentiableWithinAt
    hW.differentiableWithinAt

/-- The coordinate formula within a parameter set respects subtraction of fields. -/
private theorem alongCurveInChartWithin_sub (W : ∀ t, TangentSpace I (γ t)) (s : Set 𝕜)
    (x : M) {t : 𝕜}
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V x) s t)
    (hW : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ W x) s t) :
    alongCurveInChartWithin cov γ (fun r ↦ V r - W r) s x t =
      alongCurveInChartWithin cov γ V s x t - alongCurveInChartWithin cov γ W s x t := by
  rw [alongCurveInChartWithin_apply, alongCurveInChartWithin_apply,
    alongCurveInChartWithin_apply, sectionCoord_sub, derivWithin_sub hV hW]
  simp only [Pi.sub_apply, map_sub, sub_apply]
  abel

/-- Covariant differentiation within a parameter set respects subtraction of differentiable
fields. -/
theorem alongCurveWithin_sub (W : ∀ t, TangentSpace I (γ t)) (s : Set 𝕜) {t : 𝕜}
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ W (γ t)) s t) :
    alongCurveWithin cov γ (fun r ↦ V r - W r) s t =
      alongCurveWithin cov γ V s t - alongCurveWithin cov γ W s t := by
  rw [alongCurveWithin_apply, alongCurveWithin_apply, alongCurveWithin_apply,
    alongCurveInChartWithin_sub cov γ V W s (γ t) hV hW, map_sub]

/-- Covariant differentiation along a curve respects subtraction of differentiable fields. -/
theorem alongCurve_sub (W : ∀ t, TangentSpace I (γ t)) {t : 𝕜}
    (hV : DifferentiableAt 𝕜 (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt 𝕜 (sectionCoord (F := E) γ W (γ t)) t) :
    alongCurve cov γ (fun r ↦ V r - W r) t =
      alongCurve cov γ V t - alongCurve cov γ W t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact alongCurveWithin_sub cov γ V W Set.univ hV.differentiableWithinAt
    hW.differentiableWithinAt

/-- The coordinate formula within a parameter set obeys the scalar Leibniz rule. -/
private theorem alongCurveInChartWithin_smul (f : 𝕜 → 𝕜) (s : Set 𝕜) (x : M) {t : 𝕜}
    (hf : DifferentiableWithinAt 𝕜 f s t)
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V x) s t) :
    alongCurveInChartWithin cov γ (fun r ↦ f r • V r) s x t =
      derivWithin f s t • sectionCoord (F := E) γ V x t +
        f t • alongCurveInChartWithin cov γ V s x t := by
  rw [alongCurveInChartWithin_apply, alongCurveInChartWithin_apply, sectionCoord_smul,
    derivWithin_smul hf hV]
  simp only [Pi.smul_apply', map_smul, smul_add]
  abel

/-- The moving-chart candidate within a parameter set obeys the scalar Leibniz rule. -/
theorem alongCurveWithin_smul (f : 𝕜 → 𝕜) (s : Set 𝕜) {t : 𝕜}
    (hf : DifferentiableWithinAt 𝕜 f s t)
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V (γ t)) s t) :
    alongCurveWithin cov γ (fun r ↦ f r • V r) s t =
      derivWithin f s t • V t + f t • alongCurveWithin cov γ V s t := by
  rw [alongCurveWithin_apply, alongCurveWithin_apply,
    alongCurveInChartWithin_smul cov γ V f s (γ t) hf hV, map_add, map_smul, map_smul,
    sectionCoord_apply,
    (trivializationAt E (TangentSpace I) (γ t)).symmL_continuousLinearMapAt (R := 𝕜)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)) (V t)]

/-- The unrestricted moving-chart candidate obeys the scalar Leibniz rule. -/
theorem alongCurve_smul (f : 𝕜 → 𝕜) {t : 𝕜} (hf : DifferentiableAt 𝕜 f t)
    (hV : DifferentiableAt 𝕜 (sectionCoord (F := E) γ V (γ t)) t) :
    alongCurve cov γ (fun r ↦ f r • V r) t =
      deriv f t • V t + f t • alongCurve cov γ V t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ, ← derivWithin_univ]
  exact alongCurveWithin_smul cov γ V f Set.univ hf.differentiableWithinAt
    hV.differentiableWithinAt

/-- The coordinate formula within a parameter set commutes with multiplication by a constant
scalar, without a differentiability hypothesis on the field. -/
private theorem alongCurveInChartWithin_const_smul (c : 𝕜) (s : Set 𝕜) (x : M) (t : 𝕜) :
    alongCurveInChartWithin cov γ (fun r ↦ c • V r) s x t =
      c • alongCurveInChartWithin cov γ V s x t := by
  have hcoord : sectionCoord (F := E) γ (fun r ↦ c • V r) x =
      c • sectionCoord (F := E) γ V x := by
    rw [sectionCoord_smul (F := E) γ V (fun _ ↦ c) x]
    rfl
  rw [alongCurveInChartWithin_apply, alongCurveInChartWithin_apply, hcoord,
    derivWithin_const_smul_field]
  simp only [Pi.smul_apply, map_smul, smul_apply, smul_add]

/-- The moving-chart candidate within a parameter set commutes with multiplication by a constant
scalar, without a differentiability hypothesis on the field. -/
@[simp]
theorem alongCurveWithin_const_smul (c : 𝕜) (s : Set 𝕜) (t : 𝕜) :
    alongCurveWithin cov γ (fun r ↦ c • V r) s t = c • alongCurveWithin cov γ V s t := by
  rw [alongCurveWithin_apply, alongCurveWithin_apply,
    alongCurveInChartWithin_const_smul cov γ V c s (γ t) t, map_smul]

/-- The unrestricted moving-chart candidate commutes with multiplication by a constant scalar,
without a differentiability hypothesis on the field. -/
@[simp]
theorem alongCurve_const_smul (c : 𝕜) (t : 𝕜) :
    alongCurve cov γ (fun r ↦ c • V r) t = c • alongCurve cov γ V t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact alongCurveWithin_const_smul cov γ V c Set.univ t

/-- The moving-chart candidate of the zero field within a parameter set is zero. -/
@[simp]
theorem alongCurveWithin_zero (s : Set 𝕜) (t : 𝕜) :
    alongCurveWithin cov γ (fun r : 𝕜 ↦ (0 : TangentSpace I (γ r))) s t = 0 := by
  rw [alongCurveWithin_apply, alongCurveInChartWithin_apply, sectionCoord_zero (γ := γ)]
  simp only [derivWithin_zero, Pi.zero_apply, map_zero, zero_apply, add_zero]

/-- The unrestricted moving-chart candidate of the zero field is zero. -/
@[simp]
theorem alongCurve_zero (t : 𝕜) :
    alongCurve cov γ (fun r : 𝕜 ↦ (0 : TangentSpace I (γ r))) t = 0 := by
  rw [← alongCurveWithin_univ]
  exact alongCurveWithin_zero cov γ Set.univ t

/-! ### Constant curves -/

/-- Along a constant curve at `x`, the moving-chart candidate within a parameter set is the
ordinary derivative within that set of the field, read in the model space `E = T_x M`.  No
differentiability of the field is needed; where the set does not have unique derivatives at `t`,
both sides are `0`. -/
@[simp]
theorem alongCurveWithin_const (x : M) (W : 𝕜 → E) {s : Set 𝕜} {t : 𝕜} :
    alongCurveWithin cov (fun _ : 𝕜 ↦ x) W s t = derivWithin W s t := by
  have hx := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  set L : E ≃L[𝕜] E := (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt 𝕜 x hx
  have hcoord : sectionCoord (F := E) (V := TangentSpace I) (fun _ : 𝕜 ↦ x) W x = L ∘ W :=
    funext fun r ↦ (sectionCoord_apply (F := E) (V := TangentSpace I) _ W x r).trans
      (congrFun (Trivialization.coe_continuousLinearEquivAt_eq (R := 𝕜) _ hx) (W r)).symm
  -- Unfold the candidate by `change`: `W` is `E`-valued, so rewriting with the defining lemmas
  -- would have to see through the identification `TangentSpace I x = E`.
  change (trivializationAt E (TangentSpace I) x).symmL 𝕜 x
      (derivWithin (sectionCoord (F := E) (V := TangentSpace I) (fun _ : 𝕜 ↦ x) W x) s t +
        christoffelMap (Module.finBasis 𝕜 E)
          (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet)) x
            (sectionCoord (F := E) (V := TangentSpace I) (fun _ : 𝕜 ↦ x) W x t)
            (derivWithin (extChartAt I x ∘ fun _ : 𝕜 ↦ x) s t)) = _
  by_cases hs : UniqueDiffWithinAt 𝕜 s t
  swap
  · simp only [derivWithin_zero_of_not_uniqueDiffWithinAt hs, map_zero, add_zero]
    rfl
  -- `L` is an equivalence, so it commutes with `derivWithin` even where `W` is not
  -- differentiable.
  have hderiv : derivWithin (L ∘ W) s t = L (derivWithin W s t) := by
    simp only [derivWithin, L.comp_fderivWithin hs]
    rfl
  have hchart : derivWithin (extChartAt I x ∘ fun _ : 𝕜 ↦ x) s t = 0 := by
    rw [Function.comp_def, derivWithin_fun_const, Pi.zero_apply]
  rw [hcoord, hderiv, hchart, map_zero, add_zero,
    ← Trivialization.symm_continuousLinearEquivAt_eq _ hx]
  exact L.symm_apply_apply _

/-- Along a constant curve at `x`, the unrestricted moving-chart candidate is the ordinary
derivative of the field, read in the model space `E = T_x M`. -/
@[simp]
theorem alongCurve_const (x : M) (W : 𝕜 → E) (t : 𝕜) :
    alongCurve cov (fun _ : 𝕜 ↦ x) W t = deriv W t :=
  (alongCurveWithin_univ cov _ W t).symm.trans
    ((alongCurveWithin_const cov x W).trans
      (congrFun (derivWithin_univ (f := W)) t))

/-- Along a constant curve at `x`, the moving-chart candidate within a parameter set is the
ordinary derivative of the field in the fixed tangent space `TangentSpace I x`. -/
theorem alongCurveWithin_const_of_hasDerivWithinAt (x : M) {W : 𝕜 → TangentSpace I x}
    {W' : TangentSpace I x} {s : Set 𝕜} {t : 𝕜} (hW : HasDerivWithinAt W W' s t)
    (hs : UniqueDiffWithinAt 𝕜 s t) :
    alongCurveWithin cov (fun _ ↦ x) W s t = W' := by
  -- The fibre carries only its topology here; borrow the norm of the model space `E`, which
  -- induces that topology, to read off the derivative.
  let _ : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let _ : NormedSpace 𝕜 (TangentSpace I x) := inferInstanceAs (NormedSpace 𝕜 E)
  exact (alongCurveWithin_const cov x W).trans (hW.derivWithin hs)

/-- Along a constant curve at `x`, the unrestricted moving-chart candidate is the ordinary
derivative of the field in the fixed tangent space `TangentSpace I x`. -/
theorem alongCurve_const_of_hasDerivAt (x : M) {W : 𝕜 → TangentSpace I x} {W' : TangentSpace I x}
    {t : 𝕜} (hW : HasDerivAt W W' t) :
    alongCurve cov (fun _ ↦ x) W t = W' := by
  rw [← alongCurveWithin_univ]
  refine alongCurveWithin_const_of_hasDerivWithinAt cov x ?_ uniqueDiffWithinAt_univ
  -- `HasDerivAt.hasDerivWithinAt` needs a normed target, which the fibre lacks. Both predicates
  -- are `HasDerivAtFilter` at a filter, so rewriting `𝓝[univ] t` to `𝓝 t` turns the goal into
  -- `HasDerivAtFilter W W' t (𝓝 t)`, the definition of `HasDerivAt W W' t`.
  rwa [HasDerivWithinAt, nhdsWithin_univ]

/-! ### Locality and reparametrization -/

/-- Intersecting the parameter set with a neighbourhood of `t` does not change the moving-chart
candidate there. -/
theorem alongCurveWithin_inter {s u : Set 𝕜} {t : 𝕜} (hu : u ∈ 𝓝 t) :
    alongCurveWithin cov γ V (s ∩ u) t = alongCurveWithin cov γ V s t := by
  rw [alongCurveWithin_apply, alongCurveWithin_apply, alongCurveInChartWithin_apply,
    alongCurveInChartWithin_apply, derivWithin_inter hu, derivWithin_inter hu]

/-- On a parameter set which is a neighbourhood of `t`, the restricted moving-chart candidate
equals the unrestricted one. -/
theorem alongCurveWithin_of_mem_nhds {s : Set 𝕜} {t : 𝕜} (hs : s ∈ 𝓝 t) :
    alongCurveWithin cov γ V s t = alongCurve cov γ V t := by
  rw [alongCurveWithin_apply, alongCurve_apply, alongCurveInChartWithin_apply,
    alongCurveInChartWithin_apply, derivWithin_of_mem_nhds hs, derivWithin_of_mem_nhds hs,
    derivWithin_univ, derivWithin_univ]

/-- Restricting the parameter set preserves the moving-chart candidate when derivatives on the
larger set are defined and the smaller set has a unique derivative at `t`. -/
theorem alongCurveWithin_subset {s u : Set 𝕜} {t : 𝕜} (hsu : s ⊆ u)
    (hs : UniqueDiffWithinAt 𝕜 s t)
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V (γ t)) u t)
    (hγ : DifferentiableWithinAt 𝕜 (extChartAt I (γ t) ∘ γ) u t) :
    alongCurveWithin cov γ V s t = alongCurveWithin cov γ V u t := by
  rw [alongCurveWithin_apply, alongCurveWithin_apply, alongCurveInChartWithin_apply,
    alongCurveInChartWithin_apply, derivWithin_subset hsu hs hV,
    derivWithin_subset hsu hs hγ]

/-- The moving-chart candidate within a parameter set depends only on the germ of the field along
that set, together with its value at the parameter under consideration. -/
theorem alongCurveWithin_congr {W : ∀ t, TangentSpace I (γ t)} {s : Set 𝕜} {t : 𝕜}
    (h : ∀ᶠ r in 𝓝[s] t, V r = W r) (ht : V t = W t) :
    alongCurveWithin cov γ V s t = alongCurveWithin cov γ W s t := by
  have hpoint : sectionCoord (F := E) γ V (γ t) t = sectionCoord (F := E) γ W (γ t) t := by
    rw [sectionCoord_apply, sectionCoord_apply, ht]
  have hcoord : sectionCoord (F := E) γ V (γ t) =ᶠ[𝓝[s] t]
      sectionCoord (F := E) γ W (γ t) := h.mono fun r hr ↦ by
    rw [sectionCoord_apply, sectionCoord_apply, hr]
  rw [alongCurveWithin_apply, alongCurveWithin_apply, alongCurveInChartWithin_apply,
    alongCurveInChartWithin_apply, hcoord.derivWithin_eq hpoint, hpoint]

/-- The unrestricted moving-chart candidate depends only on the germ of the field at the parameter
under consideration. -/
theorem alongCurve_congr {W : ∀ t, TangentSpace I (γ t)} {t : 𝕜}
    (h : ∀ᶠ r in 𝓝 t, V r = W r) : alongCurve cov γ V t = alongCurve cov γ W t := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ]
  exact alongCurveWithin_congr cov γ V (by rwa [nhdsWithin_univ]) h.self_of_nhds

/-- The moving-chart candidate within a parameter set is natural under differentiable
reparametrization mapping that set into the parameter set of the original curve. The curve and the
field must both read differentiably at `φ t` in the chart centred at `γ (φ t)`. -/
theorem alongCurveWithin_comp (φ : 𝕜 → 𝕜) {s s' : Set 𝕜} {t : 𝕜}
    (hφ : DifferentiableWithinAt 𝕜 φ s' t) (hmaps : Set.MapsTo φ s' s)
    (hγ : DifferentiableWithinAt 𝕜 (extChartAt I (γ (φ t)) ∘ γ) s (φ t))
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V (γ (φ t))) s (φ t)) :
    alongCurveWithin cov (γ ∘ φ) (fun r ↦ V (φ r)) s' t =
      derivWithin φ s' t • alongCurveWithin cov γ V s (φ t) := by
  have hVcomp : derivWithin (sectionCoord (F := E) γ V (γ (φ t)) ∘ φ) s' t =
      derivWithin φ s' t • derivWithin (sectionCoord (F := E) γ V (γ (φ t))) s (φ t) :=
    derivWithin.scomp t hV hφ hmaps
  have hγcomp : derivWithin ((extChartAt I (γ (φ t)) ∘ γ) ∘ φ) s' t =
      derivWithin φ s' t • derivWithin (extChartAt I (γ (φ t)) ∘ γ) s (φ t) :=
    derivWithin.scomp t hγ hφ hmaps
  rw [alongCurveWithin_apply, alongCurveWithin_apply, alongCurveInChartWithin_apply,
    alongCurveInChartWithin_apply, sectionCoord_comp, ← Function.comp_assoc]
  simp only [Function.comp_apply]
  rw [hVcomp, hγcomp, map_smul, ← smul_add, map_smul]

/-- The unrestricted moving-chart candidate is natural under differentiable reparametrization.
The curve and the field must both read differentiably at `φ t` in the chart centred at
`γ (φ t)`. -/
theorem alongCurve_comp (φ : 𝕜 → 𝕜) {t : 𝕜} (hφ : DifferentiableAt 𝕜 φ t)
    (hγ : DifferentiableAt 𝕜 (extChartAt I (γ (φ t)) ∘ γ) (φ t))
    (hV : DifferentiableAt 𝕜 (sectionCoord (F := E) γ V (γ (φ t))) (φ t)) :
    alongCurve cov (γ ∘ φ) (fun r ↦ V (φ r)) t =
      deriv φ t • alongCurve cov γ V (φ t) := by
  rw [← alongCurveWithin_univ, ← alongCurveWithin_univ, ← derivWithin_univ]
  exact alongCurveWithin_comp cov γ V φ hφ.differentiableWithinAt (Set.mapsTo_univ φ Set.univ)
    hγ.differentiableWithinAt hV.differentiableWithinAt

/-! ### Finite sums -/

/-- Covariant differentiation within a parameter set commutes with finite sums of fields having
differentiable coordinate readings. -/
theorem alongCurveWithin_sum {ι : Type*} (A : Finset ι) (W : ι → ∀ r, TangentSpace I (γ r))
    {s : Set 𝕜} {t : 𝕜}
    (hW : ∀ i ∈ A, DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ (W i) (γ t)) s t) :
    alongCurveWithin cov γ (fun r ↦ ∑ i ∈ A, W i r) s t =
      ∑ i ∈ A, alongCurveWithin cov γ (W i) s t := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have hWA : ∀ j ∈ A, DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ (W j) (γ t)) s t :=
      fun j hj ↦ hW j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [alongCurveWithin_add cov γ (W i) _ s (hW i (Finset.mem_insert_self i A))
      (differentiableWithinAt_sectionCoord_sum γ hWA), ih hWA]

/-- Covariant differentiation along a curve commutes with finite sums of fields having
differentiable coordinate readings. -/
theorem alongCurve_sum {ι : Type*} (A : Finset ι) (W : ι → ∀ r, TangentSpace I (γ r)) {t : 𝕜}
    (hW : ∀ i ∈ A, DifferentiableAt 𝕜 (sectionCoord (F := E) γ (W i) (γ t)) t) :
    alongCurve cov γ (fun r ↦ ∑ i ∈ A, W i r) t = ∑ i ∈ A, alongCurve cov γ (W i) t := by
  simpa only [alongCurveWithin_univ] using
    alongCurveWithin_sum cov γ A W (s := Set.univ) fun i hi ↦ (hW i hi).differentiableWithinAt

end CovariantDerivative
