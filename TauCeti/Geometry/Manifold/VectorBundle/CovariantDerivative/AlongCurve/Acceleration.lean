/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Chart

/-!
# The covariant acceleration of a curve

The *covariant acceleration* of a curve `γ` for a connection `∇` on the tangent bundle is the
covariant derivative of its velocity field along `γ`, `D_t γ'`.  It is the along-curve derivative
`CovariantDerivative.alongCurveWithin` of `AlongCurve/Basic.lean` specialised to the velocity
field `TauCeti.Manifold.curveVelocityWithin`, both taken within a parameter set `s`; the
unrestricted acceleration is the `s = Set.univ` case.  Geodesics are the curves whose covariant
acceleration for the Levi-Civita connection vanishes, and the first variation formula for the
energy integrates the inner product of the acceleration with the variation field.

In a chart the acceleration is the classical second-order expression `u'' + Γ (u', u')`, where
`u` is the curve read in the extended chart and `Γ` is the Christoffel map of the connection.  For
a `C²` curve this holds in *every* chart whose trivialization contains the current point of the
curve, by the chart independence `CovariantDerivative.symmL_alongCurveInChartWithin` of the
along-curve derivative.  Under a reparametrization `φ` the acceleration obeys the chain rule
`D_t (γ ∘ φ)' = φ'' γ'(φ t) + (φ')² D_t γ'(φ t)`.

## Main definitions and results

* `CovariantDerivative.accelerationWithin`: the covariant acceleration within a parameter set,
  unfolded by `CovariantDerivative.accelerationWithin_def`, and
  `CovariantDerivative.acceleration` its unrestricted case, unfolded by
  `CovariantDerivative.acceleration_def`.
* `CovariantDerivative.accelerationWithin_of_mem_nhds`: on a neighbourhood of the parameter the
  acceleration within the set is the unrestricted one.
* `CovariantDerivative.accelerationWithin_const`: a constant curve has zero acceleration.
* `CovariantDerivative.accelerationWithin_eq_symmL`: **the acceleration in a chart**,
  `u'' + Γ (u', u')` read in an arbitrary chart around the current point.
* `CovariantDerivative.accelerationWithin_eq_zero_iff`: the acceleration vanishes exactly when
  `u'' + Γ (u', u')` does in the chart at the current point.
* `CovariantDerivative.accelerationWithin_comp` and `CovariantDerivative.acceleration_comp`: the
  chain rule for the acceleration under reparametrization.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhauser, 1992, Ch. 2, §2 and Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4, the acceleration of a
  curve and its coordinate formula.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Basic

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  (cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)) (γ : 𝕜 → M)

/-- The **covariant acceleration** `D_t γ'` of the curve `γ` within the parameter set `s`: the
derivative along `γ`, for the connection `cov`, of the velocity field of `γ` within `s`.  It
inherits the junk values of `CovariantDerivative.alongCurveWithin` where the curve is not
differentiable or `s` does not have unique derivatives. -/
def accelerationWithin (s : Set 𝕜) (t : 𝕜) : TangentSpace I (γ t) :=
  alongCurveWithin cov γ (curveVelocityWithin I γ s) s t

/-- The **covariant acceleration** `D_t γ'` of the curve `γ`, with unrestricted derivatives.  This
is the `s = Set.univ` case of `CovariantDerivative.accelerationWithin`. -/
def acceleration (t : 𝕜) : TangentSpace I (γ t) :=
  accelerationWithin cov γ univ t

/-- The covariant acceleration within a parameter set is the derivative of the velocity field
along the curve. -/
theorem accelerationWithin_def (s : Set 𝕜) (t : 𝕜) :
    accelerationWithin cov γ s t = alongCurveWithin cov γ (curveVelocityWithin I γ s) s t :=
  (rfl)

/-- Restricting the acceleration to the whole parameter space gives the unrestricted
acceleration. -/
@[simp]
theorem accelerationWithin_univ (t : 𝕜) :
    accelerationWithin cov γ univ t = acceleration cov γ t :=
  (rfl)

/-- The unrestricted covariant acceleration is the unrestricted derivative of the unrestricted
velocity field along the curve. -/
theorem acceleration_def (t : 𝕜) :
    acceleration cov γ t = alongCurve cov γ (curveVelocity I γ) t := by
  rw [← accelerationWithin_univ, accelerationWithin_def, curveVelocityWithin_univ,
    alongCurveWithin_univ]

/-- On a parameter set which is a neighbourhood of `t`, the acceleration within that set is the
unrestricted acceleration: both the velocity near `t` and its derivative along the curve are then
the unrestricted ones. -/
theorem accelerationWithin_of_mem_nhds {s : Set 𝕜} {t : 𝕜} (hs : s ∈ 𝓝 t) :
    accelerationWithin cov γ s t = acceleration cov γ t := by
  have hcongr : ∀ᶠ r in 𝓝[s] t, curveVelocityWithin I γ s r = curveVelocity I γ r := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (interior_mem_nhds.mpr hs)] with r hr
    exact curveVelocityWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hr)
  rw [accelerationWithin_def, acceleration_def,
    alongCurveWithin_congr cov γ _ hcongr (curveVelocityWithin_of_mem_nhds hs),
    alongCurveWithin_of_mem_nhds cov γ _ hs]

/-- A constant curve has zero covariant acceleration within any parameter set. -/
@[simp]
theorem accelerationWithin_const (x : M) (s : Set 𝕜) (t : 𝕜) :
    accelerationWithin cov (fun _ : 𝕜 ↦ x) s t = 0 := by
  have hzero : curveVelocityWithin I (fun _ : 𝕜 ↦ x) s =
      fun r : 𝕜 ↦ (0 : TangentSpace I ((fun _ : 𝕜 ↦ x) r)) :=
    funext fun _ ↦ curveVelocityWithin_const x
  rw [accelerationWithin_def, hzero, alongCurveWithin_zero]

/-- A constant curve has zero unrestricted covariant acceleration. -/
@[simp]
theorem acceleration_const (x : M) (t : 𝕜) : acceleration cov (fun _ : 𝕜 ↦ x) t = 0 :=
  accelerationWithin_const cov x univ t

/-- The covariant acceleration vanishes exactly when the curve read in the extended chart at the
current point solves the second-order equation `u'' + Γ (u', u') = 0` there. -/
theorem accelerationWithin_eq_zero_iff {s : Set 𝕜} {t : 𝕜}
    (hs : UniqueDiffOn 𝕜 s) (hγ : MDifferentiableOn 𝓘(𝕜, 𝕜) I γ s) (ht : t ∈ s) :
    accelerationWithin cov γ s t = 0 ↔
      derivWithin (derivWithin (extChartAt I (γ t) ∘ γ) s) s t +
        christoffelMap (Module.finBasis 𝕜 E)
          (cov.isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t)
          (derivWithin (extChartAt I (γ t) ∘ γ) s t)
          (derivWithin (extChartAt I (γ t) ∘ γ) s t) = 0 := by
  set e := trivializationAt E (TangentSpace I) (γ t)
  have hmem : γ t ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  rw [accelerationWithin_def, alongCurveWithin_apply,
    alongCurveInChartWithin_curveVelocityWithin cov γ hs hγ ht hmem]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  -- The coordinate formula is transported by a fibrewise linear equivalence, so its vanishing is
  -- equivalent to the vanishing of its reading in the chart.
  have h' := congrArg (e.continuousLinearMapAt 𝕜 (γ t)) h
  rwa [e.continuousLinearMapAt_symmL (R := 𝕜) hmem, map_zero] at h'

/-- **The chain rule for the covariant acceleration.**  If `φ` maps the parameter set `u` into
`s` and is differentiable on `u`, with `derivWithin φ u` differentiable at `t`, then
`D_t (γ ∘ φ)' = φ''(t) γ'(φ t) + φ'(t)² D_t γ'(φ t)`.  The curve must be differentiable on `s`,
and its velocity field must read differentiably at `φ t` in the chart centred at `γ (φ t)`. -/
theorem accelerationWithin_comp {φ : 𝕜 → 𝕜} {s u : Set 𝕜} {t : 𝕜} (hu : UniqueDiffOn 𝕜 u)
    (ht : t ∈ u) (hφ : DifferentiableOn 𝕜 φ u)
    (hφ' : DifferentiableWithinAt 𝕜 (derivWithin φ u) u t) (hmaps : MapsTo φ u s)
    (hγ : MDifferentiableOn 𝓘(𝕜, 𝕜) I γ s)
    (hV : DifferentiableWithinAt 𝕜
      (sectionCoord (F := E) γ (curveVelocityWithin I γ s) (γ (φ t))) s (φ t)) :
    accelerationWithin cov (γ ∘ φ) u t =
      derivWithin (derivWithin φ u) u t • curveVelocityWithin I γ s (φ t) +
        derivWithin φ u t ^ 2 • accelerationWithin cov γ s (φ t) := by
  have hvelocity : ∀ r ∈ u, curveVelocityWithin I (γ ∘ φ) u r =
      derivWithin φ u r • curveVelocityWithin I γ s (φ r) := fun r hr ↦
    curveVelocityWithin_comp (hφ r hr).hasDerivWithinAt hmaps (hγ (φ r) (hmaps hr)) (hu r hr)
  have hcongr : curveVelocityWithin I (γ ∘ φ) u =ᶠ[𝓝[u] t]
      fun r ↦ derivWithin φ u r • curveVelocityWithin I γ s (φ r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hvelocity r hr
  have hchart : DifferentiableWithinAt 𝕜 (extChartAt I (γ (φ t)) ∘ γ) s (φ t) :=
    (hasDerivWithinAt_extChartAt_comp_curve
      (hasMFDerivWithinAt_curveVelocityWithin (hγ (φ t) (hmaps ht)))).differentiableWithinAt
  have hVcomp : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) (γ ∘ φ)
      (fun r ↦ curveVelocityWithin I γ s (φ r)) ((γ ∘ φ) t)) u t := by
    rw [sectionCoord_comp]
    exact hV.comp t (hφ t ht) hmaps
  rw [accelerationWithin_def, alongCurveWithin_congr cov (γ ∘ φ) _ hcongr (hvelocity t ht),
    alongCurveWithin_smul cov (γ ∘ φ) _ _ u hφ' hVcomp,
    alongCurveWithin_comp cov γ _ φ (hφ t ht) hmaps hchart hV, accelerationWithin_def, smul_smul,
    sq]

/-- **The chain rule for the unrestricted covariant acceleration**:
`D_t (γ ∘ φ)' = φ''(t) γ'(φ t) + φ'(t)² D_t γ'(φ t)`. -/
theorem acceleration_comp {φ : 𝕜 → 𝕜} {t : 𝕜} (hφ : Differentiable 𝕜 φ)
    (hφ' : DifferentiableAt 𝕜 (deriv φ) t) (hγ : MDifferentiable 𝓘(𝕜, 𝕜) I γ)
    (hV : DifferentiableAt 𝕜 (sectionCoord (F := E) γ (curveVelocity I γ) (γ (φ t))) (φ t)) :
    acceleration cov (γ ∘ φ) t =
      deriv (deriv φ) t • curveVelocity I γ (φ t) + deriv φ t ^ 2 • acceleration cov γ (φ t) := by
  rw [← accelerationWithin_univ, ← accelerationWithin_univ, ← curveVelocityWithin_univ,
    ← derivWithin_univ, ← derivWithin_univ]
  rw [← curveVelocityWithin_univ] at hV
  exact accelerationWithin_comp cov γ uniqueDiffOn_univ (mem_univ t) hφ.differentiableOn
    (by rwa [derivWithin_univ, differentiableWithinAt_univ]) (mapsTo_univ φ univ)
    hγ.mdifferentiableOn (hV.differentiableWithinAt)

end Basic

section Chart

variable [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  (cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)) (γ : 𝕜 → M)

/-- **The covariant acceleration in a chart.**  For a `C²` curve on a parameter set with unique
derivatives, the acceleration at `t` is the classical second-order expression `u'' + Γ (u', u')`,
for `u` the curve read in the extended chart at `x` and `Γ` the Christoffel map of `cov` there,
transported back from the trivialization at `x`.  The chart is arbitrary, provided its
trivialization contains `γ t`. -/
theorem accelerationWithin_eq_symmL {x : M} {s : Set 𝕜} {t : 𝕜} (hs : UniqueDiffOn 𝕜 s)
    (hγ : ContMDiffOn 𝓘(𝕜, 𝕜) I 2 γ s) (ht : t ∈ s)
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    accelerationWithin cov γ s t =
      (trivializationAt E (TangentSpace I) x).symmL 𝕜 (γ t)
        (derivWithin (derivWithin (extChartAt I x ∘ γ) s) s t +
          christoffelMap (Module.finBasis 𝕜 E)
            (cov.isCovariantDerivativeOn
              (s := (trivializationAt E (TangentSpace I) x).baseSet)) (γ t)
            (derivWithin (extChartAt I x ∘ γ) s t) (derivWithin (extChartAt I x ∘ γ) s t)) := by
  have hγd : MDifferentiableOn 𝓘(𝕜, 𝕜) I γ s := hγ.mdifferentiableOn (by norm_num)
  rw [← alongCurveInChartWithin_curveVelocityWithin cov γ hs hγd ht hx,
    symmL_alongCurveInChartWithin cov γ _ hx (hs t ht) (hγd t ht)
      (differentiableWithinAt_sectionCoord_curveVelocityWithin γ hs hγ ht
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))),
    accelerationWithin_def]

end Chart

end CovariantDerivative
