/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Reparametrization

/-!
# Jacobi fields under affine reparametrization

Let `V` be a Jacobi field along a geodesic `γ` on a parameter set `s`, and let `φ t = a * t + b`
map a parameter set `u` with unique derivatives into `s`. Then `t ↦ V (φ t)` is a Jacobi field along
the reparametrized geodesic `γ ∘ φ` on `u`. Its covariant derivative at `t` is `a` times the
covariant derivative of `V` at `φ t`, so the initial data `(V(t₀), D_t V(t₀))` of the
reparametrized field are `(V(φ t₀), a D_t V(φ t₀))`.

Both covariant derivatives and the velocity gain one factor of `a` each, so the two terms of the
Jacobi equation `D_t² V + R(V, γ')γ' = 0` are multiplied by the same factor `a²`. The affine maps
include the time translations `t ↦ t + b` and the scalings `t ↦ a * t`; the case `a = 0` gives a
constant field along a constant curve.

## Main results

* `TauCeti.Manifold.IsJacobiFieldOn.alongCurveWithin_comp_affine`: the covariant derivative of the
  reparametrized field.
* `TauCeti.Manifold.IsJacobiFieldOn.comp_affine`: affine reparametrization preserves Jacobi
  fields.
* `TauCeti.Manifold.IsJacobiFieldOn.comp_affine_of_eqOn` and
  `TauCeti.Manifold.IsJacobiFieldOn.alongCurveWithin_comp_affine_of_eqOn`: transporting an
  affinely reparametrized Jacobi field and its covariant derivative across a curve agreeing with
  `γ ∘ φ` on `u`.
* `TauCeti.Manifold.IsJacobiFieldOn.comp_sub_const_of_eqOn`,
  `TauCeti.Manifold.IsJacobiFieldOn.alongCurveWithin_comp_sub_const_of_eqOn`, and
  `TauCeti.Manifold.IsJacobiFieldOn.prodMk_alongCurveWithin_comp_sub_const_eq_of_eqOn_of_heq`:
  time-shifting a Jacobi field and its initial data from `0` to `a` along a curve agreeing with
  `t ↦ γ (t - a)`.
* `TauCeti.Manifold.IsJacobiFieldOn.comp_add_const` and
  `TauCeti.Manifold.IsJacobiFieldOn.comp_mul_left`: the time-translation and scaling cases.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (Jacobi fields).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s u : Set ℝ} {t : ℝ}

/-- The covariant derivative of a Jacobi field reparametrized by `t ↦ a * t + b` is `a` times the
reparametrized covariant derivative. -/
theorem IsJacobiFieldOn.alongCurveWithin_comp_affine (h : IsJacobiFieldOn I γ V s) (a b : ℝ)
    (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ a * t + b) u s) (ht : t ∈ u) :
    alongCurveWithin (leviCivitaConnection I M) (γ ∘ fun t : ℝ ↦ a * t + b)
        (fun r ↦ V (a * r + b)) u t =
      a • alongCurveWithin (leviCivitaConnection I M) γ V s (a * t + b) := by
  have hφ : HasDerivWithinAt (fun t : ℝ ↦ a * t + b) a u t :=
    ((hasDerivAt_const_mul a).add_const b).hasDerivWithinAt
  rw [alongCurveWithin_comp _ γ V _ hφ.differentiableWithinAt hmaps
      (hasDerivWithinAt_extChartAt_comp_curve (hasMFDerivWithinAt_curveVelocityWithin
        (h.isGeodesicCurveOn.mdifferentiableOn _ (hmaps ht)))).differentiableWithinAt
      (h.differentiableWithinAt_sectionCoord (hmaps ht)),
    hφ.derivWithin (hu t ht)]

/-- **Affine reparametrization of Jacobi fields.** A Jacobi field along a geodesic remains a
Jacobi field after the affine reparametrization `t ↦ a * t + b`, provided that map carries the
new parameter set into the original one. -/
theorem IsJacobiFieldOn.comp_affine (h : IsJacobiFieldOn I γ V s) (a b : ℝ)
    (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ a * t + b) u s) :
    IsJacobiFieldOn I (γ ∘ fun t : ℝ ↦ a * t + b) (fun r ↦ V (a * r + b)) u := by
  have hφ (r : ℝ) : HasDerivWithinAt (fun t : ℝ ↦ a * t + b) a u r :=
    ((hasDerivAt_const_mul a).add_const b).hasDerivWithinAt
  have hfirst := fun r (hr : r ∈ u) ↦ h.alongCurveWithin_comp_affine a b hu hmaps hr
  refine ⟨h.isGeodesicCurveOn.comp_affine a b hu hmaps, ?_, fun r hr ↦ ?_⟩
  · have hφ' : ContDiff ℝ 2 (fun t : ℝ ↦ a * t + b) := by fun_prop
    exact h.contMDiffOn.comp hφ'.contMDiff.contMDiffOn hmaps
  -- The second covariant derivative gains a factor `a` from each differentiation.
  have hsecond : alongCurveWithin (leviCivitaConnection I M) (γ ∘ fun t : ℝ ↦ a * t + b)
      (alongCurveWithin (leviCivitaConnection I M) (γ ∘ fun t : ℝ ↦ a * t + b)
        (fun r ↦ V (a * r + b)) u) u r =
        a • a • alongCurveWithin (leviCivitaConnection I M) γ
          (alongCurveWithin (leviCivitaConnection I M) γ V s) s (a * r + b) := by
    rw [alongCurveWithin_congr _ _ _ (mem_of_superset self_mem_nhdsWithin hfirst) (hfirst r hr),
      alongCurveWithin_const_smul,
      alongCurveWithin_comp _ γ _ _ (hφ r).differentiableWithinAt hmaps
        (hasDerivWithinAt_extChartAt_comp_curve (hasMFDerivWithinAt_curveVelocityWithin
          (h.isGeodesicCurveOn.mdifferentiableOn _ (hmaps hr)))).differentiableWithinAt
        (h.differentiableWithinAt_sectionCoord_alongCurveWithin (hmaps hr)),
      (hφ r).derivWithin (hu r hr)]
  have hvel := curveVelocityWithin_comp (hφ r) hmaps
    (h.isGeodesicCurveOn.mdifferentiableOn _ (hmaps hr)) (hu r hr)
  -- Both terms of the Jacobi equation at `r` are `a²` times those of the original equation.
  rw [hsecond, hvel]
  simpa [smul_smul, ← smul_add] using congrArg ((a * a) • ·) (h.equation _ (hmaps hr))

/-- Transporting an affinely reparametrized Jacobi field via `tangentSpaceCast` to a curve `δ`
that agrees with `γ ∘ (t ↦ a * t + b)` on `u` produces a Jacobi field along `δ`. -/
theorem IsJacobiFieldOn.comp_affine_of_eqOn {δ : ℝ → M} (h : IsJacobiFieldOn I γ V s)
    (a b : ℝ) (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ a * t + b) u s)
    (hcurve : EqOn δ (γ ∘ fun t : ℝ ↦ a * t + b) u) :
    IsJacobiFieldOn I δ
      (fun r ↦ tangentSpaceCast I (γ (a * r + b)) (δ r) (V (a * r + b))) u :=
  (h.comp_affine a b hu hmaps).congr_totalSpace fun _ hr ↦
    TotalSpace.ext (hcurve hr) (TauCeti.heq_tangentSpaceCast (hcurve hr).symm _)

/-- The covariant derivative of a `tangentSpaceCast`-transported affine reparametrization of a
Jacobi field is `a` times the `tangentSpaceCast` of the reparametrized covariant derivative. -/
theorem IsJacobiFieldOn.alongCurveWithin_comp_affine_of_eqOn {δ : ℝ → M}
    (h : IsJacobiFieldOn I γ V s) (a b : ℝ) (hu : UniqueDiffOn ℝ u)
    (hmaps : MapsTo (fun t : ℝ ↦ a * t + b) u s)
    (hcurve : EqOn δ (γ ∘ fun t : ℝ ↦ a * t + b) u) (ht : t ∈ u) :
    alongCurveWithin (leviCivitaConnection I M) δ
        (fun r ↦ tangentSpaceCast I (γ (a * r + b)) (δ r) (V (a * r + b))) u t =
      a • tangentSpaceCast I (γ (a * t + b)) (δ t)
        (alongCurveWithin (leviCivitaConnection I M) γ V s (a * t + b)) := by
  have hheq : ∀ r ∈ u,
      HEq (tangentSpaceCast I (γ (a * r + b)) (δ r) (V (a * r + b))) (V (a * r + b)) :=
    fun r hr ↦ TauCeti.heq_tangentSpaceCast (hcurve hr).symm _
  have hD := alongCurveWithin_congr_heq (leviCivitaConnection I M)
    (fun r ↦ tangentSpaceCast I (γ (a * r + b)) (δ r) (V (a * r + b)))
    (hcurve.eventuallyEq_of_mem self_mem_nhdsWithin) (hcurve ht)
    (mem_of_superset self_mem_nhdsWithin hheq) (hheq t ht)
  rw [h.alongCurveWithin_comp_affine a b hu hmaps ht] at hD
  rw [← map_smul]
  exact eq_of_heq (hD.trans (TauCeti.heq_tangentSpaceCast (hcurve ht).symm _).symm)

/-- Transporting a Jacobi field shifted by `t ↦ t - a` via `tangentSpaceCast` to a curve `δ`
that agrees with `fun t ↦ γ (t - a)` on `u` produces a Jacobi field along `δ`. -/
theorem IsJacobiFieldOn.comp_sub_const_of_eqOn {δ : ℝ → M} (h : IsJacobiFieldOn I γ V s)
    (a : ℝ) (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ t - a) u s)
    (hcurve : EqOn δ (fun t ↦ γ (t - a)) u) :
    IsJacobiFieldOn I δ
      (fun r ↦ tangentSpaceCast I (γ (r - a)) (δ r) (V (r - a))) u :=
  (h.comp_affine_of_eqOn 1 (-a) hu
    (fun _ hr ↦ by simpa only [one_mul, ← sub_eq_add_neg] using hmaps hr)
    (fun _ hr ↦ by
      simpa only [Function.comp_apply, one_mul, ← sub_eq_add_neg] using hcurve hr)).congr fun r _ ↦
    congrArg (fun x ↦ tangentSpaceCast I (γ x) (δ r) (V x)) (by ring)

/-- The covariant derivative of a `tangentSpaceCast`-transported time-shifted Jacobi field is
the `tangentSpaceCast` of the shifted covariant derivative. -/
theorem IsJacobiFieldOn.alongCurveWithin_comp_sub_const_of_eqOn {δ : ℝ → M}
    (h : IsJacobiFieldOn I γ V s) (a : ℝ) (hu : UniqueDiffOn ℝ u)
    (hmaps : MapsTo (fun t : ℝ ↦ t - a) u s)
    (hcurve : EqOn δ (fun t ↦ γ (t - a)) u) (ht : t ∈ u) :
    alongCurveWithin (leviCivitaConnection I M) δ
        (fun r ↦ tangentSpaceCast I (γ (r - a)) (δ r) (V (r - a))) u t =
      tangentSpaceCast I (γ (t - a)) (δ t)
        (alongCurveWithin (leviCivitaConnection I M) γ V s (t - a)) := by
  have hcongr (r : ℝ) : tangentSpaceCast I (γ (r - a)) (δ r) (V (r - a)) =
      tangentSpaceCast I (γ (1 * r + (-a))) (δ r) (V (1 * r + (-a))) :=
    congrArg (fun x ↦ tangentSpaceCast I (γ x) (δ r) (V x)) (by ring)
  rw [alongCurveWithin_congr _ δ _ (Eventually.of_forall hcongr) (hcongr t),
    h.alongCurveWithin_comp_affine_of_eqOn 1 (-a) hu
      (fun _ hr ↦ by simpa only [one_mul, ← sub_eq_add_neg] using hmaps hr)
      (fun _ hr ↦ by simpa only [Function.comp_apply, one_mul, ← sub_eq_add_neg] using hcurve hr)
      ht,
    one_smul]
  exact congrArg
    (fun x ↦ tangentSpaceCast I (γ x) (δ t)
      (alongCurveWithin (leviCivitaConnection I M) γ V s x))
    (by ring)

/-- Under the time shift `r ↦ r - a` onto a curve `δ` agreeing with `fun t ↦ γ (t - a)` on `u`,
the value and covariant derivative at `a ∈ u` of the `tangentSpaceCast`-transported Jacobi field
equal any pair `(v, w)` heterogeneously equal to `(V 0, D_t V 0)`. -/
theorem IsJacobiFieldOn.prodMk_alongCurveWithin_comp_sub_const_eq_of_eqOn_of_heq {δ : ℝ → M}
    (h : IsJacobiFieldOn I γ V s) {a : ℝ} (hu : UniqueDiffOn ℝ u)
    (hmaps : MapsTo (fun t : ℝ ↦ t - a) u s)
    (hcurve : EqOn δ (fun t ↦ γ (t - a)) u) (ha : a ∈ u)
    {v w : TangentSpace I (δ a)}
    (hv : HEq (V 0) v)
    (hw : HEq (alongCurveWithin (leviCivitaConnection I M) γ V s 0) w) :
    (tangentSpaceCast I (γ (a - a)) (δ a) (V (a - a)),
      alongCurveWithin (leviCivitaConnection I M) δ
        (fun r ↦ tangentSpaceCast I (γ (r - a)) (δ r) (V (r - a))) u a) = (v, w) := by
  have h0 : δ a = γ 0 := by simpa only [sub_self] using hcurve ha
  refine Prod.ext ?_ ?_
  · rw [congrArg (fun x ↦ tangentSpaceCast I (γ x) (δ a) (V x)) (sub_self a)]
    exact eq_of_heq ((TauCeti.heq_tangentSpaceCast h0.symm _).trans hv)
  · rw [h.alongCurveWithin_comp_sub_const_of_eqOn a hu hmaps hcurve ha,
      congrArg (fun x ↦ tangentSpaceCast I (γ x) (δ a)
        (alongCurveWithin (leviCivitaConnection I M) γ V s x)) (sub_self a)]
    exact eq_of_heq ((TauCeti.heq_tangentSpaceCast h0.symm _).trans hw)

/-- **Time translation of Jacobi fields.** A Jacobi field remains a Jacobi field after the
translation `t ↦ t + b` of its parameter. -/
theorem IsJacobiFieldOn.comp_add_const (h : IsJacobiFieldOn I γ V s) (b : ℝ)
    (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ t + b) u s) :
    IsJacobiFieldOn I (γ ∘ fun t : ℝ ↦ t + b) (fun r ↦ V (r + b)) u := by
  -- The field depends on the reparametrization through its fibres, so the affine map is
  -- generalized before it is identified with `t ↦ t + b`.
  have key : ∀ φ : ℝ → ℝ, φ = (fun t ↦ 1 * t + b) →
      IsJacobiFieldOn I (γ ∘ φ) (fun r ↦ V (φ r)) u := by
    rintro φ rfl
    exact h.comp_affine 1 b hu (by simpa using hmaps)
  exact key _ (by simp)

/-- **Scaling of Jacobi fields.** A Jacobi field remains a Jacobi field after the scaling
`t ↦ a * t` of its parameter. -/
theorem IsJacobiFieldOn.comp_mul_left (h : IsJacobiFieldOn I γ V s) (a : ℝ)
    (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ a * t) u s) :
    IsJacobiFieldOn I (γ ∘ fun t : ℝ ↦ a * t) (fun r ↦ V (a * r)) u := by
  -- As in `IsJacobiFieldOn.comp_add_const`, the affine map is generalized first.
  have key : ∀ φ : ℝ → ℝ, φ = (fun t ↦ a * t + 0) →
      IsJacobiFieldOn I (γ ∘ φ) (fun r ↦ V (φ r)) u := by
    rintro φ rfl
    exact h.comp_affine a 0 hu (by simpa using hmaps)
  exact key _ (by simp)

end TauCeti.Manifold
