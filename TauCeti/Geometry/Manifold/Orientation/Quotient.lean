/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.Geometry.Manifold.Instances.Quotient

/-!
# Orientations of quotient manifolds

Let a group `G` act freely and properly discontinuously by `C¹` maps on a manifold `M`, so that the
orbit space `M ⧸ G` is a manifold and the orbit projection `π : M → M ⧸ G` is a local
diffeomorphism (`TauCeti.isLocalDiffeomorph_quotientMk`). If every element of `G` preserves an
orientation `o` of `M`, then `o` descends to an orientation `o.quotient ho` of `M ⧸ G`
(`TauCeti.Manifold.Orientation.quotient`): its tangent orientation at the orbit of `x` is the image
of the tangent orientation of `o` at `x` under the derivative of `π`. This does not depend on the
point `x` of the orbit, because `π ∘ (g • ·) = π` and `g • ·` carries the tangent orientation of `o`
at `x` to that at `g • x`. The tangent orientations are locally constant since `π` is a local
diffeomorphism (`IsLocalDiffeomorphAt.eventually_mapOrientation_eq`).

The descended orientation is characterised by the orbit projection preserving orientation at every
point (`TauCeti.Manifold.Orientation.eq_quotient_iff`). This is how the mapping torus of an
orientation-preserving diffeomorphism is oriented.

## Main definitions

* `TauCeti.Manifold.Orientation.quotient o ho`: the orientation of `M ⧸ G` descended from an
  orientation `o` of `M` preserved by every element of `G`.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_quotientMk`: the orbit projection
  preserves orientation from `o` to the descended orientation.
* `TauCeti.Manifold.Orientation.eq_quotient_iff`: the descended orientation is the only orientation
  of `M ⧸ G` from which the orbit projection preserves orientation everywhere.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15 (orientations and local diffeomorphisms) and
  Chapter 21 (quotients by discrete group actions).
-/

public section

noncomputable section

open Filter Module
open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I 1 G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M]
  [LocallyCompactSpace M] {ι : Type*} [Fintype ι]

local notation "π" => Quotient.mk (MulAction.orbitRel G M)

/-- The derivative of the orbit projection at `x`, as a continuous linear equivalence. -/
private def quotientMkDerivEquiv (x : M) :
    TangentSpace I x ≃L[ℝ] TangentSpace I (π x) :=
  (isLocalDiffeomorph_quotientMk (G := G) (I := I) (n := 1) x).mfderivToContinuousLinearEquiv
    one_ne_zero

omit [FiniteDimensional ℝ E] in
private theorem coe_quotientMkDerivEquiv (x : M) :
    (quotientMkDerivEquiv (G := G) (I := I) x : TangentSpace I x →L[ℝ] TangentSpace I (π x)) =
      mfderiv I I π x :=
  IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe _ _

variable (o : Orientation I M ι) (ho : ∀ (g : G) x, IsOrientationPreservingAt o o (g • ·) x)
include ho

/-- Over a point of the orbit space, the derivatives of the orbit projection carry the tangent
orientations of `o` at any two points of the orbit to the same orientation. -/
private theorem map_quotientMkDerivEquiv_eq {x x' : M} (h : π x = π x') :
    _root_.Orientation.map ι (quotientMkDerivEquiv (G := G) (I := I) x).toLinearEquiv
        (o.orientationAt x) =
      _root_.Orientation.map ι (quotientMkDerivEquiv (G := G) (I := I) x').toLinearEquiv
        (o.orientationAt x') := by
  obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.1 (Quotient.exact h.symm)
  obtain ⟨D, hD, hDo⟩ := (isOrientationPreservingAt_iff _ _ _ _).mp (ho g x)
  have hcomp :
      D.toLinearEquiv.trans (quotientMkDerivEquiv (G := G) (I := I) (g • x)).toLinearEquiv =
        (quotientMkDerivEquiv (G := G) (I := I) x).toLinearEquiv := by
    ext v
    have := mfderiv_quotientMk_smul_apply (G := G) (I := I) (n := 1) one_ne_zero
      ((isLocalDiffeomorph_quotientMk (G := G) (I := I) (n := 1) (g • x)).mdifferentiableAt
        one_ne_zero) v
    rw [← hD, ← coe_quotientMkDerivEquiv, ← coe_quotientMkDerivEquiv] at this
    exact this
  rw [← hDo, ← _root_.Orientation.map_trans, hcomp]
  -- The two sides differ only in how the tangent space at the common orbit is written.
  rfl

open Classical in
/-- The tangent orientations of the descended orientation: at an orbit `y`, the image of the
tangent orientation of `o` at a chosen point of `y` under the derivative of the orbit
projection. -/
private def quotientOrientationAt (y : MulAction.orbitRel.Quotient G M) :
    _root_.Orientation ℝ (TangentSpace I y) ι :=
  -- The tangent spaces at `y` and at the orbit of its chosen point are both the model space.
  _root_.Orientation.map ι (quotientMkDerivEquiv (G := G) (I := I) y.out).toLinearEquiv
    (o.orientationAt y.out)

/-- The derivative of the orbit projection at `x` carries the tangent orientation of `o` at `x`
to the descended tangent orientation at the orbit of `x`. -/
private theorem map_quotientMkDerivEquiv_eq_quotientOrientationAt (x : M) :
    _root_.Orientation.map ι (quotientMkDerivEquiv (G := G) (I := I) x).toLinearEquiv
        (o.orientationAt x) = quotientOrientationAt o (π x) :=
  map_quotientMkDerivEquiv_eq o ho (Quotient.out_eq _).symm

open Classical in
/-- The orientation of the orbit space `M ⧸ G` of a free, properly discontinuous action by
orientation-preserving maps, descended from an orientation `o` of `M`: its tangent orientation at
the orbit of `x` is the image of that of `o` at `x` under the derivative of the orbit projection,
which does not depend on the point `x` of the orbit. -/
def quotient : Orientation I (MulAction.orbitRel.Quotient G M) ι :=
  -- The model orientation only selects a representative lift, which the quotient forgets.
  ofVectorBundleOrientation
    (((finBasisOfFinrankEq ℝ E o.card_eq.symm).reindex (Fintype.equivFin ι).symm).orientation)
    o.card_eq
    ⟨quotientOrientationAt o, fun y₀ ↦ by
      obtain ⟨a, rfl⟩ := Quotient.mk_surjective y₀
      exact (isLocalDiffeomorph_quotientMk (G := G) (I := I) (n := 1)
        a).eventually_mapOrientation_eq o _ (.of_forall fun x ↦
          ⟨quotientMkDerivEquiv x, coe_quotientMkDerivEquiv x,
            map_quotientMkDerivEquiv_eq_quotientOrientationAt o ho x⟩)⟩

/-- The orbit projection preserves orientation from `o` to the descended orientation. -/
@[simp]
theorem isOrientationPreservingAt_quotientMk (x : M) :
    IsOrientationPreservingAt o (o.quotient ho) π x := by
  rw [isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ _ (coe_quotientMkDerivEquiv x), quotient,
    orientationAt_ofVectorBundleOrientation, VectorBundleOrientation.coe_mk]
  exact map_quotientMkDerivEquiv_eq_quotientOrientationAt o ho x

/-- The descended orientation is the only orientation of the orbit space from which the orbit
projection preserves orientation at every point. -/
theorem eq_quotient_iff {o' : Orientation I (MulAction.orbitRel.Quotient G M) ι} :
    o' = o.quotient ho ↔ ∀ x, IsOrientationPreservingAt o o' π x := by
  refine ⟨fun h ↦ h ▸ isOrientationPreservingAt_quotientMk o ho, fun h ↦ ext fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
  exact (h x).orientationAt_eq (isOrientationPreservingAt_quotientMk o ho x)

end TauCeti.Manifold.Orientation
