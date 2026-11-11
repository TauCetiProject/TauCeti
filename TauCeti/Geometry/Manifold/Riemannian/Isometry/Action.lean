/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group

/-!
# The action of the isometry group

The isometry group `Isom(M)` of a Riemannian manifold acts on `M` by evaluation: `Φ • x = Φ x`.
This file records that action, its faithfulness and the regularity of each element's action,
mirroring the action of the self-diffeomorphism group in `TauCeti.Geometry.Diffeomorphism.Action`.

A Riemannian manifold is *homogeneous* when its isometry group acts transitively, which is
`MulAction.IsPretransitive (Isom I M) M` for the action recorded here. The model spaces of
Thurston's eight three-dimensional geometries are homogeneous in this sense, and the model geometry
is the pair `(X, Isom(X))`.

Conversely, each element of a group acting on `M` by smooth maps preserving the metric is an
element of `Isom(M)`, and the tangent representation of the stabilizer of a point acts by linear
isometries whenever the differentials at that point preserve the metric.

## Main definitions

* `TauCeti.RiemannianIsometry.applyMulAction`: the action of `Isom I M` on `M` by evaluation.
* `TauCeti.RiemannianIsometry.applyFaithfulSMul`: the action is faithful.
* `TauCeti.RiemannianIsometry.applyContinuousConstSMul` and
  `TauCeti.RiemannianIsometry.applyContMDiffConstSMul`: each isometry acts by a smooth
  homeomorphism, so `Isom(M)` generates a structure groupoid on `M` and `(Isom M, M)`-manifolds are
  smooth manifolds.
* `TauCeti.RiemannianIsometry.constSMul`: an element of a group acting by smooth maps preserving
  the metric, as an isometry.

## Main results

* `TauCeti.inner_tangentRepresentation_apply`: the tangent representation of the stabilizer of a
  point acts by linear isometries when the differentials at that point preserve the metric.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, Chapter 2
  (isometries and homogeneous Riemannian manifolds).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983) 401–487
  (model geometries as homogeneous spaces of their isometry groups).
-/

public section

open Bundle Manifold MulAction
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The isometry group acts on `M` by evaluation. -/
instance applyMulAction : MulAction (Isom I M) M where
  smul Φ x := Φ x
  one_smul := one_apply
  mul_smul := mul_apply

/-- The action of the isometry group on `M` is evaluation. -/
@[simp]
theorem smul_def (Φ : Isom I M) (x : M) : Φ • x = Φ x := rfl

/-- The isometry group acts faithfully on `M`. -/
instance applyFaithfulSMul : FaithfulSMul (Isom I M) M :=
  ⟨fun h ↦ RiemannianIsometry.ext h⟩

/-- Each isometry acts on `M` by a homeomorphism. -/
instance applyContinuousConstSMul : ContinuousConstSMul (Isom I M) M :=
  ⟨fun Φ ↦ Φ.toDiffeomorph.continuous⟩

/-- Each isometry acts on `M` by a smooth map. -/
instance applyContMDiffConstSMul : ContMDiffConstSMul I ∞ (Isom I M) M :=
  ⟨fun Φ ↦ Φ.toDiffeomorph.contMDiff⟩

section ConstSMul

variable {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul I ∞ K M]
  (hK : ∀ (k : K) (x : M) (u w : TangentSpace I x),
    inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x w) = inner ℝ u w)

/-- An element of a group acting on `M` by smooth maps that preserve the metric, as a Riemannian
isometry of `M`. -/
def constSMul (k : K) : Isom I M where
  toEquiv := MulAction.toPerm k
  contMDiff_toFun := ContMDiffConstSMul.contMDiff_const_smul k
  contMDiff_invFun := ContMDiffConstSMul.contMDiff_const_smul k⁻¹
  inner_mfderiv' := hK k

/-- The isometry `constSMul hK k` is the action of `k`. -/
@[simp]
theorem coe_constSMul (k : K) : ⇑(constSMul hK k) = (k • ·) :=
  (rfl)

/-- The isometry `constSMul hK k` sends `x` to `k • x`. -/
theorem constSMul_apply (k : K) (x : M) : constSMul hK k x = k • x :=
  (rfl)

end ConstSMul

end TauCeti.RiemannianIsometry

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The inner products of two vectors in the tangent spaces at two equal points agree. Both
tangent spaces are the model space, so the vectors are compared there. -/
private theorem inner_congr {q p : M} (h : q = p) {u w : TangentSpace I q}
    {u' w' : TangentSpace I p} (hu : (u : E) = u') (hw : (w : E) = w') :
    inner ℝ u w = inner ℝ u' w' := by
  subst h hu hw
  rfl

/-- **The tangent representation of a group of isometries is orthogonal.** If the differential at
`x` of every element of the stabilizer of `x` preserves the metric, for instance for a group acting
by isometries, the tangent representation of the stabilizer acts on `T_x M` by linear
isometries. -/
theorem inner_tangentRepresentation_apply {K : Type*} [Group K] [MulAction K M] {x : M}
    (hK : ∀ g ∈ stabilizer K x, ∀ u w : TangentSpace I x,
      inner ℝ (mfderiv I I (g • ·) x u) (mfderiv I I (g • ·) x w) = inner ℝ u w)
    (hd : ∀ g ∈ stabilizer K x, MDifferentiableAt I I (fun y : M ↦ g • y) x)
    (g : stabilizer K x) (u w : TangentSpace I x) :
    inner ℝ (tangentRepresentation hd g u) (tangentRepresentation hd g w) = inner ℝ u w := by
  rw [tangentRepresentation_apply, ← hK g g.2 u w]
  exact inner_congr (I := I) g.2.symm rfl rfl

end TauCeti

end
