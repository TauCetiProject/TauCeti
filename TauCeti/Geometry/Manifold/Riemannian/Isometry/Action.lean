/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group

import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# The action of the isometry group

The isometry group `Isom(M)` of a Riemannian manifold acts on `M` by evaluation: `Φ • x = Φ x`.
This file records that action, its faithfulness and the regularity of each element's action,
mirroring the action of the self-diffeomorphism group in `TauCeti.Geometry.Diffeomorphism.Action`.

A Riemannian manifold is *homogeneous* when its isometry group acts transitively, which is
`MulAction.IsPretransitive (Isom I M) M` for the action recorded here. The model spaces of
Thurston's eight three-dimensional geometries are homogeneous in this sense, and the model geometry
is the pair `(X, Isom(X))`.

Conversely, each element of a group acting on `M` by a smooth map preserving the metric is an
element of `Isom(M)`, and a group acting by such maps maps homomorphically to `Isom(M)`. The
tangent representation of the stabilizer of a point acts by linear isometries whenever the
differentials at that point preserve the metric.

## Main definitions

* `TauCeti.RiemannianIsometry.applyMulAction`: the action of `Isom I M` on `M` by evaluation.
* `TauCeti.RiemannianIsometry.applyFaithfulSMul`: the action is faithful.
* `TauCeti.RiemannianIsometry.applyContinuousConstSMul` and
  `TauCeti.RiemannianIsometry.applyContMDiffConstSMul`: each isometry acts by a smooth
  homeomorphism, so `Isom(M)` generates a structure groupoid on `M` and `(Isom M, M)`-manifolds are
  smooth manifolds.
* `TauCeti.RiemannianIsometry.constSMulHom`: a group acting by smooth maps preserving the metric,
  as a homomorphism to the isometry group.

## Main results

* `TauCeti.RiemannianIsometry.constSMul_inv`: the isometry
  `TauCeti.RiemannianIsometry.constSMul` given by an inverse is the inverse isometry.
* `TauCeti.inner_tangentRepresentation_apply`: inner products of vectors moved by the tangent
  representation of the stabilizer of a point are those of their images under the differentials.

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

variable {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul I ∞ K M] {k : K}
  {hk : ∀ (x : M) (u w : TangentSpace I x),
    inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x w) = inner ℝ u w}

/-- The isometry `constSMul k hk` sends `x` to `k • x`. -/
theorem constSMul_apply (x : M) : constSMul k hk x = k • x := by
  rw [coe_constSMul]

/-- The isometry given by an inverse is the inverse isometry. -/
theorem constSMul_inv {hk' : ∀ (x : M) (u w : TangentSpace I x),
      inner ℝ (mfderiv I I (k⁻¹ • ·) x u) (mfderiv I I (k⁻¹ • ·) x w) = inner ℝ u w} :
    constSMul k⁻¹ hk' = (constSMul k hk : Isom I M)⁻¹ :=
  (symm_constSMul hk').symm

variable (hK : ∀ (k : K) (x : M) (u w : TangentSpace I x),
  inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x w) = inner ℝ u w)

/-- A group acting on `M` by smooth maps preserving the metric, as a homomorphism to the isometry
group. -/
def constSMulHom : K →* Isom I M where
  toFun k := constSMul k (hK k)
  map_one' := constSMul_one _
  map_mul' k l := constSMul_mul (ha := hK k) (hK l) _

/-- The homomorphism `constSMulHom hK` sends `k` to the isometry `constSMul k (hK k)`. -/
@[simp]
theorem constSMulHom_apply (k : K) : constSMulHom hK k = constSMul k (hK k) :=
  (rfl)

/-- For a faithful action, the homomorphism to the isometry group is injective. -/
theorem constSMulHom_injective [FaithfulSMul K M] : Function.Injective (constSMulHom hK) :=
  fun k l h ↦ eq_of_smul_eq_smul fun x ↦ by
    simpa using DFunLike.congr_fun h x

end ConstSMul

end TauCeti.RiemannianIsometry

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **Inner products under the tangent representation.** For `g` in the stabilizer of `x`, the
inner product at `x` of two vectors moved by the tangent representation is the inner product at
`g • x = x` of their images under the differential of `g • ·`. So the tangent representation acts
by linear isometries of `T_x M` exactly when these differentials preserve the metric at `x`. -/
theorem inner_tangentRepresentation_apply {K : Type*} [Group K] [MulAction K M] {x : M}
    (hd : ∀ g ∈ stabilizer K x, MDifferentiableAt I I (fun y : M ↦ g • y) x)
    (g : stabilizer K x) (u w : TangentSpace I x) :
    inner ℝ (tangentRepresentation hd g u) (tangentRepresentation hd g w) =
      inner ℝ (mfderiv I I ((g : K) • ·) x u) (mfderiv I I ((g : K) • ·) x w) := by
  rw [tangentRepresentation_apply]
  exact inner_tangentSpace_congr (I := I) g.2.symm rfl rfl

end TauCeti

end
