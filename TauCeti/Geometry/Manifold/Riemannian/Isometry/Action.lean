/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

## Main definitions

* `TauCeti.RiemannianIsometry.applyMulAction`: the action of `Isom I M` on `M` by evaluation.
* `TauCeti.RiemannianIsometry.applyFaithfulSMul`: the action is faithful.
* `TauCeti.RiemannianIsometry.applyContinuousConstSMul` and
  `TauCeti.RiemannianIsometry.applyContMDiffConstSMul`: each isometry acts by a smooth
  homeomorphism, so `Isom(M)` generates a structure groupoid on `M` and `(Isom M, M)`-manifolds are
  smooth manifolds.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, Chapter 2
  (isometries and homogeneous Riemannian manifolds).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983) 401–487
  (model geometries as homogeneous spaces of their isometry groups).
-/

public section

open Bundle Manifold
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

end TauCeti.RiemannianIsometry

end
