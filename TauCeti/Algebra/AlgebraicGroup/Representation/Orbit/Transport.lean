/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Translation
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Hom
import TauCeti.Algebra.Coalgebra.Comodule.Inverse

/-!
# Transport of vector orbits and their closure order

A bijective comodule morphism identifies rational vector orbits. On finite-dimensional
representations, its extension by the identity on the trivial coordinate induces an
isomorphism of projective completions. This isomorphism transports the full geometric
orbit images and their closures. Over an algebraically closed field, for a finite-type
affine group, the rational-orbit equivalence is therefore an order isomorphism for the
closure order.

This separates change of the representation space from restriction of the acting group.
In particular an equivariant differential can be used to compare adjoint orbit closures
without replacing geometric orbit images by their rational points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §1.3.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule.Hom

universe u

variable {k H M N : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M]
  [AddCommGroup N] [Module k N] [Comodule k H N]

/-- A bijective comodule morphism identifies the sets of rational vector orbits.
No finite-dimensionality or algebraic-closedness hypothesis is required. -/
noncomputable def vectorOrbitEquiv (f : Hom k H M N) (hf : Function.Bijective f) :
    VectorOrbit k H M ≃ VectorOrbit k H N :=
  { toFun := VectorOrbit.lift (fun v ↦ VectorOrbit.mk (f v)) fun g v ↦ by
      rw [f.map_basePointsRepresentation, VectorOrbit.mk_basePointsRepresentation]
    invFun := VectorOrbit.lift (fun w ↦ VectorOrbit.mk (f.inverse hf w)) fun g w ↦ by
      rw [(f.inverse hf).map_basePointsRepresentation, VectorOrbit.mk_basePointsRepresentation]
    left_inv := by
      intro O
      induction O using VectorOrbit.ind with | h v
      simp only [VectorOrbit.lift_mk, ← comp_apply, inverse_comp_self, id_apply]
    right_inv := by
      intro O
      induction O using VectorOrbit.ind with | h w
      simp only [VectorOrbit.lift_mk, ← comp_apply, comp_inverse, id_apply] }

/-- Transport sends the orbit of `v` to the orbit of its image. -/
@[simp]
theorem vectorOrbitEquiv_mk (f : Hom k H M N) (hf : Function.Bijective f) (v : M) :
    f.vectorOrbitEquiv hf (VectorOrbit.mk v) = VectorOrbit.mk (f v) := by
  simp only [vectorOrbitEquiv, Equiv.coe_fn_mk, VectorOrbit.lift_mk]

/-- Inverse transport sends the orbit of `w` to that of the inverse linear image. -/
@[simp]
theorem vectorOrbitEquiv_symm_mk (f : Hom k H M N) (hf : Function.Bijective f) (w : N) :
    (f.vectorOrbitEquiv hf).symm (VectorOrbit.mk w) =
      VectorOrbit.mk ((LinearEquiv.ofBijective f.toLinearMap hf).symm w) := by
  apply (f.vectorOrbitEquiv hf).injective
  rw [Equiv.apply_symm_apply, vectorOrbitEquiv_mk]
  exact congrArg VectorOrbit.mk
    ((LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply w).symm

attribute [local instance] prodTrivial

variable [Module.Finite k M] [Module.Finite k N]

/-- Extending a comodule isomorphism by the identity on the trivial coordinate
intertwines the vector orbit morphisms in their projective completions. -/
@[reassoc]
theorem projectiveOrbitMap_mk_one_comp_mapIso (f : Hom k H M N)
    (hf : Function.Bijective f) (v : M) :
    projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v) ≫
        (Proj.symmetricAlgebraMapIso k
          ((LinearEquiv.ofBijective f.toLinearMap hf).prodCongr
            (LinearEquiv.refl k k)).dualMap).hom =
      projectiveOrbitMap (H := H) ((f v, 1) : N × k)
        (Module.isUnimodular_mk_one (f v)) := by
  let e := (LinearEquiv.ofBijective f.toLinearMap hf).prodCongr (LinearEquiv.refl k k)
  have hcoords : orbitCoordinates (H := H) ((f v, 1) : N × k) =
      (orbitCoordinates (H := H) ((v, 1) : M × k)).comp
        (SymmetricAlgebra.map k e.dualMap.toLinearMap) := by
    ext φ
    simp [matrixCoefficient_prodTrivial, matrixCoefficient_map,
      LinearEquiv.dualMap, e]
    rfl
  rw [projectiveOrbitMap_def, projectiveOrbitMap_def,
    Proj.symmetricAlgebraMapIso_hom, Proj.fromOfGlobalSections_map]
  congr 1
  rw [hcoords]
  apply RingHom.ext
  intro s
  simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom,
    SymmetricAlgebra.gradedMap_apply]
  rfl

/-- The projective completion isomorphism transports full geometric vector orbit images,
including their nonclosed points. -/
theorem image_vectorOrbitEquiv (f : Hom k H M N) (hf : Function.Bijective f)
    (O : VectorOrbit k H M) :
    (f.vectorOrbitEquiv hf O).image =
      (Proj.symmetricAlgebraMapIso k
        ((LinearEquiv.ofBijective f.toLinearMap hf).prodCongr
          (LinearEquiv.refl k k)).dualMap).hom '' O.image := by
  induction O using VectorOrbit.ind with | h v
  rw [vectorOrbitEquiv_mk, VectorOrbit.image_mk, VectorOrbit.image_mk, ← Set.range_comp]
  exact congrArg Set.range (funext fun x ↦
    (congrArg (fun q : Spec (.of H) ⟶ _ ↦ q x)
      (f.projectiveOrbitMap_mk_one_comp_mapIso hf v)).symm)

/-- The same isomorphism transports orbit closures in the projective completions. -/
theorem closure_image_vectorOrbitEquiv (f : Hom k H M N) (hf : Function.Bijective f)
    (O : VectorOrbit k H M) :
    closure (f.vectorOrbitEquiv hf O).image =
      (Proj.symmetricAlgebraMapIso k
        ((LinearEquiv.ofBijective f.toLinearMap hf).prodCongr
          (LinearEquiv.refl k k)).dualMap).hom '' closure O.image := by
  rw [image_vectorOrbitEquiv]
  exact (Scheme.homeoOfIso (Proj.symmetricAlgebraMapIso k
    ((LinearEquiv.ofBijective f.toLinearMap hf).prodCongr
      (LinearEquiv.refl k k)).dualMap)).image_closure O.image |>.symm

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- A comodule isomorphism identifies the closure orders on rational vector orbits. -/
noncomputable def vectorOrbitOrderIso (f : Hom k H M N) (hf : Function.Bijective f) :
    VectorOrbit k H M ≃o VectorOrbit k H N where
  toEquiv := f.vectorOrbitEquiv hf
  map_rel_iff' := by
    intro O O'
    rw [VectorOrbit.le_iff_closure_image_subset, VectorOrbit.le_iff_closure_image_subset,
      closure_image_vectorOrbitEquiv, closure_image_vectorOrbitEquiv]
    exact Set.image_subset_image_iff
      (Scheme.homeoOfIso (Proj.symmetricAlgebraMapIso k
        ((LinearEquiv.ofBijective f.toLinearMap hf).prodCongr
          (LinearEquiv.refl k k)).dualMap)).injective

/-- Forgetting the order structure recovers the rational-orbit equivalence. -/
@[simp]
theorem vectorOrbitOrderIso_toEquiv (f : Hom k H M N) (hf : Function.Bijective f) :
    (f.vectorOrbitOrderIso hf).toEquiv = f.vectorOrbitEquiv hf := (rfl)

/-- The closure-order isomorphism acts on representatives by the comodule morphism. -/
@[simp]
theorem vectorOrbitOrderIso_mk (f : Hom k H M N) (hf : Function.Bijective f) (v : M) :
    f.vectorOrbitOrderIso hf (VectorOrbit.mk v) = VectorOrbit.mk (f v) :=
  f.vectorOrbitEquiv_mk hf v

/-- The inverse closure-order isomorphism acts by the inverse linear equivalence. -/
@[simp]
theorem vectorOrbitOrderIso_symm_mk (f : Hom k H M N) (hf : Function.Bijective f) (w : N) :
    (f.vectorOrbitOrderIso hf).symm (VectorOrbit.mk w) =
      VectorOrbit.mk ((LinearEquiv.ofBijective f.toLinearMap hf).symm w) :=
  f.vectorOrbitEquiv_symm_mk hf w

end TauCeti.Comodule.Hom
