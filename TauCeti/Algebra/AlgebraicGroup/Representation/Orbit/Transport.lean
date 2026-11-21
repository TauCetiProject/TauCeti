/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
public import TauCeti.Algebra.Coalgebra.Comodule.Inverse
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Hom
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion

/-!
# Transport of vector orbits and their closure order

A comodule morphism induces a map on rational vector orbits, which is injective or
bijective when the morphism is. On finite-dimensional representations, an injective
morphism extends by the identity on the trivial coordinate to induce a closed immersion
of projective completions. This transports the full geometric orbit images and their
closures. Over an algebraically closed field, for a finite-type affine group, the
resulting orbit map is an order embedding for the closure order and an order isomorphism
when the morphism is bijective.

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

universe u v w x y

section Rational

variable {k : Type u} {H : Type v} {M : Type w} {N : Type x}
  [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M]
  [AddCommGroup N] [Module k N] [Comodule k H N]

/-- A comodule morphism sends each rational vector orbit to the orbit of its image. -/
def vectorOrbitMap (f : Hom k H M N) : VectorOrbit k H M → VectorOrbit k H N :=
  VectorOrbit.lift (fun v ↦ VectorOrbit.mk (f v)) fun g v ↦ by
    rw [f.map_basePointsRepresentation, VectorOrbit.mk_basePointsRepresentation]

/-- The orbit map acts on representatives by the comodule morphism. -/
@[simp]
theorem vectorOrbitMap_mk (f : Hom k H M N) (v : M) :
    f.vectorOrbitMap (VectorOrbit.mk v) = VectorOrbit.mk (f v) :=
  VectorOrbit.lift_mk ..

/-- An injective comodule morphism reflects rational conjugacy. -/
theorem vectorOrbitMap_injective (f : Hom k H M N) (hf : Function.Injective f) :
    Function.Injective f.vectorOrbitMap := by
  intro O O'
  induction O using VectorOrbit.ind with | h v
  induction O' using VectorOrbit.ind with | h w
  simp only [vectorOrbitMap_mk, VectorOrbit.mk_eq_mk_iff]
  rintro ⟨g, hg⟩
  exact ⟨g, hf (by rwa [f.map_basePointsRepresentation])⟩

/-- A bijective comodule morphism identifies the sets of rational vector orbits.
No finite-dimensionality or algebraic-closedness hypothesis is required. -/
noncomputable def vectorOrbitEquiv (f : Hom k H M N) (hf : Function.Bijective f) :
    VectorOrbit k H M ≃ VectorOrbit k H N :=
  { toFun := f.vectorOrbitMap
    invFun := (f.inverse hf).vectorOrbitMap
    left_inv := by
      intro O
      induction O using VectorOrbit.ind with | h v
      simp only [vectorOrbitMap_mk, ← comp_apply, inverse_comp_self, id_apply]
    right_inv := by
      intro O
      induction O using VectorOrbit.ind with | h w
      simp only [vectorOrbitMap_mk, ← comp_apply, comp_inverse, id_apply] }

/-- The underlying function of orbit transport is the forward orbit map. -/
theorem coe_vectorOrbitEquiv (f : Hom k H M N) (hf : Function.Bijective f) :
    ⇑(f.vectorOrbitEquiv hf) = f.vectorOrbitMap := (rfl)

/-- Transport sends the orbit of `v` to the orbit of its image. -/
@[simp]
theorem vectorOrbitEquiv_mk (f : Hom k H M N) (hf : Function.Bijective f) (v : M) :
    f.vectorOrbitEquiv hf (VectorOrbit.mk v) = VectorOrbit.mk (f v) := by
  rw [coe_vectorOrbitEquiv, vectorOrbitMap_mk]

/-- Inverse transport sends the orbit of `w` to that of the inverse linear image. -/
theorem vectorOrbitEquiv_symm_mk (f : Hom k H M N) (hf : Function.Bijective f) (w : N) :
    (f.vectorOrbitEquiv hf).symm (VectorOrbit.mk w) =
      VectorOrbit.mk ((LinearEquiv.ofBijective f.toLinearMap hf).symm w) := by
  apply (f.vectorOrbitEquiv hf).injective
  rw [Equiv.apply_symm_apply, vectorOrbitEquiv_mk, ← coe_toLinearMap,
    LinearEquiv.apply_ofBijective_symm_apply]

/-- Inverse transport recovers the original orbit from the orbit of an image vector. -/
@[simp]
theorem vectorOrbitEquiv_symm_mk_apply (f : Hom k H M N) (hf : Function.Bijective f) (v : M) :
    (f.vectorOrbitEquiv hf).symm (VectorOrbit.mk (f v)) = VectorOrbit.mk v := by
  rw [← vectorOrbitEquiv_mk f hf, Equiv.symm_apply_apply]

-- Simplify transport before `simp` rewrites `Hom.id` to the categorical identity.
/-- Transport along the identity morphism is the identity equivalence. -/
@[simp↓]
theorem vectorOrbitEquiv_id (h : Function.Bijective (id k H M)) :
    (id k H M).vectorOrbitEquiv h = Equiv.refl _ := by
  ext O
  induction O using VectorOrbit.ind with | h v
  simp only [vectorOrbitEquiv_mk, id_apply, Equiv.refl_apply]

/-- Transport along a composite is the composite of the two transports. -/
theorem vectorOrbitEquiv_comp {P : Type y} [AddCommGroup P] [Module k P] [Comodule k H P]
    (g : Hom k H N P) (f : Hom k H M N) (hg : Function.Bijective g) (hf : Function.Bijective f) :
    (g.comp f).vectorOrbitEquiv (by
      simpa only [← coe_toLinearMap, comp_toLinearMap, LinearMap.coe_comp] using hg.comp hf) =
      (f.vectorOrbitEquiv hf).trans (g.vectorOrbitEquiv hg) := by
  ext O
  induction O using VectorOrbit.ind with | h v
  rw [vectorOrbitEquiv_mk, comp_apply, Equiv.trans_apply, vectorOrbitEquiv_mk, vectorOrbitEquiv_mk]

/-- Transport along the inverse morphism reverses the original transport. -/
@[simp]
theorem vectorOrbitEquiv_inverse (f : Hom k H M N) (hf : Function.Bijective f)
    (h : Function.Bijective (f.inverse hf)) :
    (f.inverse hf).vectorOrbitEquiv h = (f.vectorOrbitEquiv hf).symm := by
  ext O
  induction O using VectorOrbit.ind with | h w
  rw [vectorOrbitEquiv_mk, vectorOrbitEquiv_symm_mk, ← coe_toLinearMap, inverse_toLinearMap,
    LinearEquiv.coe_coe]

end Rational

attribute [local instance] prodTrivial

variable {k H M N : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M]
  [AddCommGroup N] [Module k N] [Comodule k H N]

private theorem projectiveCompletion_gradedMap_surjective (f : Hom k H M N)
    (hf : Function.Injective f) :
    Function.Surjective (SymmetricAlgebra.gradedMap k
      (f.toLinearMap.prodMap (LinearMap.id (M := k))).dualMap) := by
  have h : Function.Injective (f.toLinearMap.prodMap (LinearMap.id (M := k))) := by
    rw [LinearMap.coe_prodMap, LinearMap.id_coe, coe_toLinearMap]
    exact hf.prodMap Function.injective_id
  simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
    SymmetricAlgebra.map_surjective k _ (LinearMap.dualMap_surjective_of_injective h)

/-- An injective comodule morphism extends by the identity on the trivial coordinate to give
a map of projective completions. -/
noncomputable def projectiveCompletionMap (f : Hom k H M N) (hf : Function.Injective f) :
    Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k))) ⟶
      Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (N × k))) :=
  Proj.map (SymmetricAlgebra.gradedMap k (f.toLinearMap.prodMap (LinearMap.id (M := k))).dualMap)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _
      (projectiveCompletion_gradedMap_surjective f hf))

/-- The map of projective completions of an injective comodule morphism is a closed immersion. -/
theorem isClosedImmersion_projectiveCompletionMap (f : Hom k H M N) (hf : Function.Injective f) :
    IsClosedImmersion (f.projectiveCompletionMap hf) := by
  rw [projectiveCompletionMap]
  exact Proj.isClosedImmersion_map _ _ (projectiveCompletion_gradedMap_surjective f hf)

/-- For a bijection, the map of completions is the forward map of the projective linear
isomorphism. -/
theorem projectiveCompletionMap_eq_symmetricAlgebraMapIso_hom (f : Hom k H M N)
    (hf : Function.Bijective f) :
    f.projectiveCompletionMap hf.injective =
      (Proj.symmetricAlgebraMapIso k ((LinearEquiv.ofBijective f.toLinearMap hf).prodCongr
        (LinearEquiv.refl k k)).dualMap).hom := by
  let e := (LinearEquiv.ofBijective f.toLinearMap hf).prodCongr (LinearEquiv.refl k k)
  have h : e.dualMap.toLinearMap = (f.toLinearMap.prodMap (LinearMap.id (M := k))).dualMap := by
    exact LinearMap.ext fun φ ↦ LinearMap.ext fun p ↦ by
      simp [e, LinearEquiv.dualMap_apply, LinearEquiv.prodCongr_apply]
  rw [projectiveCompletionMap, Proj.symmetricAlgebraMapIso_hom]
  -- Both projective maps are induced by the same graded coordinate map.
  dsimp only [e] at h
  simp only [h]

variable [Module.Finite k M] [Module.Finite k N]

/-- An injective comodule morphism intertwines the vector orbit morphisms in their projective
completions. -/
@[reassoc]
theorem projectiveOrbitMap_mk_one_comp_projectiveCompletionMap (f : Hom k H M N)
    (hf : Function.Injective f) (v : M) :
    projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v) ≫
        f.projectiveCompletionMap hf =
      projectiveOrbitMap (H := H) ((f v, 1) : N × k)
        (Module.isUnimodular_mk_one (f v)) := by
  let e := f.toLinearMap.prodMap (LinearMap.id (M := k))
  have hcoords : orbitCoordinates (H := H) ((f v, 1) : N × k) =
      (orbitCoordinates (H := H) ((v, 1) : M × k)).comp
        (SymmetricAlgebra.map k e.dualMap) := by
    ext φ
    have hinl : (φ ∘ₗ LinearMap.inl k N k) ∘ₗ f.toLinearMap =
        e.dualMap φ ∘ₗ LinearMap.inl k M k := by
      ext m
      simp [e]
    have htriv : e.dualMap φ (0, 1) = φ (0, 1) := by simp [e]
    simp only [LinearMap.coe_comp, LinearMap.coe_ofClass, Function.comp_apply, orbitCoordinates_ι,
      AlgHom.coe_comp, SymmetricAlgebra.map_apply_ι, matrixCoefficient_prodTrivial,
      matrixCoefficient_map, hinl, htriv]
  rw [projectiveOrbitMap_def, projectiveOrbitMap_def, projectiveCompletionMap,
    Proj.fromOfGlobalSections_map]
  congr 1
  rw [hcoords, RingHom.comp_assoc]
  simp only [SymmetricAlgebra.gradedMap_toRingHom, AlgHom.toRingHom_eq_coe,
    AlgHom.comp_toRingHom, e]

/-- A comodule isomorphism intertwines the vector orbit morphisms via the induced projective
linear isomorphism. -/
@[reassoc]
theorem projectiveOrbitMap_mk_one_comp_symmetricAlgebraMapIso_hom (f : Hom k H M N)
    (hf : Function.Bijective f) (v : M) :
    projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v) ≫
        (Proj.symmetricAlgebraMapIso k
          ((LinearEquiv.ofBijective f.toLinearMap hf).prodCongr
            (LinearEquiv.refl k k)).dualMap).hom =
      projectiveOrbitMap (H := H) ((f v, 1) : N × k)
        (Module.isUnimodular_mk_one (f v)) := by
  rw [← f.projectiveCompletionMap_eq_symmetricAlgebraMapIso_hom hf,
    f.projectiveOrbitMap_mk_one_comp_projectiveCompletionMap hf.injective v]

/-- The map of completions transports the full geometric images of rational vector orbits. -/
theorem image_vectorOrbitMap (f : Hom k H M N) (hf : Function.Injective f) (O : VectorOrbit k H M) :
    (f.vectorOrbitMap O).image = f.projectiveCompletionMap hf '' O.image := by
  induction O using VectorOrbit.ind with | h v
  rw [vectorOrbitMap_mk, VectorOrbit.image_mk, VectorOrbit.image_mk, ← Set.range_comp,
    ← f.projectiveOrbitMap_mk_one_comp_projectiveCompletionMap hf v, Scheme.Hom.comp_base,
    TopCat.coe_comp]

/-- The closed immersion of completions transports the closures of geometric orbit images. -/
theorem closure_image_vectorOrbitMap (f : Hom k H M N) (hf : Function.Injective f)
    (O : VectorOrbit k H M) :
    closure (f.vectorOrbitMap O).image = f.projectiveCompletionMap hf '' closure O.image := by
  let := f.isClosedImmersion_projectiveCompletionMap hf
  rw [image_vectorOrbitMap f hf, (IsClosedImmersion.isClosedEmbedding _).closure_image_eq]

/-- The projective completion isomorphism transports full geometric vector orbit images,
including their nonclosed points. -/
theorem image_vectorOrbitEquiv (f : Hom k H M N) (hf : Function.Bijective f)
    (O : VectorOrbit k H M) :
    (f.vectorOrbitEquiv hf O).image =
      (Proj.symmetricAlgebraMapIso k
        ((LinearEquiv.ofBijective f.toLinearMap hf).prodCongr
          (LinearEquiv.refl k k)).dualMap).hom '' O.image := by
  rw [coe_vectorOrbitEquiv, image_vectorOrbitMap f hf.injective,
    f.projectiveCompletionMap_eq_symmetricAlgebraMapIso_hom hf]

/-- The same isomorphism transports orbit closures in the projective completions. -/
theorem closure_image_vectorOrbitEquiv (f : Hom k H M N) (hf : Function.Bijective f)
    (O : VectorOrbit k H M) :
    closure (f.vectorOrbitEquiv hf O).image =
      (Proj.symmetricAlgebraMapIso k
        ((LinearEquiv.ofBijective f.toLinearMap hf).prodCongr
          (LinearEquiv.refl k k)).dualMap).hom '' closure O.image := by
  rw [coe_vectorOrbitEquiv, closure_image_vectorOrbitMap f hf.injective,
    f.projectiveCompletionMap_eq_symmetricAlgebraMapIso_hom hf]

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- An injective comodule morphism preserves and reflects the closure order on rational
vector orbits. -/
noncomputable def vectorOrbitOrderEmbedding (f : Hom k H M N) (hf : Function.Injective f) :
    VectorOrbit k H M ↪o VectorOrbit k H N where
  toFun := f.vectorOrbitMap
  inj' := f.vectorOrbitMap_injective hf
  map_rel_iff' := by
    intro O O'
    -- Reduce the anonymous order embedding's coercion to its underlying orbit map.
    change f.vectorOrbitMap O ≤ f.vectorOrbitMap O' ↔ O ≤ O'
    rw [VectorOrbit.le_iff_closure_image_subset, VectorOrbit.le_iff_closure_image_subset,
      closure_image_vectorOrbitMap f hf, closure_image_vectorOrbitMap f hf]
    let := f.isClosedImmersion_projectiveCompletionMap hf
    exact Set.image_subset_image_iff (IsClosedImmersion.isClosedEmbedding _).injective

/-- The closure-order embedding acts by the forward orbit map. -/
@[simp]
theorem coe_vectorOrbitOrderEmbedding (f : Hom k H M N) (hf : Function.Injective f) :
    ⇑(f.vectorOrbitOrderEmbedding hf) = f.vectorOrbitMap := (rfl)

/-- A comodule isomorphism identifies the closure orders on rational vector orbits. -/
noncomputable def vectorOrbitOrderIso (f : Hom k H M N) (hf : Function.Bijective f) :
    VectorOrbit k H M ≃o VectorOrbit k H N where
  toEquiv := f.vectorOrbitEquiv hf
  map_rel_iff' := (f.vectorOrbitOrderEmbedding hf.injective).map_rel_iff'

/-- Forgetting the order structure recovers the rational-orbit equivalence. -/
@[simp]
theorem vectorOrbitOrderIso_toEquiv (f : Hom k H M N) (hf : Function.Bijective f) :
    (f.vectorOrbitOrderIso hf).toEquiv = f.vectorOrbitEquiv hf := (rfl)

/-- The underlying function of the order isomorphism is rational orbit transport. -/
@[simp]
theorem coe_vectorOrbitOrderIso (f : Hom k H M N) (hf : Function.Bijective f) :
    ⇑(f.vectorOrbitOrderIso hf) = ⇑(f.vectorOrbitEquiv hf) := by
  rw [← OrderIso.coe_toEquiv, vectorOrbitOrderIso_toEquiv]

/-- The underlying function of the inverse order isomorphism is inverse rational orbit transport. -/
@[simp]
theorem coe_vectorOrbitOrderIso_symm (f : Hom k H M N) (hf : Function.Bijective f) :
    ⇑(f.vectorOrbitOrderIso hf).symm = ⇑(f.vectorOrbitEquiv hf).symm := by
  rw [← OrderIso.coe_symm_toEquiv, vectorOrbitOrderIso_toEquiv]

/-- The closure-order isomorphism acts on representatives by the comodule morphism. -/
theorem vectorOrbitOrderIso_mk (f : Hom k H M N) (hf : Function.Bijective f) (v : M) :
    f.vectorOrbitOrderIso hf (VectorOrbit.mk v) = VectorOrbit.mk (f v) := by
  rw [coe_vectorOrbitOrderIso, vectorOrbitEquiv_mk]

/-- The inverse closure-order isomorphism acts by the inverse linear equivalence. -/
theorem vectorOrbitOrderIso_symm_mk (f : Hom k H M N) (hf : Function.Bijective f) (w : N) :
    (f.vectorOrbitOrderIso hf).symm (VectorOrbit.mk w) =
      VectorOrbit.mk ((LinearEquiv.ofBijective f.toLinearMap hf).symm w) := by
  rw [coe_vectorOrbitOrderIso_symm, vectorOrbitEquiv_symm_mk]

-- As for `vectorOrbitEquiv_id`, keep the comodule identity visible until transport simplifies.
/-- Transport along the identity morphism is the identity order isomorphism. -/
@[simp↓]
theorem vectorOrbitOrderIso_id (h : Function.Bijective (id k H M)) :
    (id k H M).vectorOrbitOrderIso h = OrderIso.refl _ := by
  apply RelIso.toEquiv_injective
  rw [vectorOrbitOrderIso_toEquiv, vectorOrbitEquiv_id, OrderIso.refl_toEquiv]

/-- Order transport along a composite is the composite of the two transports. -/
theorem vectorOrbitOrderIso_comp {P : Type u} [AddCommGroup P] [Module k P] [Comodule k H P]
    [Module.Finite k P]
    (g : Hom k H N P) (f : Hom k H M N) (hg : Function.Bijective g) (hf : Function.Bijective f) :
    (g.comp f).vectorOrbitOrderIso (by
      simpa only [← coe_toLinearMap, comp_toLinearMap, LinearMap.coe_comp] using hg.comp hf) =
      (f.vectorOrbitOrderIso hf).trans (g.vectorOrbitOrderIso hg) := by
  apply RelIso.toEquiv_injective
  simp only [OrderIso.toEquiv_trans, vectorOrbitOrderIso_toEquiv, vectorOrbitEquiv_comp g f hg hf]

/-- Order transport along the inverse morphism reverses the original transport. -/
@[simp]
theorem vectorOrbitOrderIso_inverse (f : Hom k H M N) (hf : Function.Bijective f)
    (h : Function.Bijective (f.inverse hf)) :
    (f.inverse hf).vectorOrbitOrderIso h = (f.vectorOrbitOrderIso hf).symm := by
  apply RelIso.toEquiv_injective
  simp only [OrderIso.toEquiv_symm, vectorOrbitOrderIso_toEquiv, vectorOrbitEquiv_inverse]

end TauCeti.Comodule.Hom
