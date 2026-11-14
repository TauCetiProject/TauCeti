/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Naturality
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.DominantPoints

/-!
# Orbit comparison under restriction of representations

Restricting a representation along a surjective affine-group morphism preserves its
geometric orbit images, including their nonclosed points. Over an algebraically closed
field, for groups of finite type, it also identifies rational orbits and their closure
orders. This applies to isogenies, including inseparable isogenies: the comparison uses
surjectivity on spectra, rather than an isomorphism of tangent spaces.

`BialgHom.vectorOrbitOrderIsoCorestrict` is the order isomorphism. Its forward and inverse
maps both send the orbit of a vector to the orbit of the same vector in the other action.
`BialgHom.image_vectorOrbitOrderIsoCorestrict` identifies the geometric images, so that
the comparison retains orbit closures, boundaries and dimensions in the same ambient
projective completion. The underlying rational-orbit equivalence is available whenever
the morphism is surjective on rational points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  §1.3, for the application to adjoint orbits under central isogenies.
-/

public section

open TauCeti TauCeti.Comodule

namespace BialgHom

universe u

variable {k H K M : Type u} [Field k] [CommRing H] [CommRing K]
  [HopfAlgebra k H] [HopfAlgebra k K] [AddCommGroup M] [Module k M] [Comodule k H M]

/-- Restriction along a morphism surjective on rational points identifies rational vector
orbits. The equivalence does not require finite-dimensional representations. -/
def vectorOrbitEquivCorestrict (f : H →ₐc[k] K)
    (hf : Function.Surjective (mapDomain (A := k) f)) :
    (letI : Comodule k K M := Corestrict f.toCoalgHom
     VectorOrbit k K M) ≃ VectorOrbit k H M := by
  letI : Comodule k K M := Corestrict f.toCoalgHom
  refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  · refine VectorOrbit.lift (H := K) (fun v : M => VectorOrbit.mk (H := H) v) ?_
    intro g v
    rw [basePointsRepresentation_corestrict]
    exact VectorOrbit.mk_basePointsRepresentation _ _
  · refine VectorOrbit.lift (H := H) (fun v : M => VectorOrbit.mk (H := K) v) ?_
    intro g v
    obtain ⟨q, rfl⟩ := hf g
    rw [← basePointsRepresentation_corestrict f q]
    exact VectorOrbit.mk_basePointsRepresentation _ _
  · intro O
    induction O using VectorOrbit.ind with | h v
    simp only [VectorOrbit.lift_mk]
  · intro O
    induction O using VectorOrbit.ind with | h v
    simp only [VectorOrbit.lift_mk]

/-- The rational-orbit comparison sends the orbit of a vector to its original orbit. -/
@[simp]
theorem vectorOrbitEquivCorestrict_mk (f : H →ₐc[k] K)
    (hf : Function.Surjective (mapDomain (A := k) f)) (v : M) :
    vectorOrbitEquivCorestrict (M := M) f hf
        (letI : Comodule k K M := Corestrict f.toCoalgHom
         VectorOrbit.mk v) = VectorOrbit.mk v := by
  simp [vectorOrbitEquivCorestrict]

/-- The inverse rational-orbit comparison sends the orbit of a vector to its restricted orbit. -/
@[simp]
theorem vectorOrbitEquivCorestrict_symm_mk (f : H →ₐc[k] K)
    (hf : Function.Surjective (mapDomain (A := k) f)) (v : M) :
    (vectorOrbitEquivCorestrict (M := M) f hf).symm (VectorOrbit.mk v) =
      (letI : Comodule k K M := Corestrict f.toCoalgHom
       VectorOrbit.mk v) := by
  simp [vectorOrbitEquivCorestrict]

variable [Module.Finite k M]

attribute [local instance] prodTrivial

/-- Restriction along a surjective affine-group morphism preserves the full geometric
orbit image of a vector in its projective completion. -/
theorem range_projectiveOrbitMap_mk_one_corestrict (f : H →ₐc[k] K)
    (hf : Function.Surjective (PrimeSpectrum.comap f.toAlgHom.toRingHom)) (v : M) :
    (letI : Comodule k K M := Corestrict f.toCoalgHom
     Set.range (projectiveOrbitMap (H := K) ((v, 1) : M × k)
       (Module.isUnimodular_mk_one v))) =
      Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v)) := by
  rw [corestrict_prodTrivial k H f]
  exact range_projectiveOrbitMap_corestrict (M := M × k) f hf _ _

section Order

variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.FiniteType k K]

/-- A surjective affine-group morphism of finite type identifies the closure orders on
rational vector orbits of a representation and its restriction. -/
noncomputable def vectorOrbitOrderIsoCorestrict (f : H →ₐc[k] K)
    (hf : Function.Surjective (PrimeSpectrum.comap f.toAlgHom.toRingHom)) :
    (letI : Comodule k K M := Corestrict f.toCoalgHom
     VectorOrbit k K M) ≃o VectorOrbit k H M := by
  have hp : Function.Surjective (mapDomain (A := k) f) := by
    intro g
    obtain ⟨q, hq⟩ := CommHopfAlgCat.mapPointsFunctor_app_surjective_of_dominant
      (_root_.CommHopfAlgCat.ofHom f) hf.denseRange g
    exact ⟨q, (mapDomain_apply f q).trans
      ((CommHopfAlgCat.Hom.mapPointsFunctor_app_apply _ _ q).symm.trans hq)⟩
  refine { toEquiv := vectorOrbitEquivCorestrict f hp, map_rel_iff' := ?_ }
  intro O O'
  let : Comodule k K M := Corestrict f.toCoalgHom
  induction O using VectorOrbit.ind with | h v
  induction O' using VectorOrbit.ind with | h w
  simp only [vectorOrbitEquivCorestrict_mk, VectorOrbit.le_iff_closure_image_subset,
    VectorOrbit.image_mk, range_projectiveOrbitMap_mk_one_corestrict f hf]

/-- The order comparison preserves the vector representing an orbit. -/
@[simp]
theorem vectorOrbitOrderIsoCorestrict_mk (f : H →ₐc[k] K)
    (hf : Function.Surjective (PrimeSpectrum.comap f.toAlgHom.toRingHom)) (v : M) :
    vectorOrbitOrderIsoCorestrict (M := M) f hf
        (letI : Comodule k K M := Corestrict f.toCoalgHom
         VectorOrbit.mk v) = VectorOrbit.mk v := by
  simp [vectorOrbitOrderIsoCorestrict, vectorOrbitEquivCorestrict]

/-- The inverse order comparison preserves the vector representing an orbit. -/
@[simp]
theorem vectorOrbitOrderIsoCorestrict_symm_mk (f : H →ₐc[k] K)
    (hf : Function.Surjective (PrimeSpectrum.comap f.toAlgHom.toRingHom)) (v : M) :
    (vectorOrbitOrderIsoCorestrict (M := M) f hf).symm (VectorOrbit.mk v) =
      (letI : Comodule k K M := Corestrict f.toCoalgHom
       VectorOrbit.mk v) := by
  simp [vectorOrbitOrderIsoCorestrict, vectorOrbitEquivCorestrict]

/-- The orbit-order comparison preserves the entire geometric image, not only its rational
points. Its closure and boundary therefore agree as well. -/
@[simp]
theorem image_vectorOrbitOrderIsoCorestrict (f : H →ₐc[k] K)
    (hf : Function.Surjective (PrimeSpectrum.comap f.toAlgHom.toRingHom))
    (O : letI : Comodule k K M := Corestrict f.toCoalgHom
      VectorOrbit k K M) :
    (vectorOrbitOrderIsoCorestrict f hf O).image =
      (letI : Comodule k K M := Corestrict f.toCoalgHom
       O.image) := by
  let : Comodule k K M := Corestrict f.toCoalgHom
  induction O using VectorOrbit.ind with | h v
  simp only [vectorOrbitOrderIsoCorestrict_mk, VectorOrbit.image_mk,
    range_projectiveOrbitMap_mk_one_corestrict f hf]

end Order

end BialgHom
