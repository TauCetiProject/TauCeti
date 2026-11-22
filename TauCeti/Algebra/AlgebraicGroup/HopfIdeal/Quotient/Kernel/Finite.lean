/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import Mathlib.Algebra.Category.Ring.Epi

/-!
# Finite homomorphisms with trivial kernel

A finite homomorphism of affine group schemes with trivial scheme-theoretic kernel is a
closed immersion. In Hopf coordinates, its coordinate map is surjective exactly when its
kernel Hopf ideal is the augmentation ideal. Testing the kernel on all algebras is essential:
injectivity on field-valued points alone would not detect infinitesimal kernels.

A homomorphism with trivial kernel is injective on points over every algebra, so its coordinate
map is an epimorphism of commutative rings (`epi_ofHom_of_kernelHopfIdeal_eq_augmentation`).
The finite case then uses Mathlib's theorem that a finite ring epimorphism is surjective. This
supplies the trivial-kernel criterion for isogenies without assuming smoothness or a field base.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- A homomorphism of affine groups with trivial scheme-theoretic kernel is a monomorphism of
affine schemes: its coordinate map is an epimorphism of commutative rings. The kernel is tested
on all algebras, so this sees infinitesimal kernels. -/
theorem epi_ofHom_of_kernelHopfIdeal_eq_augmentation (f : H ⟶ K)
    (hker : kernelHopfIdeal f = HopfIdeal.augmentation R K) :
    Epi (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) := by
  have hinj (A : CommAlgCat.{v} R) :
      Function.Injective ((CommHopfAlgCat.Hom.mapPointsFunctor f).app A) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    erw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at hg
    have hmem := (mapPointsFunctor_app_eq_one_iff f A g).mp hg
    rw [hker] at hmem
    exact eq_one_of_mem_quotientPointsSubgroup_augmentation K A hmem
  refine ⟨fun {A} g h hgh ↦ ?_⟩
  let : Algebra R A := (g.hom.comp (algebraMap R K)).toAlgebra
  let g' : K →ₐ[R] A := ⟨g.hom, fun _ ↦ rfl⟩
  let h' : K →ₐ[R] A := ⟨h.hom, fun r ↦ by
    have he := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hgh)
      (algebraMap R H r)
    -- The chosen algebra structure on `A` is restriction along `g`.
    change h.hom (algebraMap R K r) = g.hom (algebraMap R K r)
    rw [← f.hom.toAlgHom.commutes r]
    exact he.symm⟩
  have he : (CommHopfAlgCat.Hom.mapPointsFunctor f).app (CommAlgCat.of R A) (toConv g') =
      (CommHopfAlgCat.Hom.mapPointsFunctor f).app (CommAlgCat.of R A) (toConv h') := by
    apply WithConv.ofConv_injective
    ext x
    erw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply,
      CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply]
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hgh) x
  have he' := congrArg WithConv.ofConv (hinj (CommAlgCat.of R A) he)
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom he')

/-- A finite affine group homomorphism has trivial scheme-theoretic kernel exactly when it is
a closed immersion, expressed as surjectivity of its coordinate map. -/
theorem surjective_iff_kernelHopfIdeal_eq_augmentation (f : H ⟶ K)
    (hf : f.hom.toAlgHom.Finite) :
    Function.Surjective f.hom ↔ kernelHopfIdeal f = HopfIdeal.augmentation R K := by
  refine ⟨kernelHopfIdeal_eq_augmentation_of_surjective f, fun hker ↦ ?_⟩
  have := epi_ofHom_of_kernelHopfIdeal_eq_augmentation f hker
  exact RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) hf

end TauCeti.CommHopfAlgCat
