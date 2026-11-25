/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Epi
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

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- A finite affine group homomorphism has trivial scheme-theoretic kernel exactly when it is
a closed immersion, expressed as surjectivity of its coordinate map. -/
theorem surjective_iff_kernelHopfIdeal_eq_augmentation (f : H ⟶ K)
    (hf : f.hom.toAlgHom.Finite) :
    Function.Surjective f.hom ↔ kernelHopfIdeal f = HopfIdeal.augmentation R K := by
  refine ⟨kernelHopfIdeal_eq_augmentation_of_surjective f, fun hker ↦ ?_⟩
  have := epi_ofHom_of_kernelHopfIdeal_eq_augmentation f hker
  exact RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) hf

end TauCeti.CommHopfAlgCat
