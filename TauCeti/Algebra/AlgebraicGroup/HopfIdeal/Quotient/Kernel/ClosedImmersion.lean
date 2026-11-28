/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.EqualizerPushout
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.FaithfullyFlat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Epi
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Dimension
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced

/-!
# Homomorphisms with trivial kernel are closed immersions

Let `f : H ⟶ K` be a morphism of finite-type commutative Hopf algebras over a field `k`.
Contravariantly it represents a homomorphism of affine groups `Spec K ⟶ Spec H`. If the source
`Spec K` is geometrically reduced (equivalently smooth) and the homomorphism has trivial
scheme-theoretic kernel, then it is a closed immersion: the coordinate map `f` is surjective.

The proof factors `f` through its image. The factor `imageι f : H / ker f ⟶ K` is faithfully
flat because the source is geometrically reduced, so it is a regular monomorphism of commutative
rings. Its kernel is the kernel of `f`, which is trivial, so it is injective on points over every
algebra and hence an epimorphism of commutative rings. A regular monomorphism which is an
epimorphism is an isomorphism, so `f` is the surjection onto its image followed by an isomorphism.

A closed immersion of smooth connected affine groups which does not drop the Lie dimension is an
isomorphism (`isIso_of_surjective_of_finrank_le`). Combined with the closed-immersion theorem
this gives an isomorphism criterion for homomorphisms with trivial kernel.

## Main declarations

* `TauCeti.CommHopfAlgCat.surjective_of_kernelHopfIdeal_eq_augmentation`: a homomorphism from a
  geometrically reduced affine group with trivial kernel is a closed immersion.
* `TauCeti.CommHopfAlgCat.surjective_iff_kernelHopfIdeal_eq_augmentation_of_isGeometricallyReduced`:
  for geometrically reduced source, the homomorphism is a closed immersion exactly when its kernel
  is trivial.
* `TauCeti.CommHopfAlgCat.isIso_of_kernelHopfIdeal_eq_augmentation_of_finrank_le`: a homomorphism
  of smooth connected affine groups with trivial kernel and no drop in Lie dimension is an
  isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 5.34 and Proposition 1.70.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §15.3.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}

section GeometricallyReduced

variable [Algebra.FiniteType k H] [Algebra.FiniteType k K] [Algebra.IsGeometricallyReduced k K]

/-- For a homomorphism from a geometrically reduced affine group with trivial kernel, the
coordinate map from the image to the source is bijective: the homomorphism maps its source
isomorphically onto its scheme-theoretic image. -/
theorem imageι_bijective_of_kernelHopfIdeal_eq_augmentation (f : H ⟶ K)
    (hker : kernelHopfIdeal f = HopfIdeal.augmentation k K) :
    Function.Bijective (imageι f).hom := by
  have : Epi (CommRingCat.ofHom (imageι f).hom.toAlgHom.toRingHom) :=
    epi_ofHom_of_kernelHopfIdeal_eq_augmentation (imageι f) (by rw [kernelHopfIdeal_imageι, hker])
  have := isIso_of_regularMono_of_epi _
    (CommRingCat.regularMonoOfFaithfullyFlat
      (CommRingCat.ofHom (imageι f).hom.toAlgHom.toRingHom) (faithfullyFlat_imageι f))
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (imageι f).hom.toAlgHom.toRingHom)

/-- **A homomorphism with trivial kernel from a geometrically reduced affine group is a closed
immersion.** If the kernel Hopf ideal of `f : H ⟶ K` is the augmentation ideal, so that the
represented homomorphism `Spec K ⟶ Spec H` has trivial scheme-theoretic kernel, then the
coordinate map `f` is surjective. -/
theorem surjective_of_kernelHopfIdeal_eq_augmentation (f : H ⟶ K)
    (hker : kernelHopfIdeal f = HopfIdeal.augmentation k K) :
    Function.Surjective f.hom := by
  have hf : ⇑f.hom = (imageι f).hom ∘ (mkImage f).hom := by
    ext x
    exact (imageι_mkImage_apply f x).symm
  rw [hf]
  exact (imageι_bijective_of_kernelHopfIdeal_eq_augmentation f hker).2.comp (mkImage_surjective f)

/-- For a homomorphism from a geometrically reduced affine group, being a closed immersion is
equivalent to having trivial scheme-theoretic kernel. -/
theorem surjective_iff_kernelHopfIdeal_eq_augmentation_of_isGeometricallyReduced (f : H ⟶ K) :
    Function.Surjective f.hom ↔ kernelHopfIdeal f = HopfIdeal.augmentation k K :=
  ⟨kernelHopfIdeal_eq_augmentation_of_surjective f,
    surjective_of_kernelHopfIdeal_eq_augmentation f⟩

end GeometricallyReduced

/-- **A homomorphism of smooth connected affine groups with trivial kernel and no drop in Lie
dimension is an isomorphism.** Here `f : H ⟶ K` represents `Spec K ⟶ Spec H`: trivial kernel
makes it a closed immersion, and a closed smooth connected subgroup of the same Lie dimension is
the whole group. -/
theorem isIso_of_kernelHopfIdeal_eq_augmentation_of_finrank_le (f : H ⟶ K)
    (hH_smooth : smoothCommHopfAlgProperty k H) (hH_connected : ConnectedSpace (PrimeSpectrum H))
    (hK_smooth : smoothCommHopfAlgProperty k K) (hK_connected : ConnectedSpace (PrimeSpectrum K))
    (hker : kernelHopfIdeal f = HopfIdeal.augmentation k K)
    (hfinrank :
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) ≤
        Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k))) :
    IsIso f := by
  let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff _).mp hH_smooth
  let _ : Algebra.Smooth k K := (smoothCommHopfAlgProperty_iff _).mp hK_smooth
  have : Algebra.IsGeometricallyReduced k K :=
    (geometricallyReducedCommHopfAlgProperty_of_smooth k K hK_smooth).isGeometricallyReduced
  exact isIso_of_surjective_of_finrank_le f (surjective_of_kernelHopfIdeal_eq_augmentation f hker)
    hH_smooth hH_connected hK_smooth hK_connected hfinrank

end TauCeti.CommHopfAlgCat
