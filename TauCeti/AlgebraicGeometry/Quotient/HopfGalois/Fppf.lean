/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.Finiteness
public import TauCeti.AlgebraicGeometry.Quotient.HopfGalois.Basic
public import TauCeti.CategoryTheory.Sites.KernelPair

/-!
# Hopf–Galois torsors represent fppf quotient sheaves

Let `H` be a commutative bialgebra over `R`, and let `A` be a commutative comodule algebra
faithfully flat over an algebra `B` acting by coinvariants. When the Galois map
`A ⊗[B] A → A ⊗[R] H` is bijective and `H` is finitely presented over `R`, the projection
`Spec A ⟶ Spec B` is an fppf covering. Its kernel pair is the action and projection from
`Spec (A ⊗[R] H)`. Consequently `Spec B` represents their coequalizer in fppf sheaves,
with the universal property for maps to every fppf sheaf, not only representable ones.

The finite locally free case follows without any finite-presentation hypothesis on `A/B`:
finite projectivity of `H/R` supplies finite presentation, and both finiteness conditions
descend through the Galois isomorphism. An antipode is unnecessary for these conclusions;
when `H` is a Hopf algebra they say that the base of the torsor is its fppf quotient.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé IV, §3,
  and Exposé V, §4.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §8.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

universe u

section Finite

variable {R : Type*} {H A B : Type u} [CommSemiring R] [CommRing H] [Bialgebra R H]
  [CommRing A] [Algebra R A] [ComoduleAlgebra R H A] [CommRing B] [Algebra R B]
  [Algebra B A] [IsScalarTower R B A]

/-- A bijective Galois map identifies the action and projection with the kernel pair of
`Spec A ⟶ Spec B`. Faithful flatness is not needed for this square. -/
theorem isPullback_SpecMap_of_bijective_galoisMap
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hbij : Function.Bijective (galoisMap B hB)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)))
      (Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap B A)))
      (Spec.map (CommRingCat.ofHom (algebraMap B A))) := by
  apply isPullback_SpecMap_of_isPushout
  exact (CommRingCat.isPushout_tensorProduct B A A).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (AlgEquiv.ofBijective (galoisMap B hB) hbij).toRingEquiv.toCommRingCatIso
    (by simp) (by simp) (by ext; simp)
    (by ext; simp [← Algebra.TensorProduct.one_def])

variable [Module.FaithfullyFlat B A]

/-- A faithfully flat Galois torsor for a module-finite bialgebra has finite projection. -/
theorem isFinite_SpecMap_of_bijective_galoisMap [Module.Finite R H]
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hbij : Function.Bijective (galoisMap B hB)) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap B A))) := by
  have := finite_of_bijective_galoisMap hB hbij
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

end Finite

variable {R : Type*} {H A B : Type u} [CommRing R] [CommRing H] [Bialgebra R H]
  [CommRing A] [Algebra R A] [ComoduleAlgebra R H A] [CommRing B] [Algebra R B]
  [Algebra B A] [IsScalarTower R B A] [Module.FaithfullyFlat B A]

/-- Finite presentation of the acting bialgebra makes the faithfully flat torsor projection
locally of finite presentation, hence an fppf covering. -/
theorem locallyOfFinitePresentation_SpecMap_of_bijective_galoisMap
    [Algebra.FinitePresentation R H]
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hbij : Function.Bijective (galoisMap B hB)) :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap B A))) := by
  have := finitePresentation_of_bijective_galoisMap hB hbij
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- The base of a faithfully flat Galois extension for a finitely presented bialgebra
represents the fppf quotient sheaf: the Yoneda image of `Spec A ⟶ Spec B` is the coequalizer
of the projection and the action. -/
noncomputable def isColimitFppfYonedaCofork
    [Algebra.FinitePresentation R H]
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hbij : Function.Bijective (galoisMap B hB)) :
    IsColimit (Cofork.ofπ
      (Scheme.fppfTopology.yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap B A))))
      (by simp only [← Functor.map_comp,
        (isPullback_SpecMap_of_bijective_galoisMap hB hbij).w]) :
      Cofork
        (Scheme.fppfTopology.yoneda.map (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H))))
        (Scheme.fppfTopology.yoneda.map
          (Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom)))) := by
  have := locallyOfFinitePresentation_SpecMap_of_bijective_galoisMap hB hbij
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap B A))).2
      ((RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance)
  exact IsKernelPair.isColimitYonedaCofork Scheme.fppfTopology
    (isPullback_SpecMap_of_bijective_galoisMap hB hbij)
    (Precoverage.generate_mem_toGrothendieck
      (Spec.map (CommRingCat.ofHom (algebraMap B A))).singleton_mem_fppfPrecoverage)

/-- Every invariant map from a faithfully flat Galois torsor to an arbitrary fppf sheaf
descends uniquely to its base. The acting bialgebra need only be finitely presented. -/
theorem existsUnique_fppfYoneda_comp_eq_of_bijective_galoisMap
    [Algebra.FinitePresentation R H]
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hbij : Function.Bijective (galoisMap B hB))
    {F : Sheaf Scheme.fppfTopology (Type u)}
    (f : Scheme.fppfTopology.yoneda.obj (Spec (.of A)) ⟶ F)
    (hf : Scheme.fppfTopology.yoneda.map
        (Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom)) ≫ f =
      Scheme.fppfTopology.yoneda.map (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H))) ≫ f) :
    ∃! g : Scheme.fppfTopology.yoneda.obj (Spec (.of B)) ⟶ F,
      Scheme.fppfTopology.yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap B A))) ≫ g = f :=
  Cofork.IsColimit.existsUnique
    (isColimitFppfYonedaCofork hB hbij) f hf.symm

end TauCeti.ComoduleAlgebra
