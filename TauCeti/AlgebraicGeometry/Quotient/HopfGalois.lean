/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra

/-!
# The base of a Hopf–Galois torsor is a categorical quotient of schemes

Let `H` be a commutative `R`-bialgebra and `A` a commutative `H`-comodule algebra, so that the
affine monoid scheme `G = Spec H` acts on `X = Spec A` by the morphism
`act = Spec (coact) : Spec (A ⊗[R] H) ⟶ X`. Let `B` be an algebra over which `A` is faithfully
flat, acting on `A` by coinvariants, and suppose that the Galois map
`A ⊗[B] A → A ⊗[R] H` is bijective, so that `q : X ⟶ Y = Spec B` is a `G`-torsor:
`X × G ≅ X ×_Y X` by `(x, g) ↦ (x, x g)`.

This file shows that `q` is then a categorical quotient of `X` by `G` in the category of all
schemes: a morphism `f : X ⟶ Z` to an arbitrary scheme `Z` which is invariant, in the sense that
`act ≫ f` and `pr ≫ f` agree on `Spec (A ⊗[R] H)`, where `pr` is the projection to `X`, factors
uniquely through `q`. Over an affine target this is the algebraic statement
`TauCeti.ComoduleAlgebra.existsUnique_comp_eq`.

The proof uses that a faithfully flat morphism of affine schemes is a regular epimorphism in the
category of schemes (`AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine`): `q` is
the coequalizer of the two projections of its kernel pair `X ×_Y X = Spec (A ⊗[B] A)`. Under the
Galois isomorphism these projections become `pr` and `act`, so an invariant morphism coequalizes
the kernel pair.

## Main results

* `TauCeti.ComoduleAlgebra.existsUnique_SpecMap_comp_eq`: an invariant morphism from `Spec A` to
  any scheme factors uniquely through `Spec A ⟶ Spec B`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé IV, §§3.4 and 5.1, and
  Exposé V, §4.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, §8.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

universe u

variable {R : Type*} {H A B : Type u} [CommSemiring R] [CommRing H] [Bialgebra R H] [CommRing A]
  [Algebra R A] [ComoduleAlgebra R H A] [CommRing B] [Algebra R B] [Algebra B A]
  [IsScalarTower R B A]

/-- On the kernel pair `Spec (A ⊗[B] A)` of `Spec A ⟶ Spec B`, the two projections agree after
an invariant morphism, once the Galois map is bijective. -/
private theorem SpecMap_includeLeft_comp_eq
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hbij : Function.Bijective (galoisMap B hB)) {Z : Scheme.{u}} (f : Spec (.of A) ⟶ Z)
    (hf : Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ f) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[B] A)) ≫ f =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).toRingHom) ≫ f := by
  have : IsIso (CommRingCat.ofHom (galoisMap B hB).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  -- Under the Galois isomorphism the two projections become `a ↦ a ⊗ 1` and the coaction.
  have hl : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[B] A) ≫
      CommRingCat.ofHom (galoisMap B hB).toRingHom =
        CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
    ext a
    simp
  have hr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).toRingHom ≫
      CommRingCat.ofHom (galoisMap B hB).toRingHom =
        CommRingCat.ofHom (coactAlgHom R H A).toRingHom := by
    ext a
    simp [← Algebra.TensorProduct.one_def]
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (galoisMap B hB).toRingHom)),
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hl, hr, hf]

/-- **The base of a torsor is a categorical quotient.** Let `A` be a comodule algebra which is
faithfully flat over an algebra `B` acting by coinvariants, with bijective Galois map. A morphism
`f : Spec A ⟶ Z` to any scheme which is invariant under the action, in the sense that composing
it with the action `Spec (coact)` and with the projection `Spec (a ↦ a ⊗ 1)` from
`Spec (A ⊗[R] H)` gives the same morphism, factors uniquely through `Spec A ⟶ Spec B`. -/
theorem existsUnique_SpecMap_comp_eq [Module.FaithfullyFlat B A]
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (hbij : Function.Bijective (galoisMap B hB)) {Z : Scheme.{u}} (f : Spec (.of A) ⟶ Z)
    (hf : Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ f) :
    ∃! g : Spec (.of B) ⟶ Z, Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ g = f := by
  set π := Spec.map (CommRingCat.ofHom (algebraMap B A))
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap B A))).2
    ((RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance)
  have : IsRegularEpi π := isRegularEpi_of_flat_of_surjective_of_isAffine π
  -- The two projections of the kernel pair agree after `f`.
  have hker : pullback.fst π π ≫ f = pullback.snd π π ≫ f := by
    rw [← cancel_epi (pullbackSpecIso B A A).inv, pullbackSpecIso_inv_fst_assoc,
      pullbackSpecIso_inv_snd_assoc]
    exact SpecMap_includeLeft_comp_eq hB hbij f hf
  have hdesc : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ Spec (.of A)), g₁ ≫ π = g₂ ≫ π →
      g₁ ≫ f = g₂ ≫ f := fun g₁ g₂ h ↦ by
    simpa using pullback.lift g₁ g₂ h ≫= hker
  exact ⟨EffectiveEpi.desc π f hdesc, EffectiveEpi.fac π f hdesc,
    fun g hg ↦ EffectiveEpi.uniq π f hdesc g hg⟩

end TauCeti.ComoduleAlgebra
