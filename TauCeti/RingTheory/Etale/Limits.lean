/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Property
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import TauCeti.RingTheory.Etale.Equalizer

/-!
# Finite limits of finite étale algebras

Finite products and equalizers of finite étale algebras are finite étale: in Mathlib's language
for properties of ring homomorphisms, finite and étale ring homomorphisms each have finite products
(`RingHom.Finite.hasFiniteProducts`, `RingHom.Etale.hasFiniteProducts`), and finite étale ring
homomorphisms have equalizers (`RingHom.hasEqualizers_finite_and_etale`), which is a restatement
of `AlgHom.etale_equalizer` and `AlgHom.finite_equalizer`.

Consequently the full subcategory `CommAlgCat.FiniteEtale R` of commutative `R`-algebras is closed
under finite products and equalizers, so it has finite limits and its inclusion into
`CommAlgCat R` preserves them. Through the anti-equivalence between finite étale algebras and
finite étale schemes over `Spec R`, these are finite colimits of finite étale schemes, among them
the quotients by finite groups required of a Galois category.

The closure statements are obtained from Mathlib's
`RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape` and
`RingHom.HasEqualizers.isClosedUnderLimitsOfShape` for the corresponding property of objects of
`Under R`, pulled back along the equivalence `commAlgCatEquivUnder` between commutative
`R`-algebras and commutative rings under `R`.

## Main results

* `RingHom.Finite.hasFiniteProducts`, `RingHom.Etale.hasFiniteProducts`: finite products of
  finite, respectively étale, algebras are finite, respectively étale.
* `RingHom.hasEqualizers_finite_and_etale`: equalizers of finite étale algebras are finite étale.
* `CommAlgCat.finiteEtale_eq_inverseImage`: finite étaleness of a commutative `R`-algebra is
  finite étaleness of its structure map, as a ring under `R`.
* `HasFiniteLimits (CommAlgCat.FiniteEtale R)`, with finite limits preserved by the inclusion into
  `CommAlgCat R`.

## References

* H. W. Lenstra, *Galois theory for schemes*, Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits MorphismProperty

universe u

namespace RingHom

/-- Finite products of finite algebras are finite. -/
theorem Finite.hasFiniteProducts : HasFiniteProducts @Finite := by
  intro R _ ι _ S _ _ hS
  simp_rw [finite_algebraMap] at hS ⊢
  infer_instance

/-- Finite products of étale algebras are étale. -/
theorem Etale.hasFiniteProducts : HasFiniteProducts @Etale := by
  intro R _ ι _ S _ _ hS
  simp_rw [etale_algebraMap] at hS ⊢
  infer_instance

/-- **Equalizers of finite étale algebras are finite étale.** -/
theorem hasEqualizers_finite_and_etale :
    HasEqualizers fun f ↦ f.Finite ∧ f.Etale := by
  intro R S T _ _ _ _ _ f g ⟨_, _⟩ ⟨_, _⟩
  simp_rw [finite_algebraMap, etale_algebraMap] at *
  exact ⟨inferInstance, inferInstance⟩

end RingHom

namespace CommAlgCat

variable (R : Type u) [CommRing R]

/-- A commutative `R`-algebra is finite étale exactly when its structure map is finite and étale,
viewed as a commutative ring under `R` through `commAlgCatEquivUnder`. -/
theorem finiteEtale_eq_inverseImage :
    finiteEtale.{u} R =
      (RingHom.toMorphismProperty fun f ↦ f.Finite ∧ f.Etale).underObj.inverseImage
        (commAlgCatEquivUnder (.of R)).functor := by
  ext A
  exact (RingHom.finite_algebraMap.and RingHom.etale_algebraMap).symm

instance : (finiteEtale.{u} R).IsClosedUnderLimitsOfShape WalkingParallelPair := by
  have := RingHom.HasEqualizers.isClosedUnderLimitsOfShape (Q := fun f ↦ f.Finite ∧ f.Etale)
    (RingHom.finite_respectsIso.and RingHom.Etale.respectsIso)
    @RingHom.hasEqualizers_finite_and_etale (.of R)
  rw [finiteEtale_eq_inverseImage]
  infer_instance

instance : (finiteEtale.{u} R).IsClosedUnderFiniteProducts := by
  have := RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape (Q := fun f ↦ f.Finite ∧ f.Etale)
    (RingHom.finite_respectsIso.and RingHom.Etale.respectsIso)
    (RingHom.Finite.hasFiniteProducts.and @RingHom.Etale.hasFiniteProducts) (.of R)
  rw [finiteEtale_eq_inverseImage]
  exact ⟨fun _ _ ↦ inferInstance⟩

/-- Finite étale `R`-algebras have finite limits, computed in commutative `R`-algebras. -/
instance : HasFiniteLimits (FiniteEtale.{u} R) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- The inclusion of finite étale `R`-algebras into commutative `R`-algebras preserves finite
limits. -/
instance : PreservesFiniteLimits (finiteEtale.{u} R).ι :=
  have : PreservesFiniteProducts (finiteEtale.{u} R).ι := ⟨fun _ ↦ inferInstance⟩
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

end CommAlgCat
