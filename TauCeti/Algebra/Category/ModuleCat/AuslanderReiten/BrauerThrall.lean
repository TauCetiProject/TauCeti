/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
public import TauCeti.CategoryTheory.AlmostSplit.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
import TauCeti.Algebra.Category.ModuleCat.HaradaSai
import TauCeti.Algebra.Category.FGModuleCat.RepresentationFinite
import TauCeti.Algebra.Category.ModuleCat.Injective.LeftAlmostSplit
import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
import TauCeti.CategoryTheory.AlmostSplit.Finiteness

/-!
# The first Brauer–Thrall conjecture

The **first Brauer–Thrall conjecture**, proved by Roiter, says that an algebra whose finitely
generated indecomposable modules have bounded length has only finitely many of them up to
isomorphism. This file proves it for finite-dimensional algebras over a field, through Auslander's
argument with almost-split sequences and the Harada–Sai lemma:

* every nonzero module receives a nonzero morphism from an indecomposable summand of the ring;
* such a morphism, unless it is an isomorphism, factors through a left almost split map, whose
  target has finitely many indecomposable summands;
* a chain of `2 ^ b - 1` non-isomorphisms between indecomposable modules of length at most `b`
  vanishes by the Harada–Sai lemma, so the factoring process stops after finitely many steps.

At an indecomposable injective module, which starts no almost-split sequence, the left almost split
map is `TauCeti.exists_isAtom_isLeftAlmostSplit_ofHom_mkQ`. Over any Artinian ring, the conjecture
therefore holds as soon as every finitely generated indecomposable non-injective module has a left
almost split map with finitely generated target
(`TauCeti.isRepresentationFinite_of_length_le_of_isLeftAlmostSplit`). Over a finite-dimensional
algebra this is the existence half of the Auslander–Reiten theorem,
`ModuleCat.exists_isAlmostSplit_of_not_injective`.

## Main results

* `TauCeti.isRepresentationFinite_of_length_le`: **the first Brauer–Thrall conjecture** for a
  finite-dimensional algebra.
* `TauCeti.isRepresentationFinite_iff_exists_length_le`: a finite-dimensional algebra is
  representation-finite exactly when the lengths of its finitely generated indecomposable modules
  are bounded.

## References

* M. Auslander, *Representation theory of Artin algebras II*, Comm. Algebra 1 (1974), 269–310.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Corollary VI.1.5.
* A. V. Roiter, *Unboundedness of the dimensions of the indecomposable representations of an
  algebra which has infinitely many indecomposable representations*, Izv. Akad. Nauk SSSR
  Ser. Mat. 32 (1968), 1275–1282.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {A : Type v} [Ring A]

/-- **The first Brauer–Thrall conjecture from left almost split maps.** Let `A` be an Artinian ring
over which every finitely generated indecomposable non-injective module has a left almost split map
with finitely generated target. If the finitely generated indecomposable modules have bounded
length, then `A` is representation-finite. -/
theorem isRepresentationFinite_of_length_le_of_isLeftAlmostSplit [IsArtinianRing A] (b : ℕ)
    (hlen : ∀ M : ModuleCat.{max v w} A, Module.Finite A M → Indecomposable M →
      Module.length A M ≤ b)
    (hsrc : ∀ N : ModuleCat.{max v w} A, Module.Finite A N → Indecomposable N → ¬ Injective N →
      ∃ (E : ModuleCat.{max v w} A) (i : N ⟶ E), Module.Finite A E ∧ IsLeftAlmostSplit i) :
    IsRepresentationFinite.{max v w} A := by
  let T : ObjectProperty (ModuleCat.{max v w} A) := fun M ↦ Module.Finite A M ∧ Indecomposable M
  have hlocal (X : ModuleCat.{max v w} A) (hX : T X) : IsLocalRing (End X) := by
    have := hX.1
    exact (indecomposable_iff_isLocalRing_end X
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)).mp hX.2
  -- A finitely generated module is a finite biproduct of objects of `T`.
  have hsum (E : ModuleCat.{max v w} A) [Module.Finite A E] :
      ∃ (n : ℕ) (F : Fin n → ModuleCat.{max v w} A), Nonempty (E ≅ ⨁ F) ∧ ∀ j, T (F j) := by
    obtain ⟨n, F, hF, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct E
    refine ⟨n, F, ⟨e⟩, fun j ↦ ⟨?_, hF j⟩⟩
    exact Module.Finite.of_surjective (e.hom ≫ biproduct.π F j).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  -- Every object of `T` has a left almost split map into a finite biproduct of objects of `T`.
  have hsrc' (X : ModuleCat.{max v w} A) (hX : T X) :
      ∃ (n : ℕ) (F : Fin n → ModuleCat.{max v w} A) (i : X ⟶ ⨁ F),
        (∀ j, T (F j)) ∧ IsLeftAlmostSplit i := by
    have := hlocal X hX
    obtain ⟨hf, hi⟩ := hX
    have hE : ∃ (E : ModuleCat.{max v w} A) (i : X ⟶ E), Module.Finite A E ∧
        IsLeftAlmostSplit i := by
      by_cases hinj : Injective X
      · obtain ⟨S, -, hS⟩ := exists_isAtom_isLeftAlmostSplit_ofHom_mkQ (N := X)
        exact ⟨_, _, inferInstanceAs (Module.Finite A (X ⧸ S)), hS⟩
      · exact hsrc X hf hi hinj
    obtain ⟨E, i, hE, hi⟩ := hE
    obtain ⟨n, F, ⟨e⟩, hF⟩ := hsum E
    exact ⟨n, F, i ≫ e.hom, hF, hi.comp_iso e.hom⟩
  -- The indecomposable summands of the ring.
  let G : ModuleCat.{max v w} A := ModuleCat.of A (ULift.{w} A)
  have : Module.Finite A G := Module.Finite.equiv (ULift.moduleEquiv (R := A) (M := A)).symm
  obtain ⟨m, P, ⟨e⟩, hP⟩ := hsum G
  obtain ⟨S, hS, -, hSmem⟩ := exists_finite_forall_iso_of_hom_ne_zero T hlocal hsrc' (2 ^ b - 1)
    (fun X f hX hf ↦ ofSequence_map_eq_zero_of_length_le f (fun n ↦ (hX n).2)
      (fun n ↦ hlen _ (hX n).1 (hX n).2) hf le_rfl)
    (Set.finite_range P) (by rintro _ ⟨j, rfl⟩; exact hP j)
  refine isRepresentationFinite_of_forall_exists_iso hS fun M hf hi ↦ ?_
  -- A nonzero module receives a nonzero morphism from the ring, hence from a summand.
  have : Nontrivial M := ((indecomposable_iff_isIndecomposableModule M).mp hi).nontrivial
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  let t : G ⟶ M := ModuleCat.ofHom
    (LinearMap.toSpanSingleton A M x ∘ₗ (ULift.moduleEquiv (R := A) (M := A)).toLinearMap)
  have ht : e.inv ≫ t ≠ 0 := fun h ↦ hx <| by
    have h₀ : t = 0 := by simpa using congrArg (e.hom ≫ ·) h
    simpa [t, G] using ConcreteCategory.congr_hom h₀ (ULift.up 1 : ULift.{w} A)
  obtain ⟨j, hj⟩ : ∃ j, biproduct.ι P j ≫ e.inv ≫ t ≠ 0 := by
    by_contra! hzero
    exact ht (biproduct.hom_ext' _ _ fun j ↦ by rw [hzero j, comp_zero])
  exact hSmem M ⟨hf, hi⟩ (P j) ⟨j, rfl⟩ _ hj

/-- **The first Brauer–Thrall conjecture** for a finite-dimensional algebra: if the finitely
generated indecomposable modules have bounded length, then there are only finitely many of them up
to isomorphism. -/
theorem isRepresentationFinite_of_length_le (k : Type u) [Field k] [Algebra k A]
    [FiniteDimensional k A] (b : ℕ)
    (hlen : ∀ M : ModuleCat.{max u v w} A, Module.Finite A M → Indecomposable M →
      Module.length A M ≤ b) :
    IsRepresentationFinite.{max u v w} A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  refine isRepresentationFinite_of_length_le_of_isLeftAlmostSplit.{v, max u w} b hlen
    fun N hf hi hinj ↦ ?_
  have := hf
  obtain ⟨E, _, i, _, _, hE, _, hS⟩ := ModuleCat.exists_isAlmostSplit_of_not_injective k N hi hinj
  exact ⟨E, i, hE, hS.isLeftAlmostSplit_f⟩

/-- **A finite-dimensional algebra is representation-finite exactly when the lengths of its
finitely generated indecomposable modules are bounded.** -/
theorem isRepresentationFinite_iff_exists_length_le (k : Type u) [Field k] [Algebra k A]
    [FiniteDimensional k A] :
    IsRepresentationFinite.{max u v w} A ↔
      ∃ b : ℕ, ∀ M : ModuleCat.{max u v w} A, Module.Finite A M → Indecomposable M →
        Module.length A M ≤ b := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact ⟨IsRepresentationFinite.exists_length_le,
    fun ⟨b, hb⟩ ↦ isRepresentationFinite_of_length_le.{u, v, w} k b hb⟩

end TauCeti
