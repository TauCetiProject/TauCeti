/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleComposite
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt
import TauCeti.CategoryTheory.Preadditive.Radical.Nilpotent
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# Categories with finitely many indecomposable objects

Let `C` be a linear category over a commutative Artinian ring `R` with finite biproducts, in which
idempotents split and the endomorphisms of every object are finitely generated over `R`; for
instance a Hom-finite idempotent-complete linear category over a field. Suppose that every
indecomposable object is isomorphic to one of finitely many objects `P i`. Then:

* the radical of `C` is nilpotent
  (`TauCeti.exists_jacobsonRadicalIdeal_pow_eq_bot_of_finite_indecomposables`);
* every morphism between indecomposable objects that is not an isomorphism is a sum of composites
  of irreducible morphisms between indecomposable objects
  (`TauCeti.mem_closure_isIrreducibleComposite_of_finite_indecomposables`).

Every object is a direct summand of a finite sum of objects with local endomorphism rings
(`TauCeti.exists_isLocalRing_end_sum_comp_eq_id`). These are indecomposable
(`TauCeti.indecomposable_of_isLocalRing_end`), hence isomorphic to some `P i`, so every object is a
direct summand of a finite sum of copies of `G = ⨁ i, P i`. The endomorphism ring of `G` is
finitely generated over `R`, hence Artinian, and the radical is nilpotent by
`TauCeti.exists_jacobsonRadicalIdeal_pow_eq_bot`. By Fitting's lemma
(`TauCeti.isLocalRing_end_of_indecomposable`) indecomposable objects have local endomorphism rings,
between which the radical morphisms are the non-isomorphisms, and the second statement follows from
`TauCeti.mem_closure_isIrreducibleComposite_of_mem_jacobsonRadical`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable (R : Type*) [CommRing R] [IsArtinianRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [HasFiniteBiproducts C] [IsIdempotentComplete C]
  [∀ X : C, Module.Finite R (X ⟶ X)] {ι : Type*} [Finite ι] (P : ι → C)

include R

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- **The radical of a category with finitely many indecomposable objects is nilpotent**: in an
idempotent-complete linear category over a commutative Artinian ring `R` with finite biproducts
and endomorphisms finitely generated over `R`, in which every indecomposable object is isomorphic
to some `P i`, some power of the radical vanishes. -/
theorem exists_jacobsonRadicalIdeal_pow_eq_bot_of_finite_indecomposables
    (hP : ∀ X : C, Indecomposable X → ∃ i, Nonempty (X ≅ P i)) :
    ∃ N : ℕ, jacobsonRadicalIdeal C ^ N = ⊥ := by
  have := Fintype.ofFinite ι
  have : Module.Finite R (End (⨁ P)) := Module.Finite.equiv End.linearEquiv.symm
  have : IsArtinianRing (End (⨁ P)) := IsArtinianRing.of_finite R _
  refine exists_jacobsonRadicalIdeal_pow_eq_bot (⨁ P) fun X ↦ ?_
  obtain ⟨n, W, a, b, hW, hab⟩ := exists_isLocalRing_end_sum_comp_eq_id R X
  have hWP (j : Fin n) : ∃ i, Nonempty (W j ≅ P i) := by
    have := hW j
    exact hP _ indecomposable_of_isLocalRing_end
  choose σ e using hWP
  refine ⟨n, fun j ↦ a j ≫ (e j).some.hom ≫ biproduct.ι P (σ j),
    fun j ↦ biproduct.π P (σ j) ≫ (e j).some.inv ≫ b j, ?_⟩
  simpa using hab

/-- **In a category with finitely many indecomposable objects, every non-isomorphism between
indecomposable objects is a sum of composites of irreducible morphisms** between objects with
local endomorphism rings, that is, between indecomposable objects. The category is an
idempotent-complete linear category over a commutative Artinian ring `R` with finite biproducts and
endomorphisms finitely generated over `R`, in which every indecomposable object is isomorphic to
some `P i`. -/
theorem mem_closure_isIrreducibleComposite_of_finite_indecomposables
    (hP : ∀ X : C, Indecomposable X → ∃ i, Nonempty (X ≅ P i)) {X Y : C} (hX : Indecomposable X)
    (hY : Indecomposable Y) {f : X ⟶ Y} (hf : ¬ IsIso f) :
    f ∈ AddSubgroup.closure {g : X ⟶ Y | IsIrreducibleComposite g} := by
  have := isLocalRing_end_of_indecomposable (R := R) hX
  have := isLocalRing_end_of_indecomposable (R := R) hY
  obtain ⟨N, hN⟩ := exists_jacobsonRadicalIdeal_pow_eq_bot_of_finite_indecomposables R P hP
  exact mem_closure_isIrreducibleComposite_of_mem_jacobsonRadical
    (fun Z ↦ exists_isLocalRing_end_sum_comp_eq_id R Z) hN
    (mem_jacobsonRadical_iff_not_isIso.mpr hf)

end TauCeti
