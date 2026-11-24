/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Gallagher
public import TauCeti.RepresentationTheory.CharacterTable.Automorphism

/-!
# Checks for Gallagher's correspondence

These examples exercise `TauCeti.gallagher_bijOn` in its two degenerate cases.

* `N = G`: the quotient `G ⧸ G` is trivial, its only irreducible character is `1`, and the
  correspondence says that `χ` is the only irreducible character of `G` lying over its own
  restriction to `G`.
* `N = 1`: every irreducible character lies over the trivial character of the trivial subgroup,
  and for a linear character `χ` the correspondence says that multiplication by `χ` permutes the
  irreducible characters of `G`, read through `G ⧸ ⊥`.
-/

public section

open Finset

namespace TauCeti.Examples.RepresentationTheory.Gallagher

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {G : Type*} [Group G] [Fintype G]

/-- A group with one element has the trivial character as its only irreducible character. -/
theorem irreducibleCharacters_of_subsingleton {Q : Type*} [Group Q] [Subsingleton Q] :
    irreducibleCharacters k Q = {fun _ => 1} := by
  have : Finite Q := Finite.of_subsingleton
  let : Invertible (Nat.card Q : k) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨i, hi⟩ := exists_irreducibleCharacter_eq_one k Q
  have : Subsingleton (ConjClasses Q) := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective a
    obtain ⟨y, rfl⟩ := ConjClasses.mk_surjective b
    rw [Subsingleton.elim x y]⟩
  have hcard : Nat.card (irreducibleCharacters k Q) = 1 := by
    rw [card_irreducibleCharacters, Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, ⟨ConjClasses.mk 1⟩⟩
  obtain ⟨⟨f, hf⟩, hx⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have h1 : (fun _ : Q => (1 : k)) ∈ irreducibleCharacters k Q := hi ▸ irreducibleCharacter_mem k i
  ext g
  refine ⟨fun hg => ?_, fun hg => (Set.mem_singleton_iff.mp hg) ▸ h1⟩
  have e1 := congrArg Subtype.val (hx ⟨g, hg⟩)
  have e2 := congrArg Subtype.val (hx ⟨_, h1⟩)
  exact Set.mem_singleton_iff.mpr (e1.trans e2.symm)

open scoped Classical in
/-- **`N = G`**: an irreducible character `χ` is the only irreducible character lying over its
restriction to `⊤`, the image of the trivial character of `G ⧸ ⊤`. -/
example {χ : G → k} (hχ : χ ∈ irreducibleCharacters k G) :
    irreducibleCharactersOver k (⊤ : Subgroup G) (fun n => χ n) = {χ} := by
  have hθ : (fun n : (⊤ : Subgroup G) => χ n) ∈ irreducibleCharacters k (⊤ : Subgroup G) :=
    (⊤ : Subgroup G).subtype.comp_mem_irreducibleCharacters
      (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩) hχ
  have := QuotientGroup.subsingleton_quotient_top (G := G)
  rw [← (gallagher_bijOn hχ hθ fun _ => rfl).image_eq, irreducibleCharacters_of_subsingleton,
    Set.image_singleton]
  simp

open scoped Classical in
/-- **`N = 1`**: every irreducible character of `G` lies over the trivial character of `⊥`. -/
example : irreducibleCharactersOver k (⊥ : Subgroup G) (fun _ => 1) =
    irreducibleCharacters k G := by
  ext ψ
  refine ⟨fun h => (mem_irreducibleCharactersOver_iff.mp h).1,
    fun h => mem_irreducibleCharactersOver_iff.mpr ⟨h, ?_⟩⟩
  rw [Fintype.sum_subsingleton _ 1]
  simpa using apply_one_ne_zero_of_mem_irreducibleCharacters h

open scoped Classical in
/-- **`N = 1`** with a linear character `χ`: multiplication by `χ`, read through `G ⧸ ⊥`, maps
the irreducible characters of `G ⧸ ⊥` bijectively onto those of `G`. -/
example {χ : G → k} (hχ : χ ∈ irreducibleCharacters k G) (h1 : χ 1 = 1) :
    Set.BijOn (fun (β : G ⧸ (⊥ : Subgroup G) → k) (g : G) => χ g * β g)
      (irreducibleCharacters k (G ⧸ (⊥ : Subgroup G))) (irreducibleCharacters k G) := by
  have hθ : (fun _ => 1 : (⊥ : Subgroup G) → k) ∈ irreducibleCharacters k (⊥ : Subgroup G) := by
    rw [irreducibleCharacters_of_subsingleton]
    rfl
  have h := gallagher_bijOn hχ hθ fun n => by
    rw [Subgroup.mem_bot.mp n.property, h1]
  convert h using 1
  ext ψ
  refine ⟨fun h => mem_irreducibleCharactersOver_iff.mpr ⟨h, ?_⟩,
    fun h => (mem_irreducibleCharactersOver_iff.mp h).1⟩
  rw [Fintype.sum_subsingleton _ 1]
  simpa using apply_one_ne_zero_of_mem_irreducibleCharacters h

end TauCeti.Examples.RepresentationTheory.Gallagher
