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

These examples check `TauCeti.irreducibleCharactersOver` and `TauCeti.gallagher_bijOn` in the two
degenerate cases.

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

/-- **`N = 1`**: every irreducible character of `G` lies over the trivial character of `⊥`. -/
example : irreducibleCharactersOver k (⊥ : Subgroup G) (fun _ => 1) = irreducibleCharacters k G :=
  irreducibleCharactersOver_bot one_ne_zero

/-- **`N = 1`** with a linear character `χ`: multiplication by `χ`, read through `G ⧸ ⊥`, maps
the irreducible characters of `G ⧸ ⊥` bijectively onto those of `G`. -/
example {χ : G → k} (hχ : χ ∈ irreducibleCharacters k G) (h1 : χ 1 = 1) :
    Set.BijOn (fun (β : G ⧸ (⊥ : Subgroup G) → k) (g : G) => χ g * β g)
      (irreducibleCharacters k (G ⧸ (⊥ : Subgroup G))) (irreducibleCharacters k G) := by
  have hθ : (fun _ => 1 : (⊥ : Subgroup G) → k) ∈ irreducibleCharacters k (⊥ : Subgroup G) := by
    simp
  have h := gallagher_bijOn hχ hθ fun n => by
    rw [Subgroup.mem_bot.mp n.property, h1]
  rwa [irreducibleCharactersOver_bot one_ne_zero] at h

end TauCeti.Examples.RepresentationTheory.Gallagher
