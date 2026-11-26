/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Gallagher
public import TauCeti.RepresentationTheory.CharacterTable.Automorphism
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter

/-!
# Checks for Gallagher's correspondence

These examples check `TauCeti.irreducibleCharactersOver` and `TauCeti.gallagher_bijOn` in the two
degenerate cases `N = G` and `N = 1`, and in the explicit case `G = C₂`, `χ̂ = sgn`.

* `N = G`: the quotient `G ⧸ G` is trivial, its only irreducible character is `1`, and the
  correspondence says that `χ` is the only irreducible character of `G` lying over its own
  restriction to `G`.
* `N = 1`: every irreducible character lies over the trivial character of the trivial subgroup,
  and for a linear character `χ` the correspondence `TauCeti.gallagher_bijOn_bot` says that
  multiplication by `χ` permutes the irreducible characters of `G`, read through `G ⧸ ⊥`.
* `N = 1`, `G = C₂` (as `Equiv.Perm (Fin 2)`) and `χ̂ = sgn` (`TauCeti.signLinearCharacter` read
  in `k`): the bijection exchanges `1` and `sgn`, so it is not the identity, although `χ̂` restricts
  to the trivial character of `1`.
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

/-! ### `G = C₂`, `χ̂ = sgn` -/

section Sign

/-- Multiplication by `sgn` sends the trivial character to `sgn`. -/
example : (fun g => (signLinearCharacter k (Fin 2) g : k) * 1) =
    fun g => (signLinearCharacter k (Fin 2) g : k) := by
  simp

/-- Multiplication by `sgn` sends `sgn` to the trivial character. -/
example : (fun g => (signLinearCharacter k (Fin 2) g : k) * signLinearCharacter k (Fin 2) g) =
    fun _ => 1 := by
  funext g
  simp [← Int.cast_mul]

/-- So the bijection is not the identity: `sgn` is not the trivial character. -/
example : (fun g => (signLinearCharacter k (Fin 2) g : k)) ≠ fun _ => 1 := fun h => by
  have := congrFun h (Equiv.swap 0 1)
  rw [signLinearCharacter_swap (by decide)] at this
  norm_num at this

/-- The correspondence of `gallagher_bijOn_bot` with `χ̂ = sgn`. -/
example : Set.BijOn
    (fun (β : Equiv.Perm (Fin 2) ⧸ (⊥ : Subgroup (Equiv.Perm (Fin 2))) → k) g =>
      (signLinearCharacter k (Fin 2) g : k) * β g)
    (irreducibleCharacters k (Equiv.Perm (Fin 2) ⧸ (⊥ : Subgroup (Equiv.Perm (Fin 2)))))
    (irreducibleCharacters k (Equiv.Perm (Fin 2))) :=
  gallagher_bijOn_bot (signLinearCharacter k (Fin 2)).coe_mem_irreducibleCharacters (by simp)

end Sign

end TauCeti.Examples.RepresentationTheory.Gallagher
