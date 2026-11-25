/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Gallagher
public import TauCeti.RepresentationTheory.CharacterTable.Automorphism
public import TauCeti.RepresentationTheory.LinearCharacter.Basic

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
* `N = 1`, `G = C₂` (as `Equiv.Perm (Fin 2)`) and `χ̂ = sgn`: the bijection exchanges `1` and `sgn`,
  so it is not the identity, although `χ̂` restricts to the trivial character of `1`.
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

/-! ### `G = C₂`, `χ̂ = sgn` -/

section Sign

variable (k) in
/-- The sign character of `C₂ = Equiv.Perm (Fin 2)` with values in `k`. -/
noncomputable def sgn : Equiv.Perm (Fin 2) → k :=
  fun g => ((Equiv.Perm.sign g : ℤˣ) : ℤ)

omit [IsAlgClosed k] [CharZero k] in
/-- The sign is an irreducible character: the character of the line on which `g` acts by its
sign. -/
theorem sgn_mem_irreducibleCharacters : sgn k ∈ irreducibleCharacters k (Equiv.Perm (Fin 2)) := by
  let χ : Equiv.Perm (Fin 2) →* kˣ := (Units.map (Int.castRingHom k).toMonoidHom).comp
    Equiv.Perm.sign
  have := Representation.isIrreducible_of_finrank_eq_one (Representation.ofLinearCharacter χ)
    (Module.finrank_self k)
  have h : (Representation.ofLinearCharacter χ).character = sgn k := funext fun g => by
    rw [Representation.char_ofLinearCharacter]
    rfl
  exact h ▸ character_mem_irreducibleCharacters _

omit [IsAlgClosed k] [CharZero k] in
/-- `sgn` restricts to the trivial character of `⊥`. -/
theorem sgn_one : sgn k 1 = 1 := by
  simp [sgn]

/-- Multiplication by `sgn` sends the trivial character to `sgn`. -/
example : (fun g => sgn k g * 1) = sgn k := by
  simp

/-- Multiplication by `sgn` sends `sgn` to the trivial character. -/
example : (fun g => sgn k g * sgn k g) = fun _ => 1 := by
  funext g
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> simp [sgn, h]

/-- So the bijection is not the identity: `sgn` is not the trivial character. -/
example : sgn k ≠ fun _ => 1 := fun h => by
  have := congrFun h (Equiv.swap 0 1)
  rw [sgn, Equiv.Perm.sign_swap (by decide)] at this
  norm_num at this

/-- The correspondence of `gallagher_bijOn` at `N = 1` with `χ̂ = sgn`. -/
example : Set.BijOn
    (fun (β : Equiv.Perm (Fin 2) ⧸ (⊥ : Subgroup (Equiv.Perm (Fin 2))) → k) g => sgn k g * β g)
    (irreducibleCharacters k (Equiv.Perm (Fin 2) ⧸ (⊥ : Subgroup (Equiv.Perm (Fin 2)))))
    (irreducibleCharacters k (Equiv.Perm (Fin 2))) := by
  have hθ : (fun _ => 1 : (⊥ : Subgroup (Equiv.Perm (Fin 2))) → k) ∈
      irreducibleCharacters k (⊥ : Subgroup (Equiv.Perm (Fin 2))) := by
    simp
  have h := gallagher_bijOn sgn_mem_irreducibleCharacters hθ fun n => by
    rw [Subgroup.mem_bot.mp n.property, sgn_one]
  rwa [irreducibleCharactersOver_bot one_ne_zero] at h

end Sign

end TauCeti.Examples.RepresentationTheory.Gallagher
