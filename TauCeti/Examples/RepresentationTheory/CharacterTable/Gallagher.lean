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
degenerate cases `N = G` and `N = 1`, and in the explicit case `G = C₂`, `χ̂ = sgn`.

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

omit [Fintype G] in
/-- **`N = 1`** with a linear character `χ`: multiplication by `χ`, read through `G ⧸ ⊥`, maps
the irreducible characters of `G ⧸ ⊥` bijectively onto those of `G`. -/
private theorem bijOn_bot [Finite G] {χ : G → k} (hχ : χ ∈ irreducibleCharacters k G)
    (h1 : χ 1 = 1) :
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
private theorem sgn_mem_irreducibleCharacters :
    sgn k ∈ irreducibleCharacters k (Equiv.Perm (Fin 2)) := by
  rw [show sgn k = fun g => ((Units.map (Int.castRingHom k).toMonoidHom).comp Equiv.Perm.sign g : k)
    from funext fun g => by simp [sgn]]
  exact MonoidHom.coe_mem_irreducibleCharacters _

omit [IsAlgClosed k] [CharZero k] in
/-- `sgn` restricts to the trivial character of `⊥`. -/
private theorem sgn_one : sgn k 1 = 1 := by
  simp [sgn]

/-- Multiplication by `sgn` sends the trivial character to `sgn`. -/
example : (fun g => sgn k g * 1) = sgn k := by
  simp

/-- Multiplication by `sgn` sends `sgn` to the trivial character. -/
example : (fun g => sgn k g * sgn k g) = fun _ => 1 := by
  funext g
  simp only [sgn, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- So the bijection is not the identity: `sgn` is not the trivial character. -/
example : sgn k ≠ fun _ => 1 := fun h => by
  have := congrFun h (Equiv.swap 0 1)
  rw [sgn, Equiv.Perm.sign_swap (by decide)] at this
  norm_num at this

/-- The correspondence of `gallagher_bijOn` at `N = 1` with `χ̂ = sgn`. -/
example : Set.BijOn
    (fun (β : Equiv.Perm (Fin 2) ⧸ (⊥ : Subgroup (Equiv.Perm (Fin 2))) → k) g => sgn k g * β g)
    (irreducibleCharacters k (Equiv.Perm (Fin 2) ⧸ (⊥ : Subgroup (Equiv.Perm (Fin 2)))))
    (irreducibleCharacters k (Equiv.Perm (Fin 2))) :=
  bijOn_bot sgn_mem_irreducibleCharacters sgn_one

end Sign

end TauCeti.Examples.RepresentationTheory.Gallagher
