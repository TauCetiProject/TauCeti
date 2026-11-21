/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Characters at the class representatives

Characters are class functions, and class data `d : TauCeti.ClassData G` lists one representative
`d.rep i` of every conjugacy class. So two characters of `G` agree as soon as they agree at the
representatives `d.rep i`: an identity of characters reduces to finitely many checks, one per
numbered class.

## Main results

* `TauCeti.ClassData.character_rep_index`: a character takes at each element its value at the
  representative of the class of that element.
* `TauCeti.ClassData.character_eq_of_rep`: two characters agreeing at the class representatives
  of `d` are equal.
* `TauCeti.ClassData.finrank_intertwiningMap_of_character_rep`: in characteristic zero, the
  dimension of the space of intertwiners between two representations whose characters take
  integer values at the class representatives is the pairing of those values.
-/

public section

namespace TauCeti.ClassData

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- A character takes at each element `g` its value at the representative `d.rep (d.index g)`
of the class of `g`, since characters are class functions. -/
theorem character_rep_index [DecidableRel (IsConj : G → G → Prop)] (d : ClassData G)
    (ρ : Representation k G V) (g : G) :
    ρ.character (d.rep (d.index g)) = ρ.character g := by
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (d.isConj_rep_index g)
  conv_rhs => rw [← hτ]
  rw [Representation.char_conj]

/-- **Characters are determined at the class representatives** of class data `d`: characters are
class functions and every element is conjugate to some `d.rep i`. -/
theorem character_eq_of_rep (d : ClassData G) {ρ : Representation k G V}
    {ρ' : Representation k G W} (h : ∀ i, ρ.character (d.rep i) = ρ'.character (d.rep i)) :
    ρ.character = ρ'.character := by
  classical
  funext g
  rw [← d.character_rep_index ρ, ← d.character_rep_index ρ', h]

/-- **Hom-dimensions from the characters at the class representatives**: in characteristic zero,
if the characters of `ρ` and `σ` take the integer values `a` and `b` at the class representatives
of `d`, the space of intertwiners from `ρ` to `σ` has dimension `n` as soon as the pairing
`∑_g b(g) a(g⁻¹)` of these values over `G` is `|G| n`. -/
theorem finrank_intertwiningMap_of_character_rep [CharZero k] [Fintype G]
    [DecidableRel (IsConj : G → G → Prop)] [FiniteDimensional k V] [FiniteDimensional k W]
    (d : ClassData G) {ρ : Representation k G V} {σ : Representation k G W}
    (a b : Fin d.numClasses → ℤ) (n : ℕ) (hρ : ∀ j, ρ.character (d.rep j) = a j)
    (hσ : ∀ j, σ.character (d.rep j) = b j)
    (hab : ∑ g : G, b (d.index g) * a (d.index g⁻¹) = Fintype.card G * n) :
    Module.finrank k (ρ.IntertwiningMap σ) = n := by
  have hρ' (g : G) := (d.character_rep_index ρ g).symm.trans (hρ _)
  have hσ' (g : G) := (d.character_rep_index σ g).symm.trans (hσ _)
  let : Invertible (Nat.card G : k) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero)
  apply Nat.cast_injective (R := k)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp_rw [hσ', hρ', ← Int.cast_mul]
  rw [← Int.cast_sum, hab, Nat.card_eq_fintype_card]
  push_cast
  rw [inv_mul_cancel_left₀ (by exact_mod_cast Fintype.card_ne_zero)]

end TauCeti.ClassData
