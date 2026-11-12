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

end TauCeti.ClassData
