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

* `TauCeti.ClassData.character_eq_of_rep`: two characters agreeing at the class representatives
  of `d` are equal.
-/

public section

namespace TauCeti.ClassData

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- **Characters are determined at the class representatives** of class data `d`: characters are
class functions and every element is conjugate to some `d.rep i`. -/
theorem character_eq_of_rep (d : ClassData G) {ρ : Representation k G V}
    {ρ' : Representation k G W} (h : ∀ i, ρ.character (d.rep i) = ρ'.character (d.rep i)) :
    ρ.character = ρ'.character := by
  classical
  funext g
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (d.isConj_rep_index g)
  rw [← hτ, Representation.char_conj, Representation.char_conj, h]

end TauCeti.ClassData
