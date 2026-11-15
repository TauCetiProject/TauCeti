/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LinearCharacter.OrderTwo
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# Simple representations of point stabilizers in S₃

A point stabilizer has only two elements. Its irreducible representations over any field
are the trivial line and the restriction of the sign line. These are the source simple
modules for the induction calculations in the exact Grothendieck group of S₃.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

namespace Representation.IsIrreducible

open TauCeti

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Every simple representation of a point stabilizer in S₃ is the trivial line or the
restricted sign line. In characteristic two these possibilities coincide. -/
theorem nonempty_equiv_trivial_or_sign_stabilizer_perm_fin_three {a : Fin 3}
    {ρ : Representation k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a) V}
    (hρ : ρ.IsIrreducible) :
    Nonempty (ρ.Equiv (Representation.trivial k _ k)) ∨
      Nonempty (ρ.Equiv (Representation.ofLinearCharacter
        ((signLinearCharacter k (Fin 3)).comp
          (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype))) := by
  let t : MulAction.stabilizer (Equiv.Perm (Fin 3)) a :=
    ⟨Equiv.swap (a + 1) (a + 2), (mem_stabilizer_perm_fin_three_iff a _).mpr (Or.inr rfl)⟩
  have ht : t * t = 1 := Subtype.ext (Equiv.swap_mul_self _ _)
  have hG (g : MulAction.stabilizer (Equiv.Perm (Fin 3)) a) : g = 1 ∨ g = t :=
    ((mem_stabilizer_perm_fin_three_iff a g).mp g.property).imp
      (fun h ↦ Subtype.ext h) (fun h ↦ Subtype.ext h)
  have hne : a + 1 ≠ a + 2 := (by decide : ∀ a : Fin 3, a + 1 ≠ a + 2) a
  exact hρ.nonempty_equiv_trivial_or_ofLinearCharacter_of_forall_eq_one_or_eq t ht hG
    ((signLinearCharacter k (Fin 3)).comp
      (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype)
    (signLinearCharacter_swap hne)

end Representation.IsIrreducible
