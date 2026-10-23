/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.GroupTheory.Perm.PermCongr
import TauCeti.GroupTheory.SpecificGroups.Affine.Primitive

/-!
# Jordan's theorem for a prime cycle: the bound is sharp

Jordan's theorem `TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` says that a
primitive permutation group of degree `n` containing a cycle of prime length `p`, with
`p + 3 ≤ n`, contains the alternating group. This file shows that the bound cannot be weakened to
`p ≤ n` or to `p + 1 ≤ n`. The witnesses are affine groups `AGL(1, q)` acting on `q` points: they
are primitive, too small to contain the alternating group once `q ≥ 5`, and yet contain long
cycles.

* `AGL(1, 5)` is primitive of degree `5` and contains a `5`-cycle.
* `AGL(1, 8)` is primitive of degree `8` and contains a `7`-cycle.

## Main results

* `TauCeti.not_forall_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem_of_card_support_eq`:
  Jordan's theorem fails for a cycle of prime length `p` in degree `p`.
* Jordan's theorem fails for a cycle of prime length `p` in degree `p + 1`:
`TauCeti.not_forall_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq`

## References

* H. Wielandt, *Finite Permutation Groups*, §13.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, §3.3 and §7.7.
-/

public section

open Equiv Equiv.Perm Finset MulAction

namespace TauCeti

/-- **Jordan's theorem fails in degree `p`.** A primitive permutation group of degree `n`
containing a cycle of prime length `p` need not contain the alternating group when `p = n`: the
affine group `AGL(1, 5)` is primitive on five points and contains a `5`-cycle. This shows that the
bound `p + 3 ≤ n` of `TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` cannot be
weakened to `p ≤ n`. -/
theorem not_forall_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem_of_card_support_eq :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Perm α)), IsPreprimitive G α →
      ∀ g ∈ G, g.IsCycle → (#g.support).Prime → #g.support = Nat.card α →
        alternatingGroup α ≤ G := by
  intro h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card (ZMod 5) = 5 := Nat.card_zmod 5
  obtain ⟨g, hg, hc, hs⟩ :=
    AffineGroup.exists_isCycle_mem_range_toPermHom_support_eq_univ (F := ZMod 5)
      (by rw [hcard]; exact Nat.prime_five)
  have hs' : #g.support = Nat.card (ZMod 5) := by
    rw [hs, card_univ, Nat.card_eq_fintype_card]
  refine AffineGroup.not_alternatingGroup_le_range_toPermHom (F := ZMod 5) hcard.ge
    (h _ _ ((isPreprimitive_range_toPermHom_iff _ _).2 inferInstance) g hg hc ?_ hs')
  rw [hs', hcard]
  exact Nat.prime_five

/-- **Jordan's theorem fails in degree `p + 1`.** A primitive permutation group of degree `n`
containing a cycle of prime length `p` need not contain the alternating group when `p + 1 = n`:
the affine group `AGL(1, 8)` of the field with eight elements is primitive on eight points and
contains a `7`-cycle. This shows that the bound `p + 3 ≤ n` of
`TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` cannot be weakened to
`p + 1 ≤ n`. -/
theorem not_forall_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Perm α)), IsPreprimitive G α →
      ∀ g ∈ G, g.IsCycle → (#g.support).Prime → #g.support + 1 = Nat.card α →
        alternatingGroup α ≤ G := by
  intro h
  classical
  let _ : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 3) = 8 := GaloisField.card 2 3 (by norm_num)
  obtain ⟨g, hg, hc, hs⟩ :=
    AffineGroup.exists_isCycle_mem_range_toPermHom_support_eq_compl_zero
      (F := GaloisField 2 3) (by omega)
  have hs' : #g.support = 7 := by
    rw [hs, card_compl, card_singleton, ← Nat.card_eq_fintype_card, hcard]
  refine AffineGroup.not_alternatingGroup_le_range_toPermHom (F := GaloisField 2 3) (by omega)
    (h _ _ ((isPreprimitive_range_toPermHom_iff _ _).2 inferInstance) g hg hc ?_ (by omega))
  rw [hs']
  exact Nat.prime_seven

end TauCeti
