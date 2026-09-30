/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Point stabilizers in faithful primitive actions

This file records the fixed-point property that distinguishes a nonregular primitive action from
a regular one.  In a faithful primitive action, a nontrivial point stabilizer fixes only its base
point.  Equivalently, it moves every other point.

This is the local ingredient in the primitivity of the product action of a permutation wreath
product: a stabilizer element can change one coordinate of a tuple while leaving a constant tuple
fixed.

## Main results

* `TauCeti.MulAction.fixedPoints_stabilizer_eq_singleton`: a nontrivial point stabilizer in a
  faithful primitive action fixes exactly its base point.
* `TauCeti.MulAction.exists_mem_stabilizer_smul_ne`: such a stabilizer moves every other point.
-/

public section

open scoped Pointwise

namespace TauCeti.MulAction

open _root_.MulAction

variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
  [IsPreprimitive G X] [Nontrivial X]

/-- In a faithful primitive action, the fixed-point set of a nontrivial point stabilizer is the
singleton consisting of that point. -/
@[simp]
theorem fixedPoints_stabilizer_eq_singleton (a : X) (ha : stabilizer G a ≠ ⊥) :
    fixedPoints (stabilizer G a) X = {a} := by
  apply Set.Subset.antisymm
  · intro b hb
    rw [Set.mem_singleton_iff]
    by_contra hba
    have hle : stabilizer G a ≤ stabilizer G b := by
      intro g hg
      rw [mem_stabilizer_iff]
      exact hb ⟨g, hg⟩
    have heq : stabilizer G b = stabilizer G a :=
      ((IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G a).le_iff_eq
        (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G b).ne_top).mp hle
    -- The points with the same stabilizer as `a` form a block: translating a stabilizer is
    -- conjugation, so two translated stabilizer classes are either equal or disjoint.
    let B : Set X := {x | stabilizer G x = stabilizer G a}
    have hmem (g : G) (x : X) :
        x ∈ g • B ↔ stabilizer G x = stabilizer G (g • a) := by
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      -- Expose membership in the stabilizer class after transporting it by the set action.
      change stabilizer G (g⁻¹ • x) = stabilizer G a ↔
        stabilizer G x = stabilizer G (g • a)
      constructor
      · intro h
        have hmap := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
        rw [← stabilizer_smul_eq_stabilizer_map_conj g (g⁻¹ • x),
          ← stabilizer_smul_eq_stabilizer_map_conj g a] at hmap
        simpa using hmap
      · intro h
        have hmap := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) h
        rw [← stabilizer_smul_eq_stabilizer_map_conj g⁻¹ x,
          ← stabilizer_smul_eq_stabilizer_map_conj g⁻¹ (g • a)] at hmap
        simpa using hmap
    have hB : IsBlock G B := by
      rw [isBlock_iff_smul_eq_or_disjoint]
      intro g
      by_cases hg : stabilizer G (g • a) = stabilizer G a
      · left
        ext x
        rw [hmem]
        exact hg ▸ Iff.rfl
      · right
        rw [Set.disjoint_left]
        intro x hxg hx
        -- Here `hx` is membership in the stabilizer class `B`.
        change stabilizer G x = stabilizer G a at hx
        exact hg ((hmem g x).mp hxg |>.symm.trans hx)
    have hnotSubsingleton : ¬ B.Subsingleton := by
      intro h
      exact hba (h (show a ∈ B by simp [B]) (show b ∈ B by exact heq)).symm
    have hB_univ : B = Set.univ :=
      (IsPreprimitive.isTrivialBlock_of_isBlock hB).resolve_left hnotSubsingleton
    -- If that block is universal, every element stabilizing `a` fixes every point, and
    -- faithfulness forces the stabilizer to be trivial.
    apply ha
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    apply FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := X)
    intro x
    have hx : stabilizer G x = stabilizer G a := by
      have : x ∈ B := hB_univ.symm ▸ Set.mem_univ x
      exact this
    have hgx : g ∈ stabilizer G x := hx.symm ▸ hg
    simpa only [one_smul] using mem_stabilizer_iff.mp hgx
  · intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst b
    exact fun g ↦ mem_stabilizer_iff.mp g.property

/-- A nontrivial point stabilizer in a faithful primitive action moves every other point. -/
theorem exists_mem_stabilizer_smul_ne (a : X) (ha : stabilizer G a ≠ ⊥) {b : X}
    (hab : b ≠ a) : ∃ g : G, g ∈ stabilizer G a ∧ g • b ≠ b := by
  have hb : b ∉ fixedPoints (stabilizer G a) X := by
    rw [fixedPoints_stabilizer_eq_singleton a ha, Set.mem_singleton_iff]
    exact hab
  simp only [mem_fixedPoints, not_forall] at hb
  obtain ⟨g, hg⟩ := hb
  exact ⟨g, g.property, hg⟩

end TauCeti.MulAction
