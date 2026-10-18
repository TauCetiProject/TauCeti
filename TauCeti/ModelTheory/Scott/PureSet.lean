/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Scott.Stabilization
import Mathlib.Logic.Equiv.Fintype

/-!
# Internal stabilization of pure sets

Every structure in the empty language stabilizes internally at zero: tuples with the same
equality pattern are carried to one another by a permutation. The least internal stabilization
ordinal is therefore zero, for finite, infinite, and empty sets alike. This gives the
stabilization input for computing their internal Scott rank.

The permutation extension uses Mathlib's `Equiv.Perm.exists_extending_pair`, applied to the
finite range of a tuple rather than its possibly repeated entries.
-/

public section

universe w o

namespace TauCeti

open FirstOrder Fin

variable (M : Type w) [Language.empty.Structure M]

/-- Every pure set stabilizes internally at zero, regardless of its cardinality. -/
theorem selfStabilizesCompletely_empty :
    SelfStabilizesCompletely (L := Language.empty) M (0 : Ordinal.{o}) := by
  classical
  rw [selfStabilizesCompletely_def]
  intro n a b
  refine ⟨fun hab => ?_, fun hab => hab.mono le_self_add⟩
  have hat := BFEquiv.zero.mp hab
  let g : Set.range a → M := fun x => b (Classical.choose x.property)
  have hg (x : Set.range a) : a (Classical.choose x.property) = x :=
    Classical.choose_spec x.property
  have hg_inj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact (hg x).symm.trans (((hat.eq_iff _ _).mpr hxy).trans (hg y))
  have : Finite (Set.range a) := .of_surjective _ (Set.codRestrict_range_surjective a)
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    (Subtype.val : Set.range a → M) g Subtype.val_injective hg_inj
  have heab (i : Fin n) : e (a i) = b i := by
    rw [he ⟨a i, ⟨i, rfl⟩⟩]
    exact (hat.eq_iff _ _).mp (hg ⟨a i, ⟨i, rfl⟩⟩)
  have hext (x : M) : SameAtomicType (L := Language.empty) (snoc a x) (snoc b (e x)) := by
    have hmap : e ∘ snoc a x = snoc b (e x) := by
      funext i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simp [heab]
    rw [← hmap]
    apply (sameAtomicType_iff _ _).mpr
    exact ⟨fun i j => e.injective.eq_iff.symm, fun r => isEmptyElim r⟩
  apply (BFEquiv.add_one 0 a b).mpr
  refine ⟨hab, fun x => ⟨e x, BFEquiv.zero.mpr (hext x)⟩, fun y => ?_⟩
  exact ⟨e.symm y, BFEquiv.zero.mpr (by simpa using hext (e.symm y))⟩

/-- The least internal stabilization ordinal of a pure set is zero. -/
@[simp]
theorem selfStabilizationOrdinal_empty :
    selfStabilizationOrdinal (L := Language.empty) M = 0 :=
  le_antisymm (selfStabilizationOrdinal_le M (selfStabilizesCompletely_empty M)) bot_le

end TauCeti
