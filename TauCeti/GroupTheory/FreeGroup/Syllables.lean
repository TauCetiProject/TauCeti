/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Normal syllable lists for free groups

`exists_isSyllableNormal` writes any free group element as a product of nonzero powers of
generators with consecutive generators distinct.
-/

@[expose] public section

namespace TauCeti.FreeGroup

open _root_.FreeGroup

variable {X : Type*}

section Syllables

/-- The product `x₁ ^ e₁ ⋯ x_k ^ e_k` of a list of syllables. -/
def syllableProd (s : List (X × ℤ)) : FreeGroup X :=
  (s.map fun a ↦ of a.1 ^ a.2).prod

/-- The empty syllable list represents the identity. -/
@[simp]
theorem syllableProd_nil : syllableProd ([] : List (X × ℤ)) = 1 := by
  simp [syllableProd]

/-- The product of a nonempty syllable list factors at its head. -/
@[simp]
theorem syllableProd_cons (a : X × ℤ) (s : List (X × ℤ)) :
    syllableProd (a :: s) = of a.1 ^ a.2 * syllableProd s := by
  simp [syllableProd]

/-- A syllable list is normal when its exponents are nonzero and consecutive generators are
distinct. -/
def IsSyllableNormal (s : List (X × ℤ)) : Prop :=
  (∀ a ∈ s, a.2 ≠ 0) ∧ s.IsChain fun a b ↦ a.1 ≠ b.1

/-- Every element of a free group is the product of a normal syllable list. -/
theorem exists_isSyllableNormal (w : FreeGroup X) :
    ∃ s, IsSyllableNormal s ∧ syllableProd s = w := by
  classical
  rw [← mk_toWord (x := w)]
  induction w.toWord with
  | nil => exact ⟨[], ⟨by simp, .nil⟩, rfl⟩
  | cons a L ih =>
    obtain ⟨x, b⟩ := a
    obtain ⟨s, ⟨hs0, hsc⟩, hs⟩ := ih
    set ε : ℤ := if b then 1 else -1 with hε
    have hε0 : ε ≠ 0 := by rw [hε]; split <;> simp
    have hmk : mk ((x, b) :: L) = of x ^ ε * mk L := by
      rw [← List.singleton_append, ← mul_mk]
      cases b <;> simp [hε, of, inv_mk, invRev]
    rw [hmk, ← hs]
    match s, hs0, hsc with
    | [], _, _ => exact ⟨[(x, ε)], ⟨by simpa using hε0, .singleton _⟩, by simp⟩
    | (y, f) :: s', hs0, hsc =>
      by_cases hyx : y = x
      · subst hyx
        by_cases hf : ε + f = 0
        · refine ⟨s', ⟨fun a ha ↦ hs0 a (List.mem_cons_of_mem _ ha), hsc.tail⟩, ?_⟩
          rw [syllableProd_cons, ← mul_assoc, ← zpow_add, hf, zpow_zero, one_mul]
        · refine ⟨(y, ε + f) :: s', ⟨?_, ?_⟩, ?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hf
            · exact hs0 a (List.mem_cons_of_mem _ ha)
          · cases s' with
            | nil => exact .singleton _
            | cons c s'' => exact .cons_cons (List.isChain_cons_cons.mp hsc).1 hsc.tail
          · simp [mul_assoc, zpow_add]
      · refine ⟨(x, ε) :: (y, f) :: s', ⟨?_, .cons_cons (Ne.symm hyx) hsc⟩, by simp⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hε0
        · exact hs0 a ha

end Syllables

end TauCeti.FreeGroup
