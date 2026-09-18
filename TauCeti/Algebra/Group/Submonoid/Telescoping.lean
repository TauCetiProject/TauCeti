/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Tactic.Abel

/-!
# Telescoping differences in additive submonoids

This file records criteria for differences and sums of terms in a sequence to belong to an
additive submonoid, given membership of its consecutive differences.

## Main results

* `TauCeti.sub_mem_of_consecutive_sub_mem`: a difference of two terms telescopes into an additive
  submonoid containing the intervening consecutive differences.
* `AddSubmonoid.sub_mem_of_consecutive_sub_mem_fin`: the corresponding result for a `Fin`-indexed
  family.
* `AddSubmonoid.add_mem_of_consecutive_sub_mem_fin`: a companion criterion for sums in a
  `Fin`-indexed family.
-/

public section

namespace TauCeti

variable {M : Type*} [AddCommGroup M]

/-- A difference `f a - f b` telescopes into any additive submonoid containing all the consecutive
differences `f k - f (k + 1)` for `a ≤ k < b`. -/
theorem sub_mem_of_consecutive_sub_mem (S : AddSubmonoid M) (f : ℕ → M) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ k, a ≤ k → k < b → f k - f (k + 1) ∈ S) : f a - f b ∈ S := by
  have key := Finset.sum_Ico_sub (fun k => -f k) hab
  simp only [neg_sub_neg] at key
  rw [← key]
  exact sum_mem fun k hk => h k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2

/-- A difference `v a - v b` of a `Fin`-indexed family with `a ≤ b` lies in any additive submonoid
containing the consecutive differences `v k - v (k + 1)`. -/
theorem _root_.AddSubmonoid.sub_mem_of_consecutive_sub_mem_fin {m : ℕ} (S : AddSubmonoid M)
    (v : Fin m → M)
    (hS : ∀ a b : Fin m, (a : ℕ) + 1 = b → v a - v b ∈ S) {a b : Fin m} (hab : a ≤ b) :
    v a - v b ∈ S := by
  let f : ℕ → M := fun k => if h : k < m then v ⟨k, h⟩ else 0
  have hf (c : Fin m) : f c = v c := by simp [f]
  rw [← hf a, ← hf b]
  refine sub_mem_of_consecutive_sub_mem S f hab fun k _ hkb => ?_
  have hk : k + 1 < m := by have := b.isLt; omega
  have hk0 : k < m := by omega
  simpa [f, hk, hk0] using hS ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl

/-- A sum `v a + v b` of a `Fin`-indexed family lies in any additive submonoid containing the
consecutive differences `v k - v (k + 1)` and twice the last member, since it is
`(v a - v c) + (v b - v c) + (v c + v c)` for the last index `c`. -/
theorem _root_.AddSubmonoid.add_mem_of_consecutive_sub_mem_fin {m : ℕ} (S : AddSubmonoid M)
    (v : Fin m → M)
    (hS : ∀ a b : Fin m, (a : ℕ) + 1 = b → v a - v b ∈ S)
    (hlast : ∀ c : Fin m, (c : ℕ) + 1 = m → v c + v c ∈ S) (a b : Fin m) :
    v a + v b ∈ S := by
  let c : Fin m := ⟨m - 1, by have := a.isLt; omega⟩
  have hdecomp : v a + v b = (v a - v c) + (v b - v c) + (v c + v c) := by abel
  rw [hdecomp]
  refine S.add_mem (S.add_mem ?_ ?_) (hlast c (by simp [c]; have := a.isLt; omega))
  · exact S.sub_mem_of_consecutive_sub_mem_fin v hS (Fin.le_def.2 (by simp [c]; omega))
  · exact S.sub_mem_of_consecutive_sub_mem_fin v hS (Fin.le_def.2 (by simp [c]; omega))

end TauCeti
