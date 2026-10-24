/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Even

/-!
# Off-diagonal sums of symmetric and antisymmetric functions

The off-diagonal sum of `f : α → α → M` over a finite set `s` is
`∑ i ∈ s, ∑ j ∈ s.erase i, f i j`: every ordered pair of distinct elements of `s` contributes
once. When `f` is symmetric the two members of each unordered pair contribute equal terms, so the
whole sum is even; this is `Finset.even_sum_sum_erase`, proved by induction on `s`. When `f` is
antisymmetric the two contributions cancel, so the whole sum vanishes; this is
`Finset.sum_sum_erase_eq_zero`, proved by pairing each ordered pair with its transpose. If the
diagonal terms vanish too, then so does the full double sum (`Finset.sum_sum_eq_zero_of_diag`).

## Main results

* `Finset.even_sum_sum_erase`: the off-diagonal sum of a symmetric function over a finite set is
  even.
* `Finset.sum_sum_erase_eq_zero`: the off-diagonal sum of an antisymmetric function over a finite
  set vanishes.
* `Finset.sum_sum_eq_zero_of_diag`: the full double sum of an antisymmetric function vanishing on
  the diagonal vanishes.
-/

public section

namespace Finset

/-- **The off-diagonal sum of a symmetric function is even.** The ordered pairs of distinct
elements of `s` come in transposed couples contributing equal terms, so `f` need only be
symmetric on `s`. -/
theorem even_sum_sum_erase {α M : Type*} [DecidableEq α] [AddCommMonoid M] {f : α → α → M}
    (s : Finset α) (hf : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i) :
    Even (∑ i ∈ s, ∑ j ∈ s.erase i, f i j) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hstep : ∀ i ∈ s, ∑ j ∈ (insert a s).erase i, f i j = f i a + ∑ j ∈ s.erase i, f i j := by
      intro i hi
      have hai : a ≠ i := fun h ↦ ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hai,
        Finset.sum_insert (fun h ↦ ha (Finset.mem_of_mem_erase h))]
    rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.sum_congr rfl hstep,
      Finset.sum_add_distrib, ← add_assoc]
    refine Even.add ?_ (ih fun i hi j hj ↦
      hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_congr rfl fun i hi ↦
      hf i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)]
    exact ⟨_, rfl⟩

/-- **The off-diagonal sum of an antisymmetric function vanishes.** The ordered pairs of distinct
elements of `s` come in transposed couples contributing opposite terms, so `f` need only be
antisymmetric off the diagonal of `s`. -/
theorem sum_sum_erase_eq_zero {α M : Type*} [DecidableEq α] [AddCommMonoid M] {f : α → α → M}
    (s : Finset α) (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i j + f j i = 0) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, f i j = 0 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_involution (fun x _ ↦ ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_erase] at hx
    exact hf i hx.1 j hx.2.2 (Ne.symm hx.2.1)
  · rintro ⟨i, j⟩ hx _ h
    simp only [Finset.mem_sigma, Finset.mem_erase] at hx
    exact hx.2.1 (congrArg Sigma.fst h)
  · rintro ⟨i, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_erase] at hx ⊢
    exact ⟨hx.2.2, Ne.symm hx.2.1, hx.1⟩
  · rintro ⟨i, j⟩ _
    rfl

/-- **The double sum of an antisymmetric function vanishing on the diagonal vanishes.** The
diagonal terms are zero, and the off-diagonal sum vanishes by `Finset.sum_sum_erase_eq_zero`. -/
theorem sum_sum_eq_zero_of_diag {α M : Type*} [AddCommMonoid M] {f : α → α → M} (s : Finset α)
    (hdiag : ∀ i ∈ s, f i i = 0) (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i j + f j i = 0) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = 0 := by
  classical
  rw [← s.sum_sum_erase_eq_zero hf]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [← Finset.add_sum_erase s _ hi, hdiag i hi, zero_add]

end Finset
