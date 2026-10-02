/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
# Extending an `ℕ`-indexed grading by zero to `ℤ`

A grading indexed by the natural numbers, such as the path-length grading of a quiver algebra, is
extended to the integers by putting `⊥` in every negative degree. Integer indexing is the one in
which internal grading shifts `M{d}_p = M_{p-d}` are stated, so this is how a nonnegatively graded
module enters the signed-degree API.

## Main definitions

* `TauCeti.Graded.extendByZero`: the extension by `⊥` of an `ℕ`-indexed family to `ℤ`.

## Main results

* `TauCeti.Graded.isInternal_extendByZero`: the extension of an internal direct sum of submodules
  is still an internal direct sum.
* `TauCeti.Graded.mul_mem_extendByZero`: if multiplication adds degrees in the `ℕ`-indexed
  family, it adds signed degrees in its extension.
-/

public section

namespace TauCeti

namespace Graded

variable {α : Type*} [Bot α]

/-- The extension by zero of an `ℕ`-indexed family of graded pieces to `ℤ`: its degree-`d` piece
is `𝒜 d` in nonnegative degrees and `⊥` in negative degrees. -/
def extendByZero (𝒜 : ℕ → α) (d : ℤ) : α :=
  if 0 ≤ d then 𝒜 d.toNat else ⊥

@[simp]
theorem extendByZero_natCast (𝒜 : ℕ → α) (n : ℕ) : extendByZero 𝒜 n = 𝒜 n := by
  simp [extendByZero]

/-- The extension by zero vanishes in negative degrees. -/
theorem extendByZero_of_neg (𝒜 : ℕ → α) {d : ℤ} (hd : d < 0) : extendByZero 𝒜 d = ⊥ := by
  simp [extendByZero, not_le_of_gt hd]

/-- **The extension by zero of an internal direct sum is an internal direct sum**: its pieces in
nonnegative degrees are those of `𝒜`, and those in negative degrees vanish. -/
theorem isInternal_extendByZero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {𝒜 : ℕ → Submodule R M} (h : DirectSum.IsInternal 𝒜) :
    DirectSum.IsInternal (extendByZero 𝒜) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  obtain ⟨hind, htop⟩ := h
  refine ⟨fun d ↦ ?_, ?_⟩
  · rcases lt_or_ge d 0 with hd | hd
    · simp [extendByZero_of_neg 𝒜 hd]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
      rw [extendByZero_natCast]
      refine (hind n).mono_right (iSup₂_le fun j hj ↦ ?_)
      rcases lt_or_ge j 0 with hj0 | hj0
      · simp [extendByZero_of_neg 𝒜 hj0]
      · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
        rw [extendByZero_natCast]
        exact le_iSup₂_of_le m (fun h ↦ hj (by rw [h])) le_rfl
  · rw [eq_top_iff, ← htop]
    exact iSup_le fun n ↦ (extendByZero_natCast 𝒜 n).symm.le.trans
      (le_iSup (extendByZero 𝒜) (n : ℤ))

/-- **Multiplication adds signed degrees in the extension by zero** of an `ℕ`-indexed family in
which it adds degrees. -/
theorem mul_mem_extendByZero {R A : Type*} [Semiring R] [Semiring A] [Module R A]
    {𝒜 : ℕ → Submodule R A}
    (h𝒜 : ∀ {m n : ℕ} {x y : A}, x ∈ 𝒜 m → y ∈ 𝒜 n → x * y ∈ 𝒜 (m + n)) {m n : ℤ} {x y : A}
    (hx : x ∈ extendByZero 𝒜 m) (hy : y ∈ extendByZero 𝒜 n) :
    x * y ∈ extendByZero 𝒜 (m + n) := by
  rcases lt_or_ge m 0 with hm | hm
  · rw [extendByZero_of_neg 𝒜 hm, Submodule.mem_bot] at hx
    simp [hx]
  rcases lt_or_ge n 0 with hn | hn
  · rw [extendByZero_of_neg 𝒜 hn, Submodule.mem_bot] at hy
    simp [hy]
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [extendByZero_natCast] at hx hy
  rw [← Nat.cast_add, extendByZero_natCast]
  exact h𝒜 hx hy

end Graded

end TauCeti
