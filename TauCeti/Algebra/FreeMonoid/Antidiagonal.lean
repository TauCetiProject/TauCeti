/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite factorizations of a word

A word of length `n` has `n + 1` factorizations into a prefix and a suffix, including the
empty prefix and empty suffix. This gives `FreeMonoid` a `Finset.HasMulAntidiagonal`
instance, allowing concatenation convolution to be expressed by finite sums.
-/

public section

namespace FreeMonoid

variable {ι : Type*}

noncomputable instance instHasMulAntidiagonal : Finset.HasMulAntidiagonal (FreeMonoid ι) where
  mulAntidiagonal w := by
    classical
    exact (Finset.range (w.toList.length + 1)).image fun k =>
      (ofList (w.toList.take k), ofList (w.toList.drop k))
  mem_mulAntidiagonal {w} {p} := by
    classical
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨k, _, rfl⟩
      exact FreeMonoid.ext (List.take_append_drop _ _)
    · intro hp
      refine ⟨p.1.toList.length, ?_, ?_⟩
      · have := congrArg (fun v : FreeMonoid ι => v.toList.length) hp
        simp only [toList_mul, List.length_append] at this
        omega
      · rw [← hp, toList_mul]
        simp

open Classical in
/-- The word factorizations are precisely the cuts between consecutive letters. -/
theorem mulAntidiagonal_eq_image_range (w : FreeMonoid ι) :
    Finset.mulAntidiagonal w = (Finset.range (w.toList.length + 1)).image
      (fun k => (ofList (w.toList.take k), ofList (w.toList.drop k))) := by
  classical
  rfl

/-- Summation over word factorizations is summation over the cut positions. -/
theorem sum_mulAntidiagonal {M : Type*} [AddCommMonoid M]
    (w : FreeMonoid ι) (f : FreeMonoid ι × FreeMonoid ι → M) :
    ∑ p ∈ Finset.mulAntidiagonal w, f p =
      ∑ k ∈ Finset.range (w.toList.length + 1),
        f (ofList (w.toList.take k), ofList (w.toList.drop k)) := by
  classical
  rw [mulAntidiagonal_eq_image_range, Finset.sum_image]
  intro i hi j hj h
  have h := congrArg (fun p : FreeMonoid ι × FreeMonoid ι => p.1.toList.length) h
  simp only [List.length_take] at h
  have hi := Finset.mem_range.mp hi
  have hj := Finset.mem_range.mp hj
  omega

end FreeMonoid
