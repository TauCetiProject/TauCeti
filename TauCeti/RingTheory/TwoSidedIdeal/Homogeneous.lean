/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Two-sided ideals spanned by homogeneous elements

A relation ideal of a noncommutative graded ring is presented as `TwoSidedIdeal.span` of a set of
relators, and it is homogeneous as soon as those relators are. This file proves that, together
with the two absorption lemmas the proof runs on: if every homogeneous component of `x` lies in an
ideal, then so does every homogeneous component of `a * x`, and, when the ideal is two-sided, of
`x * a`.

Homogeneity itself is stated through Mathlib's `Ideal.IsHomogeneous`, applied to the underlying
one-sided ideal `TwoSidedIdeal.asIdeal`, which is where the quotient by a two-sided ideal is
formed.

## Main results

* `TwoSidedIdeal.homogeneous_span`: **a two-sided ideal spanned by homogeneous elements is
  homogeneous.**
* `Ideal.proj_mul_mem_left` and `Ideal.proj_mul_mem_right`: the absorption lemmas. The right one
  asks the ideal to be two-sided, through `Ideal.IsTwoSided`.

## Implementation notes

Mathlib's `Ideal.mul_homogeneous_element_mem_of_mem` supplies the homogeneous case of
`Ideal.proj_mul_mem_left`, where the homogeneous factor is on the right. Its mirror image
`Ideal.homogeneous_element_mul_mem_of_mem`, with the homogeneous factor on the left, is the one
place two-sidedness is used.

## References

Mathlib's `Ideal.homogeneous_span` is the one-sided statement that `TwoSidedIdeal.homogeneous_span`
extends from `Ideal.span` to `TwoSidedIdeal.span`, and the proof of
`Ideal.homogeneous_element_mul_mem_of_mem` is adapted from Mathlib's proof of
`Ideal.mul_homogeneous_element_mem_of_mem`, with the two factors swapped.
-/

public section

open DirectSum

variable {ι σ A : Type*}

namespace Ideal

variable [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
  [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] {I : Ideal A}

/-- **Left absorption of componentwise membership**: if every homogeneous component of `x` lies in
an ideal, so does every homogeneous component of `a * x`. -/
theorem proj_mul_mem_left {x : A} (hx : ∀ i, GradedRing.proj 𝒜 i x ∈ I) (a : A) (j : ι) :
    GradedRing.proj 𝒜 j (a * x) ∈ I := by
  classical
  rw [← sum_support_decompose 𝒜 x, Finset.mul_sum, map_sum]
  refine I.sum_mem fun l _ => mul_homogeneous_element_mem_of_mem 𝒜 a _ ⟨l, SetLike.coe_mem _⟩ ?_ j
  simpa only [GradedRing.proj_apply] using hx l

/-- The homogeneous components of `x * a`, for `x` a homogeneous element of a two-sided ideal,
lie in that ideal. This is the mirror image of `Ideal.mul_homogeneous_element_mem_of_mem`. -/
theorem homogeneous_element_mul_mem_of_mem [I.IsTwoSided] {x : A}
    (hx : SetLike.IsHomogeneousElem 𝒜 x) (hxI : x ∈ I) (a : A) (j : ι) :
    GradedRing.proj 𝒜 j (x * a) ∈ I := by
  classical
  rw [← sum_support_decompose 𝒜 a, Finset.mul_sum, map_sum]
  refine I.sum_mem fun l _ => ?_
  obtain ⟨i, hi⟩ := hx
  rw [GradedRing.proj_apply, decompose_of_mem 𝒜 (SetLike.GradedMul.mul_mem hi (SetLike.coe_mem _)),
    coe_of_apply]
  split_ifs
  · exact I.mul_mem_right _ hxI
  · exact I.zero_mem

/-- **Right absorption of componentwise membership**: if every homogeneous component of `x` lies in
a two-sided ideal, so does every homogeneous component of `x * a`. -/
theorem proj_mul_mem_right [I.IsTwoSided] {x : A} (hx : ∀ i, GradedRing.proj 𝒜 i x ∈ I) (a : A)
    (j : ι) : GradedRing.proj 𝒜 j (x * a) ∈ I := by
  classical
  rw [← sum_support_decompose 𝒜 x, Finset.sum_mul, map_sum]
  refine I.sum_mem fun l _ => homogeneous_element_mul_mem_of_mem 𝒜 ⟨l, SetLike.coe_mem _⟩ ?_ a j
  simpa only [GradedRing.proj_apply] using hx l

end Ideal

namespace TwoSidedIdeal

variable [Ring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
  [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]

/-- **A two-sided ideal spanned by homogeneous elements is homogeneous.** This supplies the
homogeneity condition needed to descend a grading to a relation quotient. -/
theorem homogeneous_span {s : Set A} (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) :
    (span s).asIdeal.IsHomogeneous 𝒜 := by
  suffices h : ∀ x ∈ span s, ∀ i, GradedRing.proj 𝒜 i x ∈ (span s).asIdeal from
    fun i x hx => by simpa only [GradedRing.proj_apply] using h x (mem_asIdeal.1 hx) i
  intro x hx
  induction hx using span_induction with
  | mem y hy =>
    intro i
    simpa only [one_mul] using Ideal.mul_homogeneous_element_mem_of_mem 𝒜 1 y (hs y hy)
      (mem_asIdeal.2 (subset_span hy)) i
  | zero => intro i; rw [map_zero]; exact Ideal.zero_mem _
  | add y z _ _ ihy ihz => intro i; rw [map_add]; exact Ideal.add_mem _ (ihy i) (ihz i)
  | neg y _ ihy => intro i; rw [map_neg]; exact (Ideal.neg_mem_iff _).2 (ihy i)
  | left_absorb a y _ ihy => exact Ideal.proj_mul_mem_left 𝒜 ihy a
  | right_absorb b y _ ihy => exact Ideal.proj_mul_mem_right 𝒜 ihy b

end TwoSidedIdeal
