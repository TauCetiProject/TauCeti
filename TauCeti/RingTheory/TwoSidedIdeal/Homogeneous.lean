/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Two-sided ideals spanned by homogeneous elements

A relation ideal of a noncommutative graded ring is presented as `TwoSidedIdeal.span` of a set of
relators, and it is homogeneous as soon as those relators are. The proof is a span induction
that runs on the componentwise absorption lemmas `Ideal.proj_mul_mem_left` and
`Ideal.proj_mul_mem_right`.

Homogeneity itself is stated through Mathlib's `Ideal.IsHomogeneous`, applied to the underlying
one-sided ideal `TwoSidedIdeal.asIdeal`, which is where the quotient by a two-sided ideal is
formed.

## Main results

* `TwoSidedIdeal.homogeneous_span`: **a two-sided ideal spanned by homogeneous elements is
  homogeneous.**

## References

Mathlib's `Ideal.homogeneous_span` is the one-sided statement that `TwoSidedIdeal.homogeneous_span`
extends from `Ideal.span` to `TwoSidedIdeal.span`.
-/

public section

variable {ι σ A : Type*}

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
