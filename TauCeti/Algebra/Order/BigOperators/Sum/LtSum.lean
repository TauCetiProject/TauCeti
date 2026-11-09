/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Comparing two sums when one index set dominates the other

Two finite sets of the same size, one of which carries a strictly larger weight at every point
than the other carries at any of its points, have strictly ordered sums
(`TauCeti.sum_lt_sum_of_forall_lt`). The two sets may be indexed by different types and weighted
by different functions; the sizes agreeing is what makes the comparison work without any pointwise
pairing of the two sets, since any bijection between them compares the weights termwise.

`TauCeti.sum_lt_sum_image_sdiff` is the form in which the comparison is used. A map `σ` that
permutes a finite set `X` but does not map a part `A` of it to itself must move some point of `A`
out of `A`; if `A` carries the larger weights, the image of the complementary part `X \ A`
therefore weighs strictly more than `X \ A` itself.

The weights take values in an additive commutative monoid preordered so that addition is strictly
monotone. This is weaker than the ordered cancellative monoids of Mathlib's
`Finset.sum_lt_sum_of_nonempty` and `Finset.sum_sdiff_lt_sum_sdiff`, and it suffices both to
compare two sums of the same length termwise and to compare two sums through the parts on which
they differ.
-/

public section

namespace TauCeti

variable {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftStrictMono M]

/-- **A set whose weights are all smaller than those of a second set of the same size has the
smaller sum.** If `s` is nonempty, `t` has as many elements as `s`, and every value of `g` on `t`
is smaller than every value of `f` on `s`, then the sum of `g` over `t` is smaller than the sum of
`f` over `s`. -/
theorem sum_lt_sum_of_forall_lt {ι κ : Type*} (f : ι → M) (g : κ → M) {s : Finset ι}
    {t : Finset κ} (hcard : t.card = s.card) (hs : s.Nonempty)
    (hlt : ∀ i ∈ s, ∀ j ∈ t, g j < f i) :
    ∑ j ∈ t, g j < ∑ i ∈ s, f i := by
  classical
  induction hs using Finset.Nonempty.cons_induction generalizing t with
  | singleton i =>
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (by simpa using hcard)
    simpa using hlt i (by simp) j (by simp)
  | cons i s hi _ ih =>
    -- pair `i` off against any element `j` of `t`, and compare the two remaining sums
    obtain ⟨j, hj⟩ : t.Nonempty := Finset.card_pos.mp (by simp [hcard])
    rw [← Finset.add_sum_erase _ _ hj, Finset.sum_cons]
    exact add_lt_add (hlt i (by simp) j hj)
      (ih (by simp [Finset.card_erase_of_mem hj, hcard, hi]) fun a ha b hb =>
        hlt a (by simp [ha]) b (Finset.mem_of_mem_erase hb))

/-- **A map permuting a set but not a prescribed part of it increases the sum over the other
part.** If every weight of `A ⊆ X` exceeds every weight of `X \ A`, and `σ` maps `X` onto itself
without mapping `A` onto itself, then the image of `X \ A` under `σ` has the larger sum. -/
theorem sum_lt_sum_image_sdiff {α : Type*} [DecidableEq α] (f : α → M) {X A : Finset α}
    {σ : α → α} (hAX : A ⊆ X) (hXimg : X.image σ = X) (himg : A.image σ ≠ A)
    (hlt : ∀ a ∈ A, ∀ b ∈ X \ A, f b < f a) :
    ∑ z ∈ X \ A, f z < ∑ z ∈ (X \ A).image σ, f z := by
  have hinj : Set.InjOn σ X := Finset.card_image_iff.mp (by rw [hXimg])
  have hσAX : A.image σ ⊆ X := hXimg ▸ Finset.image_subset_image hAX
  have hcard : (A.image σ).card = A.card := Finset.card_image_of_injOn (hinj.mono hAX)
  -- the image of `X \ A` is `X \ σ(A)`; it differs from `X \ A` by trading `σ(A) \ A`, which
  -- lies in `X \ A`, for `A \ σ(A)`, which lies in `A`
  rw [Finset.image_sdiff_of_injOn hinj hAX, hXimg]
  have hlt' :
      ∑ z ∈ (X \ A) \ (X \ A.image σ), f z < ∑ z ∈ (X \ A.image σ) \ (X \ A), f z := by
    rw [sdiff_sdiff_sdiff_cancel_left hσAX, sdiff_sdiff_sdiff_cancel_left hAX]
    exact sum_lt_sum_of_forall_lt f f (Finset.card_sdiff_comm hcard)
      (Finset.sdiff_nonempty.mpr fun h => himg (Finset.eq_of_subset_of_card_le h hcard.le).symm)
      fun a ha b hb =>
        hlt a (Finset.mem_sdiff.mp ha).1 b (Finset.sdiff_subset_sdiff hσAX le_rfl hb)
  -- the two sums agree on the common part, so comparing the differences compares them
  rw [← Finset.sum_sdiff (Finset.inter_subset_left (s₁ := X \ A) (s₂ := X \ A.image σ)),
    ← Finset.sum_sdiff (Finset.inter_subset_right (s₁ := X \ A) (s₂ := X \ A.image σ)),
    Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right]
  exact add_lt_add_left hlt' _

end TauCeti
