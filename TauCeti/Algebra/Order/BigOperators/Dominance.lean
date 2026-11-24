/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
public import TauCeti.Algebra.BigOperators.Finset.PartialSum
import TauCeti.Algebra.BigOperators.Fin

/-!
# The dominance order on finite vectors

A vector `a : Fin n → M` *dominates* `g` when the two have the same total and every leading
partial sum `∑_{j < k} a j` is at most that of `g`. For monotone vectors of natural numbers, `a`
is then the more spread out of the two. This is the order along which the monomials of a Hecke
ring are triangular in its diagonal double cosets.

Dominance is reflexive and transitive, and it is antisymmetric when addition is left
cancellative, since the leading partial sums determine the vector. In an ordered cancellative
monoid, adding a common vector to both sides neither creates nor destroys dominance.

Dominance compares the prefix sums `TauCeti.prefixSum` of every length. In an ordered additive
commutative group, `a` dominates `g` exactly when `g - a` is a combination `∑ᵢ cᵢ (eᵢ - eᵢ₊₁)` of
the consecutive coordinate differences with nonnegative coefficients, the coefficient `cᵢ` being
the difference of the prefix sums of length `i + 1`; for integer vectors the coefficients are
natural numbers. The differences `eᵢ - eᵢ₊₁` are the simple coroots of `GL_(n+1)`, so on its
cocharacters dominance is the coroot order (`TauCeti.GeneralLinear.dominates_iff_rootLE_flip`). On
vectors of length one, dominance is equality.

For vectors of natural numbers, `TauCeti.dominanceDefect g` sums the defects of the leading partial
sums of `g` from its total. It strictly decreases down the dominance order, so induction on it
is induction along that order.

## Main definitions

* `TauCeti.Dominates`: the dominance order on `Fin n → M`.
* `TauCeti.dominanceDefect`: a natural-number measure strictly decreasing down that order.

## Main results

* `TauCeti.Dominates.antisymm`: dominance is antisymmetric.
* `TauCeti.Dominates.add_right`, `TauCeti.Dominates.of_add_right`: dominance is compatible with
  adding a common vector.
* `TauCeti.dominates_iff_forall_prefixSum_le`: dominance compares prefix sums of every length.
* `TauCeti.dominates_iff_exists_nonneg_sub_eq_sum`, `TauCeti.dominates_iff_exists_nat_sub_eq_sum`:
  dominance is the order of nonnegative combinations of consecutive differences `eᵢ - eᵢ₊₁`.
* `TauCeti.dominates_iff_eq_fin_one`: on vectors of length one, dominance is equality.
* `TauCeti.Dominates.dominanceDefect_lt`: the defect strictly decreases down the order.
-/

public section

open Finset

namespace TauCeti

variable {M : Type*} {n : ℕ}

/-- `a` dominates `g`: the two vectors have the same total and every leading partial sum of `a`
is at most that of `g`. For monotone vectors of natural numbers, `a` is the more spread out of
the two. -/
def Dominates [AddCommMonoid M] [LE M] (a g : Fin n → M) : Prop :=
  ∑ i, g i = ∑ i, a i ∧ ∀ (k : ℕ) (hk : k ≤ n),
    ∑ j : Fin k, a (Fin.castLE hk j) ≤ ∑ j : Fin k, g (Fin.castLE hk j)

/-- The defining property of `TauCeti.Dominates`. -/
theorem dominates_def [AddCommMonoid M] [LE M] {a g : Fin n → M} :
    Dominates a g ↔ ∑ i, g i = ∑ i, a i ∧ ∀ (k : ℕ) (hk : k ≤ n),
      ∑ j : Fin k, a (Fin.castLE hk j) ≤ ∑ j : Fin k, g (Fin.castLE hk j) :=
  Iff.rfl

namespace Dominates

/-- Every vector dominates itself. -/
@[refl]
theorem refl [AddCommMonoid M] [Preorder M] (a : Fin n → M) : Dominates a a :=
  ⟨rfl, fun _ _ ↦ le_rfl⟩

/-- Dominance is transitive. -/
theorem trans [AddCommMonoid M] [Preorder M] {a g h : Fin n → M} (hag : Dominates a g)
    (hgh : Dominates g h) : Dominates a h :=
  ⟨hgh.1.trans hag.1, fun k hk ↦ (hag.2 k hk).trans (hgh.2 k hk)⟩

/-- Dominance is antisymmetric when addition is left cancellative: the leading partial sums
determine the vector. -/
theorem antisymm [AddCommMonoid M] [PartialOrder M] [IsLeftCancelAdd M] {a g : Fin n → M}
    (hag : Dominates a g) (hga : Dominates g a) : a = g :=
  Fin.eq_of_forall_sum_castLE_eq fun k hk ↦ (hag.2 k hk).antisymm (hga.2 k hk)

/-- Adding a common vector preserves dominance. -/
theorem add_right [AddCommMonoid M] [Preorder M] [AddRightMono M] {a g : Fin n → M}
    (h : Dominates a g) (f : Fin n → M) : Dominates (a + f) (g + f) := by
  refine ⟨?_, fun k hk ↦ ?_⟩
  · simp only [Pi.add_apply, sum_add_distrib, h.1]
  · simp only [Pi.add_apply, sum_add_distrib]
    gcongr ?_ + _
    exact h.2 k hk

/-- In an ordered cancellative monoid, a common summand can be cancelled from a dominance. -/
theorem of_add_right [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
    {a g f : Fin n → M} (h : Dominates (a + f) (g + f)) : Dominates a g := by
  refine ⟨?_, fun k hk ↦ ?_⟩
  · simpa only [Pi.add_apply, sum_add_distrib, add_left_inj] using h.1
  · simpa only [Pi.add_apply, sum_add_distrib, add_le_add_iff_right] using h.2 k hk

end Dominates

/-- Dominance compares the prefix sums `TauCeti.prefixSum k` of every length `k`; those of length
at least `n` are the totals. -/
theorem dominates_iff_forall_prefixSum_le [AddCommMonoid M] [LE M] {a g : Fin n → M} :
    Dominates a g ↔ ∑ i, g i = ∑ i, a i ∧ ∀ k, prefixSum k a ≤ prefixSum k g := by
  refine and_congr_right fun _ ↦ ⟨fun h k ↦ ?_, fun h k hk ↦ ?_⟩
  · rcases le_or_gt k n with hk | hk
    · simpa only [prefixSum_eq_sum_castLE hk] using h k hk
    · -- Only `LE M` is available, so the totals are compared through `h n` rather than
      -- through their equality and reflexivity.
      simpa only [prefixSum_of_le hk.le, Fin.castLE_rfl, id] using h n le_rfl
  · simpa only [prefixSum_eq_sum_castLE hk] using h k

/-- On vectors of length one, dominance is equality: only the totals are compared. -/
theorem dominates_iff_eq_fin_one [AddCommMonoid M] [Preorder M] {a g : Fin 1 → M} :
    Dominates a g ↔ a = g := by
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ h ▸ Dominates.refl a⟩
  simpa only [Fin.sum_univ_one, Fin.fin_one_eq_zero i] using h.1.symm

/-- **Dominance is the order of nonnegative combinations of consecutive differences.** In an
ordered additive commutative group, `a` dominates `g` exactly when `g - a` is a combination
`∑ᵢ cᵢ (eᵢ - eᵢ₊₁)` of the consecutive coordinate differences with nonnegative coefficients. The
coefficient `cᵢ` is the difference of the prefix sums of length `i + 1` of `g` and `a`. -/
theorem dominates_iff_exists_nonneg_sub_eq_sum [AddCommGroup M] [Preorder M]
    [IsOrderedAddMonoid M] {a g : Fin (n + 1) → M} :
    Dominates a g ↔ ∃ c : Fin n → M, 0 ≤ c ∧
      g - a = ∑ i, (Pi.single i.castSucc (c i) - Pi.single i.succ (c i)) := by
  rw [dominates_iff_forall_prefixSum_le]
  constructor
  · rintro ⟨hsum, h⟩
    refine ⟨fun i ↦ prefixSum (i + 1) (g - a), fun i ↦ ?_, eq_of_forall_prefixSum_eq fun k ↦ ?_⟩
    · simpa only [Pi.zero_apply, prefixSum_sub, sub_nonneg] using h (i + 1)
    rw [prefixSum_sum_single_castSucc_sub_single_succ]
    rcases k with _ | k
    · simp
    by_cases hk : k < n
    · rw [sum_eq_single_of_mem ⟨k, hk⟩ (by simp) fun j hj hne ↦
        (hne (Fin.ext (by simpa using hj))).elim]
    · rw [filter_false_of_mem fun j _ ↦ by have := j.isLt; omega, sum_empty,
        prefixSum_of_le (by omega : n + 1 ≤ k + 1)]
      simp only [Pi.sub_apply, sum_sub_distrib, hsum, sub_self]
  · rintro ⟨c, hc, hca⟩
    have key (k : ℕ) : prefixSum k g - prefixSum k a = ∑ i : Fin n with i.val + 1 = k, c i := by
      rw [← prefixSum_sub, hca, prefixSum_sum_single_castSucc_sub_single_succ]
    refine ⟨?_, fun k ↦ sub_nonneg.mp (key k ▸ sum_nonneg fun i _ ↦ hc i)⟩
    have htot := key (n + 1)
    rw [filter_false_of_mem fun j _ ↦ by have := j.isLt; omega, sum_empty,
      prefixSum_of_le le_rfl, prefixSum_of_le le_rfl] at htot
    exact sub_eq_zero.mp htot

/-- **Dominance of integer vectors is the order of natural combinations of consecutive
differences.** For `a g : Fin (n + 1) → ℤ`, `a` dominates `g` exactly when
`g - a = ∑ᵢ cᵢ (eᵢ - eᵢ₊₁)` with natural-number coefficients `cᵢ`. -/
theorem dominates_iff_exists_nat_sub_eq_sum {a g : Fin (n + 1) → ℤ} :
    Dominates a g ↔ ∃ c : Fin n → ℕ,
      g - a = ∑ i, c i • (Pi.single i.castSucc 1 - Pi.single i.succ 1 : Fin (n + 1) → ℤ) := by
  have hsmul (m : ℕ) (x y : Fin (n + 1)) :
      m • (Pi.single x 1 - Pi.single y 1 : Fin (n + 1) → ℤ) =
        Pi.single x (m : ℤ) - Pi.single y (m : ℤ) := by
    rw [nsmul_sub, ← Pi.single_nsmul, ← Pi.single_nsmul, nsmul_one]
  rw [dominates_iff_exists_nonneg_sub_eq_sum]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i ↦ (c i).toNat, h.trans (sum_congr rfl fun i _ ↦ ?_)⟩
    rw [hsmul, Int.toNat_of_nonneg (hc i)]
  · rintro ⟨c, h⟩
    exact ⟨fun i ↦ c i, fun i ↦ Int.natCast_nonneg (c i),
      h.trans (sum_congr rfl fun i _ ↦ hsmul _ _ _)⟩

/-- The defects of the leading partial sums of `g` from its total, summed. It strictly decreases
down the dominance order (`TauCeti.Dominates.dominanceDefect_lt`), so induction on it is
induction along that order. -/
def dominanceDefect (g : Fin n → ℕ) : ℕ :=
  ∑ k : Fin (n + 1), (∑ i, g i - ∑ j : Fin k, g (Fin.castLE (Nat.lt_succ_iff.1 k.isLt) j))

/-- The defining equation of `TauCeti.dominanceDefect`. -/
theorem dominanceDefect_def (g : Fin n → ℕ) : dominanceDefect g =
    ∑ k : Fin (n + 1), (∑ i, g i - ∑ j : Fin k, g (Fin.castLE (Nat.lt_succ_iff.1 k.isLt) j)) :=
  (rfl)

/-- **The defect strictly decreases down the dominance order.** If `a` dominates `g` and
`a ≠ g`, then `dominanceDefect g < dominanceDefect a`. -/
theorem Dominates.dominanceDefect_lt {a g : Fin n → ℕ} (h : Dominates a g) (hne : a ≠ g) :
    dominanceDefect g < dominanceDefect a := by
  -- termwise, `∑ a - (partial sum of g) ≤ ∑ a - (partial sum of a)`, as `∑ g = ∑ a`
  have key (k : ℕ) (hk : k ≤ n) :
      ∑ j : Fin k, a (Fin.castLE hk j) ≤ ∑ j : Fin k, g (Fin.castLE hk j) ∧
        ∑ j : Fin k, g (Fin.castLE hk j) ≤ ∑ i, a i :=
    ⟨h.2 k hk, h.1 ▸ Fin.sum_castLE_le_sum hk g⟩
  rw [dominanceDefect_def, dominanceDefect_def, h.1]
  refine sum_lt_sum (fun k _ ↦ Nat.sub_le_sub_left (key k _).1 _) ?_
  -- some partial sum is strict, since the partial sums determine the vector
  by_contra! hle
  refine hne (Fin.eq_of_forall_sum_castLE_eq fun k hk ↦ ?_)
  have h₁ : ∑ i, a i - ∑ j : Fin k, a (Fin.castLE hk j) ≤
      ∑ i, a i - ∑ j : Fin k, g (Fin.castLE hk j) :=
    hle ⟨k, Nat.lt_succ_of_le hk⟩ (mem_univ _)
  have := key k hk
  omega

end TauCeti
