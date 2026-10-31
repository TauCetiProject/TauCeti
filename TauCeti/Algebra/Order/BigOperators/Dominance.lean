/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
