/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Fintype.BigOperators
import TauCeti.Data.Finsupp.Order

/-!
# Degree allocation for disjoint theta couplings

A coupling monomial consumes `q` degrees at its source and one degree at its partner.
When the couplings form a matching with disjoint source and partner sets, the available
multidegree bounds each multiplicity independently. For a near pair of long places both
available degrees lie between `b` and `2b`, so the source alone limits the multiplicity
of a coupling with exponent `q = p^e ≥ 2`.

The near-pair allocation is from `New.Data.powerDegree_add_partnerDegree_le_of_isNearPair` in
`grh/src/New/Derivatives/Sharpness/Cases.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

namespace TauCeti

/-- For disjoint couplings the total multidegree fits exactly when each multiplicity
fits both its source and its partner. The costs `q i` count degrees at the source. -/
theorem sum_couplingDegrees_le_iff {ι σ : Type*} [Fintype ι] (src dst : ι ↪ σ)
    (hdisj : Disjoint (Set.range src) (Set.range dst)) (q j : ι → ℕ) (l : σ →₀ ℕ) :
    (∑ i, (Finsupp.single (src i) (q i * j i) + Finsupp.single (dst i) (j i))) ≤ l ↔
      ∀ i, q i * j i ≤ l (src i) ∧ j i ≤ l (dst i) := by
  have hinj : (Sum.elim src dst).Injective :=
    src.injective.sumElim dst.injective fun i k h ↦
      Set.disjoint_left.mp hdisj ⟨i, rfl⟩ ⟨k, h.symm⟩
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib,
    Sum.forall, forall_and] using
    Finsupp.sum_single_le_iff_of_injective hinj (Sum.elim (fun i ↦ q i * j i) j)
      (l := l) (fun _ ↦ Nat.zero_le _)

/-- For disjoint near pairs, use each coupling `z_src^q * z_dst` as many times as
its source degree permits. The partner has room for all of those copies: the source
degree is at most `2b`, the partner degree at least `b`, and `q` is at least two. -/
theorem sum_couplingDegrees_le_of_bounds {ι σ : Type*} [Fintype ι] (src dst : ι ↪ σ)
    (hdisj : Disjoint (Set.range src) (Set.range dst)) (q : ι → ℕ) (hq : ∀ i, 2 ≤ q i)
    (l : σ →₀ ℕ) {b : ℕ} (hsrc : ∀ i, l (src i) ≤ 2 * b) (hdst : ∀ i, b ≤ l (dst i)) :
    (∑ i, (Finsupp.single (src i) (q i * (l (src i) / q i)) +
      Finsupp.single (dst i) (l (src i) / q i))) ≤ l := by
  refine (sum_couplingDegrees_le_iff src dst hdisj _ _ l).2 fun i ↦ ⟨Nat.mul_div_le _ _, ?_⟩
  exact Nat.div_le_of_le_mul ((hsrc i).trans (Nat.mul_le_mul (hq i) (hdst i)))

end TauCeti
