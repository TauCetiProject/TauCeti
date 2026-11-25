/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
public import TauCeti.Algebra.BigOperators.Finset.PartialSum
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.Finset.Filter
import TauCeti.Algebra.BigOperators.Finset.Pairs

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

The pairing `⟨2ρ, ν⟩ = ∑_{i < j} (νᵢ - νⱼ)` of a vector with the sum `2ρ` of the positive roots
`eᵢ - eⱼ` (`i < j`) of `GL_n` (`TauCeti.twoRhoPairing`) is additive and has coordinates
`n - 1 - 2i`. Once the total is added back, it is a positive combination of the prefix sums
(`TauCeti.twoRhoPairing_add_nsmul_sum`), so it is strictly monotone for dominance
(`TauCeti.Dominates.twoRhoPairing_lt`).

## Main definitions

* `TauCeti.Dominates`: the dominance order on `Fin n → M`.
* `TauCeti.dominanceDefect`: a natural-number measure strictly decreasing down that order.
* `TauCeti.twoRhoPairing ν`: the pairing `⟨2ρ, ν⟩ = ∑_{i < j} (νᵢ - νⱼ)`.

## Main results

* `TauCeti.Dominates.antisymm`: dominance is antisymmetric.
* `TauCeti.Dominates.add_right`, `TauCeti.Dominates.of_add_right`: dominance is compatible with
  adding a common vector.
* `TauCeti.dominates_iff_forall_prefixSum_le`: dominance compares prefix sums of every length.
* `TauCeti.dominates_iff_exists_nonneg_sub_eq_sum`, `TauCeti.dominates_iff_exists_nat_sub_eq_sum`:
  dominance is the order of nonnegative combinations of consecutive differences `eᵢ - eᵢ₊₁`.
* `TauCeti.dominates_iff_eq_fin_one`: on vectors of length one, dominance is equality.
* `TauCeti.Dominates.dominanceDefect_lt`: the defect strictly decreases down the order.
* `TauCeti.twoRhoPairing_eq_sum_zsmul`: `⟨2ρ, ν⟩ = ∑ᵢ (n - 1 - 2i) νᵢ`.
* `TauCeti.twoRhoPairing_ite_lt`: the vector with `a` entries `m` followed by `n - a` entries `0`
  pairs to `a (n - a) m`.
* `TauCeti.Dominates.twoRhoPairing_le`, `TauCeti.Dominates.twoRhoPairing_lt`,
  `TauCeti.Dominates.twoRhoPairing_eq_iff`: monotonicity of `⟨2ρ, ·⟩` along dominance, with
  equality only for equal vectors.
* `TauCeti.sum_twoRhoPairing_eq_sum_twoRhoPairing_iff`: for a finite family of dominances, the
  sums of the pairings agree only for equal families.
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

/-! ### The pairing with `2ρ` -/

section Pairing

variable [AddCommGroup M]

/-- The pairing `⟨2ρ, ν⟩ = ∑_{i < j} (νᵢ - νⱼ)` of a vector `ν` with the sum `2ρ` of the positive
roots `eᵢ - eⱼ` (`i < j`) of `GL_n` for its upper-triangular Borel subgroup. For the Newton vector
`ν_b` of a class `b` this is the integer `d_b = ⟨2ρ, ν_b⟩`, which for Shimura varieties of PEL
type is the dimension of the central leaves in the Newton stratum of `b`. -/
def twoRhoPairing (ν : Fin n → M) : M :=
  ∑ i, ∑ j ∈ Ioi i, (ν i - ν j)

/-- The defining formula of `TauCeti.twoRhoPairing`. -/
theorem twoRhoPairing_def (ν : Fin n → M) :
    twoRhoPairing ν = ∑ i, ∑ j ∈ Ioi i, (ν i - ν j) :=
  (rfl)

/-- The zero vector pairs to `0` with `2ρ`. -/
@[simp]
theorem twoRhoPairing_zero : twoRhoPairing (0 : Fin n → M) = 0 := by
  simp [twoRhoPairing_def]

/-- The pairing with `2ρ` is additive. -/
@[simp]
theorem twoRhoPairing_add (ν ν' : Fin n → M) :
    twoRhoPairing (ν + ν') = twoRhoPairing ν + twoRhoPairing ν' := by
  simp only [twoRhoPairing_def, Pi.add_apply, add_sub_add_comm, sum_add_distrib]

/-- The pairing with `2ρ` commutes with negation. -/
@[simp]
theorem twoRhoPairing_neg (ν : Fin n → M) : twoRhoPairing (-ν) = -twoRhoPairing ν :=
  eq_neg_of_add_eq_zero_left (by rw [← twoRhoPairing_add, neg_add_cancel, twoRhoPairing_zero])

/-- The pairing with `2ρ` commutes with subtraction. -/
@[simp]
theorem twoRhoPairing_sub (ν ν' : Fin n → M) :
    twoRhoPairing (ν - ν') = twoRhoPairing ν - twoRhoPairing ν' := by
  simp only [sub_eq_add_neg, twoRhoPairing_add, twoRhoPairing_neg]

/-- The pairing with `2ρ` commutes with scalar multiplication. -/
@[simp]
theorem twoRhoPairing_smul {R : Type*} [Monoid R] [DistribMulAction R M] (c : R)
    (ν : Fin n → M) : twoRhoPairing (c • ν) = c • twoRhoPairing ν := by
  simp only [twoRhoPairing_def, Pi.smul_apply, ← smul_sub, smul_sum]

/-- **The coordinates of `2ρ`.** `⟨2ρ, ν⟩ = ∑ᵢ (n - 1 - 2i) νᵢ`. These coefficients are the
coordinates of the root-datum vector `2ρ` of the diagonal torus, computed for `GL_(n+1)` in
`TauCeti.GeneralLinear.twoWeylVector_diagonalRootBase_apply`. -/
theorem twoRhoPairing_eq_sum_zsmul (ν : Fin n → M) :
    twoRhoPairing ν = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * i) • ν i := by
  have hswap := (sum_sum_Iio_eq_sum_sum_Ioi fun i (_ : Fin n) ↦ ν i).symm
  rw [twoRhoPairing_def]
  simp only [sum_sub_distrib, hswap, sum_const, Fin.card_Ioi, Fin.card_Iio]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← natCast_zsmul, ← natCast_zsmul, ← sub_smul]
  congr 1
  have := i.isLt
  omega

/-- **`⟨2ρ, ·⟩` through prefix sums.** Once the total is added back, `⟨2ρ, ν⟩` is the sum of the
prefix sums `S_k + S_(k+1)` of `ν` over `k < n`. Each prefix sum `S_k` with `0 < k < n` occurs
twice, so a vector with the same total and larger prefix sums has a larger pairing. -/
theorem twoRhoPairing_add_nsmul_sum (ν : Fin n → M) :
    twoRhoPairing ν + n • ∑ i, ν i =
      ∑ k ∈ range n, (prefixSum k ν + prefixSum (k + 1) ν) := by
  have h₁ (i : Fin n) : #{k ∈ range n | (i : ℕ) < k} = n - 1 - i := by
    rw [show {k ∈ range n | (i : ℕ) < k} = Ioo (i : ℕ) n by ext; simp; omega, Nat.card_Ioo]
    omega
  have h₂ (i : Fin n) : #{k ∈ range n | (i : ℕ) < k + 1} = n - i := by
    rw [show {k ∈ range n | (i : ℕ) < k + 1} = Ico (i : ℕ) n by ext; simp; omega, Nat.card_Ico]
  have e₁ : ∑ k ∈ range n, prefixSum k ν = ∑ i : Fin n, (n - 1 - (i : ℕ)) • ν i := by
    simp only [prefixSum_def]
    exact (sum_sum_filter_eq_sum_card_nsmul (range n) univ ν fun i k ↦ (i : ℕ) < k).trans
      (by simp only [h₁])
  have e₂ : ∑ k ∈ range n, prefixSum (k + 1) ν = ∑ i : Fin n, (n - (i : ℕ)) • ν i := by
    simp only [prefixSum_def]
    exact (sum_sum_filter_eq_sum_card_nsmul (range n) univ ν fun i k ↦ (i : ℕ) < k + 1).trans
      (by simp only [h₂])
  rw [sum_add_distrib, e₁, e₂, twoRhoPairing_eq_sum_zsmul, smul_sum, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, ← add_smul, ← add_smul]
  congr 1
  have := i.isLt
  omega

/-- Adding a constant to every coordinate does not change `⟨2ρ, ν⟩`. -/
@[simp]
theorem twoRhoPairing_add_const (ν : Fin n → M) (c : M) :
    twoRhoPairing (fun i ↦ ν i + c) = twoRhoPairing ν := by
  simp only [twoRhoPairing_def, add_sub_add_right_eq_sub]

/-- A constant vector has `⟨2ρ, ν⟩ = 0`: central cocharacters pair trivially with every root. -/
@[simp]
theorem twoRhoPairing_const (c : M) : twoRhoPairing (fun _ : Fin n ↦ c) = 0 := by
  simp [twoRhoPairing_def]

/-- **Minuscule vectors.** The vector with `a` leading entries `m` and the remaining entries `0`
has `⟨2ρ, ν⟩ = a (n - a) m`. For `n = 2a` and `m = 1` this is `a²`, the dimension of a Shimura
variety of a unitary group of signature `(a, a)` at one infinite place. -/
theorem twoRhoPairing_ite_lt (a : ℕ) (m : M) :
    twoRhoPairing (fun i : Fin n ↦ if (i : ℕ) < a then m else 0) = (a * (n - a)) • m := by
  rcases le_or_gt a n with ha | ha
  swap
  · -- for `n < a` the vector is constant
    simp [show ∀ i : Fin n, (i : ℕ) < a from fun i ↦ i.isLt.trans ha, Nat.sub_eq_zero_of_le ha.le]
  have hrange : ∑ i : Fin n with i.val < a, ((n : ℤ) - 1 - 2 * i) =
      ∑ i ∈ range a, ((n : ℤ) - 1 - 2 * i) := by
    rw [sum_filter, Fin.sum_univ_eq_sum_range (fun i ↦ if i < a then (n : ℤ) - 1 - 2 * i else 0),
      ← sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    omega
  have hsum (b : ℕ) : ∑ i ∈ range b, ((n : ℤ) - 1 - 2 * i) = b * ((n : ℤ) - b) := by
    induction b with
    | zero => simp
    | succ b ih => rw [sum_range_succ, ih]; push_cast; ring
  rw [twoRhoPairing_eq_sum_zsmul]
  simp only [smul_ite, smul_zero]
  rw [← sum_filter, ← sum_smul, hrange, hsum, ← natCast_zsmul, Nat.cast_mul, Nat.cast_sub ha]

end Pairing

/-! ### Monotonicity of `⟨2ρ, ·⟩` along dominance -/

section Monotone

variable [AddCommGroup M] {a g : Fin n → M}

/-- **`⟨2ρ, ·⟩` is monotone for dominance.** If `a ≼ g`, that is `TauCeti.Dominates a g`: equal
totals and leading partial sums of `a` at most those of `g`, then `⟨2ρ, a⟩ ≤ ⟨2ρ, g⟩`. -/
theorem Dominates.twoRhoPairing_le [Preorder M] [IsOrderedAddMonoid M] (h : Dominates a g) :
    twoRhoPairing a ≤ twoRhoPairing g := by
  obtain ⟨htot, h'⟩ := dominates_iff_forall_prefixSum_le.mp h
  have key := twoRhoPairing_add_nsmul_sum a
  rw [← htot] at key
  rw [← add_le_add_iff_right (n • ∑ i, g i), key, twoRhoPairing_add_nsmul_sum g]
  exact sum_le_sum fun k _ ↦ add_le_add (h' k) (h' (k + 1))

variable [PartialOrder M] [IsOrderedAddMonoid M]

/-- **`⟨2ρ, ·⟩` is strictly monotone for dominance.** If `a ≼ g` (`TauCeti.Dominates a g`) and
`a ≠ g`, then `⟨2ρ, a⟩ < ⟨2ρ, g⟩`. -/
theorem Dominates.twoRhoPairing_lt (h : Dominates a g) (hne : a ≠ g) :
    twoRhoPairing a < twoRhoPairing g := by
  obtain ⟨htot, h'⟩ := dominates_iff_forall_prefixSum_le.mp h
  -- some prefix sum differs, necessarily one of length `k < n`, since longer ones are totals
  obtain ⟨k, hk⟩ : ∃ k, prefixSum k a ≠ prefixSum k g := by
    by_contra! hall
    exact hne (eq_of_forall_prefixSum_eq hall)
  have hkn : k < n := by
    by_contra! hkn
    exact hk (by rw [prefixSum_of_le hkn, prefixSum_of_le hkn, htot])
  have key := twoRhoPairing_add_nsmul_sum a
  rw [← htot] at key
  rw [← add_lt_add_iff_right (n • ∑ i, g i), key, twoRhoPairing_add_nsmul_sum g]
  exact sum_lt_sum (fun k _ ↦ add_le_add (h' k) (h' (k + 1)))
    ⟨k, mem_range.mpr hkn, add_lt_add_of_lt_of_le ((h' k).lt_of_ne hk) (h' (k + 1))⟩

/-- If `a ≼ g` (`TauCeti.Dominates a g`), then `⟨2ρ, a⟩ = ⟨2ρ, g⟩` only for `a = g`. -/
theorem Dominates.twoRhoPairing_eq_iff (h : Dominates a g) :
    twoRhoPairing a = twoRhoPairing g ↔ a = g :=
  ⟨fun heq ↦ by_contra fun hne ↦ (h.twoRhoPairing_lt hne).ne heq, fun h ↦ h ▸ rfl⟩

/-- **Families of dominances.** If `ν w ≼ μ w` (`TauCeti.Dominates (ν w) (μ w)`) for every `w` in a
finite type, then `∑_w ⟨2ρ, ν w⟩ = ∑_w ⟨2ρ, μ w⟩` only for `ν = μ`. Since each term is at most the
corresponding one (`TauCeti.Dominates.twoRhoPairing_le`), the family `μ` is then the only one on
which the sum attains its maximum. -/
theorem sum_twoRhoPairing_eq_sum_twoRhoPairing_iff {W : Type*} [Fintype W]
    {ν μ : W → Fin n → M} (h : ∀ w, Dominates (ν w) (μ w)) :
    ∑ w, twoRhoPairing (ν w) = ∑ w, twoRhoPairing (μ w) ↔ ν = μ := by
  rw [sum_eq_sum_iff_of_le fun w _ ↦ (h w).twoRhoPairing_le, funext_iff]
  exact forall_congr' fun w ↦ by rw [(h w).twoRhoPairing_eq_iff, imp_iff_right (mem_univ w)]

end Monotone

end TauCeti
