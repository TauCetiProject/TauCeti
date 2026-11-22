/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Fin
public import TauCeti.Algebra.Order.BigOperators.Dominance
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Newton vectors of `GL_n` and the admissible set `B(GL_n, μ)`

By the Dieudonné–Manin classification, an isocrystal of height `n` over an algebraically closed
field of characteristic `p` is determined up to isomorphism by its *Newton vector*: the decreasing
list `ν = (ν₀ ≥ ν₁ ≥ ⋯ ≥ νₙ₋₁)` of its rational slopes, counted with multiplicity. A slope `λ`
occurs with a multiplicity `m` such that `m λ ∈ ℤ`, since the simple isocrystal of slope `r / s` in
lowest terms has height `s`. This identifies the set `B(GL_n)` of `σ`-conjugacy classes of
`GL_n(L)` with the set of such vectors; under it, the Kottwitz invariant is the total slope.

This file develops the combinatorics of these vectors that the Newton stratification uses.

* The pairing `⟨2ρ, ν⟩ = ∑_{i < j} (νᵢ - νⱼ)` with the sum of the positive roots of `GL_n`
  (`TauCeti.twoRhoPairing`). For the Newton vector `ν_b` of a Newton stratum of a Shimura variety
  of PEL type, `d_b = ⟨2ρ, ν_b⟩` is the dimension of its central leaves.
* The order `ν ≼ ν'` on Newton vectors is the dominance order `TauCeti.Dominates ν ν'`: equal
  totals, and leading partial sums of `ν` at most those of `ν'`. The pairing with `2ρ` is
  strictly monotone for it (`TauCeti.Dominates.twoRhoPairing_lt`), because it is a positive
  combination of the prefix sums once the total is fixed
  (`TauCeti.twoRhoPairing_add_nsmul_sum`).
* For an integral cocharacter `μ`, the admissible set `B(GL_n, μ)` consists of the Newton vectors
  `ν ≼ μ`, that is `TauCeti.Dominates ν μ` (`TauCeti.admissibleNewtonVectors`). It is finite
  (`TauCeti.finite_admissibleNewtonVectors`): its slopes lie between the last and the first
  coordinates of `μ`, and have denominators dividing `n!`. When `μ` is decreasing it is itself the
  largest element of `B(GL_n, μ)`, the ordinary class, and by the strict monotonicity of
  `⟨2ρ, ·⟩` the only element on which `⟨2ρ, ·⟩` attains its maximum `⟨2ρ, μ⟩`. The same holds
  for products of general linear groups
  (`TauCeti.sum_twoRhoPairing_eq_sum_twoRhoPairing_intCast_iff`).

For instance `B(GL₂, (1, 0))` consists of the ordinary vector `(1, 0)` and the basic vector
`(1/2, 1/2)` (`TauCeti.admissibleNewtonVectors_one_zero`), with pairings `1` and `0`; the vector
`(1/2, 0)` is not a Newton vector, since the slope `1/2` would occur only once.

## Main definitions

* `TauCeti.twoRhoPairing ν`: the pairing `⟨2ρ, ν⟩ = ∑_{i < j} (νᵢ - νⱼ)`.
* `TauCeti.IsNewtonVector ν`: `ν` is decreasing and each slope `λ` of multiplicity `m` has
  `m λ ∈ ℤ`.
* `TauCeti.admissibleNewtonVectors μ`: the Newton vectors `ν ≼ μ` for an integral vector `μ`.

## Main results

* `TauCeti.twoRhoPairing_eq_sum_zsmul`: `⟨2ρ, ν⟩ = ∑ᵢ (n - 1 - 2i) νᵢ`.
* `TauCeti.twoRhoPairing_indicator`: the minuscule vector with `a` entries `m` followed by `n - a`
  entries `0` pairs to `a (n - a) m`.
* `TauCeti.Dominates.twoRhoPairing_le`, `TauCeti.Dominates.twoRhoPairing_lt`,
  `TauCeti.Dominates.twoRhoPairing_eq_iff`: monotonicity of `⟨2ρ, ·⟩` along dominance, with
  equality only for equal vectors.
* `TauCeti.IsNewtonVector.exists_int_factorial_mul_eq`: `n! νᵢ` is an integer.
* `TauCeti.finite_admissibleNewtonVectors`: `B(GL_n, μ)` is finite.
* `TauCeti.sum_twoRhoPairing_eq_sum_twoRhoPairing_intCast_iff`: in a product of general linear
  groups, the sum of the pairings with `2ρ` is maximal only at `μ`.
* `TauCeti.admissibleNewtonVectors_one_zero`: `B(GL₂, (1, 0)) = {(1, 0), (1/2, 1/2)}`.

## References

* R. E. Kottwitz, *Isocrystals with additional structure*, Compositio Math. 56 (1985), §§4–6.
* M. Rapoport and M. Richartz, *On the classification and specialization of F-isocrystals with
  additional structure*, Compositio Math. 103 (1996), §§1–2.
* A. Caraiani and P. Scholze, *On the generic part of the cohomology of compact unitary Shimura
  varieties*, Ann. of Math. 186 (2017), §3.1.
-/

public section

open Finset

namespace TauCeti

variable {M : Type*} {n : ℕ}

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

/-- A sum over `k < n` of sums over the coordinates `i` selected by a condition on `(i, k)`
counts, for each coordinate, the `k` that select it. -/
private theorem sum_range_sum_filter (ν : Fin n → M) (p : Fin n → ℕ → Prop)
    [∀ i, DecidablePred (p i)] :
    ∑ k ∈ range n, ∑ i with p i k, ν i = ∑ i, #{k ∈ range n | p i k} • ν i := by
  rw [sum_comm' (t' := univ) (s' := fun i ↦ {k ∈ range n | p i k}) (by simp)]
  simp only [sum_const]

/-- **The coordinates of `2ρ`.** `⟨2ρ, ν⟩ = ∑ᵢ (n - 1 - 2i) νᵢ`. These coefficients are the
coordinates of the root-datum vector `2ρ` of the diagonal torus, computed for `GL_(n+1)` in
`TauCeti.GeneralLinear.twoWeylVector_diagonalRootBase_apply`. -/
theorem twoRhoPairing_eq_sum_zsmul (ν : Fin n → M) :
    twoRhoPairing ν = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * i) • ν i := by
  have hswap : ∑ i : Fin n, ∑ j ∈ Ioi i, ν j = ∑ j : Fin n, ∑ _i ∈ Iio j, ν j :=
    sum_comm' (t' := univ) (s' := fun j ↦ Iio j) (by simp)
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
    exact (sum_range_sum_filter ν fun i k ↦ (i : ℕ) < k).trans (by simp only [h₁])
  have e₂ : ∑ k ∈ range n, prefixSum (k + 1) ν = ∑ i : Fin n, (n - (i : ℕ)) • ν i := by
    simp only [prefixSum_def]
    exact (sum_range_sum_filter ν fun i k ↦ (i : ℕ) < k + 1).trans (by simp only [h₂])
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
theorem twoRhoPairing_indicator (a : ℕ) (m : M) :
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
  rw [← sum_filter, ← sum_smul, hrange, hsum, ← natCast_zsmul]
  push_cast [ha]
  rfl

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

end Monotone

/-! ### Newton vectors -/

/-- `ν` is a **Newton vector**: the slope vector of an isocrystal of height `n`. Its coordinates
decrease, and each slope `λ = νᵢ`, occurring with multiplicity `m`, satisfies `m λ ∈ ℤ`. -/
structure IsNewtonVector (ν : Fin n → ℚ) : Prop where
  /-- The slopes are listed in decreasing order. -/
  antitone : Antitone ν
  /-- A slope `λ` of multiplicity `m` has `m λ ∈ ℤ`. -/
  exists_int_card_mul_eq : ∀ i, ∃ z : ℤ, (#{j | ν j = ν i} : ℚ) * ν i = z

/-- A decreasing integral vector is a Newton vector. -/
theorem isNewtonVector_intCast {μ : Fin n → ℤ} (hμ : Antitone μ) :
    IsNewtonVector fun i ↦ (μ i : ℚ) := by
  refine ⟨fun i j hij ↦ Int.cast_le.mpr (hμ hij), fun i ↦ ?_⟩
  exact ⟨#{j | (μ j : ℚ) = μ i} * μ i, by push_cast; rfl⟩

/-- A constant vector `(c, …, c)` of height `n` is a Newton vector exactly when `n c ∈ ℤ`. These
are the basic Newton vectors. -/
theorem isNewtonVector_const_iff {c : ℚ} :
    IsNewtonVector (fun _ : Fin n ↦ c) ↔ ∃ z : ℤ, n * c = z := by
  refine ⟨fun h ↦ ?_, fun ⟨z, hz⟩ ↦ ⟨fun _ _ _ ↦ le_rfl, fun _ ↦ ⟨z, by simpa using hz⟩⟩⟩
  rcases n with _ | n
  · exact ⟨0, by simp⟩
  · simpa using h.exists_int_card_mul_eq 0

/-- **Denominators of slopes.** The coordinates of a Newton vector of height `n` become integers
after multiplication by `n!`. -/
theorem IsNewtonVector.exists_int_factorial_mul_eq {ν : Fin n → ℚ} (hν : IsNewtonVector ν)
    (i : Fin n) : ∃ z : ℤ, (n.factorial : ℚ) * ν i = z := by
  obtain ⟨z, hz⟩ := hν.exists_int_card_mul_eq i
  have hpos : 0 < #{j | ν j = ν i} := card_pos.mpr ⟨i, by simp⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hpos (card_le_univ _ |>.trans (Fintype.card_fin n).le)
  exact ⟨c * z, by rw [hc]; push_cast; rw [mul_comm (#_ : ℚ), mul_assoc, hz]⟩

/-! ### The admissible set -/

/-- The **admissible set** `B(GL_n, μ)` of an integral cocharacter `μ`: the Newton vectors
`ν ≼ μ` (`TauCeti.Dominates ν μ`), that is with the same total slope as `μ` and leading partial
sums at most those of `μ`. For decreasing `μ` this is the set of Newton vectors of the
`μ`-admissible classes in `B(GL_n)`. -/
def admissibleNewtonVectors (μ : Fin n → ℤ) : Set (Fin n → ℚ) :=
  {ν | IsNewtonVector ν ∧ Dominates ν fun i ↦ (μ i : ℚ)}

/-- Membership in `B(GL_n, μ)`: a Newton vector `ν` with `ν ≼ μ`. -/
@[simp]
theorem mem_admissibleNewtonVectors {μ : Fin n → ℤ} {ν : Fin n → ℚ} :
    ν ∈ admissibleNewtonVectors μ ↔ IsNewtonVector ν ∧ Dominates ν fun i ↦ (μ i : ℚ) :=
  Iff.rfl

/-- A decreasing integral cocharacter lies in its own admissible set: it is the ordinary class. -/
theorem intCast_mem_admissibleNewtonVectors {μ : Fin n → ℤ} (hμ : Antitone μ) :
    (fun i ↦ (μ i : ℚ)) ∈ admissibleNewtonVectors μ :=
  ⟨isNewtonVector_intCast hμ, Dominates.refl _⟩

/-- The coordinates of an admissible vector lie between the last and the first coordinates of the
cocharacter. -/
private theorem mem_Icc_of_mem_admissibleNewtonVectors {μ : Fin (n + 1) → ℤ}
    {ν : Fin (n + 1) → ℚ} (hν : ν ∈ admissibleNewtonVectors μ) (i : Fin (n + 1)) :
    ν i ∈ Set.Icc (μ (Fin.last n) : ℚ) (μ 0) := by
  obtain ⟨hN, hdom⟩ := hν
  obtain ⟨htot, hpre⟩ := dominates_iff_forall_prefixSum_le.mp hdom
  -- the first coordinate is the prefix sum of length `1`, the last one the total minus the
  -- prefix sum of length `n`
  have hfirst (x : Fin (n + 1) → ℚ) : prefixSum 1 x = x 0 := by
    rw [prefixSum_succ (Nat.succ_pos n), prefixSum_zero, zero_add, Fin.mk_zero']
  have hlast (x : Fin (n + 1) → ℚ) : ∑ i, x i = prefixSum n x + x (Fin.last n) := by
    rw [← prefixSum_of_le le_rfl]
    exact prefixSum_succ (Nat.lt_succ_self n) x
  have h₁ := hpre 1
  have h₂ := hpre n
  rw [hfirst, hfirst] at h₁
  rw [hlast, hlast] at htot
  exact ⟨by linarith [hN.antitone (Fin.le_last i)], (hN.antitone (Fin.zero_le i)).trans h₁⟩

/-- **Finiteness of the admissible set.** For every integral cocharacter `μ`, the set
`B(GL_n, μ)` of Newton vectors `ν ≼ μ` is finite. -/
theorem finite_admissibleNewtonVectors (μ : Fin n → ℤ) : (admissibleNewtonVectors μ).Finite := by
  rcases n with _ | n
  · exact Set.toFinite _
  -- every coordinate is `z / (n + 1)!` for an integer `z` in a bounded interval
  have hN : (0 : ℚ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  refine (Set.Finite.pi (t := fun _ ↦ (fun z : ℤ ↦ (z : ℚ) / (n + 1).factorial) ''
    Set.Icc ((n + 1).factorial * μ (Fin.last n)) ((n + 1).factorial * μ 0))
    fun _ ↦ (Set.finite_Icc _ _).image _).subset ?_
  intro ν hν i _
  obtain ⟨z, hz⟩ := hν.1.exists_int_factorial_mul_eq i
  obtain ⟨hlo, hhi⟩ := mem_Icc_of_mem_admissibleNewtonVectors hν i
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · have : ((n + 1).factorial : ℚ) * μ (Fin.last n) ≤ z :=
      hz ▸ mul_le_mul_of_nonneg_left hlo hN.le
    exact_mod_cast this
  · have : (z : ℚ) ≤ (n + 1).factorial * μ 0 := hz ▸ mul_le_mul_of_nonneg_left hhi hN.le
    exact_mod_cast this
  · simp only [← hz, mul_div_cancel_left₀ _ hN.ne']

/-- **The ordinary class in a product of general linear groups.** Let `ν = (ν_w)_w` be a finite
family with `ν_w ∈ B(GL_n, μ_w)` for every `w`. Then `∑_w ⟨2ρ, ν_w⟩ ≤ ∑_w ⟨2ρ, μ_w⟩`, and equality
holds only for `ν_w = μ_w` for every `w`. For decreasing `μ_w` this is the ordinary class, and for
the group `∏_w GL_n` this says that the ordinary class is the only admissible class whose dimension
`d_b` attains the maximum. -/
theorem sum_twoRhoPairing_eq_sum_twoRhoPairing_intCast_iff {W : Type*} [Fintype W]
    {μ : W → Fin n → ℤ} {ν : W → Fin n → ℚ} (hν : ∀ w, ν w ∈ admissibleNewtonVectors (μ w)) :
    ∑ w, twoRhoPairing (ν w) = ∑ w, twoRhoPairing (fun i ↦ (μ w i : ℚ)) ↔
      ν = fun w i ↦ (μ w i : ℚ) := by
  rw [sum_eq_sum_iff_of_le fun w _ ↦ (hν w).2.twoRhoPairing_le, funext_iff]
  exact forall_congr' fun w ↦ by rw [(hν w).2.twoRhoPairing_eq_iff, imp_iff_right (mem_univ w)]

/-- **`B(GL₂, (1, 0))`.** The admissible set of the cocharacter `(1, 0)` of `GL₂` consists of the
ordinary vector `(1, 0)` and the basic vector `(1/2, 1/2)`. -/
theorem admissibleNewtonVectors_one_zero :
    admissibleNewtonVectors ![1, 0] = {![1, 0], ![1 / 2, 1 / 2]} := by
  -- on `GL₂`, dominance by `(1, 0)` says: total slope `1` and first slope at most `1`
  have hdom (ν : Fin 2 → ℚ) : (Dominates ν fun i ↦ ((![1, 0] : Fin 2 → ℤ) i : ℚ)) ↔
      ν 0 + ν 1 = 1 ∧ ν 0 ≤ 1 := by
    rw [dominates_def]
    refine ⟨fun ⟨htot, h⟩ ↦ ⟨by simpa [Fin.sum_univ_two, eq_comm] using htot, by simpa using h 1⟩,
      fun ⟨htot, h⟩ ↦ ⟨by simpa [Fin.sum_univ_two] using htot.symm, fun k hk ↦ ?_⟩⟩
    interval_cases k <;> simp [Fin.sum_univ_two, htot, h]
  ext ν
  simp only [mem_admissibleNewtonVectors, hdom, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, htot, h₀⟩
    have h₁₀ : ν 1 ≤ ν 0 := hN.antitone (Fin.zero_le 1)
    by_cases heq : ν 0 = ν 1
    · -- equal slopes: the basic vector
      right
      ext i
      fin_cases i <;> simp <;> linarith
    · -- distinct slopes: each occurs once, so is an integer, which forces `(1, 0)`
      left
      have hcard : #{j | ν j = ν 0} = 1 :=
        card_eq_one.mpr ⟨0, by ext j; fin_cases j <;> simp [Ne.symm heq]⟩
      obtain ⟨z, hz⟩ := hN.exists_int_card_mul_eq 0
      rw [hcard, Nat.cast_one, one_mul] at hz
      have hz₁ : z ≤ 1 := by exact_mod_cast hz ▸ h₀
      have hz₀ : 0 < z := by exact_mod_cast (show (0 : ℚ) < z by linarith)
      have hν₀ : ν 0 = 1 := by rw [hz, show z = 1 by omega, Int.cast_one]
      ext i
      fin_cases i <;> simp <;> linarith
  · rintro (rfl | rfl)
    · refine ⟨?_, by norm_num, by norm_num⟩
      have : (![1, 0] : Fin 2 → ℚ) = fun i ↦ ((![1, 0] : Fin 2 → ℤ) i : ℚ) := by
        ext i; fin_cases i <;> simp
      rw [this]
      exact isNewtonVector_intCast (by simp [antitone_vecCons])
    · refine ⟨?_, by norm_num, by norm_num⟩
      have : (![1 / 2, 1 / 2] : Fin 2 → ℚ) = fun _ ↦ 1 / 2 := by
        ext i; fin_cases i <;> simp
      rw [this, isNewtonVector_const_iff]
      exact ⟨1, by norm_num⟩

end TauCeti
