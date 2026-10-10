/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Data.Fin.Tuple.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Sign

/-!
# Weak majorization and transfer descent

For real tuples `x y : Fin n → ℝ`, the prefix sum `prefixSum k x` is the sum of the first `k`
coordinates of `x`. For antitone nonnegative tuples, `x` is *weakly majorized* by `y`
(often written `x ≺w y`) when every prefix sum of `x` is at most the corresponding prefix sum
of `y`.

A set of real tuples is *symmetric convex* when it is convex, invariant under permutations of
the coordinates, and invariant under changing the sign of one coordinate. Such a set is solid
(it contains every tuple dominated coordinatewise in absolute value by one of its members) and
closed under Robin Hood transfers, which move mass from a larger coordinate to a smaller one.
The main theorem is the *transfer descent*: a symmetric convex set containing `y` contains every
antitone nonnegative `z` whose prefix sums are bounded by those of `y`. The proof is an induction
on the length of the tuples. The last coordinate of `y` is set equal to that of `z` by one
coordinate shrink or by one Robin Hood transfer, without breaking the prefix bounds, and the
remaining coordinates are handled in the section of the set at that last value, which is again
symmetric convex.

Applied to the sublevel sets of a symmetric gauge (a seminorm invariant under permutations and
sign changes of the coordinates), the descent shows that symmetric gauges are monotone for weak
majorization. This is the convex engine behind Ky Fan dominance: once singular values are
compared by their Ky Fan sums, every symmetric gauge of them is compared at once.

## Main definitions

* `TauCeti.prefixSum k x`: the sum of the first `k` coordinates of `x : Fin n → ℝ`.
* `TauCeti.IsWeaklyMajorizedBy x y`: weak majorization of antitone nonnegative tuples.
* `TauCeti.robinHood x i j δ`: the transfer of `δ` from coordinate `i` to coordinate `j`.
* `TauCeti.IsTTransform x y`: `y` is a Robin Hood transfer of `x` followed by a permutation of
  the coordinates.
* `TauCeti.IsSymmetricConvex K`: `K` is convex, permutation invariant, and sign invariant.
* `Seminorm.IsSymmetricGauge p`: the seminorm `p` is a symmetric gauge; the sup norm is one,
  `Seminorm.isSymmetricGauge_normSeminorm`.

## Main results

* `TauCeti.IsSymmetricConvex.isSolid`: symmetric convex sets are solid.
* `TauCeti.IsSymmetricConvex.robinHood_mem`: symmetric convex sets are closed under Robin Hood
  transfers.
* `TauCeti.IsSymmetricConvex.mem_of_prefixSum_le`: transfer descent.
* `Seminorm.IsSymmetricGauge.apply_le_of_prefixSum_le`, `TauCeti.IsWeaklyMajorizedBy.apply_le`:
  symmetric gauges are monotone for weak majorization.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §II.1
  and §IV.1.
* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer (2011), §1.A and §2.B.
-/

public section

open Finset Function

namespace TauCeti

variable {n : ℕ}

/-! ### Prefix sums -/

/-- The prefix sum `∑_{i < k} x i` of the first `k` coordinates of `x`. For `n ≤ k` it is the
sum of all coordinates. -/
def prefixSum (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n with i.val < k, x i

@[simp]
theorem prefixSum_zero (x : Fin n → ℝ) : prefixSum 0 x = 0 := by
  simp [prefixSum]

theorem prefixSum_of_le {k : ℕ} (hk : n ≤ k) (x : Fin n → ℝ) : prefixSum k x = ∑ i, x i := by
  rw [prefixSum, filter_true_of_mem fun i _ ↦ i.isLt.trans_le hk]

@[simp]
theorem prefixSum_min (k : ℕ) (x : Fin n → ℝ) : prefixSum (min k n) x = prefixSum k x := by
  rcases le_total k n with hk | hk
  · rw [min_eq_left hk]
  · rw [min_eq_right hk, prefixSum_of_le le_rfl, prefixSum_of_le hk]

@[simp]
theorem prefixSum_add (k : ℕ) (x y : Fin n → ℝ) :
    prefixSum k (x + y) = prefixSum k x + prefixSum k y := by
  simp [prefixSum, sum_add_distrib]

@[simp]
theorem prefixSum_smul (k : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    prefixSum k (c • x) = c * prefixSum k x := by
  simp [prefixSum, mul_sum]

theorem prefixSum_mono (k : ℕ) {x y : Fin n → ℝ} (h : x ≤ y) : prefixSum k x ≤ prefixSum k y :=
  sum_le_sum fun i _ ↦ h i

/-- Prefix sums of length `k` only see the coordinates below `k`. -/
theorem prefixSum_congr {k : ℕ} {x y : Fin n → ℝ} (h : ∀ i : Fin n, (i : ℕ) < k → x i = y i) :
    prefixSum k x = prefixSum k y :=
  sum_congr rfl fun i hi ↦ h i (mem_filter.1 hi).2

/-- If `y` has at least the total sum of `x` and lies below `x` from coordinate `k` on, then the
prefix sum of length `k` of `x` is at most that of `y`. -/
theorem prefixSum_le_of_sum_le {k : ℕ} {x y : Fin n → ℝ} (hsum : ∑ i, x i ≤ ∑ i, y i)
    (h : ∀ i : Fin n, k ≤ (i : ℕ) → y i ≤ x i) : prefixSum k x ≤ prefixSum k y := by
  have hx := sum_filter_add_sum_filter_not univ (fun i : Fin n ↦ (i : ℕ) < k) x
  have hy := sum_filter_add_sum_filter_not univ (fun i : Fin n ↦ (i : ℕ) < k) y
  have htail : ∑ i : Fin n with ¬i.val < k, y i ≤ ∑ i : Fin n with ¬i.val < k, x i :=
    sum_le_sum fun i hi ↦ h i (not_lt.1 (mem_filter.1 hi).2)
  unfold prefixSum
  linarith

/-- Up to the length of the shorter tuple, prefix sums do not see the last coordinate. -/
theorem prefixSum_init {k : ℕ} (hk : k ≤ n) (x : Fin (n + 1) → ℝ) :
    prefixSum k (Fin.init x) = prefixSum k x := by
  simp only [prefixSum, sum_filter, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    not_lt.2 hk, ite_false, add_zero, Fin.init_def]

/-- Padding with zeros does not change prefix sums. -/
@[simp]
theorem prefixSum_append_zero {m : ℕ} (k : ℕ) (x : Fin n → ℝ) :
    prefixSum k (Fin.append x (0 : Fin m → ℝ)) = prefixSum k x := by
  simp [prefixSum, sum_filter, Fin.sum_univ_add]

/-! ### Weak majorization -/

/-- The antitone nonnegative tuple `x` is *weakly majorized* by the antitone nonnegative tuple
`y` (often written `x ≺w y`) when `prefixSum k x ≤ prefixSum k y` for every `k`. -/
structure IsWeaklyMajorizedBy (x y : Fin n → ℝ) : Prop where
  antitone_left : Antitone x
  antitone_right : Antitone y
  nonneg_left : 0 ≤ x
  nonneg_right : 0 ≤ y
  prefixSum_le : ∀ k, prefixSum k x ≤ prefixSum k y

namespace IsWeaklyMajorizedBy

variable {x y z x₁ x₂ y₁ y₂ : Fin n → ℝ}

/-- Every antitone nonnegative tuple weakly majorizes itself. -/
theorem refl (hx : Antitone x) (hx0 : 0 ≤ x) : IsWeaklyMajorizedBy x x :=
  ⟨hx, hx, hx0, hx0, fun _ ↦ le_rfl⟩

@[trans]
theorem trans (hxy : IsWeaklyMajorizedBy x y) (hyz : IsWeaklyMajorizedBy y z) :
    IsWeaklyMajorizedBy x z :=
  ⟨hxy.antitone_left, hyz.antitone_right, hxy.nonneg_left, hyz.nonneg_right,
    fun k ↦ (hxy.prefixSum_le k).trans (hyz.prefixSum_le k)⟩

theorem add (h₁ : IsWeaklyMajorizedBy x₁ y₁) (h₂ : IsWeaklyMajorizedBy x₂ y₂) :
    IsWeaklyMajorizedBy (x₁ + x₂) (y₁ + y₂) :=
  ⟨h₁.antitone_left.add h₂.antitone_left, h₁.antitone_right.add h₂.antitone_right,
    fun i ↦ add_nonneg (h₁.nonneg_left i) (h₂.nonneg_left i),
    fun i ↦ add_nonneg (h₁.nonneg_right i) (h₂.nonneg_right i),
    fun k ↦ by simpa using add_le_add (h₁.prefixSum_le k) (h₂.prefixSum_le k)⟩

theorem smul (h : IsWeaklyMajorizedBy x y) {c : ℝ} (hc : 0 ≤ c) :
    IsWeaklyMajorizedBy (c • x) (c • y) :=
  ⟨h.antitone_left.const_smul hc, h.antitone_right.const_smul hc,
    fun i ↦ mul_nonneg hc (h.nonneg_left i), fun i ↦ mul_nonneg hc (h.nonneg_right i),
    fun k ↦ by simpa using mul_le_mul_of_nonneg_left (h.prefixSum_le k) hc⟩

/-- Appending the same number of zeros to two tuples preserves weak majorization. -/
theorem append_zero (h : IsWeaklyMajorizedBy x y) (m : ℕ) :
    IsWeaklyMajorizedBy (Fin.append x (0 : Fin m → ℝ)) (Fin.append y (0 : Fin m → ℝ)) := by
  -- Padding an antitone nonnegative tuple with zeros keeps it antitone and nonnegative.
  have hpad : ∀ v : Fin n → ℝ, Antitone v → 0 ≤ v →
      Antitone (Fin.append v (0 : Fin m → ℝ)) ∧ 0 ≤ Fin.append v (0 : Fin m → ℝ) := by
    intro v hv hv0
    refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
    · induction i using Fin.addCases with
      | left i =>
        induction j using Fin.addCases with
        | left j =>
          simp only [Fin.le_def, Fin.val_castAdd] at hij
          simpa using hv (Fin.le_def.2 hij)
        | right j => simpa using hv0 i
      | right i =>
        induction j using Fin.addCases with
        | left j =>
          simp only [Fin.le_def, Fin.val_castAdd, Fin.val_natAdd] at hij
          omega
        | right j => simp
    · induction i using Fin.addCases with
      | left i => simpa using hv0 i
      | right i => simp
  obtain ⟨hx, hx0⟩ := hpad x h.antitone_left h.nonneg_left
  obtain ⟨hy, hy0⟩ := hpad y h.antitone_right h.nonneg_right
  exact ⟨hx, hy, hx0, hy0, fun k ↦ by simpa using h.prefixSum_le k⟩

end IsWeaklyMajorizedBy

/-! ### Robin Hood transfers -/

section RobinHood

variable {ι : Type*} [DecidableEq ι]

/-- The *Robin Hood transfer* of `δ` from coordinate `i` to coordinate `j` of `x`: the tuple
obtained by subtracting `δ` from `x i` and adding it to `x j`. It is an elementary step of
majorization when `0 ≤ δ ≤ x i - x j`, that is, when mass moves from a larger coordinate to a
smaller one so that both new values lie between `x j` and `x i`; the two coordinates may swap
order. -/
def robinHood (x : ι → ℝ) (i j : ι) (δ : ℝ) : ι → ℝ :=
  x - Pi.single (M := fun _ ↦ ℝ) i δ + Pi.single (M := fun _ ↦ ℝ) j δ

@[simp]
theorem robinHood_self (x : ι → ℝ) (i : ι) (δ : ℝ) : robinHood x i i δ = x := by
  simp [robinHood]

@[simp]
theorem robinHood_apply_left (x : ι → ℝ) {i j : ι} (hij : i ≠ j) (δ : ℝ) :
    robinHood x i j δ i = x i - δ := by
  simp [robinHood, hij]

@[simp]
theorem robinHood_apply_right (x : ι → ℝ) {i j : ι} (hij : i ≠ j) (δ : ℝ) :
    robinHood x i j δ j = x j + δ := by
  simp [robinHood, hij.symm]

@[simp]
theorem robinHood_apply_of_ne (x : ι → ℝ) {i j k : ι} (hi : k ≠ i) (hj : k ≠ j) (δ : ℝ) :
    robinHood x i j δ k = x k := by
  simp [robinHood, hi, hj]

/-- A Robin Hood transfer preserves the total sum. -/
@[simp]
theorem sum_robinHood [Fintype ι] (x : ι → ℝ) (i j : ι) (δ : ℝ) :
    ∑ k, robinHood x i j δ k = ∑ k, x k := by
  simp [robinHood, sum_add_distrib, sum_sub_distrib]

/-- `y` is a *T-transform* of `x`: it is obtained from `x` by one Robin Hood transfer from a
coordinate to a coordinate with no larger value, followed by a permutation of the
coordinates. -/
def IsTTransform (x y : ι → ℝ) : Prop :=
  ∃ (i j : ι) (δ : ℝ) (σ : Equiv.Perm ι),
    0 ≤ δ ∧ δ ≤ x i - x j ∧ y = robinHood x i j δ ∘ σ

/-- A T-transform preserves the total sum. -/
theorem IsTTransform.sum_eq [Fintype ι] {x y : ι → ℝ} (h : IsTTransform x y) :
    ∑ k, y k = ∑ k, x k := by
  obtain ⟨i, j, δ, σ, -, -, rfl⟩ := h
  rw [← sum_robinHood x i j δ]
  exact Equiv.sum_comp σ (robinHood x i j δ)

end RobinHood

/-! ### Symmetric convex sets -/

section SymmetricConvex

variable {ι : Type*} [DecidableEq ι]

/-- A set of real tuples is *symmetric convex* when it is convex, invariant under permutations
of the coordinates, and invariant under changing the sign of one coordinate. Sublevel sets of
symmetric gauges are the motivating examples. -/
structure IsSymmetricConvex (K : Set (ι → ℝ)) : Prop where
  convex : Convex ℝ K
  comp_perm_mem : ∀ (σ : Equiv.Perm ι), ∀ x ∈ K, x ∘ σ ∈ K
  update_neg_mem : ∀ x ∈ K, ∀ i, update x i (-x i) ∈ K

namespace IsSymmetricConvex

variable {K : Set (ι → ℝ)} {x : ι → ℝ}

/-- A coordinate of a member of a symmetric convex set may be replaced by any value of no larger
absolute value. -/
theorem update_mem (hK : IsSymmetricConvex K) (hx : x ∈ K) (i : ι) {t : ℝ}
    (ht : |t| ≤ |x i|) : update x i t ∈ K := by
  rcases eq_or_ne (x i) 0 with h0 | h0
  · rw [h0, abs_zero, abs_nonpos_iff] at ht
    rwa [ht, ← h0, update_eq_self]
  -- `update x i t` is a convex combination of `x` and of `x` with the sign of `x i` changed.
  have hr : |t / x i| ≤ 1 := by
    rw [abs_div]
    exact div_le_one_of_le₀ ht (abs_nonneg _)
  have hmem := hK.convex hx (hK.update_neg_mem x hx i)
    (a := (1 + t / x i) / 2) (b := (1 - t / x i) / 2)
    (by linarith [neg_abs_le (t / x i)]) (by linarith [le_abs_self (t / x i)]) (by ring)
  convert hmem using 1
  ext k
  rcases eq_or_ne k i with rfl | hk
  · simp only [update_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · simp only [update_of_ne hk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Symmetric convex sets are solid.** A symmetric convex set containing `x` contains every
tuple whose coordinates are bounded in absolute value by those of `x`. -/
theorem isSolid [Finite ι] (hK : IsSymmetricConvex K) :
    LatticeOrderedAddCommGroup.IsSolid K := by
  cases nonempty_fintype ι
  intro x hx w hw
  have h (i : ι) : |w i| ≤ |x i| := by simpa using hw i
  suffices ∀ s : Finset ι, s.piecewise w x ∈ K by simpa using this univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using hx
  | insert a s ha ih =>
    rw [piecewise_insert]
    exact hK.update_mem ih a (by rw [piecewise_eq_of_notMem _ _ _ ha]; exact h a)

/-- **Symmetric convex sets are closed under Robin Hood transfers.** -/
theorem robinHood_mem (hK : IsSymmetricConvex K) (hx : x ∈ K) {i j : ι} {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ' : δ ≤ x i - x j) : robinHood x i j δ ∈ K := by
  rcases eq_or_ne i j with rfl | hij
  · simpa using hx
  rcases (sub_nonneg.1 (hδ.trans hδ')).eq_or_lt with heq | hlt
  · obtain rfl : δ = 0 := le_antisymm (by linarith) hδ
    simpa [robinHood] using hx
  -- `robinHood x i j δ` is a convex combination of `x` and of `x` with `x i` and `x j` swapped.
  have hpos : 0 < x i - x j := sub_pos.2 hlt
  have hmem := hK.convex hx (hK.comp_perm_mem (Equiv.swap i j) x hx)
    (a := 1 - δ / (x i - x j)) (b := δ / (x i - x j))
    (by rw [sub_nonneg]; exact div_le_one_of_le₀ hδ' hpos.le) (div_nonneg hδ hpos.le)
    (by ring)
  convert hmem using 1
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, comp_apply]
  rcases eq_or_ne k i with rfl | hki
  · rw [robinHood_apply_left x hij, Equiv.swap_apply_left]
    field_simp
    ring
  rcases eq_or_ne k j with rfl | hkj
  · rw [robinHood_apply_right x hij, Equiv.swap_apply_right]
    field_simp
    ring
  · rw [robinHood_apply_of_ne x hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    ring

/-- Symmetric convex sets are closed under T-transforms. -/
theorem mem_of_isTTransform (hK : IsSymmetricConvex K) (hx : x ∈ K) {y : ι → ℝ}
    (h : IsTTransform x y) : y ∈ K := by
  obtain ⟨i, j, δ, σ, hδ, hδ', rfl⟩ := h
  exact hK.comp_perm_mem σ _ (hK.robinHood_mem hx hδ hδ')

/-- The section of a symmetric convex set of `(n + 1)`-tuples at a fixed value of the last
coordinate is a symmetric convex set of `n`-tuples. -/
theorem preimage_snoc {K : Set (Fin (n + 1) → ℝ)} (hK : IsSymmetricConvex K) (c : ℝ) :
    IsSymmetricConvex ((fun x : Fin n → ℝ ↦ (Fin.snoc x c : Fin (n + 1) → ℝ)) ⁻¹' K) where
  convex := by
    intro x hx y hy a b ha hb hab
    rw [Set.mem_preimage] at hx hy ⊢
    convert hK.convex hx hy ha hb hab using 1
    ext i
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    | cast i => simp
  comp_perm_mem σ := by
    induction σ using Equiv.Perm.swap_induction_on' with
    | one => simp
    | mul_swap σ a b _ ih =>
      intro x hx
      have hswap := hK.comp_perm_mem (Equiv.swap a.castSucc b.castSucc) _ (ih x hx)
      rw [Set.mem_preimage]
      convert hswap using 1
      ext i
      induction i using Fin.lastCases with
      | last =>
        simp [Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last a).symm
          (Fin.castSucc_ne_last b).symm]
      | cast i =>
        simp only [comp_apply, Fin.snoc_castSucc, Equiv.Perm.coe_mul]
        rw [← Fin.coe_castSuccEmb, Function.Embedding.swap_apply, Fin.coe_castSuccEmb,
          Fin.snoc_castSucc, comp_apply]
  update_neg_mem x hx i := by
    have := hK.update_neg_mem _ hx i.castSucc
    simp only [Fin.snoc_castSucc] at this
    rwa [Set.mem_preimage, Fin.snoc_update]

/-- The inductive step of transfer descent: a single coordinate shrink or a single Robin Hood
transfer turns a member `y` of `K` into a member whose last coordinate is that of `z`, while
keeping the prefix bounds of length at most `n`. -/
private theorem exists_mem_apply_last_eq {K : Set (Fin (n + 1) → ℝ)} (hK : IsSymmetricConvex K)
    {y z : Fin (n + 1) → ℝ} (hy : y ∈ K) (hz : Antitone z) (hz0 : 0 ≤ z)
    (h : ∀ k, prefixSum k z ≤ prefixSum k y) :
    ∃ r ∈ K, r (Fin.last n) = z (Fin.last n) ∧ ∀ k ≤ n, prefixSum k z ≤ prefixSum k r := by
  set c := z (Fin.last n)
  have hc : ∀ i, c ≤ z i := fun i ↦ hz (Fin.le_last i)
  rcases le_or_gt c (y (Fin.last n)) with hcy | hcy
  · -- Shrink the last coordinate of `y` to `c`.
    refine ⟨update y (Fin.last n) c, hK.update_mem hy _ ?_, by simp, fun k hk ↦ ?_⟩
    · rw [abs_of_nonneg (hz0 _), abs_of_nonneg ((hz0 _).trans hcy)]
      exact hcy
    · refine (h k).trans_eq (prefixSum_congr fun i hi ↦ ?_)
      rw [update_of_ne (Fin.ne_of_lt (Fin.lt_last_iff_ne_last.2 ?_))]
      exact Fin.ne_of_lt (Fin.lt_def.2 (by simpa using hi.trans_le hk))
  -- Some coordinate of `y` other than the last is at least `c`; transfer from the last such
  -- coordinate `j` to the last coordinate.
  have hex : ∃ j : Fin n, c ≤ y j.castSucc := by
    by_contra! hlt
    have htot := h (n + 1)
    rw [prefixSum_of_le le_rfl, prefixSum_of_le le_rfl, Fin.sum_univ_castSucc,
      Fin.sum_univ_castSucc] at htot
    have hsum : ∑ i : Fin n, y i.castSucc ≤ ∑ i : Fin n, z i.castSucc :=
      sum_le_sum fun i _ ↦ (hlt i).le.trans (hc _)
    linarith
  classical
  let S : Finset (Fin n) := {j | c ≤ y j.castSucc}
  have hS : S.Nonempty := let ⟨j, hj⟩ := hex; ⟨j, by simpa [S] using hj⟩
  let j := S.max' hS
  have hj : c ≤ y j.castSucc := by simpa [S] using S.max'_mem hS
  have hjmax : ∀ i : Fin n, j < i → y i.castSucc < c := fun i hi ↦ by
    by_contra! hci
    exact not_le.2 hi (S.le_max' i (by simpa [S] using hci))
  have hjl : j.castSucc ≠ Fin.last n := Fin.castSucc_ne_last j
  refine ⟨robinHood y j.castSucc (Fin.last n) (c - y (Fin.last n)),
    hK.robinHood_mem hy (by linarith) (by linarith), by simp [hjl], fun k hk ↦ ?_⟩
  rcases le_or_gt k j with hkj | hkj
  · -- Below `j` the transfer changes nothing.
    refine (h k).trans_eq (prefixSum_congr fun i hi ↦ (robinHood_apply_of_ne _ ?_ ?_ _).symm)
    · exact Fin.ne_of_lt (Fin.lt_def.2 (by simpa using hi.trans_le hkj))
    · exact Fin.ne_of_lt (Fin.lt_def.2 (by simpa using hi.trans_le (by omega)))
  · -- From `k > j` on, the transferred tuple lies below `z`, and the total sum is unchanged.
    refine prefixSum_le_of_sum_le (by simpa [prefixSum_of_le] using h (n + 1)) fun i hi ↦ ?_
    induction i using Fin.lastCases with
    | last => simpa [hjl] using hc (Fin.last n)
    | cast i =>
      have hji : j < i := Fin.lt_def.2 (by simpa using hkj.trans_le hi)
      rw [robinHood_apply_of_ne _ (Fin.castSucc_injective n |>.ne hji.ne')
        (Fin.castSucc_ne_last i)]
      exact (hjmax i hji).le.trans (hc _)

/-- **Transfer descent.** A symmetric convex set containing a tuple `y` contains every antitone
nonnegative tuple `z` whose prefix sums are bounded by those of `y`. No order or sign condition
on `y` is needed. -/
theorem mem_of_prefixSum_le {K : Set (Fin n → ℝ)} (hK : IsSymmetricConvex K) {y z : Fin n → ℝ}
    (hy : y ∈ K) (hz : Antitone z) (hz0 : 0 ≤ z) (h : ∀ k, prefixSum k z ≤ prefixSum k y) :
    z ∈ K := by
  induction n with
  | zero => rwa [Subsingleton.elim z y]
  | succ n ih =>
    obtain ⟨r, hrK, hrl, hr⟩ := exists_mem_apply_last_eq hK hy hz hz0 h
    have hinit : Fin.init z ∈
        (fun x : Fin n → ℝ ↦ (Fin.snoc x (z (Fin.last n)) : Fin (n + 1) → ℝ)) ⁻¹' K := by
      refine ih (hK.preimage_snoc _) (y := Fin.init r) ?_
        (fun a b hab ↦ hz (Fin.castSucc_le_castSucc_iff.2 hab)) (fun i ↦ hz0 _) fun k ↦ ?_
      · rwa [Set.mem_preimage, ← hrl, Fin.snoc_init_self]
      · have hk := hr (min k n) (min_le_right k n)
        rwa [← prefixSum_init (min_le_right k n) z, ← prefixSum_init (min_le_right k n) r,
          prefixSum_min, prefixSum_min] at hk
    rwa [Set.mem_preimage, Fin.snoc_init_self] at hinit

end IsSymmetricConvex

end SymmetricConvex

/-- Weak majorization descends into symmetric convex sets. -/
theorem IsWeaklyMajorizedBy.mem {K : Set (Fin n → ℝ)} {x y : Fin n → ℝ}
    (h : IsWeaklyMajorizedBy x y) (hK : IsSymmetricConvex K) (hy : y ∈ K) : x ∈ K :=
  hK.mem_of_prefixSum_le hy h.antitone_left h.nonneg_left h.prefixSum_le

end TauCeti

/-! ### Symmetric gauges -/

namespace Seminorm

open TauCeti

variable {ι : Type*} [DecidableEq ι]

/-- A seminorm `p` on real tuples is a *symmetric gauge* when it is invariant under permutations
of the coordinates and under changing the sign of one coordinate. -/
structure IsSymmetricGauge (p : Seminorm ℝ (ι → ℝ)) : Prop where
  map_comp_perm : ∀ (σ : Equiv.Perm ι) (x : ι → ℝ), p (x ∘ σ) = p x
  map_update_neg : ∀ (x : ι → ℝ) (i : ι), p (update x i (-x i)) = p x

namespace IsSymmetricGauge

variable {p : Seminorm ℝ (ι → ℝ)}

/-- The sublevel sets of a symmetric gauge are symmetric convex. -/
theorem isSymmetricConvex_setOf_le (hp : p.IsSymmetricGauge) (c : ℝ) :
    IsSymmetricConvex {x : ι → ℝ | p x ≤ c} where
  convex := by simpa using p.convexOn.convex_le c
  comp_perm_mem σ x hx := by simpa [Set.mem_ofPred_eq, hp.map_comp_perm] using hx
  update_neg_mem x hx i := by simpa [Set.mem_ofPred_eq, hp.map_update_neg] using hx

end IsSymmetricGauge

/-- The sup norm on real tuples is a symmetric gauge. -/
theorem isSymmetricGauge_normSeminorm [Fintype ι] :
    (normSeminorm ℝ (ι → ℝ)).IsSymmetricGauge where
  map_comp_perm σ x := σ.surjective.pi_norm_comp x
  map_update_neg x i := by
    simp only [coe_normSeminorm, Pi.norm_def]
    congr 2
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [update_of_ne hj]

/-- **Symmetric gauges are monotone for prefix-sum domination.** If `z` is antitone and
nonnegative and its prefix sums are bounded by those of `y`, then `p z ≤ p y`. -/
theorem IsSymmetricGauge.apply_le_of_prefixSum_le {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
    (hp : p.IsSymmetricGauge) {y z : Fin n → ℝ} (hz : Antitone z) (hz0 : 0 ≤ z)
    (h : ∀ k, prefixSum k z ≤ prefixSum k y) : p z ≤ p y :=
  (hp.isSymmetricConvex_setOf_le (p y)).mem_of_prefixSum_le (y := y) (by simp) hz hz0 h

end Seminorm

namespace TauCeti

/-- **Symmetric gauges are monotone for weak majorization.** -/
theorem IsWeaklyMajorizedBy.apply_le {n : ℕ} {x y : Fin n → ℝ} (h : IsWeaklyMajorizedBy x y)
    {p : Seminorm ℝ (Fin n → ℝ)} (hp : p.IsSymmetricGauge) : p x ≤ p y :=
  hp.apply_le_of_prefixSum_le h.antitone_left h.nonneg_left h.prefixSum_le

end TauCeti
