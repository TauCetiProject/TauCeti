/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.MulAction
public import TauCeti.Analysis.SpecialFunctions.Log.Base

/-!
# Rounding norms up to the powers of a constant

Fix `0 < c < 1`. Every real number `x` has a least upper bound in the discrete set
`c ^ ℤ ∪ {0}`: for `x > 0` it is the unique power `c ^ n` with `c ^ (n + 1) < x ≤ c ^ n`, and
for `x ≤ 0` it is `0`. We call this value `TauCeti.zpowCeil c x`. It is monotone, it lies within
the factor `c` of `x` (`x ≤ zpowCeil c x` and `c * zpowCeil c x < x` for `x > 0`), it commutes
with multiplication by powers of `c`, and it is submultiplicative on nonnegative numbers.

Applied to the norm of an ultrametric seminormed group `M`, rounding produces a new ultrametric
seminorm `TauCeti.zpowCeilAddGroupSeminorm` with values in `c ^ ℤ ∪ {0}`. It is
bounded-equivalent to the original norm, `c * zpowCeil c ‖m‖ ≤ ‖m‖ ≤ zpowCeil c ‖m‖`, and it
vanishes exactly where the norm does. For a contractive scalar action of a
seminormed ring `R`, rounding gives `zpowCeil c ‖a • m‖ ≤ zpowCeil c ‖a‖ * zpowCeil c ‖m‖`.
Thus the rounded norm is again a contractive module norm when the norm of `R` already takes
values in `c ^ ℤ ∪ {0}`, and in general it still scales exactly under every scalar `a` with
`‖a • m‖ = c ^ n * ‖m‖`, such as a multiplicative pseudo-uniformiser of norm `c`.

Rounding is the standard device for replacing a Banach module over a discretely valued ring by
one whose norm takes values in the value group of the ring. Strict inequalities against powers
of `c` then become non-strict ones (`zpowCeil_lt_zpow_iff`), which is what makes the open unit
ball of the rounded norm a principal multiple of the closed unit ball. This is the input to
Serre's reduction of orthonormalisability to freeness of a residue module.

## Main definitions

* `TauCeti.zpowCeil c x`: the least element of `c ^ ℤ ∪ {0}` that is at least `x`.
* `TauCeti.zpowCeilAddGroupSeminorm hc₀ hc₁ M`: the norm of an ultrametric seminormed group
  rounded up to `c ^ ℤ ∪ {0}`.
* `TauCeti.zpowCeilAddGroupNorm hc₀ hc₁ M`: the same construction on a normed group, as a norm.

## Main results

* `TauCeti.zpowCeil_le_iff`: `zpowCeil c x ≤ y ↔ x ≤ y` whenever `y` lies in `c ^ ℤ ∪ {0}`.
* `TauCeti.zpowCeil_eq_zpow_iff`: `zpowCeil c x = c ^ n ↔ c ^ (n + 1) < x ∧ x ≤ c ^ n`.
* `TauCeti.le_zpowCeil` and `TauCeti.mul_zpowCeil_lt`: `x ≤ zpowCeil c x` and, for `x > 0`,
  `c * zpowCeil c x < x`.
* `TauCeti.zpowCeil_zpow_mul`: `zpowCeil c (c ^ n * x) = c ^ n * zpowCeil c x`.
* `TauCeti.zpowCeil_norm_smul_le`: rounding is compatible with contractive scalar actions.
* `TauCeti.isNonarchimedean_zpowCeilAddGroupSeminorm`: the rounded seminorm is ultrametric.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §1.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Real

namespace TauCeti

/-- The least element of `c ^ ℤ ∪ {0}` that is at least `x`, for `0 < c < 1`: the power
`c ^ n` with `c ^ (n + 1) < x ≤ c ^ n` when `x > 0`, and `0` when `x ≤ 0`. -/
noncomputable def zpowCeil (c x : ℝ) : ℝ :=
  if 0 < x then c ^ ⌊logb c x⌋ else 0

variable {c x y : ℝ}

/-- A positive number is rounded to `c ^ ⌊logb c x⌋`. -/
theorem zpowCeil_of_pos (hx : 0 < x) : zpowCeil c x = c ^ ⌊logb c x⌋ := by
  simp [zpowCeil, hx]

/-- A nonpositive number is rounded to `0`. -/
theorem zpowCeil_of_nonpos (hx : x ≤ 0) : zpowCeil c x = 0 := by
  simp [zpowCeil, hx.not_gt]

/-- Zero is rounded to `0`. -/
@[simp]
theorem zpowCeil_zero : zpowCeil c 0 = 0 := zpowCeil_of_nonpos le_rfl

/-- Rounded values are nonnegative. -/
theorem zpowCeil_nonneg (hc₀ : 0 ≤ c) (x : ℝ) : 0 ≤ zpowCeil c x := by
  unfold zpowCeil
  split_ifs
  exacts [zpow_nonneg hc₀ _, le_rfl]

/-- The rounding of `x` is positive exactly when `x` is. -/
theorem zpowCeil_pos_iff (hc₀ : 0 < c) : 0 < zpowCeil c x ↔ 0 < x := by
  unfold zpowCeil
  split_ifs with hx
  · simpa [hx] using zpow_pos hc₀ _
  · simpa using hx

/-- The rounding of `x` vanishes exactly when `x ≤ 0`. -/
theorem zpowCeil_eq_zero_iff (hc₀ : 0 < c) : zpowCeil c x = 0 ↔ x ≤ 0 := by
  rw [← not_lt, ← zpowCeil_pos_iff hc₀, (zpowCeil_nonneg hc₀.le x).lt_iff_ne', not_not]

/-- A positive number is rounded to an integer power of `c`. -/
theorem exists_zpowCeil_eq_zpow (hx : 0 < x) : ∃ n : ℤ, zpowCeil c x = c ^ n :=
  ⟨_, zpowCeil_of_pos hx⟩

section BaseLtOne

variable (hc₀ : 0 < c) (hc₁ : c < 1)
include hc₀ hc₁

/-- **Rounding up dominates**: `x ≤ zpowCeil c x`. -/
theorem le_zpowCeil (x : ℝ) : x ≤ zpowCeil c x := by
  rcases le_or_gt x 0 with hx | hx
  · rwa [zpowCeil_of_nonpos hx]
  · rw [zpowCeil_of_pos hx, ← le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hx]

/-- **Rounding up loses less than the factor `c`**: `c * zpowCeil c x < x` for `x > 0`. -/
theorem mul_zpowCeil_lt (hx : 0 < x) : c * zpowCeil c x < x := by
  rw [zpowCeil_of_pos hx, ← zpow_one_add₀ hc₀.ne', add_comm, ← not_le,
    ← le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hx]
  omega

/-- The non-strict form of `mul_zpowCeil_lt`, valid for every `x ≥ 0`. -/
theorem mul_zpowCeil_le (hx : 0 ≤ x) : c * zpowCeil c x ≤ x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · exact (mul_zpowCeil_lt hc₀ hc₁ hx).le

/-- `zpowCeil c x` is the integer power `c ^ n` exactly when `x` lies in the half-open interval
`(c ^ (n + 1), c ^ n]`. -/
theorem zpowCeil_eq_zpow_iff (n : ℤ) : zpowCeil c x = c ^ n ↔ c ^ (n + 1) < x ∧ x ≤ c ^ n := by
  refine ⟨fun h ↦ ?_, fun ⟨hlt, hle⟩ ↦ ?_⟩
  · have hx : 0 < x := (zpowCeil_pos_iff hc₀).mp (h ▸ zpow_pos hc₀ n)
    refine ⟨?_, h ▸ le_zpowCeil hc₀ hc₁ x⟩
    rw [zpow_add_one₀ hc₀.ne', mul_comm, ← h]
    exact mul_zpowCeil_lt hc₀ hc₁ hx
  · have hx : 0 < x := (zpow_pos hc₀ _).trans hlt
    rw [zpowCeil_of_pos hx]
    congr 1
    have h₁ := (le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hx n).mpr hle
    have h₂ := mt (le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hx (n + 1)).mp hlt.not_ge
    omega

/-- An integer power of `c` is its own rounding. -/
@[simp]
theorem zpowCeil_zpow (n : ℤ) : zpowCeil c (c ^ n) = c ^ n :=
  (zpowCeil_eq_zpow_iff hc₀ hc₁ n).mpr
    ⟨zpow_lt_zpow_right_of_lt_one₀ hc₀ hc₁ (Int.lt_succ n), le_rfl⟩

/-- One is its own rounding. -/
@[simp]
theorem zpowCeil_one : zpowCeil c 1 = 1 := by
  simpa using zpowCeil_zpow hc₀ hc₁ 0

/-- The constant `c` is its own rounding. -/
@[simp]
theorem zpowCeil_self : zpowCeil c c = c := by
  simpa using zpowCeil_zpow hc₀ hc₁ 1

/-- Rounding up is monotone. -/
theorem monotone_zpowCeil : Monotone (zpowCeil c) := by
  intro x y hxy
  rcases le_or_gt x 0 with hx | hx
  · rw [zpowCeil_of_nonpos hx]
    exact zpowCeil_nonneg hc₀.le y
  · have hy := hx.trans_le hxy
    rw [zpowCeil_of_pos hx, zpowCeil_of_pos hy, zpow_le_zpow_iff_right_of_lt_one₀ hc₀ hc₁,
      le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hx]
    exact hxy.trans ((le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hy _).mp le_rfl)

/-- Rounding up is idempotent. -/
@[simp]
theorem zpowCeil_zpowCeil (x : ℝ) : zpowCeil c (zpowCeil c x) = zpowCeil c x := by
  rcases le_or_gt x 0 with hx | hx
  · simp [zpowCeil_of_nonpos hx]
  · obtain ⟨n, hn⟩ := exists_zpowCeil_eq_zpow (c := c) hx
    rw [hn, zpowCeil_zpow hc₀ hc₁]

/-- A nonnegative number is its own rounding exactly when it is `0` or an integer power
of `c`. -/
theorem zpowCeil_eq_self_iff (hx : 0 ≤ x) : zpowCeil c x = x ↔ x = 0 ∨ ∃ n : ℤ, c ^ n = x := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases hx.eq_or_lt with rfl | hx
    · exact .inl rfl
    · obtain ⟨n, hn⟩ := exists_zpowCeil_eq_zpow (c := c) hx
      exact .inr ⟨n, hn ▸ h⟩
  · rintro (rfl | ⟨n, rfl⟩)
    exacts [zpowCeil_zero, zpowCeil_zpow hc₀ hc₁ n]

/-- **Rounding up is a closure operator onto `c ^ ℤ ∪ {0}`**: for `y` in that set,
`zpowCeil c x ≤ y ↔ x ≤ y`. -/
theorem zpowCeil_le_iff (hy : zpowCeil c y = y) : zpowCeil c x ≤ y ↔ x ≤ y :=
  ⟨(le_zpowCeil hc₀ hc₁ x).trans, fun h ↦ hy ▸ monotone_zpowCeil hc₀ hc₁ h⟩

/-- **Discreteness of the rounded values**: `zpowCeil c x` lies strictly below `c ^ n` exactly
when `x ≤ c ^ (n + 1)`. In particular `zpowCeil c x < 1 ↔ x ≤ c`. -/
theorem zpowCeil_lt_zpow_iff (n : ℤ) : zpowCeil c x < c ^ n ↔ x ≤ c ^ (n + 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases le_or_gt x 0 with hx | hx
    · exact hx.trans (zpow_pos hc₀ _).le
    · rw [zpowCeil_of_pos hx, zpow_lt_zpow_iff_right_of_lt_one₀ hc₀ hc₁] at h
      rw [← le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hx]
      omega
  · exact ((zpowCeil_le_iff hc₀ hc₁ (zpowCeil_zpow hc₀ hc₁ _)).mpr h).trans_lt
      (zpow_lt_zpow_right_of_lt_one₀ hc₀ hc₁ (Int.lt_succ n))

/-- **Rounding commutes with scaling by powers of `c`**:
`zpowCeil c (c ^ n * x) = c ^ n * zpowCeil c x`. -/
theorem zpowCeil_zpow_mul (n : ℤ) (x : ℝ) : zpowCeil c (c ^ n * x) = c ^ n * zpowCeil c x := by
  have hcn : 0 < c ^ n := zpow_pos hc₀ n
  rcases le_or_gt x 0 with hx | hx
  · rw [zpowCeil_of_nonpos hx, zpowCeil_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hcn.le hx),
      mul_zero]
  · obtain ⟨k, hk⟩ := exists_zpowCeil_eq_zpow (c := c) hx
    obtain ⟨hlt, hle⟩ := (zpowCeil_eq_zpow_iff hc₀ hc₁ k).mp hk
    rw [hk, ← zpow_add₀ hc₀.ne', zpowCeil_eq_zpow_iff hc₀ hc₁, add_assoc,
      zpow_add₀ hc₀.ne' n (k + 1), zpow_add₀ hc₀.ne' n k]
    exact ⟨mul_lt_mul_of_pos_left hlt hcn, mul_le_mul_of_nonneg_left hle hcn.le⟩

/-- **Rounding up is submultiplicative** on a nonnegative left factor:
`zpowCeil c (x * y) ≤ zpowCeil c x * zpowCeil c y`. -/
theorem zpowCeil_mul_le (hx : 0 ≤ x) (y : ℝ) :
    zpowCeil c (x * y) ≤ zpowCeil c x * zpowCeil c y := by
  have h₀ : 0 ≤ zpowCeil c x * zpowCeil c y :=
    mul_nonneg (zpowCeil_nonneg hc₀.le x) (zpowCeil_nonneg hc₀.le y)
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rcases le_or_gt y 0 with hy | hy
  · rwa [zpowCeil_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hx.le hy)]
  obtain ⟨k, hk⟩ := exists_zpowCeil_eq_zpow (c := c) hx
  obtain ⟨l, hl⟩ := exists_zpowCeil_eq_zpow (c := c) hy
  rw [hk, hl, ← zpow_add₀ hc₀.ne', zpowCeil_le_iff hc₀ hc₁ (zpowCeil_zpow hc₀ hc₁ _),
    zpow_add₀ hc₀.ne', ← hk, ← hl]
  exact mul_le_mul (le_zpowCeil hc₀ hc₁ x) (le_zpowCeil hc₀ hc₁ y) hy.le
    (zpowCeil_nonneg hc₀.le x)

section Group

variable {M : Type*} [SeminormedAddGroup M]

/-- **Rounding preserves the ultrametric inequality**. -/
theorem zpowCeil_norm_add_le_max [IsUltrametricDist M] (m n : M) :
    zpowCeil c ‖m + n‖ ≤ max (zpowCeil c ‖m‖) (zpowCeil c ‖n‖) :=
  (monotone_zpowCeil hc₀ hc₁ (IsUltrametricDist.norm_add_le_max m n)).trans_eq
    (monotone_zpowCeil hc₀ hc₁).map_max

/-- **Rounding is compatible with contractive scalar actions**:
`zpowCeil c ‖a • m‖ ≤ zpowCeil c ‖a‖ * zpowCeil c ‖m‖`. When `‖a‖` lies in `c ^ ℤ ∪ {0}`
(`zpowCeil_eq_self_iff`), the right-hand side is `‖a‖ * zpowCeil c ‖m‖`. -/
theorem zpowCeil_norm_smul_le {R : Type*} [SeminormedAddGroup R] [SMulZeroClass R M]
    [IsBoundedSMul R M] (a : R) (m : M) :
    zpowCeil c ‖a • m‖ ≤ zpowCeil c ‖a‖ * zpowCeil c ‖m‖ :=
  (monotone_zpowCeil hc₀ hc₁ (norm_smul_le a m)).trans (zpowCeil_mul_le hc₀ hc₁ (norm_nonneg a) _)

variable (M)

/-- The norm of an ultrametric seminormed group rounded up to `c ^ ℤ ∪ {0}`, for `0 < c < 1`.
It satisfies `‖m‖ ≤ zpowCeil c ‖m‖` and, for `‖m‖ ≠ 0`, `c * zpowCeil c ‖m‖ < ‖m‖`, so it is
bounded-equivalent to the original norm. -/
noncomputable def zpowCeilAddGroupSeminorm [IsUltrametricDist M] : AddGroupSeminorm M where
  toFun m := zpowCeil c ‖m‖
  map_zero' := by simp
  add_le' m n := (zpowCeil_norm_add_le_max hc₀ hc₁ m n).trans <|
    max_le_add_of_nonneg (zpowCeil_nonneg hc₀.le _) (zpowCeil_nonneg hc₀.le _)
  neg' m := by simp

/-- The rounded seminorm of `m` is the rounding of `‖m‖`. -/
@[simp]
theorem zpowCeilAddGroupSeminorm_apply [IsUltrametricDist M] (m : M) :
    zpowCeilAddGroupSeminorm hc₀ hc₁ M m = zpowCeil c ‖m‖ := (rfl)

/-- The rounded seminorm is ultrametric. -/
theorem isNonarchimedean_zpowCeilAddGroupSeminorm [IsUltrametricDist M] :
    IsNonarchimedean (zpowCeilAddGroupSeminorm hc₀ hc₁ M) :=
  zpowCeil_norm_add_le_max hc₀ hc₁

end Group

/-- The norm of an ultrametric normed group rounded up to `c ^ ℤ ∪ {0}`, for `0 < c < 1`, as a
group norm. -/
noncomputable def zpowCeilAddGroupNorm (M : Type*) [NormedAddGroup M] [IsUltrametricDist M] :
    AddGroupNorm M where
  __ := zpowCeilAddGroupSeminorm hc₀ hc₁ M
  eq_zero_of_map_eq_zero' _ h := norm_le_zero_iff.mp <| (zpowCeil_eq_zero_iff hc₀).mp h

/-- The rounded norm of `m` is the rounding of `‖m‖`. -/
@[simp]
theorem zpowCeilAddGroupNorm_apply {M : Type*} [NormedAddGroup M] [IsUltrametricDist M]
    (m : M) : zpowCeilAddGroupNorm hc₀ hc₁ M m = zpowCeil c ‖m‖ := (rfl)

end BaseLtOne

end TauCeti
