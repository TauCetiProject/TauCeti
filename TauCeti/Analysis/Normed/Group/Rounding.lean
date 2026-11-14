/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.MulAction
public import TauCeti.Analysis.Normed.Group.CompatibleNorm
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

`zpowCeilNormedAddCommGroup` installs this rounded norm while retaining the original uniformity
and topology definitionally. Thus completeness and continuous linear maps are unchanged.
Ultrametricity and contractive scalar actions with discrete scalar norms can be installed
explicitly using `isUltrametricDist_zpowCeilNormedAddCommGroup` and
`isBoundedSMul_zpowCeilNormedAddCommGroup`.

## Main definitions

* `TauCeti.zpowCeil c x`: the least element of `c ^ ℤ ∪ {0}` that is at least `x`.
* `TauCeti.zpowCeilAddGroupSeminorm hc₀ M`: the norm of an ultrametric seminormed group
  rounded to `c ^ ℤ ∪ {0}` by `zpowCeil c` (upward for `0 < c < 1`).
* `TauCeti.zpowCeilAddGroupNorm hc₀ M`: the same construction on a normed group, as a norm.

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
@[simp]
theorem zpowCeil_eq_zero_iff : zpowCeil c x = 0 ↔ x ≤ 0 := by
  unfold zpowCeil
  split_ifs with hx
  · rw [iff_false_right hx.not_ge]
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exact zpow_ne_zero _ hc
  · simpa using hx

/-- A positive number is rounded to an integer power of `c`. -/
theorem exists_zpowCeil_eq_zpow (hx : 0 < x) : ∃ n : ℤ, zpowCeil c x = c ^ n :=
  ⟨_, zpowCeil_of_pos hx⟩

/-- One is its own rounding. -/
@[simp]
theorem zpowCeil_one : zpowCeil c 1 = 1 := by
  simp [zpowCeil]

section Shell

open Set NNReal

/-- **The shell, for a positive real number**: for a real base `0 < r < 1`, every `a > 0` has a
unique rescaling `r ^ n * a`, `n ∈ ℤ`, with `r < r ^ n * a ≤ 1`. -/
theorem existsUnique_zpow_mul_mem_Ioc {r a : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ha : 0 < a) :
    ∃! n : ℤ, r ^ n * a ∈ Ioc r 1 := by
  -- Package `r` and `a` as units of `ℝ≥0`; the shell is then a fundamental domain for
  -- multiplication by the powers of `r⁻¹`.
  let q : ℝ≥0ˣ := Units.mk0 r.toNNReal (Real.toNNReal_pos.mpr hr0).ne'
  let u : ℝ≥0ˣ := Units.mk0 a.toNNReal (Real.toNNReal_pos.mpr ha).ne'
  have hq : 1 < q⁻¹ := one_lt_inv'.mpr <| by
    simpa [← Units.val_lt_val, q, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0.le] using hr1
  convert existsUnique_sub_zpow_mem_Ioc hq u q using 2 with n
  simp [← Units.val_lt_val, ← Units.val_le_val, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, q, u,
    Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ hr0.le, mul_comm]

end Shell

section BasePos

variable (hc₀ : 0 < c)
include hc₀

/-- An integer power of `c` is its own rounding. -/
@[simp]
theorem zpowCeil_zpow (n : ℤ) : zpowCeil c (c ^ n) = c ^ n := by
  rcases eq_or_ne c 1 with rfl | hc
  · simp [zpowCeil]
  · rw [zpowCeil_of_pos (zpow_pos hc₀ n), logb_zpow_self hc₀ hc, Int.floor_intCast]

/-- The constant `c` is its own rounding. -/
@[simp]
theorem zpowCeil_self : zpowCeil c c = c := by
  simpa using zpowCeil_zpow hc₀ 1

/-- `zpowCeil c` is monotone (for any `0 < c`). -/
theorem monotone_zpowCeil : Monotone (zpowCeil c) := by
  intro x y hxy
  rcases le_or_gt x 0 with hx | hx
  · rw [zpowCeil_of_nonpos hx]
    exact zpowCeil_nonneg hc₀.le y
  · have hy := hx.trans_le hxy
    rw [zpowCeil_of_pos hx, zpowCeil_of_pos hy]
    rcases lt_or_ge c 1 with hc₁ | hc₁
    · rw [zpow_le_zpow_iff_right_of_lt_one₀ hc₀ hc₁,
        le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hx]
      exact hxy.trans ((le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hy _).mp le_rfl)
    · rcases hc₁.eq_or_lt with rfl | hc₁
      · simp
      · exact zpow_le_zpow_right₀ hc₁.le (Int.floor_mono (Real.logb_le_logb_of_le hc₁ hx hxy))

/-- `zpowCeil c` is idempotent (for any `0 < c`). -/
@[simp]
theorem zpowCeil_zpowCeil (x : ℝ) : zpowCeil c (zpowCeil c x) = zpowCeil c x := by
  rcases le_or_gt x 0 with hx | hx
  · simp [zpowCeil_of_nonpos hx]
  · obtain ⟨n, hn⟩ := exists_zpowCeil_eq_zpow (c := c) hx
    rw [hn, zpowCeil_zpow hc₀]

/-- A number is its own rounding exactly when it is `0` or an integer power of `c`. -/
theorem zpowCeil_eq_self_iff : zpowCeil c x = x ↔ x = 0 ∨ ∃ n : ℤ, c ^ n = x := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [zpowCeil_of_nonpos hx.le] at h
      exact absurd h.symm hx.ne
    · exact .inl rfl
    · obtain ⟨n, hn⟩ := exists_zpowCeil_eq_zpow (c := c) hx
      exact .inr ⟨n, hn ▸ h⟩
  · rintro (rfl | ⟨n, rfl⟩)
    exacts [zpowCeil_zero, zpowCeil_zpow hc₀ n]

/-- **Rounding commutes with scaling by powers of `c`**:
`zpowCeil c (c ^ n * x) = c ^ n * zpowCeil c x`. -/
theorem zpowCeil_zpow_mul (n : ℤ) (x : ℝ) : zpowCeil c (c ^ n * x) = c ^ n * zpowCeil c x := by
  have hcn : 0 < c ^ n := zpow_pos hc₀ n
  rcases le_or_gt x 0 with hx | hx
  · rw [zpowCeil_of_nonpos hx, zpowCeil_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hcn.le hx),
      mul_zero]
  · rcases eq_or_ne c 1 with rfl | hc
    · simp [zpowCeil, hx]
    · rw [zpowCeil_of_pos hx, zpowCeil_of_pos (mul_pos hcn hx), Real.logb_mul hcn.ne' hx.ne',
        logb_zpow_self hc₀ hc, Int.floor_intCast_add, zpow_add₀ hc₀.ne']

section Group

variable {M : Type*} [SeminormedAddGroup M]

/-- **Rounding preserves the ultrametric inequality**. -/
theorem zpowCeil_norm_add_le_max [IsUltrametricDist M] (m n : M) :
    zpowCeil c ‖m + n‖ ≤ max (zpowCeil c ‖m‖) (zpowCeil c ‖n‖) :=
  (monotone_zpowCeil hc₀ (IsUltrametricDist.norm_add_le_max m n)).trans_eq
    (monotone_zpowCeil hc₀).map_max

variable (M)

/-- The norm of an ultrametric seminormed group rounded to `c ^ ℤ ∪ {0}` by `zpowCeil c`. For
`0 < c < 1` it is rounded up: it satisfies `‖m‖ ≤ zpowCeil c ‖m‖` and, for `‖m‖ ≠ 0`,
`c * zpowCeil c ‖m‖ < ‖m‖`, so it is bounded-equivalent to the original norm. -/
noncomputable def zpowCeilAddGroupSeminorm [IsUltrametricDist M] : AddGroupSeminorm M where
  toFun m := zpowCeil c ‖m‖
  map_zero' := by simp
  add_le' m n := (zpowCeil_norm_add_le_max hc₀ m n).trans <|
    max_le_add_of_nonneg (zpowCeil_nonneg hc₀.le _) (zpowCeil_nonneg hc₀.le _)
  neg' m := by simp

/-- The rounded seminorm of `m` is the rounding of `‖m‖`. -/
@[simp]
theorem zpowCeilAddGroupSeminorm_apply [IsUltrametricDist M] (m : M) :
    zpowCeilAddGroupSeminorm hc₀ M m = zpowCeil c ‖m‖ := (rfl)

/-- The rounded seminorm is ultrametric. -/
theorem isNonarchimedean_zpowCeilAddGroupSeminorm [IsUltrametricDist M] :
    IsNonarchimedean (zpowCeilAddGroupSeminorm hc₀ M) :=
  zpowCeil_norm_add_le_max hc₀

end Group

/-- The norm of an ultrametric normed group rounded to `c ^ ℤ ∪ {0}` by `zpowCeil c` (rounded up
for `0 < c < 1`), as a group norm. -/
noncomputable def zpowCeilAddGroupNorm (M : Type*) [NormedAddGroup M] [IsUltrametricDist M] :
    AddGroupNorm M where
  __ := zpowCeilAddGroupSeminorm hc₀ M
  eq_zero_of_map_eq_zero' _ h := norm_le_zero_iff.mp <| zpowCeil_eq_zero_iff.mp h

/-- The rounded norm of `m` is the rounding of `‖m‖`. -/
@[simp]
theorem zpowCeilAddGroupNorm_apply {M : Type*} [NormedAddGroup M] [IsUltrametricDist M]
    (m : M) : zpowCeilAddGroupNorm hc₀ M m = zpowCeil c ‖m‖ := (rfl)

end BasePos

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

/-- **Rounding up is a closure operator onto `c ^ ℤ ∪ {0}`**: for `y` in that set,
`zpowCeil c x ≤ y ↔ x ≤ y`. -/
theorem zpowCeil_le_iff (hy : zpowCeil c y = y) : zpowCeil c x ≤ y ↔ x ≤ y :=
  ⟨(le_zpowCeil hc₀ hc₁ x).trans, fun h ↦ hy ▸ monotone_zpowCeil hc₀ h⟩

/-- **Discreteness of the rounded values**: `zpowCeil c x` lies strictly below `c ^ n` exactly
when `x ≤ c ^ (n + 1)`. In particular `zpowCeil c x < 1 ↔ x ≤ c`. -/
theorem zpowCeil_lt_zpow_iff (n : ℤ) : zpowCeil c x < c ^ n ↔ x ≤ c ^ (n + 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases le_or_gt x 0 with hx | hx
    · exact hx.trans (zpow_pos hc₀ _).le
    · rw [zpowCeil_of_pos hx, zpow_lt_zpow_iff_right_of_lt_one₀ hc₀ hc₁] at h
      rw [← le_floor_logb_iff_zpow_le_of_base_lt_one hc₀ hc₁ hx]
      omega
  · exact ((zpowCeil_le_iff hc₀ hc₁ (zpowCeil_zpow hc₀ _)).mpr h).trans_lt
      (zpow_lt_zpow_right_of_lt_one₀ hc₀ hc₁ (Int.lt_succ n))

omit hc₁ in
/-- A number in `c ^ ℤ ∪ {0}` that is less than `1 = c ^ 0` is at most `c`. -/
theorem le_of_zpowCeil_eq_self_of_lt_one (hx : zpowCeil c x = x) (h : x < 1) : x ≤ c := by
  rcases lt_or_ge c 1 with hc₁ | hc₁
  · simpa using (zpowCeil_lt_zpow_iff hc₀ hc₁ 0).mp (by rwa [hx, zpow_zero])
  · exact h.le.trans hc₁

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
  rw [hk, hl, ← zpow_add₀ hc₀.ne', zpowCeil_le_iff hc₀ hc₁ (zpowCeil_zpow hc₀ _),
    zpow_add₀ hc₀.ne', ← hk, ← hl]
  exact mul_le_mul (le_zpowCeil hc₀ hc₁ x) (le_zpowCeil hc₀ hc₁ y) hy.le
    (zpowCeil_nonneg hc₀.le x)

section Group

variable {M : Type*} [SeminormedAddGroup M]

/-- **Rounding is compatible with contractive scalar actions**:
`zpowCeil c ‖a • m‖ ≤ zpowCeil c ‖a‖ * zpowCeil c ‖m‖`. When `‖a‖` lies in `c ^ ℤ ∪ {0}`
(`zpowCeil_eq_self_iff`), the right-hand side is `‖a‖ * zpowCeil c ‖m‖`. -/
theorem zpowCeil_norm_smul_le {R : Type*} [SeminormedAddGroup R] [SMulZeroClass R M]
    [IsBoundedSMul R M] (a : R) (m : M) :
    zpowCeil c ‖a • m‖ ≤ zpowCeil c ‖a‖ * zpowCeil c ‖m‖ :=
  (monotone_zpowCeil hc₀ (norm_smul_le a m)).trans (zpowCeil_mul_le hc₀ hc₁ (norm_nonneg a) _)

/-- Rounding the norm on a norm-one ring preserves the original scalar inequality exactly
when every scalar norm is already fixed by rounding. -/
theorem zpowCeil_norm_mul_le_iff {R : Type*} [SeminormedRing R] [NormOneClass R] :
    (∀ a x : R, zpowCeil c ‖a * x‖ ≤ ‖a‖ * zpowCeil c ‖x‖) ↔
      ∀ a : R, zpowCeil c ‖a‖ = ‖a‖ := by
  constructor
  · intro h a
    -- Test the scalar inequality on the module vector `1`.
    exact le_antisymm (by simpa [zpowCeil_one] using h a 1)
      (le_zpowCeil hc₀ hc₁ _)
  · intro h a x
    simpa only [smul_eq_mul, h] using zpowCeil_norm_smul_le hc₀ hc₁ a x

end Group

section CompatibleNorm

open scoped Uniformity

variable {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M]

/-- The rounded norm with the original uniformity and topology retained definitionally.
In particular, completeness and continuity are unchanged. -/
noncomputable abbrev zpowCeilNormedAddCommGroup : NormedAddCommGroup M :=
  (zpowCeilAddGroupNorm hc₀ M).toNormedAddCommGroupOfUniformity <|
    (zpowCeilAddGroupNorm hc₀ M).uniformity_eq_of_le
      (C := .mk c⁻¹ (inv_nonneg.mpr hc₀.le)) (D := 1)
      (fun x ↦ by simpa only [zpowCeilAddGroupNorm_apply, NNReal.coe_mk] using
        (le_inv_mul_iff₀ hc₀).2 (mul_zpowCeil_le hc₀ hc₁ (norm_nonneg x)))
      (fun x ↦ by simpa using le_zpowCeil hc₀ hc₁ ‖x‖)

/-- The compatible rounded norm is ultrametric. -/
theorem isUltrametricDist_zpowCeilNormedAddCommGroup :
    letI := zpowCeilNormedAddCommGroup (M := M) hc₀ hc₁
    IsUltrametricDist M := by
  have hadd := zpowCeil_norm_add_le_max (M := M) hc₀
  let := zpowCeilNormedAddCommGroup (M := M) hc₀ hc₁
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hadd

/-- Rounding preserves a contractive scalar action when the scalar norms already lie in
`c ^ ℤ ∪ {0}`. Without this hypothesis the original scalar norm need not act contractively. -/
theorem isBoundedSMul_zpowCeilNormedAddCommGroup {R : Type*} [SeminormedRing R]
    [Module R M] [IsBoundedSMul R M] (hR : ∀ a : R, zpowCeil c ‖a‖ = ‖a‖) :
    letI := zpowCeilNormedAddCommGroup (M := M) hc₀ hc₁
    IsBoundedSMul R M := by
  have hs (a : R) (m : M) : zpowCeil c ‖a • m‖ ≤ ‖a‖ * zpowCeil c ‖m‖ := by
    simpa only [hR] using zpowCeil_norm_smul_le hc₀ hc₁ a m
  let := zpowCeilNormedAddCommGroup (M := M) hc₀ hc₁
  exact IsBoundedSMul.of_norm_smul_le (α := R) (β := M) hs

end CompatibleNorm

end BaseLtOne

end TauCeti
