/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Basic
public import Mathlib.GroupTheory.GroupAction.Period
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# The integer cusp width of a finite-index subgroup

The image of `T = [1, 1; 0, 1]` in `GL(2, ℝ)` and its powers are the upper-triangular
shift matrices; a subgroup `𝒢` of finite relative index in `𝒮ℒ` contains some positive
power of `T`, and `Subgroup.integerCuspWidth 𝒢` is the least such exponent. The cosets of the
first `Subgroup.integerCuspWidth 𝒢` powers of `T` are pairwise distinct in `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`, and
the integer cusp width is a positive integer multiple of the strict width at `∞`.
At an irregular cusp the negative shift by the projective width lies in the group;
its slash action gives the weight-parity sign under translation.

## Main declarations

* `TauCeti.Subgroup.integerCuspWidth`: the least positive power of `T` in `𝒢` (or `0` if none
  exists).
* `TauCeti.Subgroup.natCast_mem_strictPeriods_iff`: the integer strict periods are the
  multiples of the width.
* `TauCeti.Subgroup.quotient_T_pow_integerCuspWidth_injective`: the cosets of the first
  `integerCuspWidth 𝒢` powers of `T` are pairwise distinct.
* `TauCeti.Subgroup.exists_pos_nat_integerCuspWidth_eq_mul_strictWidthInfty`: the integer cusp
  width is a positive integer multiple of the strict width at `∞`.
* `TauCeti.ModularForm.slash_T_zpow_apply`: slashing by a power of `T` is an integer shift.
* `TauCeti.neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty`: the negative shift
  belonging to the group at an irregular cusp.
* `TauCeti.SlashInvariantForm.vadd_apply_of_neg_upperRightHom_mem`: a negative
  shift in the group gives translation by the weight-parity sign.

## References

* [Mathlib PR #39087](https://github.com/leanprover-community/mathlib4/pull/39087)
  (Chris Birkbeck).
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §2.4.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup Subgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

/-- The image of `T ^ n : SL(2, ℤ)` in `GL(2, S)` for any commutative ring `S` is the
upper-triangular matrix `[1, n; 0, 1]`. -/
@[simp]
lemma ModularGroup.mapGL_T_zpow_eq_upperRightHom {S : Type*} [CommRing S] (n : ℤ) :
    Matrix.SpecialLinearGroup.mapGL S ((ModularGroup.T : SL(2, ℤ))^n) =
      Matrix.GeneralLinearGroup.upperRightHom (n : S) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mapGL_coe_matrix, ModularGroup.coe_T_zpow, -map_zpow]

/-- The image of `T ^ n : SL(2, ℤ)` in `GL(2, S)`, for a natural exponent. -/
@[simp]
lemma ModularGroup.mapGL_T_pow_eq_upperRightHom {S : Type*} [CommRing S] (n : ℕ) :
    Matrix.SpecialLinearGroup.mapGL S ((ModularGroup.T : SL(2, ℤ))^n) =
      Matrix.GeneralLinearGroup.upperRightHom (n : S) := by
  rw [← zpow_natCast, ModularGroup.mapGL_T_zpow_eq_upperRightHom, Int.cast_natCast]

/-- The coercion of `SL(2, ℤ)` into `GL(2, ℝ)` agrees with `mapGL ℝ`. -/
lemma Matrix.SpecialLinearGroup.coe_GL_eq_mapGL (g : SL(2, ℤ)) :
    (g : GL (Fin 2) ℝ) = mapGL ℝ g := rfl

/-- The Möbius action of `upperRightHom x = [1, x; 0, 1]` on `ℍ` is the shift `x +ᵥ ·`. -/
lemma Matrix.GeneralLinearGroup.upperRightHom_smul (x : ℝ) (τ : ℍ) :
    _root_.Matrix.GeneralLinearGroup.upperRightHom x • τ = x +ᵥ τ := by
  ext1
  rw [coe_smul_of_det_pos (by simp)]
  simp [num, denom, _root_.Matrix.GeneralLinearGroup.upperRightHom_apply, add_comm]

/-- Slashing a function `g : ℍ → ℂ` by the shift matrix `[1, x; 0, 1]` is the shift
`τ ↦ g (x +ᵥ τ)`. -/
lemma ModularForm.slash_upperRightHom_apply (k : ℤ) (x : ℝ) (g : ℍ → ℂ) (τ : ℍ) :
    (g ∣[k] (_root_.Matrix.GeneralLinearGroup.upperRightHom x : GL (Fin 2) ℝ)) τ =
      g (x +ᵥ τ) := by
  rw [_root_.ModularForm.slash_apply, Matrix.GeneralLinearGroup.upperRightHom_smul]
  simp [σ, denom, _root_.Matrix.GeneralLinearGroup.val_det_apply,
    _root_.Matrix.GeneralLinearGroup.upperRightHom_apply]

/-- Acting on a function `g : ℍ → ℂ` by `T ^ j` via the weight `k` slash action is the shift
`τ ↦ g ((j : ℝ) +ᵥ τ)`. -/
lemma ModularForm.slash_T_zpow_apply (k j : ℤ) (g : ℍ → ℂ) (τ : ℍ) :
    (g ∣[k] (ModularGroup.T ^ j : SL(2, ℤ))) τ = g ((j : ℝ) +ᵥ τ) := by
  rw [_root_.ModularForm.SL_slash, Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
    ModularGroup.mapGL_T_zpow_eq_upperRightHom, ModularForm.slash_upperRightHom_apply]


/-- A negative translation in the group gives the weight-parity transformation
law under translation by `h`. -/
theorem SlashInvariantForm.vadd_apply_of_neg_upperRightHom_mem
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ}
    [SlashInvariantFormClass F Γ k] (f : F)
    (hΓ : -Matrix.GeneralLinearGroup.upperRightHom h ∈ Γ) (z : ℍ) :
    f (h +ᵥ z) = (-1 : ℂ) ^ k * f z := by
  have hs := congrFun (SlashInvariantFormClass.slash_action_eq f _ hΓ) z
  rw [← mul_neg_one (Matrix.GeneralLinearGroup.upperRightHom h),
    SlashAction.slash_mul, ModularForm.slash_neg_one] at hs
  simp only [Pi.smul_apply, smul_eq_mul, TauCeti.ModularForm.slash_upperRightHom_apply] at hs
  simpa only [← inv_zpow, inv_neg_one] using
    (eq_inv_mul_iff_mul_eq₀ (zpow_ne_zero k (by norm_num : (-1 : ℂ) ≠ 0))).mpr hs

section IntegerCuspWidth

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)}

/-- The left-multiplication action of `𝒮ℒ` on the coset space `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`,
constructed explicitly: instance synthesis for this action is unstable at use sites, so
the declarations below install it with `letI`. -/
@[instance_reducible]
private def quotientTAction :
    MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :=
  letI : MulAction 𝒮ℒ 𝒮ℒ := Monoid.toMulAction _
  .quotient ..

/-- The coset of a power of `T` is the base coset exactly when the exponent is a strict
period of `𝒢`: the bridge between the coset space and the strict periods, stated without
reference to the group action. -/
@[simp]
lemma Subgroup.mk_T_pow_eq_iff {n : ℕ} :
    (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ)))^n⟧ :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) = ⟦1⟧ ↔ (n : ℝ) ∈ 𝒢.strictPeriods := by
  rw [QuotientGroup.eq]
  simp only [mul_one, inv_mem_iff, Subgroup.mem_subgroupOf,
    MonoidHom.coe_rangeRestrict, ← map_pow, ModularGroup.mapGL_T_pow_eq_upperRightHom,
    Subgroup.mem_strictPeriods_iff]

/-- A subgroup of `GL(2, ℝ)` of finite relative index in `𝒮ℒ` always has a positive
natural number in its strict periods: some positive power of `T` lands in the
subgroup. -/
lemma Subgroup.exists_pos_nat_mem_strictPeriods [𝒢.IsFiniteRelIndex 𝒮ℒ] :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ∈ 𝒢.strictPeriods := by
  obtain ⟨n, hn_pos, _, hn_mem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := 𝒢.subgroupOf 𝒮ℒ))
    ((mapGL ℝ).rangeRestrict ModularGroup.T)
  refine ⟨n, hn_pos, Subgroup.mk_T_pow_eq_iff.mp ?_⟩
  rw [QuotientGroup.eq]
  simpa using inv_mem hn_mem

/-- The powers of the coset of `T` acting on the base coset, as statements about
cosets: `t ^ n • ⟦1⟧ = ⟦t ^ n⟧` under the explicit action. -/
private lemma quotientTAction_pow_smul_mk_one (n : ℕ) :
    let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
    ((mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))))^n •
        (⟦1⟧ : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) =
      ⟦((mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))))^n⟧ := by
  intro _
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- The `MulAction.period` of the coset of `T` acting on the base coset of
`𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`. When some positive power of `T` lies in `𝒢` — in particular whenever
`𝒢` has finite relative index in `𝒮ℒ`, see `Subgroup.integerCuspWidth_pos` — this is
the smallest positive integer `n` such that the upper-triangular matrix `[1, n; 0, 1]`
lies in `𝒢`; otherwise it is `0`. -/
def Subgroup.integerCuspWidth (𝒢 : Subgroup (GL (Fin 2) ℝ)) : ℕ :=
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  MulAction.period ((mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ)))
    (⟦1⟧ : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))

/-- The integer cusp width is positive. -/
lemma Subgroup.integerCuspWidth_pos [𝒢.IsFiniteRelIndex 𝒮ℒ] : 0 < Subgroup.integerCuspWidth 𝒢 := by
  obtain ⟨n, hn_pos, hn_mem⟩ := Subgroup.exists_pos_nat_mem_strictPeriods (𝒢 := 𝒢)
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  exact MulAction.period_pos_of_fixed hn_pos
    ((quotientTAction_pow_smul_mk_one n).trans (Subgroup.mk_T_pow_eq_iff.mpr hn_mem))

/-- The integer cusp width is a strict period. -/
lemma Subgroup.integerCuspWidth_mem_strictPeriods :
    (Subgroup.integerCuspWidth 𝒢 : ℝ) ∈ 𝒢.strictPeriods := by
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  exact Subgroup.mk_T_pow_eq_iff.mp
    ((quotientTAction_pow_smul_mk_one _).symm.trans (MulAction.pow_period_smul _ _))

/-- `∞` is a cusp of a subgroup of finite relative index in `𝒮ℒ`, since its integer cusp width is
a positive strict period. -/
lemma Subgroup.isCusp_infty_of_finiteRelIndex [𝒢.IsFiniteRelIndex 𝒮ℒ] :
    IsCusp OnePoint.infty 𝒢 :=
  Subgroup.isCusp_of_mem_strictPeriods (Nat.cast_pos.mpr Subgroup.integerCuspWidth_pos)
    Subgroup.integerCuspWidth_mem_strictPeriods

/-- The integer cusp width is minimal among positive integer strict periods. -/
lemma Subgroup.integerCuspWidth_le {n : ℕ} (hpos : 0 < n)
    (hmem : (n : ℝ) ∈ 𝒢.strictPeriods) : Subgroup.integerCuspWidth 𝒢 ≤ n := by
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  exact MulAction.period_le_of_fixed hpos
    ((quotientTAction_pow_smul_mk_one n).trans (Subgroup.mk_T_pow_eq_iff.mpr hmem))

/-- The `integerCuspWidth 𝒢`-th power of `T` lies in `𝒢`. -/
lemma Subgroup.T_pow_integerCuspWidth_mem :
    ((ModularGroup.T : SL(2, ℤ)) ^ Subgroup.integerCuspWidth 𝒢 : GL (Fin 2) ℝ) ∈ 𝒢 := by
  rw [Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← map_pow,
    ModularGroup.mapGL_T_pow_eq_upperRightHom, ← mem_strictPeriods_iff]
  exact Subgroup.integerCuspWidth_mem_strictPeriods

/-- The natural numbers among the strict periods are exactly the multiples of the
integer cusp width. -/
-- Not a `simp` lemma: `simpNF` rejects it because the left-hand side already simplifies
-- through `Subgroup.mem_strictPeriods_iff`.
lemma Subgroup.natCast_mem_strictPeriods_iff {n : ℕ} :
    (n : ℝ) ∈ 𝒢.strictPeriods ↔ Subgroup.integerCuspWidth 𝒢 ∣ n := by
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  rw [← Subgroup.mk_T_pow_eq_iff, ← quotientTAction_pow_smul_mk_one n,
    Subgroup.integerCuspWidth, MulAction.pow_smul_eq_iff_period_dvd]

/-- The powers of `T` lying in `𝒢` are exactly those with exponent divisible by the
integer cusp width. -/
@[simp]
lemma Subgroup.T_pow_mem_iff {n : ℕ} :
    ((ModularGroup.T : SL(2, ℤ))^n : GL (Fin 2) ℝ) ∈ 𝒢 ↔
      Subgroup.integerCuspWidth 𝒢 ∣ n := by
  rw [Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← map_pow,
    ModularGroup.mapGL_T_pow_eq_upperRightHom, ← mem_strictPeriods_iff,
    Subgroup.natCast_mem_strictPeriods_iff]

/-- The cosets `T ^ j • (𝒢 ⊓ 𝒮ℒ)` for `j < integerCuspWidth 𝒢` are pairwise distinct in
`𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ`. -/
lemma Subgroup.quotient_T_pow_integerCuspWidth_injective :
    Function.Injective (fun j : Fin (Subgroup.integerCuspWidth 𝒢) ↦
      (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))) := by
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  set t := (mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ))
  intro j₁ j₂ hj
  simp only [map_pow] at hj
  rw [← quotientTAction_pow_smul_mk_one (j₁ : ℕ),
    ← quotientTAction_pow_smul_mk_one (j₂ : ℕ)] at hj
  -- Injectivity of iterates below the minimal period, transported along
  -- `period = minimalPeriod` and `iterate = pow-smul`.
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := (t • ·))
    (x := (⟦1⟧ : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)))
  rw [← MulAction.period_eq_minimalPeriod] at hinj
  exact Fin.ext (hinj (Set.mem_Iio.mpr j₁.isLt) (Set.mem_Iio.mpr j₂.isLt)
    (by simpa only [smul_iterate] using hj))


/-- The integer cusp width is a positive integer multiple of the strict width at `∞`. -/
lemma Subgroup.exists_pos_nat_integerCuspWidth_eq_mul_strictWidthInfty
    [𝒢.IsFiniteRelIndex 𝒮ℒ] [DiscreteTopology 𝒢.strictPeriods] :
    ∃ m : ℕ, 0 < m ∧ (Subgroup.integerCuspWidth 𝒢 : ℝ) = m * 𝒢.strictWidthInfty := by
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp <|
    Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty (𝒢 := 𝒢) ▸
      Subgroup.integerCuspWidth_mem_strictPeriods
  rw [zsmul_eq_mul] at hm
  have hm_pos : (0 : ℤ) < m := by
    have : (0 : ℝ) < m :=
      pos_of_mul_pos_left (hm ▸ mod_cast Subgroup.integerCuspWidth_pos) 𝒢.strictWidthInfty_nonneg
    exact_mod_cast this
  exact ⟨m.toNat, by lia, by rw [← hm, ← Int.cast_natCast, Int.toNat_of_nonneg hm_pos.le]⟩

end IntegerCuspWidth

/-- At an irregular cusp the negative translation by the projective width belongs
to the group. -/
theorem neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty
    (Γ : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology Γ.periods]
    (hΓ : ¬Γ.IsRegularAtInfty) :
    -Matrix.GeneralLinearGroup.upperRightHom Γ.widthInfty ∈ Γ := by
  have hmem := Γ.widthInfty_mem_periods
  simp only [Subgroup.periods, Subgroup.mem_strictPeriods_iff,
    Subgroup.mem_adjoinNegOne_iff] at hmem
  exact hmem.resolve_left fun h ↦ hΓ (Γ.isRegularAtInfty_iff.mpr
    (Subgroup.mem_strictPeriods_iff.mpr h))

/-! ### The strict period `1` of `Γ₀(N)` and `Γ₁(N)` -/

/-- `1` is a strict period of `Γ₀(N)`, viewed in `GL (Fin 2) ℝ`. -/
theorem one_mem_strictPeriods_Gamma0_map (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map (mapGL ℝ)).strictPeriods := by
  simp [CongruenceSubgroup.strictPeriods_Gamma0]

/-- `1` is a strict period of `Γ₁(N)`, viewed in `GL (Fin 2) ℝ`. -/
theorem one_mem_strictPeriods_Gamma1_map (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)).strictPeriods := by
  simp [CongruenceSubgroup.strictPeriods_Gamma1]

end TauCeti

end
