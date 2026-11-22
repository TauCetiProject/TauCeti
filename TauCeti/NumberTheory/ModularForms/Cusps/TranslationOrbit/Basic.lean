/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.GroupTheory.GroupAction.Orbit.Period
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# Cusp translation orbits and their widths

For `𝒢 ≤ GL(2, ℝ)`, the **cusp translation orbits** `CuspTranslationOrbit 𝒢` are the orbits of
left translation by `T = [1, 1; 0, 1]` on the coset space `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`. Each orbit has a
width `cuspTranslationOrbitWidth c`, the period of the `T`-action, which equals the least `m > 0`
such that `x⁻¹ T ^ m x ∈ 𝒢` for any representative `x` when `[𝒢.IsFiniteRelIndex 𝒮ℒ]`.

These definitions and basic group-action, finiteness, and width identities live here ahead of
`Norm/Cusps.lean` so that cusp-projection and congruence-width modules do not need to import the
norm and valence machinery.

## Main definitions

* `TauCeti.ModularForm.TSL`: the translation `T = [1, 1; 0, 1]` as an element of `𝒮ℒ`.
* `TauCeti.ModularForm.CuspTranslationOrbit`: the `T`-orbits on `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`.
* `TauCeti.ModularForm.cuspTranslationOrbitWidth`: the width of a cusp translation orbit.

## Main results

* `TauCeti.ModularForm.cuspTranslationOrbitWidth_mk`: the width at a representative coset.
* `TauCeti.ModularForm.intCast_cuspTranslationOrbitWidth_mk_dvd_iff` and
  `TauCeti.ModularForm.cuspTranslationOrbitWidth_mk_dvd_iff`: integral membership criteria for
  subgroups of `SL(2, ℤ)`.
* `TauCeti.ModularForm.natCast_cuspTranslationOrbitWidth_mk_inv_eq_strictWidthInfty`: equality with
  `strictWidthInfty` of `γ⁻¹ Γ γ`.
* `TauCeti.ModularForm.cuspTranslationOrbitWidth_mk_inf`: width of an intersection is the `lcm`.
* `TauCeti.ModularForm.cuspTranslationOrbitWidth_mk_one`: the base coset has width
  `Subgroup.integerCuspWidth 𝒢`.
* `TauCeti.ModularForm.sum_cuspTranslationOrbitWidth`: the widths sum to the index
  `[SL(2, ℤ) : 𝒢 ⊓ SL(2, ℤ)]`.
-/

public noncomputable section

open Matrix MulAction UpperHalfPlane Function

open scoped ModularForm MatrixGroups Pointwise

namespace TauCeti.ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)}

/-- The translation `T = [1, 1; 0, 1]`, viewed as an element of `𝒮ℒ`. Its powers generate the
translations of `ℍ` by integers, and left multiplication by them is the action whose orbits on
`𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ` are the cusp translation orbits. -/
def TSL : 𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict ModularGroup.T

/-- The image of `TSL ^ j` in `GL(2, ℝ)` is the image of `T ^ j`. -/
lemma coe_TSL_zpow (j : ℤ) :
    ((TSL ^ j : 𝒮ℒ) : GL (Fin 2) ℝ) = ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [TSL, ← map_zpow, MonoidHom.coe_rangeRestrict,
    ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]

/-- The **cusp translation orbits** of `𝒢`: the orbits of left translation by `T` on the coset
space `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`. The orbit of the coset of `x` represents the cusp `x⁻¹ ∞` of `𝒢`, indexed
for the full coset space rather than its projective quotient. -/
abbrev CuspTranslationOrbit (𝒢 : Subgroup (GL (Fin 2) ℝ)) : Type :=
  orbitRel.Quotient (Subgroup.zpowers TSL) (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)

/-- To prove a property of cusp translation orbits, it suffices to consider the orbits of
cosets represented by integral matrices. -/
@[elab_as_elim]
theorem CuspTranslationOrbit.induction_on {P : CuspTranslationOrbit 𝒢 → Prop}
    (c : CuspTranslationOrbit 𝒢)
    (h : ∀ γ : SL(2, ℤ), P
      (⟦(QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ) :
        𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit 𝒢)) : P c := by
  induction c using Quotient.inductionOn with
  | h q =>
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨γ, hγ⟩ := x.property
      have hx : x = (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ :=
        Subtype.ext hγ.symm
      rw [hx]
      exact h γ

/-- The **width** of a cusp translation orbit of `𝒢`: the period of the `T`-action. Under
`[𝒢.IsFiniteRelIndex 𝒮ℒ]`, `minimalPeriod_TSL_dvd_iff` and
`cuspTranslationOrbitWidth_mk` identify it with the least `m > 0` such that
`x⁻¹ T ^ m x ∈ 𝒢` for any representative `x` of the orbit. -/
@[expose] noncomputable def cuspTranslationOrbitWidth (c : CuspTranslationOrbit 𝒢) : ℕ :=
  minimalPeriod (TSL • ·) c.out

/-- The width of a cusp translation orbit is the period of the `T`-action at any representative
coset. -/
@[simp] lemma cuspTranslationOrbitWidth_mk (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    cuspTranslationOrbitWidth (⟦q⟧ : CuspTranslationOrbit 𝒢) =
      minimalPeriod (TSL • ·) q := by
  obtain ⟨j, hj⟩ := MulAction.exists_zpow_smul_eq_out TSL q
  rw [cuspTranslationOrbitWidth, ← hj, MulAction.minimalPeriod_zpow_smul]

/-- **What the period of a coset says about the group (integer exponent)**: `T ^ j` fixes the
coset of `x` exactly when `x⁻¹ T ^ j x ∈ 𝒢`. -/
lemma intCast_minimalPeriod_TSL_dvd_iff (x : 𝒮ℒ) (j : ℤ) :
    (minimalPeriod (TSL • ·) (QuotientGroup.mk x : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ℤ) ∣ j ↔
      ((x⁻¹ * TSL ^ j * x : 𝒮ℒ) : GL (Fin 2) ℝ) ∈ 𝒢 := by
  have hconj : ((TSL ^ j * x : 𝒮ℒ)⁻¹ * x : 𝒮ℒ) = (x⁻¹ * TSL ^ j * x : 𝒮ℒ)⁻¹ := by group
  rw [← MulAction.zpow_smul_eq_iff_minimalPeriod_dvd, MulAction.Quotient.smul_mk, smul_eq_mul,
    QuotientGroup.eq, Subgroup.mem_subgroupOf, hconj, InvMemClass.coe_inv, Subgroup.inv_mem_iff]

/-- **What the period of a coset says about the group**: `T ^ n` fixes the coset of `x` exactly
when `x⁻¹ T ^ n x ∈ 𝒢`. Thus the action period is characterized by divisibility of exactly these
exponents. When the period is positive — in particular under `[𝒢.IsFiniteRelIndex 𝒮ℒ]` — it is
the least positive such `n`, the classical width of the cusp `x⁻¹ ∞`, read for the full coset
space rather than its projective quotient. -/
lemma minimalPeriod_TSL_dvd_iff (x : 𝒮ℒ) (n : ℕ) :
    minimalPeriod (TSL • ·) (QuotientGroup.mk x : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) ∣ n ↔
      ((x⁻¹ * TSL ^ n * x : 𝒮ℒ) : GL (Fin 2) ℝ) ∈ 𝒢 := by
  simpa only [← Int.natCast_dvd_natCast, zpow_natCast] using
    intCast_minimalPeriod_TSL_dvd_iff x n

/-- For `Γ ≤ SL(2, ℤ)`, the width of the cusp translation orbit of the coset of `γ` (the cusp
`γ⁻¹ ∞`) divides an integer `j` exactly when `γ⁻¹ T ^ j γ ∈ Γ`. -/
lemma intCast_cuspTranslationOrbitWidth_mk_dvd_iff {Γ : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ))
    (j : ℤ) :
    (cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℤ) ∣ j ↔
      γ⁻¹ * ModularGroup.T ^ j * γ ∈ Γ := by
  have hconj : (((((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ)⁻¹ * TSL ^ j *
      (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ) : 𝒮ℒ) : GL (Fin 2) ℝ) =
        Matrix.SpecialLinearGroup.mapGL ℝ (γ⁻¹ * ModularGroup.T ^ j * γ) := by
    have hT : ((TSL ^ j : 𝒮ℒ) : GL (Fin 2) ℝ) =
        Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ j) := by
      rw [coe_TSL_zpow, Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
    simp only [InvMemClass.coe_inv, Subgroup.coe_mul, MonoidHom.coe_rangeRestrict, map_inv, hT,
      map_mul]
  rw [cuspTranslationOrbitWidth_mk, intCast_minimalPeriod_TSL_dvd_iff, hconj,
    Subgroup.mem_map_iff_mem Matrix.SpecialLinearGroup.mapGL_injective]

/-- For `Γ ≤ SL(2, ℤ)`, the width of the cusp translation orbit of the coset of `γ` (the cusp
`γ⁻¹ ∞`) divides `m` exactly when `γ⁻¹ T ^ m γ ∈ Γ`. -/
lemma cuspTranslationOrbitWidth_mk_dvd_iff {Γ : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (m : ℕ) :
    cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) ∣ m ↔
      γ⁻¹ * ModularGroup.T ^ m * γ ∈ Γ := by
  simpa only [← Int.natCast_dvd_natCast, zpow_natCast] using
    intCast_cuspTranslationOrbitWidth_mk_dvd_iff γ m

/-- **Strict cusp width equals integer cusp-translation-orbit width**: `strictWidthInfty` of
`γ⁻¹ Γ γ` equals the width of the cusp translation orbit of `γ⁻¹`. -/
theorem natCast_cuspTranslationOrbitWidth_mk_inv_eq_strictWidthInfty {Γ : Subgroup SL(2, ℤ)}
    (γ : SL(2, ℤ)) :
    (cuspTranslationOrbitWidth
      (⟦QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ⁻¹)⟧ :
        CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) : ℝ) =
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ •
        (Γ : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty := by
  set w₀ := cuspTranslationOrbitWidth
    (⟦QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ⁻¹)⟧ :
      CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)))
  refine (Subgroup.strictWidthInfty_eq_of_strictPeriods_eq_zmultiples ?_ (Nat.cast_nonneg _)).symm
  ext x
  rw [Subgroup.mem_strictPeriods_iff, AddSubgroup.mem_zmultiples_iff]
  refine ⟨fun hx ↦ ?_, fun ⟨m, hm⟩ ↦ ?_⟩
  · obtain ⟨j, rfl, hj_mem⟩ := exists_int_eq_and_conj_T_zpow_mem_of_upperRightHom_mem_conj γ hx
    obtain ⟨m, hm⟩ :=
      (intCast_cuspTranslationOrbitWidth_mk_dvd_iff γ⁻¹ j).mpr (by simpa using hj_mem)
    exact ⟨m, by rw [zsmul_eq_mul, mul_comm, ← Int.cast_natCast, ← Int.cast_mul, ← hm]⟩
  · have hm_mem : γ * ModularGroup.T ^ ((w₀ : ℤ) * m) * γ⁻¹ ∈ Γ := by
      simpa only [inv_inv] using
        (intCast_cuspTranslationOrbitWidth_mk_dvd_iff γ⁻¹ ((w₀ : ℤ) * m)).mp ⟨m, rfl⟩
    rw [← hm, zsmul_eq_mul, mul_comm, ← Int.cast_natCast, ← Int.cast_mul,
      ← TauCeti.ModularGroup.mapGL_T_zpow_eq_upperRightHom, Subgroup.mem_conjAct_inv_smul_iff]
    simpa [map_mul, map_inv, mul_assoc] using
      Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hm_mem

/-- **Widths of an intersection**: at every coset, the width of the cusp translation orbit for
`𝒢₁ ⊓ 𝒢₂` is the least common multiple of the widths for `𝒢₁` and for `𝒢₂`. -/
lemma cuspTranslationOrbitWidth_mk_inf (𝒢₁ 𝒢₂ : Subgroup (GL (Fin 2) ℝ)) (x : 𝒮ℒ) :
    cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk x : 𝒮ℒ ⧸ (𝒢₁ ⊓ 𝒢₂).subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit (𝒢₁ ⊓ 𝒢₂)) =
      (cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk x : 𝒮ℒ ⧸ 𝒢₁.subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit 𝒢₁)).lcm
      (cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk x : 𝒮ℒ ⧸ 𝒢₂.subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit 𝒢₂)) :=
  Nat.dvd_right_iff_eq.mp fun n ↦ by
    simp only [cuspTranslationOrbitWidth_mk, Nat.lcm_dvd_iff, minimalPeriod_TSL_dvd_iff,
      Subgroup.mem_inf]

instance [𝒢.IsFiniteRelIndex 𝒮ℒ] (c : CuspTranslationOrbit 𝒢) :
    NeZero (cuspTranslationOrbitWidth c) :=
  inferInstanceAs (NeZero (minimalPeriod (TSL • ·) c.out))

/-- Every cusp translation orbit of a finite-index subgroup has positive width. -/
lemma cuspTranslationOrbitWidth_pos [𝒢.IsFiniteRelIndex 𝒮ℒ] (c : CuspTranslationOrbit 𝒢) :
    0 < cuspTranslationOrbitWidth c :=
  Nat.pos_of_neZero _

/-- A subgroup of finite relative index has finitely many cusp translation orbits: they are the
orbits of an action on the finite coset space. -/
noncomputable instance fintypeCuspTranslationOrbit [𝒢.IsFiniteRelIndex 𝒮ℒ] :
    Fintype (CuspTranslationOrbit 𝒢) :=
  Fintype.ofFinite _

/-- The period of the base coset is the integer cusp width of `𝒢`: both are the
`MulAction.period` of `T` on the base coset. -/
lemma minimalPeriod_TSL_mk_one :
    minimalPeriod (TSL • ·) (QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) =
      Subgroup.integerCuspWidth 𝒢 := by
  rw [Subgroup.integerCuspWidth, ← TSL, MulAction.period_eq_minimalPeriod]

/-- The orbit of the base coset represents the cusp `∞`, whose width is the integer cusp width. -/
@[simp 1100] lemma cuspTranslationOrbitWidth_mk_one :
    cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit 𝒢) =
      Subgroup.integerCuspWidth 𝒢 := by
  rw [cuspTranslationOrbitWidth_mk, minimalPeriod_TSL_mk_one]

/-- **The widths of the cusp translation orbits sum to the index**
`[SL(2, ℤ) : 𝒢 ⊓ SL(2, ℤ)]`. -/
lemma sum_cuspTranslationOrbitWidth [𝒢.IsFiniteRelIndex 𝒮ℒ] :
    ∑ c : CuspTranslationOrbit 𝒢, cuspTranslationOrbitWidth c =
      Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :=
  ((𝒢.subgroupOf 𝒮ℒ).index_eq_card ▸
    Subgroup.index_eq_sum_minimalPeriod (𝒢.subgroupOf 𝒮ℒ) TSL).symm

end TauCeti.ModularForm

end
