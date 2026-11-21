/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

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
* `TauCeti.ModularForm.cuspTranslationOrbitWidth_mk_dvd_iff`: integral membership criterion for
  subgroups of `SL(2, ℤ)`.
* `TauCeti.ModularForm.cuspTranslationOrbitWidth_mk_inf`: width of an intersection is the `lcm`.
* `TauCeti.ModularForm.cuspTranslationOrbitWidth_mk_one`: the base coset has width
  `Subgroup.integerCuspWidth 𝒢`.
* `TauCeti.ModularForm.sum_cuspTranslationOrbitWidth`: the widths sum to the index
  `[SL(2, ℤ) : 𝒢 ⊓ SL(2, ℤ)]`.
-/

public noncomputable section

open Matrix MulAction UpperHalfPlane Function

open scoped ModularForm MatrixGroups

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

/-- The period of a group element on a point is constant along that element's orbit. -/
lemma minimalPeriod_zpow_smul_TSL (j : ℤ) (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    minimalPeriod (TSL • ·) (TSL ^ j • q) = minimalPeriod (TSL • ·) q := by
  have key : ∀ (b : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) (i : ℤ),
      minimalPeriod (TSL • ·) (TSL ^ i • b) ∣ minimalPeriod (TSL • ·) b :=
    fun b i ↦ MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mp (by
      rw [← mul_smul, ← zpow_natCast, ← _root_.zpow_add, add_comm, _root_.zpow_add, zpow_natCast,
        mul_smul, MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mpr dvd_rfl])
  refine Nat.dvd_antisymm (key q j) ?_
  have h := key (TSL ^ j • q) (-j)
  rwa [← mul_smul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, one_smul] at h

/-- Any representative coset `q` in a cusp translation orbit is a `TSL`-power translate of
`c.out`. -/
lemma exists_TSL_zpow_smul_eq_out (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    ∃ j : ℤ, TSL ^ j • q = (⟦q⟧ : CuspTranslationOrbit 𝒢).out := by
  obtain ⟨h, hh⟩ := (orbitRel_apply (G := Subgroup.zpowers TSL)).mp
    (Quotient.eq.mp (Quotient.out_eq (⟦q⟧ : CuspTranslationOrbit 𝒢)))
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h.property
  exact ⟨j, by rw [hj]; exact hh⟩

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
  obtain ⟨j, hj⟩ := exists_TSL_zpow_smul_eq_out (𝒢 := 𝒢) q
  rw [cuspTranslationOrbitWidth, ← hj, minimalPeriod_zpow_smul_TSL]

/-- **What the period of a coset says about the group**: `T ^ n` fixes the coset of `x` exactly
when `x⁻¹ T ^ n x ∈ 𝒢`. Thus the action period is characterized by divisibility of exactly these
exponents. When the period is positive — in particular under `[𝒢.IsFiniteRelIndex 𝒮ℒ]` — it is
the least positive such `n`, the classical width of the cusp `x⁻¹ ∞`, read for the full coset
space rather than its projective quotient. -/
lemma minimalPeriod_TSL_dvd_iff (x : 𝒮ℒ) (n : ℕ) :
    minimalPeriod (TSL • ·) (QuotientGroup.mk x : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) ∣ n ↔
      ((x⁻¹ * TSL ^ n * x : 𝒮ℒ) : GL (Fin 2) ℝ) ∈ 𝒢 := by
  have hconj : ((TSL ^ n * x : 𝒮ℒ)⁻¹ * x : 𝒮ℒ) =
      (x⁻¹ * TSL ^ n * x : 𝒮ℒ)⁻¹ := by
    group
  rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, MulAction.Quotient.smul_mk, smul_eq_mul,
    QuotientGroup.eq, Subgroup.mem_subgroupOf, hconj, InvMemClass.coe_inv, Subgroup.inv_mem_iff]

/-- For `Γ ≤ SL(2, ℤ)`, the width of the cusp translation orbit of the coset of `γ` (the cusp
`γ⁻¹ ∞`) divides `m` exactly when `γ⁻¹ T ^ m γ ∈ Γ`. -/
lemma cuspTranslationOrbitWidth_mk_dvd_iff {Γ : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (m : ℕ) :
    cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) ∣ m ↔
      γ⁻¹ * ModularGroup.T ^ m * γ ∈ Γ := by
  have hconj : (((((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ)⁻¹ * TSL ^ m *
      (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict γ) : 𝒮ℒ) : GL (Fin 2) ℝ) =
        Matrix.SpecialLinearGroup.mapGL ℝ (γ⁻¹ * ModularGroup.T ^ m * γ) := by
    have hT : ((TSL ^ m : 𝒮ℒ) : GL (Fin 2) ℝ) =
        Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ m) := by
      rw [← zpow_natCast, coe_TSL_zpow, zpow_natCast,
        Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
    simp only [InvMemClass.coe_inv, Subgroup.coe_mul, MonoidHom.coe_rangeRestrict, map_inv, hT,
      map_mul]
  rw [cuspTranslationOrbitWidth_mk, minimalPeriod_TSL_dvd_iff, hconj,
    Subgroup.mem_map_iff_mem Matrix.SpecialLinearGroup.mapGL_injective]

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

/-- The period of the base coset is the integer cusp width of `𝒢`: both are characterised by
divisibility of the exponents `n` with `T ^ n ∈ 𝒢`. -/
lemma minimalPeriod_TSL_mk_one :
    minimalPeriod (TSL • ·) (QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) =
      Subgroup.integerCuspWidth 𝒢 := by
  have hsmul : ∀ n : ℕ, (TSL ^ n • (QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)) =
      QuotientGroup.mk (TSL ^ n) := fun n ↦ by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have key : ∀ n : ℕ,
      minimalPeriod (TSL • ·) (QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) ∣ n ↔
      Subgroup.integerCuspWidth 𝒢 ∣ n := fun n ↦ by
    rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, hsmul n,
      ← Subgroup.natCast_mem_strictPeriods_iff]
    exact ⟨fun h ↦ Subgroup.mk_T_pow_eq_iff.mp h, fun h ↦ Subgroup.mk_T_pow_eq_iff.mpr h⟩
  exact Nat.dvd_antisymm ((key _).mpr dvd_rfl) ((key _).mp dvd_rfl)

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
