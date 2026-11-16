/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ModularForms.Cusps
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.RiemannHurwitz
public import TauCeti.NumberTheory.Modular.Invariants.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Elliptic.Gamma0
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective
public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
import TauCeti.Analysis.Complex.Fuchsian.Compactification.RamificationDegree
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Cofinite
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Signature
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.Geometry.Manifold.Complex.FiniteCWType
import TauCeti.NumberTheory.Modular.ConjugateTranslation
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Count
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Geometric comparison of modular-triple invariants

For a finite-index subgroup `Γ' ≤ PSL(2, ℤ)` enumerated by `e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n`,
`TauCeti.NumberTheory.Modular.Invariants.Basic` extracts the cusp widths, cusp count, elliptic
counts `ε₂`, `ε₃`, and combinatorial genus directly from the coset permutation triple
`modularTriple Γ' e`. This file identifies every one of these combinatorial invariants with its
geometric and modular-forms counterpart on the effective Fuchsian image `Γ'.map psl2zToPSL2R`
and on the lifted matrix subgroup `Γ'.liftSL ≤ SL(2, ℤ)`:

* **Cusp widths**: the period of `permT Γ' e` at the identity coset agrees with the integer cusp
  width (`TauCeti.Subgroup.integerCuspWidth`) and with Mathlib's `strictWidthInfty` and
  `widthInfty` of `Γ'.liftSL` (the last two agree because `-I ∈ Γ'.liftSL`). At every coset
  `σ`, the `permT`-period agrees with `ModularForm.cuspTranslationOrbitWidth`, and at every cusp
  `σ • ∞` it equals the width `D.width` of any normalized Fuchsian cusp datum `D` with scaling
  `psl2zToPSL2R σ⁻¹`.
* **Cusp orbits**: the cycles of `permT Γ' e` are in canonical bijection both with the Fuchsian
  cusp orbits `(Γ'.map psl2zToPSL2R).CuspOrbit` and with Mathlib's `CuspOrbits Γ'.liftSL`, so
  `cuspCount Γ' e` equals the cardinality of both orbit spaces.
* **Elliptic orbits**: the fixed points of `permS Γ' e` and `permR Γ' e` are in bijection with
  the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` of stabilizer orders `2` and `3`,
  respectively. In particular, the elliptic orbifold defect sum over the elliptic orbits equals
  `ellipticTwo Γ' e / 2 + 2 * ellipticThree Γ' e / 3`.
* **Topological genus**: combining the Fuchsian Riemann–Hurwitz formula for the finite-index
  branched cover `X(Γ') → X(1)` with the ramification-degree formula and the signature of `X(1)`
  proves that the finite-CW Euler characteristic of `(Γ'.map psl2zToPSL2R).CompactifiedQuotient`
  equals `(modularTriple Γ' e).eulerChar`, and hence that `genus Γ' e` equals the topological
  genus `TauCeti.RiemannSurface.genus (Γ'.map psl2zToPSL2R).CompactifiedQuotient`.
* **Congruence specializations**: specializing to `Γ₀(N)` recovers the classical product
  formulas for `ε∞`, `ε₂`, `ε₃` on `Gamma0Projective N`, the prime-level cusp widths
  `{1, p}`, and the full invariant vectors of `Γ₀(2)` (genus `0`) and `Γ₀(11)` (genus `1`).

## Main definitions

* `TauCeti.ModularGroup.permTCycleEquivFuchsianCuspOrbit`: bijection between cycles of
  `permT Γ' e` and Fuchsian cusp orbits of `Γ'.map psl2zToPSL2R`.
* `TauCeti.ModularGroup.fuchsianCuspOrbitEquivCuspOrbits`: bijection between Fuchsian cusp orbits
  of `Γ'.map psl2zToPSL2R` and Mathlib's `CuspOrbits Γ'.liftSL`.
* `TauCeti.ModularGroup.permTCycleEquivCuspOrbits`: bijection between cycles of `permT Γ' e` and
  Mathlib's `CuspOrbits Γ'.liftSL`.
* `TauCeti.ModularGroup.fixedPermSEquivOrderTwoEllipticOrbits`: bijection between fixed points
  of `permS Γ' e` and order-`2` elliptic orbits of `Γ'.map psl2zToPSL2R`.
* `TauCeti.ModularGroup.fixedPermREquivOrderThreeEllipticOrbits`: bijection between fixed points
  of `permR Γ' e` and order-`3` elliptic orbits of `Γ'.map psl2zToPSL2R`.

## Main results

* `TauCeti.ModularGroup.minimalPeriod_permT_one_eq_integerCuspWidth`,
  `TauCeti.ModularGroup.natCast_minimalPeriod_permT_one_eq_strictWidthInfty`,
  `TauCeti.ModularGroup.natCast_minimalPeriod_permT_one_eq_widthInfty`,
  `TauCeti.ModularGroup.minimalPeriod_permT_mk_eq_cuspTranslationOrbitWidth`,
  `TauCeti.ModularGroup.natCast_minimalPeriod_permT_eq_cuspDatum_width`: identification of
  `permT`-periods with integer, Mathlib, translation-orbit, and Fuchsian cusp widths.
* `TauCeti.ModularGroup.cuspCount_eq_card_fuchsianCuspOrbit` and
  `TauCeti.ModularGroup.cuspCount_eq_card_cuspOrbits`: the cycle count of `permT Γ' e` equals
  the number of Fuchsian and Mathlib cusp orbits.
* `TauCeti.ModularGroup.ellipticTwo_eq_card_orderTwoEllipticOrbits`,
  `TauCeti.ModularGroup.ellipticThree_eq_card_orderThreeEllipticOrbits`, and
  `TauCeti.ModularGroup.finsum_mem_ellipticOrbits_map_psl2zToPSL2R`: geometric elliptic orbit
  counts and the elliptic orbifold defect sum.
* `TauCeti.ModularGroup.eulerChar_compactifiedQuotient_eq_eulerChar` and
  `TauCeti.ModularGroup.genus_eq_riemannSurface_genus`: equality of the combinatorial and
  topological Euler characteristics and genera.
* `TauCeti.ModularGroup.cuspCount_Gamma0Projective`,
  `TauCeti.ModularGroup.cuspWidths_Gamma0Projective_of_prime`,
  `TauCeti.ModularGroup.ellipticTwo_Gamma0Projective_eq_prod`,
  `TauCeti.ModularGroup.ellipticThree_Gamma0Projective_eq_prod`,
  `TauCeti.ModularGroup.invariants_Gamma0Projective_two`, and
  `TauCeti.ModularGroup.invariants_Gamma0Projective_eleven`: closed forms and worked checks on
  `Γ₀(N)`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics
  228, Springer, 2005, §§2.4, 3.1, 3.7–3.8.
* S. Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago Press,
  1992, §4.3.
* R. A. Rankin, *Modular Forms and Functions*, Cambridge University Press, 1977, Chapter 1.
-/

public section

noncomputable section

open Equiv Equiv.Perm Function Matrix Matrix.ProjectiveSpecialLinearGroup MulAction OnePoint
  Subgroup UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.ModularGroup

variable {n : ℕ}

/-! ### Effective image in `PSL(2, ℝ)` and finite-CW compactification -/

/-- The effective image in `PSL(2, ℝ)` of the `SL(2, ℤ)`-lift `Γ'.liftSL` equals the direct
image of `Γ'` under `psl2zToPSL2R`. -/
theorem map_liftSL_sl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ)) :
    Γ'.liftSL.map sl2zToPSL2R = Γ'.map psl2zToPSL2R := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨(γ : PSL(2, ℤ)), Subgroup.mem_liftSL.mp hγ, psl2zToPSL2R_mk γ⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨γ, Subgroup.mem_liftSL.mpr hg, (psl2zToPSL2R_mk γ).symm⟩

private theorem finiteIndex_of_equiv {Γ' : Subgroup PSL(2, ℤ)}
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Γ'.FiniteIndex :=
  have : Finite (PSL(2, ℤ) ⧸ Γ') := Finite.of_equiv _ e.symm
  Subgroup.finiteIndex_of_finite_quotient

private theorem index_eq_of_equiv {Γ' : Subgroup PSL(2, ℤ)} (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Γ'.index = n := by
  rw [Subgroup.index_eq_card, Nat.card_congr e, Nat.card_fin]

/-- The relative index of `Γ'.map psl2zToPSL2R` inside the effective level-one group
`psl2zToPSL2R.range` equals the index of `Γ'` in `PSL(2, ℤ)`. -/
theorem relIndex_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ)) :
    (Γ'.map psl2zToPSL2R).relIndex psl2zToPSL2R.range = Γ'.index := by
  rw [← map_liftSL_sl2zToPSL2R, Subgroup.relIndex_map_sl2zToPSL2R,
    Subgroup.withCenter_eq_self_iff.mpr (Subgroup.center_le_liftSL Γ'), Subgroup.index_liftSL]

/-- The image in `PSL(2, ℝ)` of a finite-index subgroup of `PSL(2, ℤ)` has finite relative index
in `psl2zToPSL2R.range`. -/
theorem isFiniteRelIndex_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    (Γ'.map psl2zToPSL2R).IsFiniteRelIndex psl2zToPSL2R.range :=
  ⟨(relIndex_map_psl2zToPSL2R Γ').symm ▸ Subgroup.FiniteIndex.index_ne_zero⟩

/-- The image in `PSL(2, ℝ)` of a finite-index subgroup of `PSL(2, ℤ)` is cofinite. -/
theorem isCofinite_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    (Γ'.map psl2zToPSL2R).IsCofinite := by
  rw [← map_liftSL_sl2zToPSL2R]
  exact Γ'.liftSL.isCofinite_map_sl2zToPSL2R

/-- The compactified modular curve `X(Γ')` of a finite-index subgroup `Γ' ≤ PSL(2, ℤ)` is
compact. -/
theorem compactSpace_compactifiedQuotient_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ))
    [Γ'.FiniteIndex] :
    CompactSpace (Γ'.map psl2zToPSL2R).CompactifiedQuotient :=
  (isCofinite_map_psl2zToPSL2R Γ').compactSpace_compactifiedQuotient

/-- The compactified modular curve `X(Γ')` of a finite-index subgroup `Γ' ≤ PSL(2, ℤ)` has
finite CW type, as a compact Riemann surface. -/
instance finiteCWType_compactifiedQuotient_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ))
    [Γ'.FiniteIndex] :
    FiniteCWType (Γ'.map psl2zToPSL2R).CompactifiedQuotient :=
  have := compactSpace_compactifiedQuotient_map_psl2zToPSL2R Γ'
  inferInstance

/-! ### Cusp widths -/

/-- The `permT`-period of the identity coset agrees with `TauCeti.Subgroup.integerCuspWidth` of
the `SL(2, ℤ)`-lift `Γ'.liftSL`. -/
theorem minimalPeriod_permT_one_eq_integerCuspWidth (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      TauCeti.Subgroup.integerCuspWidth (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) := by
  refine Nat.dvd_right_iff_eq.mp fun m ↦ ?_
  have h1 : (((1 : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') =
      ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') := rfl
  rw [← h1, minimalPeriod_permT_mk_dvd_iff, inv_one, one_mul, mul_one,
    ← TauCeti.Subgroup.T_pow_mem_iff, Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← map_pow,
    Subgroup.mem_map_iff_mem Matrix.SpecialLinearGroup.mapGL_injective]

/-- The strict period subgroup of `Γ'.liftSL` in `GL(2, ℝ)` is generated by the `permT`-period of
the identity coset. -/
theorem strictPeriods_liftSL_eq_zmultiples (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Subgroup.strictPeriods (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) =
      AddSubgroup.zmultiples
        (minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) := by
  have h1 : (((1 : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') =
      ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') := rfl
  ext x
  rw [Subgroup.mem_strictPeriods_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨γ, hγ, hmat⟩
    have hentry (i j : Fin 2) :
        ((γ i j : ℤ) : ℝ) = (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
      have h := congr_fun (congr_fun (congrArg (fun g : GL (Fin 2) ℝ ↦
        (g : Matrix (Fin 2) (Fin 2) ℝ)) hmat) i) j
      simpa only [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
        algebraMap_int_eq, Int.coe_castRingHom,
        Matrix.GeneralLinearGroup.upperRightHom_apply] using h
    have h00 : γ 0 0 = 1 := by
      have h := hentry 0 0
      simp only [Matrix.of_apply, Matrix.cons_val_zero] at h
      exact_mod_cast h
    have h10 : γ 1 0 = 0 := by
      have h := hentry 1 0
      simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at h
      exact_mod_cast h
    have h11 : γ 1 1 = 1 := by
      have h := hentry 1 1
      simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      exact_mod_cast h
    have h01 : (γ 0 1 : ℝ) = x := by
      have h := hentry 0 1
      simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using h
    have hγT : γ = _root_.ModularGroup.T ^ (γ 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h10, h11, _root_.ModularGroup.coe_T_zpow]
    have hTmem : _root_.ModularGroup.T ^ (γ 0 1).natAbs ∈ Γ'.liftSL := by
      rcases Int.natAbs_eq (γ 0 1) with heq | heq
      · rwa [← zpow_natCast, ← heq, ← hγT]
      · have hneg : -(γ 0 1) = ((γ 0 1).natAbs : ℤ) := by omega
        rw [← zpow_natCast, ← hneg, _root_.zpow_neg, inv_mem_iff, ← hγT]
        exact hγ
    have hdvd_nat :
        minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) ∣
          (γ 0 1).natAbs := by
      rw [← h1, minimalPeriod_permT_mk_dvd_iff, inv_one, one_mul, mul_one]
      exact hTmem
    obtain ⟨k, hk⟩ := Int.natCast_dvd.mpr hdvd_nat
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, ← h01, hk, mul_comm]
    push_cast
    rfl
  · rintro ⟨k, rfl⟩
    set h := minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'))
    have hTpow : _root_.ModularGroup.T ^ h ∈ Γ'.liftSL := by
      have hmem := (minimalPeriod_permT_mk_dvd_iff Γ' e 1 h).mp (by rw [h1])
      simpa using hmem
    refine ⟨(_root_.ModularGroup.T ^ h) ^ k, zpow_mem hTpow k, ?_⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, ModularGroup.mapGL_T_zpow_eq_upperRightHom]
    congr 1
    rw [zsmul_eq_mul, mul_comm]
    push_cast
    rfl

/-- The `permT`-period of the identity coset agrees with Mathlib's `Subgroup.strictWidthInfty` of
`Γ'.liftSL`. -/
theorem natCast_minimalPeriod_permT_one_eq_strictWidthInfty (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) =
      Subgroup.strictWidthInfty (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) :=
  (Subgroup.strictWidthInfty_eq_of_strictPeriods_eq_zmultiples
    (strictPeriods_liftSL_eq_zmultiples Γ' e) (Nat.cast_nonneg _)).symm

/-- The `permT`-period of the identity coset agrees with Mathlib's `Subgroup.widthInfty` of
`Γ'.liftSL` (which is regular at `∞` because `-I ∈ Γ'.liftSL`). -/
theorem natCast_minimalPeriod_permT_one_eq_widthInfty (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) =
      Subgroup.widthInfty (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) := by
  have hneg : (-1 : GL (Fin 2) ℝ) ∈ (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) :=
    ⟨-1, Subgroup.neg_one_mem_liftSL Γ', by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  rw [Subgroup.widthInfty, Subgroup.adjoinNegOne_eq_self_iff.mpr hneg,
    natCast_minimalPeriod_permT_one_eq_strictWidthInfty]

/-- At every coset `σ : SL(2, ℤ)`, the `permT`-period equals the cusp translation orbit width of
`TauCeti.ModularForm.cuspTranslationOrbitWidth` for `Γ'.liftSL`. -/
theorem minimalPeriod_permT_mk_eq_cuspTranslationOrbitWidth (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ)) :
    minimalPeriod (permT Γ' e) (e ((σ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      ModularForm.cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict σ) :
          𝒮ℒ ⧸ (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            ModularForm.CuspTranslationOrbit (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ))) :=
  Nat.dvd_right_iff_eq.mp fun m ↦
    (minimalPeriod_permT_mk_dvd_iff Γ' e σ m).trans
      (ModularForm.cuspTranslationOrbitWidth_mk_dvd_iff σ m).symm

/-- At every cusp `σ • ∞`, the `permT`-period of the coset `σ⁻¹ Γ'` equals the width
`D.width` of any normalized Fuchsian cusp datum `D` for `Γ'.map psl2zToPSL2R` with scaling
`psl2zToPSL2R σ⁻¹`. -/
theorem natCast_minimalPeriod_permT_eq_cuspDatum_width (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ))
    (D : (Γ'.map psl2zToPSL2R).CuspDatum)
    (hσ : D.scaling = psl2zToPSL2R ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))) :
    (minimalPeriod (permT Γ' e)
      (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) = D.width := by
  set h :=
    minimalPeriod (permT Γ' e) (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'))
  obtain ⟨g, hg, hgen⟩ := D.generator.property
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  have hγ : γ ∈ Γ'.liftSL := Subgroup.mem_liftSL.mpr hg
  have hconj_eq : sl2zToPSL2R (σ⁻¹ * γ * σ) = upperRightHom D.width := by
    have hconj := D.scaling_mul_generator_mul_inv
    rw [hσ, ← hgen, psl2zToPSL2R_mk, psl2zToPSL2R_mk, ← map_inv, ← map_mul, ← map_mul,
      inv_inv] at hconj
    exact hconj
  have hc0 : (σ⁻¹ * γ * σ) 1 0 = 0 := by
    have h0 := (TauCeti.UpperHalfPlane.entries_of_coe_eq_upperRightHom
      ((sl2zToPSL2R_apply _).symm.trans hconj_eq)).1
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Int.coe_castRingHom] at h0
    exact_mod_cast h0
  set b : ℤ := (σ⁻¹ * γ * σ) 0 1
  obtain ⟨k, hk_eq, hk_mem⟩ : ∃ k : ℤ, (k : ℝ) = D.width ∧
      σ * _root_.ModularGroup.T ^ k * σ⁻¹ ∈ Γ'.liftSL := by
    rcases eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc0 with hT | hT
    · refine ⟨b, ?_, ?_⟩
      · have h1 : upperRightHom (b : ℝ) = upperRightHom D.width := by
          rw [← TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow, ← hT, hconj_eq]
        exact upperRightHom_injective h1
      · have h2 : σ * _root_.ModularGroup.T ^ b * σ⁻¹ = γ := by
          rw [← hT]
          group
        rwa [h2]
    · refine ⟨-b, ?_, ?_⟩
      · have h1 : upperRightHom ((-b : ℤ) : ℝ) = upperRightHom D.width := by
          rw [← TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow, ← sl2zToPSL2R_neg, ← hT, hconj_eq]
        exact upperRightHom_injective h1
      · have h2 : σ * _root_.ModularGroup.T ^ (-b) * σ⁻¹ = -γ := by
          have hT' : -(σ⁻¹ * γ * σ) = _root_.ModularGroup.T ^ (-b) := by
            conv_lhs => rw [hT]
            rw [neg_neg]
          rw [← hT', mul_neg, neg_mul]
          congr 1
          group
        rw [h2, ← neg_one_mul]
        exact mul_mem (Subgroup.neg_one_mem_liftSL Γ') hγ
  have hk_pos : (0 : ℤ) < k := by
    have : (0 : ℝ) < (k : ℝ) := hk_eq.symm ▸ D.width_pos
    exact_mod_cast this
  set m : ℕ := k.toNat
  have hm_eq : (m : ℤ) = k := Int.toNat_of_nonneg hk_pos.le
  have hm_real : (m : ℝ) = D.width := by
    rw [← hk_eq, ← hm_eq, Int.cast_natCast]
  have hdvd1 : h ∣ m := by
    rw [minimalPeriod_permT_mk_dvd_iff, inv_inv, ← zpow_natCast, hm_eq]
    exact hk_mem
  have hTh_mem : σ * _root_.ModularGroup.T ^ h * σ⁻¹ ∈ Γ'.liftSL := by
    have h1 := (minimalPeriod_permT_mk_dvd_iff Γ' e σ⁻¹ h).mp dvd_rfl
    rwa [inv_inv] at h1
  let gh : Γ'.map psl2zToPSL2R :=
    ⟨psl2zToPSL2R ((σ * _root_.ModularGroup.T ^ h * σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)),
      Subgroup.mem_map_of_mem psl2zToPSL2R (Subgroup.mem_liftSL.mp hTh_mem)⟩
  have hgh_conj : D.scaling * (gh : PSL(2, ℝ)) * D.scaling⁻¹ = upperRightHom (h : ℝ) := by
    dsimp only [gh]
    rw [hσ, psl2zToPSL2R_mk, psl2zToPSL2R_mk, ← map_inv, ← map_mul, ← map_mul, inv_inv]
    have hcancel : σ⁻¹ * (σ * _root_.ModularGroup.T ^ h * σ⁻¹) * σ =
        _root_.ModularGroup.T ^ (h : ℤ) := by
      rw [zpow_natCast]
      group
    rw [hcancel, TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow, Int.cast_natCast]
  have hgh_stab : gh ∈ stabilizer (Γ'.map psl2zToPSL2R) D.cusp := by
    rw [mem_stabilizer_iff]
    apply MulAction.injective D.scaling
    dsimp only
    rw [Subgroup.smul_def, ← mul_smul,
      show D.scaling * (gh : PSL(2, ℝ)) = (D.scaling * gh * D.scaling⁻¹) * D.scaling by group,
      mul_smul, D.scaling_smul_cusp, hgh_conj, upperRightHom_smul_infty]
  obtain ⟨r, hr⟩ := D.mem_stabilizer_iff.mp hgh_stab
  have hr_eq : (r : ℝ) * D.width = (h : ℝ) := by
    have h1 := D.scaling_mul_generator_zpow_mul_inv r
    rw [← Subgroup.coe_zpow, hr, hgh_conj] at h1
    exact (upperRightHom_injective h1).symm
  have hdvd2 : m ∣ h := by
    rw [← hm_real] at hr_eq
    have hr_int : r * (m : ℤ) = (h : ℤ) := by exact_mod_cast hr_eq
    exact Int.natCast_dvd_natCast.mp ⟨r, by linarith⟩
  rw [Nat.dvd_antisymm hdvd1 hdvd2, hm_real]

/-! ### Cusp orbits -/

private theorem psl2zToPSL2R_smul_boundary (a : SL(2, ℤ)) (c : OnePoint ℝ) :
    psl2zToPSL2R (a : PSL(2, ℤ)) • c = Matrix.SpecialLinearGroup.mapGL ℝ a • c := by
  rw [psl2zToPSL2R_mk, sl2zToPSL2R_apply, OnePoint.pslMk_smul]
  rfl

private theorem psl2zToPSL2R_smul_infty_eq_infty_iff (g : PSL(2, ℤ)) :
    psl2zToPSL2R g • (∞ : OnePoint ℝ) = ∞ ↔
      ∃ k : ℤ, g = (_root_.ModularGroup.T : PSL(2, ℤ)) ^ k := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [psl2zToPSL2R_mk, TauCeti.sl2zToPSL2R_smul_infty_eq_infty_iff]
  constructor
  · intro hc
    set b : ℤ := γ 0 1
    rcases eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hT | hT
    · refine ⟨b, ?_⟩
      rw [hT, QuotientGroup.mk_zpow]
    · refine ⟨-b, ?_⟩
      rw [hT, mk_neg, QuotientGroup.mk_zpow]
  · rintro ⟨k, hk⟩
    have hpsl : ((γ : SL(2, ℤ)) : PSL(2, ℤ)) =
        ((_root_.ModularGroup.T ^ k : SL(2, ℤ)) : PSL(2, ℤ)) := by
      simpa only [QuotientGroup.mk_zpow] using hk
    rcases mk_eq_mk_iff.mp hpsl with hmat | hmat
    · rw [← hmat, _root_.ModularGroup.coe_T_zpow]
      rfl
    · have hmat' : γ = -(_root_.ModularGroup.T ^ k) := by
        rw [← neg_neg γ, ← hmat]
      rw [hmat', Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply,
        _root_.ModularGroup.coe_T_zpow]
      simp

private theorem isCuspPoint_map_psl2zToPSL2R_smul_infty (Γ' : Subgroup PSL(2, ℤ))
    [Γ'.FiniteIndex] (g : PSL(2, ℤ)) :
    (Γ'.map psl2zToPSL2R).IsCuspPoint (psl2zToPSL2R g • (∞ : OnePoint ℝ)) := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← map_liftSL_sl2zToPSL2R, psl2zToPSL2R_mk]
  exact Γ'.liftSL.isCuspPoint_map_sl2zToPSL2R_smul_infty γ

private noncomputable def cosetRep {Γ' : Subgroup PSL(2, ℤ)} (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (x : Fin n) : PSL(2, ℤ) :=
  Quotient.out (e.symm x)

private theorem coe_cosetRep {Γ' : Subgroup PSL(2, ℤ)} (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (x : Fin n) :
    (cosetRep e x : PSL(2, ℤ) ⧸ Γ') = e.symm x :=
  Quotient.out_eq (e.symm x)

private theorem apply_cosetRep {Γ' : Subgroup PSL(2, ℤ)} (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (x : Fin n) :
    e (cosetRep e x : PSL(2, ℤ) ⧸ Γ') = x := by
  rw [coe_cosetRep, e.apply_symm_apply]

/-- **Cusp orbits via `permT`-cycles.** The cycles of `permT Γ' e` are in canonical bijection with
the Fuchsian cusp orbits `(Γ'.map psl2zToPSL2R).CuspOrbit`: the cycle of `e (g Γ')` maps to the
cusp orbit of `psl2zToPSL2R g⁻¹ • ∞`. -/
def permTCycleEquivFuchsianCuspOrbit (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃ (Γ'.map psl2zToPSL2R).CuspOrbit :=
  haveI : Γ'.FiniteIndex := finiteIndex_of_equiv e
  have key : ∀ g₁ g₂ : PSL(2, ℤ),
      (Γ'.map psl2zToPSL2R).cuspOrbitMk
          ⟨psl2zToPSL2R g₁⁻¹ • ∞,
            Subgroup.mem_cuspPoints.mpr (isCuspPoint_map_psl2zToPSL2R_smul_infty Γ' g₁⁻¹)⟩ =
        (Γ'.map psl2zToPSL2R).cuspOrbitMk
          ⟨psl2zToPSL2R g₂⁻¹ • ∞,
            Subgroup.mem_cuspPoints.mpr
              (isCuspPoint_map_psl2zToPSL2R_smul_infty Γ' g₂⁻¹)⟩ ↔
        SameCycle (permT Γ' e)
          (e (g₁ : PSL(2, ℤ) ⧸ Γ')) (e (g₂ : PSL(2, ℤ) ⧸ Γ')) := by
    intro g₁ g₂
    rw [Subgroup.cuspOrbitMk_eq_iff, mem_orbit_iff]
    constructor
    · rintro ⟨⟨_, h, hh, rfl⟩, hsmul⟩
      have hfix : psl2zToPSL2R (g₁ * h * g₂⁻¹) • (∞ : OnePoint ℝ) = ∞ := by
        rw [map_mul, map_mul, mul_smul, mul_smul, Subgroup.smul_def] at *
        have h' : psl2zToPSL2R h • psl2zToPSL2R g₂⁻¹ • (∞ : OnePoint ℝ) =
            psl2zToPSL2R g₁⁻¹ • ∞ := hsmul
        rw [h', ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
      obtain ⟨k, hk⟩ := (psl2zToPSL2R_smul_infty_eq_infty_iff _).mp hfix
      refine ⟨-k, ?_⟩
      rw [permT_zpow_apply, e.apply_eq_iff_eq, QuotientGroup.eq]
      have hmem : ((_root_.ModularGroup.T : PSL(2, ℤ)) ^ (-k) * g₁)⁻¹ * g₂ = h := by
        rw [_root_.mul_inv_rev, _root_.zpow_neg, inv_inv, mul_assoc, ← hk]
        group
      rwa [hmem]
    · rintro ⟨k, hk⟩
      rw [permT_zpow_apply, e.apply_eq_iff_eq, QuotientGroup.eq] at hk
      set h : PSL(2, ℤ) := ((_root_.ModularGroup.T : PSL(2, ℤ)) ^ k * g₁)⁻¹ * g₂
      have hh : h ∈ Γ' := hk
      refine ⟨⟨psl2zToPSL2R h, Subgroup.mem_map_of_mem _ hh⟩, ?_⟩
      have hmul : g₁ * h * g₂⁻¹ = (_root_.ModularGroup.T : PSL(2, ℤ)) ^ (-k) := by
        dsimp only [h]
        rw [_root_.mul_inv_rev, _root_.zpow_neg]
        group
      have hfix : psl2zToPSL2R (g₁ * h * g₂⁻¹) • (∞ : OnePoint ℝ) = ∞ :=
        (psl2zToPSL2R_smul_infty_eq_infty_iff _).mpr ⟨-k, hmul⟩
      have hinv := congrArg (psl2zToPSL2R g₁⁻¹ • ·) hfix
      rw [← mul_smul, ← map_mul,
        show g₁⁻¹ * (g₁ * h * g₂⁻¹) = h * g₂⁻¹ by group, map_mul, mul_smul] at hinv
      exact hinv
  let toFunAux : Fin n → (Γ'.map psl2zToPSL2R).CuspOrbit := fun x ↦
    (Γ'.map psl2zToPSL2R).cuspOrbitMk
      ⟨psl2zToPSL2R (cosetRep e x)⁻¹ • ∞,
        Subgroup.mem_cuspPoints.mpr (isCuspPoint_map_psl2zToPSL2R_smul_infty Γ' _)⟩
  have htoFunAux_eq : ∀ x y : Fin n,
      toFunAux x = toFunAux y ↔ SameCycle (permT Γ' e) x y := fun x y ↦ by
    simpa only [apply_cosetRep] using key (cosetRep e x) (cosetRep e y)
  Equiv.ofBijective
    (Quotient.lift toFunAux fun _ _ h ↦ (htoFunAux_eq _ _).mpr h)
    ⟨fun a b hab ↦ by
      induction a using Quotient.inductionOn with | h x =>
      induction b using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((htoFunAux_eq x y).mp hab),
    fun C ↦ by
      obtain ⟨c, rfl⟩ := Subgroup.cuspOrbitMk_surjective C
      have hc : (Γ'.liftSL.map sl2zToPSL2R).IsCuspPoint c.1 := by
        rw [map_liftSL_sl2zToPSL2R]
        exact Subgroup.mem_cuspPoints.mp c.2
      have hrat := (Γ'.liftSL.isCuspPoint_map_sl2zToPSL2R_iff_orbit_infty c.1).mp hc
      obtain ⟨⟨_, g, rfl⟩, hg⟩ := mem_orbit_iff.mp hrat
      let x : Fin n := e ((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')
      refine ⟨⟦x⟧, ?_⟩
      have hcusp : toFunAux x =
          (Γ'.map psl2zToPSL2R).cuspOrbitMk
            ⟨psl2zToPSL2R (g⁻¹)⁻¹ • ∞,
              Subgroup.mem_cuspPoints.mpr (isCuspPoint_map_psl2zToPSL2R_smul_infty Γ' _)⟩ :=
        (key (cosetRep e x) g⁻¹).mpr (by rw [apply_cosetRep])
      change toFunAux x = _
      rw [hcusp, inv_inv]
      congr 1
      exact Subtype.ext hg⟩

/-- Evaluating `permTCycleEquivFuchsianCuspOrbit` on the cycle of `e (g Γ')` gives the Fuchsian
cusp orbit of `psl2zToPSL2R g⁻¹ • ∞`. -/
theorem permTCycleEquivFuchsianCuspOrbit_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    ((permTCycleEquivFuchsianCuspOrbit Γ' e
        ⟦e (g : PSL(2, ℤ) ⧸ Γ')⟧ : (Γ'.map psl2zToPSL2R).CuspOrbit) :
        (Γ'.map psl2zToPSL2R).BoundaryOrbit) =
      Quotient.mk'' (psl2zToPSL2R g⁻¹ • (∞ : OnePoint ℝ)) := by
  have : Γ'.FiniteIndex := finiteIndex_of_equiv e
  set g₀ := cosetRep e (e (g : PSL(2, ℤ) ⧸ Γ'))
  change ((Γ'.map psl2zToPSL2R).cuspOrbitMk
      ⟨psl2zToPSL2R g₀⁻¹ • ∞, _⟩ : (Γ'.map psl2zToPSL2R).BoundaryOrbit) = _
  rw [Subgroup.cuspOrbitMk_val, Quotient.eq'', orbitRel_apply, mem_orbit_iff]
  have heq : (g₀ : PSL(2, ℤ) ⧸ Γ') = (g : PSL(2, ℤ) ⧸ Γ') := by
    dsimp only [g₀]
    rw [coe_cosetRep, e.symm_apply_apply]
  rw [QuotientGroup.eq] at heq
  refine ⟨⟨psl2zToPSL2R (g₀⁻¹ * g), Subgroup.mem_map_of_mem _ heq⟩, ?_⟩
  rw [Subgroup.smul_def, ← mul_smul, ← map_mul, mul_inv_cancel_right]

/-- The combinatorial cusp count equals the number of Fuchsian cusp orbits of
`Γ'.map psl2zToPSL2R`. -/
theorem cuspCount_eq_card_fuchsianCuspOrbit (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = Nat.card (Γ'.map psl2zToPSL2R).CuspOrbit := by
  rw [cuspCount_def, orbitCount_def,
    Nat.card_congr (permTCycleEquivFuchsianCuspOrbit Γ' e)]

private theorem isCuspPoint_map_psl2zToPSL2R_iff_isCusp (Γ' : Subgroup PSL(2, ℤ))
    [Γ'.FiniteIndex] (c : OnePoint ℝ) :
    (Γ'.map psl2zToPSL2R).IsCuspPoint c ↔
      IsCusp c (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) := by
  have hle : (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
    Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _
  have hrel : (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ ≠ 0 := by
    rw [← Subgroup.index_comap,
      Subgroup.comap_map_eq_self_of_injective Matrix.SpecialLinearGroup.mapGL_injective]
    exact Subgroup.FiniteIndex.index_ne_zero
  rw [← map_liftSL_sl2zToPSL2R, Γ'.liftSL.isCuspPoint_map_sl2zToPSL2R_iff_rat,
    isCusp_iff_of_relIndex_ne_zero hle hrel, isCusp_SL2Z_iff]

/-- **Fuchsian vs. Mathlib cusp orbits.** For a finite-index `Γ' ≤ PSL(2, ℤ)`, the Fuchsian
cusp orbits `(Γ'.map psl2zToPSL2R).CuspOrbit` are in canonical bijection with Mathlib's
`CuspOrbits Γ'.liftSL`. -/
def fuchsianCuspOrbitEquivCuspOrbits (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    (Γ'.map psl2zToPSL2R).CuspOrbit ≃ CuspOrbits (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) :=
  have horb : ∀ c₁ c₂ : OnePoint ℝ,
      c₁ ∈ orbit (Γ'.map psl2zToPSL2R) c₂ ↔
        c₁ ∈ orbit (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) c₂ := by
    intro c₁ c₂
    simp only [mem_orbit_iff, Subtype.exists, Subgroup.smul_def]
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, hsmul⟩
      obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
      refine ⟨Matrix.SpecialLinearGroup.mapGL ℝ γ,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_liftSL.mpr hg), ?_⟩
      rwa [← psl2zToPSL2R_smul_boundary]
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, hsmul⟩
      refine ⟨psl2zToPSL2R (γ : PSL(2, ℤ)),
        Subgroup.mem_map_of_mem _ (Subgroup.mem_liftSL.mp hγ), ?_⟩
      rwa [psl2zToPSL2R_smul_boundary]
  let invFun : CuspOrbits (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) →
      (Γ'.map psl2zToPSL2R).CuspOrbit :=
    Quotient.lift
      (fun c ↦ (Γ'.map psl2zToPSL2R).cuspOrbitMk
        ⟨c.1, Subgroup.mem_cuspPoints.mpr
          ((isCuspPoint_map_psl2zToPSL2R_iff_isCusp Γ' c.1).mpr
            (mem_cuspsSubMulAction.mp c.2))⟩)
      (fun c₁ c₂ h ↦ by
        rw [Subgroup.cuspOrbitMk_eq_iff, horb]
        obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
        exact mem_orbit_iff.mpr ⟨g, congrArg Subtype.val hg⟩)
  (Equiv.ofBijective invFun
    ⟨fun a b hab ↦ by
      induction a using Quotient.inductionOn with | h c₁ =>
      induction b using Quotient.inductionOn with | h c₂ =>
      change (Γ'.map psl2zToPSL2R).cuspOrbitMk _ = (Γ'.map psl2zToPSL2R).cuspOrbitMk _ at hab
      rw [Subgroup.cuspOrbitMk_eq_iff, horb, mem_orbit_iff] at hab
      obtain ⟨g, hg⟩ := hab
      exact Quotient.sound (orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨g, Subtype.ext hg⟩)),
    fun C ↦ by
      obtain ⟨c, rfl⟩ := Subgroup.cuspOrbitMk_surjective C
      exact ⟨Quotient.mk'' ⟨c.1, mem_cuspsSubMulAction.mpr
        ((isCuspPoint_map_psl2zToPSL2R_iff_isCusp Γ' c.1).mp
          (Subgroup.mem_cuspPoints.mp c.2))⟩, rfl⟩⟩).symm

/-- The cycles of `permT Γ' e` are in bijection with Mathlib's `CuspOrbits Γ'.liftSL`. -/
def permTCycleEquivCuspOrbits (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃
      CuspOrbits (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) :=
  haveI : Γ'.FiniteIndex := finiteIndex_of_equiv e
  (permTCycleEquivFuchsianCuspOrbit Γ' e).trans (fuchsianCuspOrbitEquivCuspOrbits Γ')

/-- The combinatorial cusp count equals the cardinality of Mathlib's `CuspOrbits Γ'.liftSL`. -/
theorem cuspCount_eq_card_cuspOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = Nat.card (CuspOrbits (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ))) := by
  rw [cuspCount_def, orbitCount_def, Nat.card_congr (permTCycleEquivCuspOrbits Γ' e)]

/-! ### Elliptic orbits -/

private theorem inv_mul_eq_of_mul_mul_inv_eq {G : Type*} [Group G] {g₁ g₂ h s : G}
    (heq : g₁ * h * g₂⁻¹ = s) : g₁⁻¹ * g₂ = h * (g₂⁻¹ * s⁻¹ * g₂) := by
  rw [← heq]
  group

private theorem coe_T_inv_mul_S_eq_coe_R_inv :
    ((_root_.ModularGroup.T⁻¹ * _root_.ModularGroup.S : SL(2, ℤ)) : PSL(2, ℤ)) =
      (R : PSL(2, ℤ))⁻¹ := by
  rw [R_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    _root_.mul_inv_rev, _root_.ModularGroup.S_inv_PSL2Z]

private theorem cardStabilizerOnOrbit_mk_inv_smul_I (Γ' : Subgroup PSL(2, ℤ)) (g : PSL(2, ℤ))
    (hg : g⁻¹ * (_root_.ModularGroup.S : PSL(2, ℤ)) * g ∈ Γ') :
    cardStabilizerOnOrbit
        (Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • I)) = 2 := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  have hmem : σ⁻¹ * _root_.ModularGroup.S * σ ∈ Γ'.liftSL := by
    rw [Subgroup.mem_liftSL, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hg
  rw [cardStabilizerOnOrbit_mk, ← map_liftSL_sl2zToPSL2R]
  have hsmul : ((σ : PSL(2, ℤ))⁻¹ • (I : ℍ)) = σ⁻¹ • I := by
    rw [← QuotientGroup.mk_inv, UpperHalfPlane.pslMk_smul]
  rw [hsmul, Γ'.liftSL.card_stabilizer_map_smul_I σ⁻¹]
  simp [hmem]

private theorem cardStabilizerOnOrbit_mk_inv_smul_ρ (Γ' : Subgroup PSL(2, ℤ)) (g : PSL(2, ℤ))
    (hg : g⁻¹ * (R : PSL(2, ℤ)) * g ∈ Γ') :
    cardStabilizerOnOrbit
        (Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • ρ)) = 3 := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  have hmem :
      σ⁻¹ * (_root_.ModularGroup.T⁻¹ * _root_.ModularGroup.S) * σ ∈ Γ'.liftSL := by
    have hconj :
        ((σ⁻¹ * (_root_.ModularGroup.T⁻¹ * _root_.ModularGroup.S) * σ : SL(2, ℤ)) :
          PSL(2, ℤ)) =
        (((σ : PSL(2, ℤ))⁻¹ * (R : PSL(2, ℤ)) * (σ : PSL(2, ℤ)))⁻¹) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        coe_T_inv_mul_S_eq_coe_R_inv]
      group
    rw [Subgroup.mem_liftSL, hconj, inv_mem_iff]
    exact hg
  rw [cardStabilizerOnOrbit_mk, ← map_liftSL_sl2zToPSL2R]
  have hsmul : ((σ : PSL(2, ℤ))⁻¹ • (ρ : ℍ)) = σ⁻¹ • ρ := by
    rw [← QuotientGroup.mk_inv, UpperHalfPlane.pslMk_smul]
  rw [hsmul, Γ'.liftSL.card_stabilizer_map_smul_ρ σ⁻¹]
  simp [hmem]

/-- **Order-`2` elliptic orbits via fixed points of `permS`.** The fixed points of `permS Γ' e`
are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having stabilizer
order `2`: the fixed point `e (g Γ')` maps to the orbit of `g⁻¹ • i`. -/
def fixedPermSEquivOrderTwoEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    {x : Fin n // permS Γ' e x = x} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} :=
  let toFun : {x : Fin n // permS Γ' e x = x} →
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} :=
    fun ⟨x, hx⟩ ↦
      let g := cosetRep e x
      have hS : g⁻¹ * (_root_.ModularGroup.S : PSL(2, ℤ)) * g ∈ Γ' :=
        (permS_apply_eq_self_iff Γ' e g).mp ((apply_cosetRep e x).symm ▸ hx)
      ⟨Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • I),
        cardStabilizerOnOrbit_mk_inv_smul_I Γ' g hS⟩
  Equiv.ofBijective toFun
    ⟨fun ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ hq ↦ by
      set g₁ := cosetRep e x₁
      set g₂ := cosetRep e x₂
      have hg₁ : e (g₁ : PSL(2, ℤ) ⧸ Γ') = x₁ := apply_cosetRep e x₁
      have hg₂ : e (g₂ : PSL(2, ℤ) ⧸ Γ') = x₂ := apply_cosetRep e x₂
      have hS₂ : g₂⁻¹ * (_root_.ModularGroup.S : PSL(2, ℤ)) * g₂ ∈ Γ' :=
        (permS_apply_eq_self_iff Γ' e g₂).mp (hg₂.symm ▸ hx₂)
      have horb : orbitRel (Γ'.map psl2zToPSL2R) ℍ (g₁⁻¹ • I) (g₂⁻¹ • I) :=
        Quotient.exact (congrArg Subtype.val hq)
      obtain ⟨⟨_, h, hh, rfl⟩, hsmul⟩ := mem_orbit_iff.mp (orbitRel_apply.mp horb)
      rw [Subgroup.smul_def, UpperHalfPlane.psl2zToPSL2R_smul] at hsmul
      have hfix : (g₁ * h * g₂⁻¹) • (I : ℍ) = I := by
        rw [mul_smul, mul_smul, hsmul, smul_inv_smul]
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (g₁ * h * g₂⁻¹)
      have haI : a • (I : ℍ) = I := by
        rwa [← UpperHalfPlane.pslMk_smul, ha]
      have ha_mem := _root_.ModularGroup.stabilizer_I.mp haI
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
      have hpsl : g₁ * h * g₂⁻¹ = 1 ∨
          g₁ * h * g₂⁻¹ = (_root_.ModularGroup.S : PSL(2, ℤ)) := by
        rcases ha_mem with rfl | rfl | rfl | rfl
        · exact Or.inl ha.symm
        · exact Or.inl (by rw [← ha, mk_neg]; rfl)
        · exact Or.inr ha.symm
        · exact Or.inr (by rw [← ha, mk_neg])
      have hg12 : g₁⁻¹ * g₂ ∈ Γ' := by
        rcases hpsl with heq | heq
        · rw [inv_mul_eq_of_mul_mul_inv_eq heq]
          simpa using hh
        · rw [inv_mul_eq_of_mul_mul_inv_eq heq, _root_.ModularGroup.S_inv_PSL2Z]
          exact mul_mem hh hS₂
      exact Subtype.ext (show x₁ = x₂ by rw [← hg₁, ← hg₂, QuotientGroup.eq.mpr hg12]),
    fun ⟨q, hq⟩ ↦ by
      induction q using Quotient.inductionOn with | h z =>
      rw [cardStabilizerOnOrbit_mk, ← map_liftSL_sl2zToPSL2R] at hq
      rcases Γ'.liftSL.exists_smul_eq_of_card_stabilizer_ne_one (z := z) (by omega) with
        ⟨γ, rfl, -⟩ | ⟨γ, -, h3⟩
      · have hS_sl : γ * _root_.ModularGroup.S * γ⁻¹ ∈ Γ'.liftSL := by
          rw [Γ'.liftSL.card_stabilizer_map_smul_I] at hq
          by_contra hnot
          simp [hnot] at hq
        let g : PSL(2, ℤ) := (γ⁻¹ : SL(2, ℤ))
        have hS_psl : g⁻¹ * (_root_.ModularGroup.S : PSL(2, ℤ)) * g ∈ Γ' := by
          have : g⁻¹ * (_root_.ModularGroup.S : PSL(2, ℤ)) * g =
              ((γ * _root_.ModularGroup.S * γ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) := by
            dsimp only [g]
            rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, inv_inv]
          rw [this]
          exact Subgroup.mem_liftSL.mp hS_sl
        let x : Fin n := e (g : PSL(2, ℤ) ⧸ Γ')
        have hx : permS Γ' e x = x := (permS_apply_eq_self_iff Γ' e g).mpr hS_psl
        refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
        dsimp only [toFun]
        set g₀ := cosetRep e x
        have heq : (g₀ : PSL(2, ℤ) ⧸ Γ') = (g : PSL(2, ℤ) ⧸ Γ') := by
          dsimp only [g₀, x]
          rw [coe_cosetRep, e.symm_apply_apply]
        rw [QuotientGroup.eq] at heq
        refine Quotient.sound (orbitRel_apply.mpr (mem_orbit_iff.mpr
          ⟨⟨psl2zToPSL2R (g₀⁻¹ * g), Subgroup.mem_map_of_mem _ heq⟩, ?_⟩))
        rw [Subgroup.smul_def, UpperHalfPlane.psl2zToPSL2R_smul, ← UpperHalfPlane.pslMk_smul,
          ← mul_smul]
        have hg_inv : (γ : PSL(2, ℤ)) = g⁻¹ := by
          dsimp only [g]
          rw [QuotientGroup.mk_inv, inv_inv]
        rw [hg_inv, mul_inv_cancel_right]
      · omega⟩

/-- **Order-`3` elliptic orbits via fixed points of `permR`.** The fixed points of `permR Γ' e`
are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having stabilizer
order `3`: the fixed point `e (g Γ')` maps to the orbit of `g⁻¹ • ρ`. -/
def fixedPermREquivOrderThreeEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    {x : Fin n // permR Γ' e x = x} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} :=
  let toFun : {x : Fin n // permR Γ' e x = x} →
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} :=
    fun ⟨x, hx⟩ ↦
      let g := cosetRep e x
      have hR : g⁻¹ * (R : PSL(2, ℤ)) * g ∈ Γ' :=
        (permR_apply_eq_self_iff Γ' e g).mp ((apply_cosetRep e x).symm ▸ hx)
      ⟨Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • ρ),
        cardStabilizerOnOrbit_mk_inv_smul_ρ Γ' g hR⟩
  Equiv.ofBijective toFun
    ⟨fun ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ hq ↦ by
      set g₁ := cosetRep e x₁
      set g₂ := cosetRep e x₂
      have hg₁ : e (g₁ : PSL(2, ℤ) ⧸ Γ') = x₁ := apply_cosetRep e x₁
      have hg₂ : e (g₂ : PSL(2, ℤ) ⧸ Γ') = x₂ := apply_cosetRep e x₂
      have hR₂ : g₂⁻¹ * (R : PSL(2, ℤ)) * g₂ ∈ Γ' :=
        (permR_apply_eq_self_iff Γ' e g₂).mp (hg₂.symm ▸ hx₂)
      have horb : orbitRel (Γ'.map psl2zToPSL2R) ℍ (g₁⁻¹ • ρ) (g₂⁻¹ • ρ) :=
        Quotient.exact (congrArg Subtype.val hq)
      obtain ⟨⟨_, h, hh, rfl⟩, hsmul⟩ := mem_orbit_iff.mp (orbitRel_apply.mp horb)
      rw [Subgroup.smul_def, UpperHalfPlane.psl2zToPSL2R_smul] at hsmul
      have hfix : (g₁ * h * g₂⁻¹) • (ρ : ℍ) = ρ := by
        rw [mul_smul, mul_smul, hsmul, smul_inv_smul]
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (g₁ * h * g₂⁻¹)
      have haρ : a • (ρ : ℍ) = ρ := by
        rwa [← UpperHalfPlane.pslMk_smul, ha]
      have ha_mem := _root_.ModularGroup.stabilizer_ρ.mp haρ
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
      have hpsl : g₁ * h * g₂⁻¹ = 1 ∨ g₁ * h * g₂⁻¹ = (R : PSL(2, ℤ)) ∨
          g₁ * h * g₂⁻¹ = (R : PSL(2, ℤ))⁻¹ := by
        rcases ha_mem with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl ha.symm
        · exact Or.inl (by rw [← ha, mk_neg]; rfl)
        · exact Or.inr (Or.inl (by rw [← ha, R_def]))
        · exact Or.inr (Or.inl (by rw [← ha, mk_neg, R_def]))
        · exact Or.inr (Or.inr (ha.symm.trans coe_T_inv_mul_S_eq_coe_R_inv))
        · exact Or.inr (Or.inr (by rw [← ha, mk_neg, coe_T_inv_mul_S_eq_coe_R_inv]))
      have hg12 : g₁⁻¹ * g₂ ∈ Γ' := by
        rcases hpsl with heq | heq | heq
        · rw [inv_mul_eq_of_mul_mul_inv_eq heq]
          simpa using hh
        · rw [inv_mul_eq_of_mul_mul_inv_eq heq,
            show g₂⁻¹ * (R : PSL(2, ℤ))⁻¹ * g₂ =
              (g₂⁻¹ * (R : PSL(2, ℤ)) * g₂)⁻¹ by group]
          exact mul_mem hh (inv_mem hR₂)
        · rw [inv_mul_eq_of_mul_mul_inv_eq heq, inv_inv]
          exact mul_mem hh hR₂
      exact Subtype.ext (show x₁ = x₂ by rw [← hg₁, ← hg₂, QuotientGroup.eq.mpr hg12]),
    fun ⟨q, hq⟩ ↦ by
      induction q using Quotient.inductionOn with | h z =>
      rw [cardStabilizerOnOrbit_mk, ← map_liftSL_sl2zToPSL2R] at hq
      rcases Γ'.liftSL.exists_smul_eq_of_card_stabilizer_ne_one (z := z) (by omega) with
        ⟨γ, -, h2⟩ | ⟨γ, rfl, -⟩
      · omega
      · have hR_sl :
            γ * (_root_.ModularGroup.T⁻¹ * _root_.ModularGroup.S) * γ⁻¹ ∈ Γ'.liftSL := by
          rw [Γ'.liftSL.card_stabilizer_map_smul_ρ] at hq
          by_contra hnot
          simp [hnot] at hq
        let g : PSL(2, ℤ) := (γ⁻¹ : SL(2, ℤ))
        have hR_psl : g⁻¹ * (R : PSL(2, ℤ)) * g ∈ Γ' := by
          have hconj :
              ((γ * (_root_.ModularGroup.T⁻¹ * _root_.ModularGroup.S) * γ⁻¹ : SL(2, ℤ)) :
                PSL(2, ℤ)) = (g⁻¹ * (R : PSL(2, ℤ)) * g)⁻¹ := by
            dsimp only [g]
            rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
              coe_T_inv_mul_S_eq_coe_R_inv]
            group
          have hmem :
              ((γ * (_root_.ModularGroup.T⁻¹ * _root_.ModularGroup.S) * γ⁻¹ : SL(2, ℤ)) :
                PSL(2, ℤ)) ∈ Γ' := Subgroup.mem_liftSL.mp hR_sl
          rw [hconj, inv_mem_iff] at hmem
          exact hmem
        let x : Fin n := e (g : PSL(2, ℤ) ⧸ Γ')
        have hx : permR Γ' e x = x := (permR_apply_eq_self_iff Γ' e g).mpr hR_psl
        refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
        dsimp only [toFun]
        set g₀ := cosetRep e x
        have heq : (g₀ : PSL(2, ℤ) ⧸ Γ') = (g : PSL(2, ℤ) ⧸ Γ') := by
          dsimp only [g₀, x]
          rw [coe_cosetRep, e.symm_apply_apply]
        rw [QuotientGroup.eq] at heq
        refine Quotient.sound (orbitRel_apply.mpr (mem_orbit_iff.mpr
          ⟨⟨psl2zToPSL2R (g₀⁻¹ * g), Subgroup.mem_map_of_mem _ heq⟩, ?_⟩))
        rw [Subgroup.smul_def, UpperHalfPlane.psl2zToPSL2R_smul, ← UpperHalfPlane.pslMk_smul,
          ← mul_smul]
        have hg_inv : (γ : PSL(2, ℤ)) = g⁻¹ := by
          dsimp only [g]
          rw [QuotientGroup.mk_inv, inv_inv]
        rw [hg_inv, mul_inv_cancel_right]⟩

/-- The combinatorial count `ellipticTwo` equals the number of order-`2` elliptic orbits of
`Γ'.map psl2zToPSL2R` on `ℍ`. -/
theorem ellipticTwo_eq_card_orderTwoEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e =
      Nat.card {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
        cardStabilizerOnOrbit q = 2} := by
  rw [ellipticTwo_def, ← Nat.card_eq_fintype_card,
    Nat.card_congr (fixedPermSEquivOrderTwoEllipticOrbits Γ' e)]

/-- The combinatorial count `ellipticThree` equals the number of order-`3` elliptic orbits of
`Γ'.map psl2zToPSL2R` on `ℍ`. -/
theorem ellipticThree_eq_card_orderThreeEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e =
      Nat.card {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
        cardStabilizerOnOrbit q = 3} := by
  rw [ellipticThree_eq_card_fixed_permR, ← Nat.card_eq_fintype_card,
    Nat.card_congr (fixedPermREquivOrderThreeEllipticOrbits Γ' e)]

/-- **The elliptic orbifold defect sum.** For any finite-index `Γ' ≤ PSL(2, ℤ)`, every elliptic
orbit has stabilizer order `2` or `3`, so `∑ₑ (1 - 1 / mₑ) = ε₂ / 2 + 2 ε₃ / 3`. -/
theorem finsum_mem_ellipticOrbits_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ∑ᶠ q ∈ (Γ'.map psl2zToPSL2R).ellipticOrbits, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) =
      (ellipticTwo Γ' e : ℝ) / 2 + 2 * (ellipticThree Γ' e : ℝ) / 3 := by
  set S₂ : Set (orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ) :=
    {q | cardStabilizerOnOrbit q = 2}
  set S₃ : Set (orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ) :=
    {q | cardStabilizerOnOrbit q = 3}
  have hunion : (Γ'.map psl2zToPSL2R).ellipticOrbits = S₂ ∪ S₃ := by
    ext q
    induction q using Quotient.inductionOn with | h z =>
    rw [Subgroup.quotientMk_mem_ellipticOrbits_iff, mem_freeLocus, ← Subgroup.card_eq_one,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq, cardStabilizerOnOrbit_mk,
      ← map_liftSL_sl2zToPSL2R]
    constructor
    · intro hne
      rcases Γ'.liftSL.exists_smul_eq_of_card_stabilizer_ne_one hne with
        ⟨_, -, h2⟩ | ⟨_, -, h3⟩
      · exact Or.inl h2
      · exact Or.inr h3
    · rintro (h2 | h3) <;> omega
  have hdisj : Disjoint S₂ S₃ := Set.disjoint_left.mpr fun _ h2 h3 ↦ by
    rw [Set.mem_ofPred_eq] at h2 h3
    omega
  have hfin₂ : S₂.Finite :=
    Set.finite_coe_iff.mp (Finite.of_equiv _ (fixedPermSEquivOrderTwoEllipticOrbits Γ' e))
  have hfin₃ : S₃.Finite :=
    Set.finite_coe_iff.mp (Finite.of_equiv _ (fixedPermREquivOrderThreeEllipticOrbits Γ' e))
  rw [hunion, finsum_mem_union hdisj hfin₂ hfin₃]
  have hsum₂ : ∑ᶠ q ∈ S₂, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) =
      (ellipticTwo Γ' e : ℝ) / 2 := by
    have hcongr : ∀ q ∈ S₂, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) = (1 / 2 : ℝ) := by
      intro q hq
      rw [Set.mem_ofPred_eq] at hq
      rw [hq]
      norm_num
    rw [finsum_mem_congr rfl hcongr, finsum_mem_eq_finite_toFinset_sum _ hfin₂,
      Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin₂,
      ← Nat.card_coe_set_eq]
    have hcard₂ : Nat.card S₂ = ellipticTwo Γ' e :=
      (ellipticTwo_eq_card_orderTwoEllipticOrbits Γ' e).symm
    rw [hcard₂]
    ring
  have hsum₃ : ∑ᶠ q ∈ S₃, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) =
      2 * (ellipticThree Γ' e : ℝ) / 3 := by
    have hcongr : ∀ q ∈ S₃, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) = (2 / 3 : ℝ) := by
      intro q hq
      rw [Set.mem_ofPred_eq] at hq
      rw [hq]
      norm_num
    rw [finsum_mem_congr rfl hcongr, finsum_mem_eq_finite_toFinset_sum _ hfin₃,
      Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin₃,
      ← Nat.card_coe_set_eq]
    have hcard₃ : Nat.card S₃ = ellipticThree Γ' e :=
      (ellipticThree_eq_card_orderThreeEllipticOrbits Γ' e).symm
    rw [hcard₃]
    ring
  rw [hsum₂, hsum₃]

/-! ### Topological Euler characteristic and genus comparison -/

/-- **Comparison of Euler characteristics.** The finite-CW Euler characteristic of the
compactified modular curve `X(Γ')` equals the combinatorial Euler characteristic of the modular
triple `modularTriple Γ' e`. -/
theorem eulerChar_compactifiedQuotient_eq_eulerChar (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    [FiniteCWType (Γ'.map psl2zToPSL2R).CompactifiedQuotient] :
    eulerChar (Γ'.map psl2zToPSL2R).CompactifiedQuotient = (modularTriple Γ' e).eulerChar := by
  have : Γ'.FiniteIndex := finiteIndex_of_equiv e
  have : (Γ'.map psl2zToPSL2R).IsFiniteRelIndex psl2zToPSL2R.range :=
    isFiniteRelIndex_map_psl2zToPSL2R Γ'
  have : CompactSpace (Γ'.map psl2zToPSL2R).CompactifiedQuotient :=
    compactSpace_compactifiedQuotient_map_psl2zToPSL2R Γ'
  have hle : Γ'.map psl2zToPSL2R ≤ psl2zToPSL2R.range := Γ'.map_le_range psl2zToPSL2R
  have hRH :=
    TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree hle
  have hR :=
    TauCeti.Fuchsian.ramificationDegree_eq_index_mul_cusps_add_elliptic_sub hle
      isCofinite_psl2zToPSL2RRange
  have hidx : ((Γ'.map psl2zToPSL2R).subgroupOf psl2zToPSL2R.range).index = n := by
    change (Γ'.map psl2zToPSL2R).relIndex psl2zToPSL2R.range = n
    rw [relIndex_map_psl2zToPSL2R, index_eq_of_equiv e]
  have h6 : (6 : ℝ) * (eulerChar (Γ'.map psl2zToPSL2R).CompactifiedQuotient : ℝ) =
      (6 : ℝ) * ((modularTriple Γ' e).eulerChar : ℝ) := by
    have hRH_real : (eulerChar (Γ'.map psl2zToPSL2R).CompactifiedQuotient : ℝ) =
        (n : ℝ) * 2 -
          (RiemannSurface.ramificationDegree (Subgroup.compactifiedQuotientMap hle) : ℝ) := by
      have hRH' := congrArg (Int.cast (R := ℝ)) hRH
      rw [hidx, eulerChar_compactifiedQuotient] at hRH'
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] using hRH'
    rw [hidx, Nat.card_unique, finsum_mem_ellipticOrbits_psl2zToPSL2RRange,
      ← cuspCount_eq_card_fuchsianCuspOrbit Γ' e,
      finsum_mem_ellipticOrbits_map_psl2zToPSL2R Γ' e] at hR
    have hcomb := congrArg (Int.cast (R := ℝ)) (six_mul_eulerChar_modularTriple Γ' e)
    push_cast at hcomb
    linarith
  exact_mod_cast mul_left_cancel₀ (by norm_num : (6 : ℝ) ≠ 0) h6

/-- **Comparison of combinatorial and topological genus.** For every finite-index subgroup
`Γ' ≤ PSL(2, ℤ)`, the combinatorial genus `genus Γ' e` agrees with the topological genus
`TauCeti.RiemannSurface.genus` of the compactified modular curve `X(Γ')`. -/
theorem genus_eq_riemannSurface_genus (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    [FiniteCWType (Γ'.map psl2zToPSL2R).CompactifiedQuotient] :
    genus Γ' e = RiemannSurface.genus (Γ'.map psl2zToPSL2R).CompactifiedQuotient :=
  (RiemannSurface.genus_eq_of_eulerChar_eq
    ((eulerChar_compactifiedQuotient_eq_eulerChar Γ' e).trans
      (two_sub_two_mul_genus Γ' e).symm)).symm

/-! ### Congruence specializations (`Γ₀(N)`) and concrete checks -/

/-- **Cusp count of `Γ₀(N)`.** For every positive `N`, `cuspCount (Gamma0Projective N) e` equals
`∑_{g ∣ N} φ(gcd(g, N / g))`. -/
theorem cuspCount_Gamma0Projective (N : ℕ) [NeZero N]
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective N ≃ Fin n) :
    cuspCount (TauCeti.CongruenceSubgroup.Gamma0Projective N) e =
      ∑ g ∈ N.divisors, Nat.totient (Nat.gcd g (N / g)) := by
  rw [cuspCount_eq_card_fuchsianCuspOrbit, ← map_liftSL_sl2zToPSL2R,
    TauCeti.CongruenceSubgroup.liftSL_Gamma0Projective, TauCeti.card_cuspOrbit_Gamma0]

/-- For prime `p`, `Γ₀(p)` has `2` cusps. -/
theorem cuspCount_Gamma0Projective_of_prime {p : ℕ} [Fact p.Prime]
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective p ≃ Fin n) :
    cuspCount (TauCeti.CongruenceSubgroup.Gamma0Projective p) e = 2 := by
  rw [cuspCount_eq_card_fuchsianCuspOrbit, ← map_liftSL_sl2zToPSL2R,
    TauCeti.CongruenceSubgroup.liftSL_Gamma0Projective, TauCeti.card_cuspOrbit_Gamma0_of_prime]

/-- For prime `p`, the cusp widths of `Γ₀(p)` are `{1, p}` (at the cusps `∞` of width `1` and
`0` of width `p`). -/
theorem cuspWidths_Gamma0Projective_of_prime {p : ℕ} [Fact p.Prime]
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective p ≃ Fin n) :
    cuspWidths (TauCeti.CongruenceSubgroup.Gamma0Projective p) e = {1, p} := by
  have hp : p.Prime := Fact.out
  have hT : (_root_.ModularGroup.T : PSL(2, ℤ)) ∈
      TauCeti.CongruenceSubgroup.Gamma0Projective p := by
    rw [TauCeti.CongruenceSubgroup.mem_Gamma0Projective_mk, CongruenceSubgroup.Gamma0_mem]
    simp [_root_.ModularGroup.T]
  have hper : minimalPeriod (permT (TauCeti.CongruenceSubgroup.Gamma0Projective p) e)
      (e ((1 : PSL(2, ℤ)) : _)) = 1 :=
    Nat.dvd_one.mp <| (minimalPeriod_permT_dvd_iff _ e 1 1).mpr (by simp [hT])
  have h1 : 1 ∈ cuspWidths (TauCeti.CongruenceSubgroup.Gamma0Projective p) e :=
    hper ▸ minimalPeriod_permT_mem_cuspWidths _ e _
  have hcard : (cuspWidths (TauCeti.CongruenceSubgroup.Gamma0Projective p) e).card = 2 := by
    rw [← cuspCount_eq_card_cuspWidths, cuspCount_Gamma0Projective_of_prime]
  have hsum : (cuspWidths (TauCeti.CongruenceSubgroup.Gamma0Projective p) e).sum = p + 1 := by
    rw [sum_cuspWidths, ← index_eq_of_equiv e,
      TauCeti.CongruenceSubgroup.Gamma0Projective_index,
      CongruenceSubgroup.Gamma0_prime_index p hp]
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h1
  have hcard_t : t.card = 1 := by
    rw [ht, Multiset.card_cons] at hcard
    omega
  obtain ⟨w, rfl⟩ := Multiset.card_eq_one.mp hcard_t
  have hw : w = p := by
    rw [ht, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    omega
  rw [ht, hw]
  rfl

/-- **Closed form of `ε₂(Γ₀(N))`.** The combinatorial count
`ellipticTwo (Gamma0Projective N) e` equals `0` when `4 ∣ N`, and `∏_{p ∣ N} (1 + χ₄(p))`
otherwise. -/
theorem ellipticTwo_Gamma0Projective_eq_prod (N : ℕ)
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective N ≃ Fin n) :
    (ellipticTwo (TauCeti.CongruenceSubgroup.Gamma0Projective N) e : ℤ) =
      if 4 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + ZMod.χ₄ p) := by
  rw [ellipticTwo_eq_card_orderTwoEllipticOrbits, ← map_liftSL_sl2zToPSL2R,
    TauCeti.CongruenceSubgroup.liftSL_Gamma0Projective,
    TauCeti.card_orderTwoElliptic_Gamma0_eq_prod]

/-- **Closed form of `ε₃(Γ₀(N))`.** The combinatorial count
`ellipticThree (Gamma0Projective N) e` equals `0` when `9 ∣ N`, and
`∏_{p ∣ N} (1 + (p | 3))` otherwise. -/
theorem ellipticThree_Gamma0Projective_eq_prod (N : ℕ)
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective N ≃ Fin n) :
    (ellipticThree (TauCeti.CongruenceSubgroup.Gamma0Projective N) e : ℤ) =
      if 9 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + legendreSym 3 p) := by
  rw [ellipticThree_eq_card_orderThreeEllipticOrbits, ← map_liftSL_sl2zToPSL2R,
    TauCeti.CongruenceSubgroup.liftSL_Gamma0Projective,
    TauCeti.card_orderThreeElliptic_Gamma0_eq_prod]

/-- **Worked check on `Γ₀(2)`**: invariant vector `(3, 0, 1, 0, {1, 2})`. -/
theorem invariants_Gamma0Projective_two
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective 2 ≃ Fin n) :
    invariants (TauCeti.CongruenceSubgroup.Gamma0Projective 2) e = ⟨3, 0, 1, 0, {1, 2}⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : n = 3 := by
    rw [← index_eq_of_equiv e, TauCeti.CongruenceSubgroup.Gamma0Projective_index,
      CongruenceSubgroup.Gamma0_prime_index 2 Nat.prime_two]
  have h2 : ellipticTwo (TauCeti.CongruenceSubgroup.Gamma0Projective 2) e = 1 := by
    have h := ellipticTwo_Gamma0Projective_eq_prod 2 e
    rw [Nat.Prime.primeFactors Nat.prime_two] at h
    norm_num [ZMod.χ₄] at h
    omega
  have h3 : ellipticThree (TauCeti.CongruenceSubgroup.Gamma0Projective 2) e = 0 := by
    have h := ellipticThree_Gamma0Projective_eq_prod 2 e
    rw [Nat.Prime.primeFactors Nat.prime_two] at h
    have hleg : legendreSym 3 ((2 : ℕ) : ℤ) = -1 := by decide
    rw [Finset.prod_singleton, hleg] at h
    norm_num at h
    omega
  have hc : cuspCount (TauCeti.CongruenceSubgroup.Gamma0Projective 2) e = 2 :=
    cuspCount_Gamma0Projective_of_prime e
  have hg : genus (TauCeti.CongruenceSubgroup.Gamma0Projective 2) e = 0 := by
    have hform := genus_formula (TauCeti.CongruenceSubgroup.Gamma0Projective 2) e
    omega
  ext <;> simp [hn, hg, h2, h3, cuspWidths_Gamma0Projective_of_prime]

/-- **Worked check on `Γ₀(11)`**: invariant vector `(12, 1, 0, 0, {1, 11})`, the first prime
level of positive genus. -/
theorem invariants_Gamma0Projective_eleven
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective 11 ≃ Fin n) :
    invariants (TauCeti.CongruenceSubgroup.Gamma0Projective 11) e = ⟨12, 1, 0, 0, {1, 11}⟩ := by
  have hp11 : Nat.Prime 11 := by decide
  have : Fact (Nat.Prime 11) := ⟨hp11⟩
  have hn : n = 12 := by
    rw [← index_eq_of_equiv e, TauCeti.CongruenceSubgroup.Gamma0Projective_index,
      CongruenceSubgroup.Gamma0_prime_index 11 hp11]
  have h2 : ellipticTwo (TauCeti.CongruenceSubgroup.Gamma0Projective 11) e = 0 := by
    have h := ellipticTwo_Gamma0Projective_eq_prod 11 e
    rw [Nat.Prime.primeFactors hp11] at h
    norm_num [ZMod.χ₄] at h
    omega
  have h3 : ellipticThree (TauCeti.CongruenceSubgroup.Gamma0Projective 11) e = 0 := by
    have h := ellipticThree_Gamma0Projective_eq_prod 11 e
    rw [Nat.Prime.primeFactors hp11] at h
    have hleg : legendreSym 3 ((11 : ℕ) : ℤ) = -1 := by decide
    rw [Finset.prod_singleton, hleg] at h
    norm_num at h
    omega
  have hc : cuspCount (TauCeti.CongruenceSubgroup.Gamma0Projective 11) e = 2 :=
    cuspCount_Gamma0Projective_of_prime e
  have hg : genus (TauCeti.CongruenceSubgroup.Gamma0Projective 11) e = 1 := by
    have hform := genus_formula (TauCeti.CongruenceSubgroup.Gamma0Projective 11) e
    omega
  ext <;> simp [hn, hg, h2, h3, cuspWidths_Gamma0Projective_of_prime]

end TauCeti.ModularGroup
