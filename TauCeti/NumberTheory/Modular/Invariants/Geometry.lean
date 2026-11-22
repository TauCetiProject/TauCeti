/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic.Cusps
public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic.Signature
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.RiemannHurwitz
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Tower
public import TauCeti.NumberTheory.Modular.Invariants.Basic
public import TauCeti.NumberTheory.ModularForms.Cusps.TranslationOrbit
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Signature
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# Geometric comparison of modular-triple invariants

For a finite-index subgroup `Γ' ≤ PSL(2, ℤ)` with coset enumeration `e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n`,
this file identifies the combinatorial invariants of `modularTriple Γ' e` (from
`TauCeti.NumberTheory.Modular.Invariants.Basic`) with their geometric, Fuchsian, and Mathlib
counterparts on `Γ'.map psl2zToPSL2R` and `Γ'.liftSL ≤ SL(2, ℤ)`:

* **Cusp widths**: `permT`-periods agree with `TauCeti.Subgroup.integerCuspWidth`, Mathlib's
  `strictWidthInfty` and `widthInfty`, `ModularForm.cuspTranslationOrbitWidth`, and normalized
  Fuchsian `CuspDatum.width` (with width quotients agreeing with `CuspDatum.widthIndex`).
* **Cusp orbits**: `permT`-cycles biject onto Fuchsian `(Γ'.map psl2zToPSL2R).CuspOrbit` and
  Mathlib's `CuspOrbits Γ'.liftSL` (`permTCycleEquivFuchsianCuspOrbit`,
  `permTCycleEquivCuspOrbits`), intertwining `cuspCycleMapOfLE` with `Subgroup.cuspOrbitMap` and
  `CuspOrbits.map`.
* **Elliptic orbits**: `S`- and `R`-fixed cosets (`fixedCosetSEquivOrderTwoEllipticOrbits`,
  `fixedCosetREquivOrderThreeEllipticOrbits`) and fixed points of `permS`, `permR`, and `σ0`
  (`fixedPermSEquivOrderTwoEllipticOrbits`, `fixedPermREquivOrderThreeEllipticOrbits`,
  `fixedσ0EquivOrderThreeEllipticOrbits`) biject onto order-`2` and order-`3` elliptic orbits of
  `Γ'.map psl2zToPSL2R` on `ℍ`, yielding the orbifold defect sum
  `finsum_mem_ellipticOrbits_map_psl2zToPSL2R`.
* **Topological genus**: Fuchsian Riemann–Hurwitz identifies the finite-CW Euler characteristic
  and topological genus of `X(Γ')` with `(modularTriple Γ' e).eulerChar` and `genus Γ' e`
  (`eulerChar_compactifiedQuotient_eq_eulerChar`, `genus_eq_riemannSurface_genus`).

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005,
  §§2.4, 3.1, 3.7–3.8.
* S. Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, Univ. of Chicago Press, 1992, §4.3.
* R. A. Rankin, *Modular Forms and Functions*, Cambridge University Press, 1977, Chapter 1.
-/

public section

noncomputable section

open Equiv Equiv.Perm Function Matrix Matrix.ProjectiveSpecialLinearGroup Matrix.SpecialLinearGroup
  MulAction OnePoint Subgroup UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.ModularGroup

open _root_.ModularGroup

variable {m n : ℕ}

/-! ### Cusp widths -/

/-- **The width of the cusp `σ ∞`.** For `σ ∈ SL(2, ℤ)`, the cycle of `permT Γ' e` through the
coset of `σ⁻¹` has length the integer width at `∞` of the conjugate `σ⁻¹ (±Γ') σ` of the lift
`±Γ' = Γ'.liftSL`. -/
theorem minimalPeriod_permT_eq_integerCuspWidth (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ)) :
    minimalPeriod (permT Γ' e) (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      TauCeti.Subgroup.integerCuspWidth
        ((ConjAct.toConjAct σ⁻¹ • Γ'.liftSL).map (mapGL ℝ)) := by
  refine Nat.dvd_right_iff_eq.mp fun j ↦ ?_
  rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd, ← TauCeti.Subgroup.T_pow_mem_iff,
    coe_GL_eq_mapGL, ← map_pow, mapGL_mem_map_conjAct_liftSL_iff ℝ]
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, Perm.iterate_eq_pow,
    permT_pow_apply_eq_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow,
    inv_inv]

/-- **The width at `∞`.** The cycle of `permT Γ' e` through the base coset has length the integer
width at `∞` of the lift `±Γ' = Γ'.liftSL`. -/
theorem minimalPeriod_permT_one_eq_integerCuspWidth (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      TauCeti.Subgroup.integerCuspWidth (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) := by
  simpa using minimalPeriod_permT_eq_integerCuspWidth Γ' e 1

/-- The cusp widths are exactly the widths at `∞` of the conjugates `σ⁻¹ (±Γ') σ`, the widths of
the cusps `σ ∞`. -/
theorem mem_cuspWidths_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) {w : ℕ} :
    w ∈ cuspWidths Γ' e ↔ ∃ σ : SL(2, ℤ),
      TauCeti.Subgroup.integerCuspWidth ((ConjAct.toConjAct σ⁻¹ • Γ'.liftSL).map (mapGL ℝ)) =
        w := by
  simp_rw [← minimalPeriod_permT_eq_integerCuspWidth Γ' e, cuspWidths_def,
    Perm.mem_fullCycleType_iff]
  refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨σ, hσ⟩ ↦ ⟨_, hσ⟩⟩
  obtain ⟨q, rfl⟩ := e.surjective i
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨σ⁻¹, by rwa [inv_inv]⟩

/-- The width at `∞` of each conjugate `σ⁻¹ (±Γ') σ`, the width of the cusp `σ ∞`, is one of the
cusp widths. -/
theorem integerCuspWidth_mem_cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (σ : SL(2, ℤ)) :
    TauCeti.Subgroup.integerCuspWidth ((ConjAct.toConjAct σ⁻¹ • Γ'.liftSL).map (mapGL ℝ)) ∈
      cuspWidths Γ' e :=
  (mem_cuspWidths_iff Γ' e).mpr ⟨σ, rfl⟩

/-- The strict period subgroup of `Γ'.liftSL` in `GL(2, ℝ)` is generated by the `permT`-period of
the identity coset. -/
theorem strictPeriods_liftSL_eq_zmultiples (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Subgroup.strictPeriods (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) =
      AddSubgroup.zmultiples
        (minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) := by
  rw [minimalPeriod_permT_one_eq_integerCuspWidth]
  exact Subgroup.strictPeriods_eq_zmultiples_integerCuspWidth _ (Subgroup.map_le_range _ _)

/-- The `permT`-period of the identity coset agrees with Mathlib's `Subgroup.strictWidthInfty` of
`Γ'.liftSL`. -/
theorem natCast_minimalPeriod_permT_one_eq_strictWidthInfty (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) =
      Subgroup.strictWidthInfty (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) :=
  (Subgroup.strictWidthInfty_eq_of_strictPeriods_eq_zmultiples
    (strictPeriods_liftSL_eq_zmultiples Γ' e) (Nat.cast_nonneg _)).symm

/-- The `permT`-period of the identity coset agrees with Mathlib's `Subgroup.widthInfty` of
`Γ'.liftSL` (regular at `∞` because `-I ∈ Γ'.liftSL`). -/
theorem natCast_minimalPeriod_permT_one_eq_widthInfty (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) =
      Subgroup.widthInfty (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) := by
  have hneg : (-1 : GL (Fin 2) ℝ) ∈ (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) :=
    ⟨-1, Subgroup.neg_one_mem_liftSL Γ', by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  rw [Subgroup.widthInfty, Subgroup.adjoinNegOne_eq_self_iff.mpr hneg,
    natCast_minimalPeriod_permT_one_eq_strictWidthInfty]

/-- At every coset `σ : SL(2, ℤ)`, the `permT`-period equals `ModularForm.cuspTranslationOrbitWidth`
for `Γ'.liftSL`. -/
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

private theorem conj_scaling_psl2zToPSL2R {Γ' : Subgroup PSL(2, ℤ)} {σ : SL(2, ℤ)}
    {D : (Γ'.map psl2zToPSL2R).CuspDatum}
    (hσ : D.scaling = psl2zToPSL2R ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))) (γ : SL(2, ℤ)) :
    D.scaling * psl2zToPSL2R (γ : PSL(2, ℤ)) * D.scaling⁻¹ = sl2zToPSL2R (σ⁻¹ * γ * σ) := by
  rw [hσ, ← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv, inv_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, psl2zToPSL2R_mk]

private theorem cuspDatum_width_dvd_of_conj_T_zpow_mem
    {Γ' : Subgroup PSL(2, ℤ)} {σ : SL(2, ℤ)} {D : (Γ'.map psl2zToPSL2R).CuspDatum}
    (hσ : D.scaling = psl2zToPSL2R ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)))
    {k : ℤ} (hk : (σ : PSL(2, ℤ)) * (T : PSL(2, ℤ)) ^ k * (σ : PSL(2, ℤ))⁻¹ ∈ Γ') :
    ∃ r : ℤ, (r : ℝ) * D.width = k := by
  let gk : Γ'.map psl2zToPSL2R :=
    ⟨sl2zToPSL2R (σ * _root_.ModularGroup.T ^ k * σ⁻¹), by
      rw [← psl2zToPSL2R_mk, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
        QuotientGroup.mk_inv]
      exact Subgroup.mem_map_of_mem psl2zToPSL2R hk⟩
  have hgk_conj : D.scaling * (gk : PSL(2, ℝ)) * D.scaling⁻¹ = upperRightHom (k : ℝ) := by
    dsimp only [gk]
    rw [← psl2zToPSL2R_mk, conj_scaling_psl2zToPSL2R hσ,
      show σ⁻¹ * (σ * _root_.ModularGroup.T ^ k * σ⁻¹) * σ = _root_.ModularGroup.T ^ k by group,
      TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow]
  have hgk_stab : gk ∈ stabilizer (Γ'.map psl2zToPSL2R) D.cusp := by
    rw [mem_stabilizer_iff]
    apply MulAction.injective D.scaling
    dsimp only
    rw [Subgroup.smul_def, ← mul_smul,
      show D.scaling * (gk : PSL(2, ℝ)) = (D.scaling * gk * D.scaling⁻¹) * D.scaling by group,
      mul_smul, D.scaling_smul_cusp, hgk_conj, upperRightHom_smul_infty]
  obtain ⟨r, hr⟩ := D.mem_stabilizer_iff_conj.mp hgk_stab
  rw [hgk_conj] at hr
  exact ⟨r, (upperRightHom_injective hr).symm⟩

/-- At every cusp `σ • ∞`, the `permT`-period of `σ⁻¹ Γ'` equals `D.width` for any normalized
Fuchsian cusp datum `D` for `Γ'.map psl2zToPSL2R` with scaling `psl2zToPSL2R σ⁻¹`. -/
theorem natCast_minimalPeriod_permT_eq_cuspDatum_width (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ))
    (D : (Γ'.map psl2zToPSL2R).CuspDatum)
    (hσ : D.scaling = psl2zToPSL2R ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))) :
    (minimalPeriod (permT Γ' e)
      (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) = D.width := by
  set h := minimalPeriod (permT Γ' e) (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'))
  obtain ⟨g, hg, hgen⟩ := D.generator.property
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  have hγ : (γ : PSL(2, ℤ)) ∈ Γ' := hg
  have hconj_eq : sl2zToPSL2R (σ⁻¹ * γ * σ) = upperRightHom D.width := by
    rw [← conj_scaling_psl2zToPSL2R hσ γ, hgen, D.scaling_mul_generator_mul_inv]
  have hc0 : (σ⁻¹ * γ * σ) 1 0 = 0 := by
    have h0 := (TauCeti.UpperHalfPlane.entries_of_coe_eq_upperRightHom
      ((sl2zToPSL2R_apply _).symm.trans hconj_eq)).1
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.map_apply,
      Int.coe_castRingHom] at h0
    exact_mod_cast h0
  obtain ⟨k, hk⟩ := TauCeti.ModularGroup.exists_coe_eq_T_zpow_of_c_eq_zero hc0
  have hk_eq : (k : ℝ) = D.width := upperRightHom_injective <| by
    rw [← TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow, ← psl2zToPSL2R_mk, QuotientGroup.mk_zpow,
      ← hk, psl2zToPSL2R_mk, hconj_eq]
  have hk_mem : ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))⁻¹ * (T : PSL(2, ℤ)) ^ k *
      ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) ∈ Γ' := by
    rw [QuotientGroup.mk_inv, inv_inv, ← hk, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    simpa [mul_assoc] using hγ
  have hk_pos : (0 : ℤ) < k := by exact_mod_cast (hk_eq.symm ▸ D.width_pos : (0 : ℝ) < k)
  set m : ℕ := k.toNat
  have hm_eq : (m : ℤ) = k := Int.toNat_of_nonneg hk_pos.le
  have hm_real : (m : ℝ) = D.width := by rw [← hk_eq, ← hm_eq, Int.cast_natCast]
  have hdvd1 : h ∣ m := by
    rw [minimalPeriod_permT_dvd_iff, ← zpow_natCast, hm_eq]
    exact hk_mem
  have hTh_mem : (σ : PSL(2, ℤ)) * (T : PSL(2, ℤ)) ^ (h : ℤ) * (σ : PSL(2, ℤ))⁻¹ ∈ Γ' := by
    have hp := (minimalPeriod_permT_dvd_iff Γ' e ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) h).mp dvd_rfl
    simpa [QuotientGroup.mk_inv, zpow_natCast] using hp
  obtain ⟨r, hr_eq⟩ := cuspDatum_width_dvd_of_conj_T_zpow_mem hσ hTh_mem
  have hdvd2 : m ∣ h := by
    have hr_int : r * (m : ℤ) = (h : ℤ) := by exact_mod_cast (hm_real ▸ hr_eq)
    exact Int.natCast_dvd_natCast.mp ⟨r, by linarith⟩
  rw [Nat.dvd_antisymm hdvd1 hdvd2, hm_real]

/-- Under a subgroup inclusion `Γ'' ≤ Γ'`, the quotient of `permT`-periods at the cusp `σ • ∞`
equals the geometric cusp ramification index `CuspDatum.widthIndex`. -/
theorem minimalPeriod_permT_div_eq_widthIndex {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ))
    (D'' : (Γ''.map psl2zToPSL2R).CuspDatum) (D' : (Γ'.map psl2zToPSL2R).CuspDatum)
    (hσ'' : D''.scaling = psl2zToPSL2R ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)))
    (hσ' : D'.scaling = psl2zToPSL2R ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))) :
    minimalPeriod (permT Γ'' e'')
        (e'' (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'')) /
      minimalPeriod (permT Γ' e')
        (e' (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      TauCeti.Subgroup.CuspDatum.widthIndex (Subgroup.map_mono h) D'' D' (hσ''.trans hσ'.symm) := by
  have hw'' := natCast_minimalPeriod_permT_eq_cuspDatum_width Γ'' e'' σ D'' hσ''
  have hw' := natCast_minimalPeriod_permT_eq_cuspDatum_width Γ' e' σ D' hσ'
  have hdvd := minimalPeriod_permT_dvd_of_le h e'' e' ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))
  have hmul : D''.width =
      ((minimalPeriod (permT Γ'' e'')
          (e'' (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'')) /
        minimalPeriod (permT Γ' e')
          (e' (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℕ) : ℝ) * D'.width := by
    rw [← hw'', ← hw', ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  exact TauCeti.Subgroup.CuspDatum.width_factor_unique D'' D' hmul
    (TauCeti.Subgroup.CuspDatum.width_eq_widthIndex_mul (Subgroup.map_mono h) D'' D'
      (hσ''.trans hσ'.symm))

/-- Under a subgroup inclusion `Γ'' ≤ Γ'`, the ratio of `cuspCycleWidth`s at the cusp `σ • ∞`
equals `CuspDatum.widthIndex`. -/
theorem cuspCycleWidth_div_eq_widthIndex {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ))
    (D'' : (Γ''.map psl2zToPSL2R).CuspDatum) (D' : (Γ'.map psl2zToPSL2R).CuspDatum)
    (hσ'' : D''.scaling = psl2zToPSL2R ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)))
    (hσ' : D'.scaling = psl2zToPSL2R ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))) :
    cuspCycleWidth Γ'' e''
        (Quotient.mk _ (e'' (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ''))) /
      cuspCycleWidth Γ' e'
        (Quotient.mk _ (e' (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'))) =
      TauCeti.Subgroup.CuspDatum.widthIndex (Subgroup.map_mono h) D'' D' (hσ''.trans hσ'.symm) := by
  rw [cuspCycleWidth_mk, cuspCycleWidth_mk]
  exact minimalPeriod_permT_div_eq_widthIndex h e'' e' σ D'' D' hσ'' hσ'

/-! ### Cusp orbits -/

/-- **Cusp orbits via `permT`-cycles.** The cycles of `permT Γ' e` are in canonical bijection with
the Fuchsian cusp orbits `(Γ'.map psl2zToPSL2R).CuspOrbit`: the cycle of `e (g Γ')` maps to the
cusp orbit of `psl2zToPSL2R g⁻¹ • ∞`. -/
def permTCycleEquivFuchsianCuspOrbit (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃ (Γ'.map psl2zToPSL2R).CuspOrbit :=
  letI := Γ'.finiteIndex_of_equiv e
  (permTCycleEquivDoubleCoset Γ' e).trans (doubleCosetEquivFuchsianCuspOrbit Γ')

/-- Evaluating `permTCycleEquivFuchsianCuspOrbit` on the cycle of `e (g Γ')` gives the Fuchsian
cusp orbit of `psl2zToPSL2R g⁻¹ • ∞`. -/
@[simp]
theorem permTCycleEquivFuchsianCuspOrbit_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    permTCycleEquivFuchsianCuspOrbit Γ' e (Quotient.mk _ (e (g : PSL(2, ℤ) ⧸ Γ'))) =
      (Γ'.map psl2zToPSL2R).cuspOrbitMk
        ⟨psl2zToPSL2R g⁻¹ • (∞ : OnePoint ℝ),
          Subgroup.mem_cuspPoints.mpr
            (letI := Γ'.finiteIndex_of_equiv e
            Γ'.isCuspPoint_map_psl2zToPSL2R_smul_infty g⁻¹)⟩ := by
  let : Γ'.FiniteIndex := Γ'.finiteIndex_of_equiv e
  rw [permTCycleEquivFuchsianCuspOrbit, Equiv.trans_apply, permTCycleEquivDoubleCoset_mk,
    doubleCosetEquivFuchsianCuspOrbit_mk]

/-- Naturality of `permTCycleEquivFuchsianCuspOrbit` under subgroup inclusion `Γ'' ≤ Γ'`: the
combinatorial cycle map `cuspCycleMapOfLE` corresponds to the geometric cusp-orbit map
`Subgroup.cuspOrbitMap`. -/
@[simp]
theorem permTCycleEquivFuchsianCuspOrbit_cuspCycleMapOfLE {Γ'' Γ' : Subgroup PSL(2, ℤ)}
    (h : Γ'' ≤ Γ') (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (q : Quotient (SameCycle.setoid (permT Γ'' e''))) :
    permTCycleEquivFuchsianCuspOrbit Γ' e' (cuspCycleMapOfLE h e'' e' q) =
      Subgroup.cuspOrbitMap (Subgroup.map_mono h) (permTCycleEquivFuchsianCuspOrbit Γ'' e'' q) := by
  induction q using Quotient.ind with | _ y =>
  obtain ⟨qy, rfl⟩ := e''.surjective y
  induction qy using QuotientGroup.induction_on with | H g =>
  rw [cuspCycleMapOfLE_mk, permTCycleEquivFuchsianCuspOrbit_mk, permTCycleEquivFuchsianCuspOrbit_mk,
    Subgroup.cuspOrbitMap_cuspOrbitMk]

/-- The combinatorial cusp count equals the number of Fuchsian cusp orbits of
`Γ'.map psl2zToPSL2R`. -/
theorem cuspCount_eq_card_fuchsianCuspOrbit (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = Nat.card (Γ'.map psl2zToPSL2R).CuspOrbit := by
  rw [cuspCount_def, orbitCount_def, Nat.card_congr (permTCycleEquivFuchsianCuspOrbit Γ' e)]

/-- The cycles of `permT Γ' e` are in bijection with Mathlib's `CuspOrbits Γ'.liftSL`. -/
def permTCycleEquivCuspOrbits (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃
      CuspOrbits (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) :=
  (permTCycleEquivFuchsianCuspOrbit Γ' e).trans (Subgroup.fuchsianCuspOrbitEquivCuspOrbits Γ')

/-- Evaluating `permTCycleEquivCuspOrbits` on the cycle of `e (g Γ')` gives Mathlib's cusp orbit
of `psl2zToPSL2R g⁻¹ • ∞`. -/
@[simp]
theorem permTCycleEquivCuspOrbits_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    permTCycleEquivCuspOrbits Γ' e (Quotient.mk _ (e (g : PSL(2, ℤ) ⧸ Γ'))) =
      Quotient.mk'' ⟨psl2zToPSL2R g⁻¹ • (∞ : OnePoint ℝ),
        mem_cuspsSubMulAction.mpr
          ((Subgroup.isCuspPoint_map_psl2zToPSL2R_iff_isCusp Γ' _).mp
            (letI := Γ'.finiteIndex_of_equiv e
            Γ'.isCuspPoint_map_psl2zToPSL2R_smul_infty g⁻¹))⟩ := by
  rw [permTCycleEquivCuspOrbits, Equiv.trans_apply, permTCycleEquivFuchsianCuspOrbit_mk,
    Subgroup.fuchsianCuspOrbitEquivCuspOrbits_cuspOrbitMk]

/-- Naturality of `permTCycleEquivCuspOrbits` under subgroup inclusion `Γ'' ≤ Γ'`: the
combinatorial cycle map `cuspCycleMapOfLE` corresponds to `CuspOrbits.map`. -/
@[simp]
theorem permTCycleEquivCuspOrbits_cuspCycleMapOfLE {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (q : Quotient (SameCycle.setoid (permT Γ'' e''))) :
    permTCycleEquivCuspOrbits Γ' e' (cuspCycleMapOfLE h e'' e' q) =
      CuspOrbits.map (Subgroup.map_mono (Subgroup.liftSL_le_liftSL_iff.mpr h))
        (permTCycleEquivCuspOrbits Γ'' e'' q) := by
  induction q using Quotient.ind with | _ y =>
  obtain ⟨qy, rfl⟩ := e''.surjective y
  induction qy using QuotientGroup.induction_on with | H g =>
  rw [cuspCycleMapOfLE_mk, permTCycleEquivCuspOrbits_mk, permTCycleEquivCuspOrbits_mk,
    CuspOrbits.map_mk]

/-- The combinatorial cusp count equals the cardinality of Mathlib's `CuspOrbits Γ'.liftSL`. -/
theorem cuspCount_eq_card_cuspOrbits (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = Nat.card (CuspOrbits (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ))) := by
  rw [cuspCount_def, orbitCount_def, Nat.card_congr (permTCycleEquivCuspOrbits Γ' e)]

/-! ### Elliptic orbits -/

private theorem injective_inverseTranslateOrbit_on_fixed {Γ' : Subgroup PSL(2, ℤ)}
    {z₀ : ℍ} {s : PSL(2, ℤ)} (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    {q₁ q₂ : PSL(2, ℤ) ⧸ Γ'} (hq₂ : s • q₂ = q₂)
    (horb : inverseTranslateOrbit Γ' z₀ q₁ = inverseTranslateOrbit Γ' z₀ q₂) :
    q₁ = q₂ := by
  have hstab' : ∀ g : PSL(2, ℤ), psl2zToPSL2R g • z₀ = z₀ ↔ g ∈ Subgroup.zpowers s := by
    intro g
    rw [UpperHalfPlane.psl2zToPSL2R_smul, ← mem_stabilizer_iff, hstab]
  rw [inverseTranslateOrbit_eq_iff_mem_orbit_zpowers Γ' hstab', mem_orbit_iff] at horb
  obtain ⟨⟨t, ht⟩, hsmul⟩ := horb
  have hle : Subgroup.zpowers s ≤ stabilizer PSL(2, ℤ) q₂ :=
    Subgroup.zpowers_le.mpr (mem_stabilizer_iff.mpr hq₂)
  have ht_fix : t • q₂ = q₂ := mem_stabilizer_iff.mp (hle ht)
  rw [Subgroup.smul_def, ht_fix] at hsmul
  exact hsmul.symm

private theorem cardStabilizerOnOrbit_inverseTranslateOrbit_eq_iff
    {Γ' : Subgroup PSL(2, ℤ)} {z₀ : ℍ} {s : PSL(2, ℤ)} {p : ℕ} (hp : 0 < p)
    (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    (hcard : Nat.card (Subgroup.zpowers s) = p)
    (q : PSL(2, ℤ) ⧸ Γ') :
    cardStabilizerOnOrbit (inverseTranslateOrbit Γ' z₀ q) = p ↔ s • q = q := by
  induction q using QuotientGroup.induction_on with | H g =>
  have : Finite (Subgroup.zpowers s) := Nat.finite_of_card_ne_zero (hcard ▸ hp.ne')
  let H : Subgroup (Subgroup.zpowers s) := (MulAut.conj g • Γ').subgroupOf (Subgroup.zpowers s)
  let f : H → stabilizer (Γ'.map psl2zToPSL2R) (psl2zToPSL2R g⁻¹ • z₀) :=
    fun ⟨⟨t, _⟩, ht⟩ ↦
      ⟨⟨psl2zToPSL2R (g⁻¹ * t * g), by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
          MulAut.smul_def, MulAut.conj_apply, inv_inv] at ht
        exact Subgroup.mem_map_of_mem psl2zToPSL2R ht⟩, by
        have htfix : t • z₀ = z₀ := mem_stabilizer_iff.mp (hstab ▸ ‹t ∈ Subgroup.zpowers s›)
        rw [mem_stabilizer_iff, Subgroup.smul_def, ← mul_smul, ← map_mul,
          show (g⁻¹ * t * g) * g⁻¹ = g⁻¹ * t by group, map_mul, mul_smul,
          UpperHalfPlane.psl2zToPSL2R_smul t, htfix]⟩
  have hf : Function.Bijective f := by
    refine ⟨fun ⟨⟨t₁, _⟩, _⟩ ⟨⟨t₂, _⟩, _⟩ h ↦ ?_, fun ⟨⟨x, hxΓ⟩, hxfix⟩ ↦ ?_⟩
    · have h' := congrArg (fun y ↦ y.val.val) h
      dsimp only [f] at h'
      exact Subtype.ext <| Subtype.ext <| by simpa using psl2zToPSL2R_injective h'
    · obtain ⟨h, hhΓ, rfl⟩ := hxΓ
      have hfix : (g * h * g⁻¹) • z₀ = z₀ := by
        rw [mem_stabilizer_iff, Subgroup.smul_def] at hxfix
        dsimp only at hxfix
        simp_rw [UpperHalfPlane.psl2zToPSL2R_smul] at hxfix
        rw [mul_smul, mul_smul, hxfix, smul_inv_smul]
      have hmem : g * h * g⁻¹ ∈ Subgroup.zpowers s := hstab ▸ mem_stabilizer_iff.mpr hfix
      refine ⟨⟨⟨g * h * g⁻¹, hmem⟩, ?_⟩, Subtype.ext <| Subtype.ext <| ?_⟩
      · rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
          MulAut.smul_def, MulAut.conj_apply, inv_inv]
        simpa [mul_assoc] using hhΓ
      · exact congrArg psl2zToPSL2R (by group)
  rw [inverseTranslateOrbit_mk, cardStabilizerOnOrbit_mk,
    ← Nat.card_congr (Equiv.ofBijective f hf), ← hcard,
    Subgroup.card_eq_iff_eq_top, Subgroup.eq_top_iff', TauCeti.smul_quotientGroup_mk_eq_self_iff]
  constructor
  · intro htop
    have hs := htop ⟨s, Subgroup.mem_zpowers s⟩
    simpa [H, Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.conj_apply] using hs
  · rintro hs ⟨t, ht⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def, MulAut.conj_apply, inv_inv]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hconj : g⁻¹ * s ^ k * g = (g⁻¹ * s * g) ^ k := by
      have : g⁻¹ * s * g = MulAut.conj g⁻¹ s := by simp
      rw [this, ← map_zpow]; simp
    rw [hconj]
    exact zpow_mem hs k

private def fixedCosetToEllipticTranslateOrbit (Γ' : Subgroup PSL(2, ℤ)) {z₀ : ℍ}
    {s : PSL(2, ℤ)} {p : ℕ} (hp : 0 < p)
    (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    (hcard : Nat.card (Subgroup.zpowers s) = p)
    (q : {q : PSL(2, ℤ) ⧸ Γ' // s • q = q}) :
    {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
      (∃ g : PSL(2, ℤ), o = Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g • z₀)) ∧
        cardStabilizerOnOrbit o = p} :=
  ⟨inverseTranslateOrbit Γ' z₀ q.val,
    ⟨by induction q.val using QuotientGroup.induction_on with | H g =>
        exact ⟨g⁻¹, by rw [inverseTranslateOrbit_mk, UpperHalfPlane.psl2zToPSL2R_smul]⟩,
      (cardStabilizerOnOrbit_inverseTranslateOrbit_eq_iff hp hstab hcard q.val).mpr q.property⟩⟩

private theorem fixedCosetToEllipticTranslateOrbit_val (Γ' : Subgroup PSL(2, ℤ)) {z₀ : ℍ}
    {s : PSL(2, ℤ)} {p : ℕ} (hp : 0 < p)
    (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    (hcard : Nat.card (Subgroup.zpowers s) = p)
    (q : {q : PSL(2, ℤ) ⧸ Γ' // s • q = q}) :
    (fixedCosetToEllipticTranslateOrbit Γ' hp hstab hcard q).val =
      inverseTranslateOrbit Γ' z₀ q.val :=
  (rfl)

private def fixedCosetEquivEllipticTranslateOrbit (Γ' : Subgroup PSL(2, ℤ)) {z₀ : ℍ}
    {s : PSL(2, ℤ)} {p : ℕ} (hp : 0 < p)
    (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    (hcard : Nat.card (Subgroup.zpowers s) = p) :
    {q : PSL(2, ℤ) ⧸ Γ' // s • q = q} ≃
      {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
        (∃ g : PSL(2, ℤ), o = Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g • z₀)) ∧
          cardStabilizerOnOrbit o = p} :=
  Equiv.ofBijective (fixedCosetToEllipticTranslateOrbit Γ' hp hstab hcard)
    ⟨fun ⟨_, _⟩ ⟨_, hq₂⟩ horb ↦ Subtype.ext <|
      injective_inverseTranslateOrbit_on_fixed hstab hq₂ (congrArg Subtype.val horb),
    fun ⟨_, ⟨g, rfl⟩, ho⟩ ↦ by
      have hfix : s • ((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') =
          ((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') := by
        rw [← cardStabilizerOnOrbit_inverseTranslateOrbit_eq_iff hp hstab hcard,
          inverseTranslateOrbit_mk, inv_inv, UpperHalfPlane.psl2zToPSL2R_smul]
        exact ho
      refine ⟨⟨((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'), hfix⟩, Subtype.ext ?_⟩
      rw [fixedCosetToEllipticTranslateOrbit_val, inverseTranslateOrbit_mk, inv_inv,
        UpperHalfPlane.psl2zToPSL2R_smul]⟩

private theorem fixedCosetEquivEllipticTranslateOrbit_val (Γ' : Subgroup PSL(2, ℤ)) {z₀ : ℍ}
    {s : PSL(2, ℤ)} {p : ℕ} (hp : 0 < p)
    (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    (hcard : Nat.card (Subgroup.zpowers s) = p)
    (q : {q : PSL(2, ℤ) ⧸ Γ' // s • q = q}) :
    (fixedCosetEquivEllipticTranslateOrbit Γ' hp hstab hcard q).val =
      inverseTranslateOrbit Γ' z₀ q.val :=
  (rfl)

private def ellipticTranslateIEquivOrderTwo (Γ' : Subgroup PSL(2, ℤ)) :
    {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
      (∃ g : PSL(2, ℤ), o = Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g • I)) ∧
        cardStabilizerOnOrbit o = 2} ≃
      {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit o = 2} where
  toFun o := ⟨o.val, o.property.2⟩
  invFun o := ⟨o.val, ⟨by
    obtain ⟨o', ho'⟩ := o
    induction o' using Quotient.inductionOn with | h z =>
    rw [cardStabilizerOnOrbit_mk, ← Γ'.map_liftSL_sl2zToPSL2R] at ho'
    rcases Γ'.liftSL.exists_smul_eq_of_card_stabilizer_ne_one (z := z) (by omega) with
      ⟨γ, rfl, -⟩ | ⟨_, -, h3⟩
    · exact ⟨(γ : PSL(2, ℤ)), by rw [UpperHalfPlane.pslMk_smul]⟩
    · omega, o.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem ellipticTranslateIEquivOrderTwo_val (Γ' : Subgroup PSL(2, ℤ))
    (o : {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
      (∃ g : PSL(2, ℤ), o = Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g • I)) ∧
        cardStabilizerOnOrbit o = 2}) :
    (ellipticTranslateIEquivOrderTwo Γ' o).val = o.val :=
  (rfl)

private def ellipticTranslateRhoEquivOrderThree (Γ' : Subgroup PSL(2, ℤ)) :
    {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
      (∃ g : PSL(2, ℤ), o = Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g • ρ)) ∧
        cardStabilizerOnOrbit o = 3} ≃
      {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit o = 3} where
  toFun o := ⟨o.val, o.property.2⟩
  invFun o := ⟨o.val, ⟨by
    obtain ⟨o', ho'⟩ := o
    induction o' using Quotient.inductionOn with | h z =>
    rw [cardStabilizerOnOrbit_mk, ← Γ'.map_liftSL_sl2zToPSL2R] at ho'
    rcases Γ'.liftSL.exists_smul_eq_of_card_stabilizer_ne_one (z := z) (by omega) with
      ⟨_, -, h2⟩ | ⟨γ, rfl, -⟩
    · omega
    · exact ⟨(γ : PSL(2, ℤ)), by rw [UpperHalfPlane.pslMk_smul]⟩, o.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem ellipticTranslateRhoEquivOrderThree_val (Γ' : Subgroup PSL(2, ℤ))
    (o : {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
      (∃ g : PSL(2, ℤ), o = Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g • ρ)) ∧
        cardStabilizerOnOrbit o = 3}) :
    (ellipticTranslateRhoEquivOrderThree Γ' o).val = o.val :=
  (rfl)

/-- **Order-`2` elliptic orbits via `S`-fixed cosets.** The cosets in `PSL(2, ℤ) ⧸ Γ'` fixed by
`S` are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having stabilizer
order `2`: the fixed coset `g Γ'` maps to the orbit of `g⁻¹ • i`. -/
def fixedCosetSEquivOrderTwoEllipticOrbits (Γ' : Subgroup PSL(2, ℤ)) :
    {q : PSL(2, ℤ) ⧸ Γ' // (S : PSL(2, ℤ)) • q = q} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} :=
  (fixedCosetEquivEllipticTranslateOrbit Γ' two_pos stabilizer_psl_I_eq_zpowers
    (by rw [Nat.card_zpowers, orderOf_coe_S])).trans (ellipticTranslateIEquivOrderTwo Γ')

/-- Evaluating `fixedCosetSEquivOrderTwoEllipticOrbits` on `g Γ'` gives the orbit of `g⁻¹ • i`. -/
@[simp]
theorem fixedCosetSEquivOrderTwoEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ)) (g : PSL(2, ℤ))
    (hg : (S : PSL(2, ℤ)) • (g : PSL(2, ℤ) ⧸ Γ') = g) :
    (fixedCosetSEquivOrderTwoEllipticOrbits Γ' ⟨g, hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • I) := by
  rw [fixedCosetSEquivOrderTwoEllipticOrbits, Equiv.trans_apply,
    ellipticTranslateIEquivOrderTwo_val, fixedCosetEquivEllipticTranslateOrbit_val,
    inverseTranslateOrbit_mk, UpperHalfPlane.psl2zToPSL2R_smul]

/-- **Order-`3` elliptic orbits via `R`-fixed cosets.** The cosets in `PSL(2, ℤ) ⧸ Γ'` fixed by
`R = S T` are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having
stabilizer order `3`: the fixed coset `g Γ'` maps to the orbit of `g⁻¹ • ρ`. -/
def fixedCosetREquivOrderThreeEllipticOrbits (Γ' : Subgroup PSL(2, ℤ)) :
    {q : PSL(2, ℤ) ⧸ Γ' // (R : PSL(2, ℤ)) • q = q} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} :=
  (fixedCosetEquivEllipticTranslateOrbit Γ' (by decide) stabilizer_psl_ρ_eq_zpowers
    (by rw [Nat.card_zpowers, orderOf_coe_R])).trans (ellipticTranslateRhoEquivOrderThree Γ')

/-- Evaluating `fixedCosetREquivOrderThreeEllipticOrbits` on `g Γ'` gives the orbit of
`g⁻¹ • ρ`. -/
@[simp]
theorem fixedCosetREquivOrderThreeEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ)) (g : PSL(2, ℤ))
    (hg : (R : PSL(2, ℤ)) • (g : PSL(2, ℤ) ⧸ Γ') = g) :
    (fixedCosetREquivOrderThreeEllipticOrbits Γ' ⟨g, hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • ρ) := by
  rw [fixedCosetREquivOrderThreeEllipticOrbits, Equiv.trans_apply,
    ellipticTranslateRhoEquivOrderThree_val, fixedCosetEquivEllipticTranslateOrbit_val,
    inverseTranslateOrbit_mk, UpperHalfPlane.psl2zToPSL2R_smul]

private def fixedPermEquivFixed (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (p : Perm (Fin n)) (a : PSL(2, ℤ))
    (hp : ∀ g : PSL(2, ℤ), p (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * a * g ∈ Γ') :
    {x : Fin n // p x = x} ≃ {q : PSL(2, ℤ) ⧸ Γ' // a • q = q} :=
  Equiv.subtypeEquiv e.symm fun x ↦ by
    obtain ⟨q, rfl⟩ := e.surjective x
    induction q using QuotientGroup.induction_on with | H g =>
    rw [e.symm_apply_apply, hp, TauCeti.smul_quotientGroup_mk_eq_self_iff]

private theorem fixedPermEquivFixed_mk (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (p : Perm (Fin n)) (a : PSL(2, ℤ))
    (hp : ∀ g : PSL(2, ℤ), p (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * a * g ∈ Γ')
    (g : PSL(2, ℤ)) (hg : p (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ')) :
    fixedPermEquivFixed Γ' e p a hp ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩ =
      ⟨(g : PSL(2, ℤ) ⧸ Γ'), by
        rw [TauCeti.smul_quotientGroup_mk_eq_self_iff, ← hp]; exact hg⟩ :=
  Subtype.ext (e.symm_apply_apply _)

/-- **Order-`2` elliptic orbits via fixed points of `permS`.** The fixed points of `permS Γ' e`
are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having stabilizer
order `2`: the fixed point `e (g Γ')` maps to the orbit of `g⁻¹ • i`. -/
def fixedPermSEquivOrderTwoEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    {x : Fin n // permS Γ' e x = x} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} :=
  (fixedPermEquivFixed Γ' e (permS Γ' e) (S : PSL(2, ℤ)) (permS_apply_eq_self_iff Γ' e)).trans
    (fixedCosetSEquivOrderTwoEllipticOrbits Γ')

/-- Evaluating `fixedPermSEquivOrderTwoEllipticOrbits` on `e (g Γ')` gives the orbit of
`g⁻¹ • i`. -/
@[simp]
theorem fixedPermSEquivOrderTwoEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ))
    (hg : permS Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ')) :
    (fixedPermSEquivOrderTwoEllipticOrbits Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • I) := by
  rw [fixedPermSEquivOrderTwoEllipticOrbits, Equiv.trans_apply, fixedPermEquivFixed_mk,
    fixedCosetSEquivOrderTwoEllipticOrbits_mk]

/-- **Order-`3` elliptic orbits via fixed points of `permR`.** The fixed points of `permR Γ' e`
are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having stabilizer
order `3`: the fixed point `e (g Γ')` maps to the orbit of `g⁻¹ • ρ`. -/
def fixedPermREquivOrderThreeEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    {x : Fin n // permR Γ' e x = x} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} :=
  (fixedPermEquivFixed Γ' e (permR Γ' e) (R : PSL(2, ℤ)) (permR_apply_eq_self_iff Γ' e)).trans
    (fixedCosetREquivOrderThreeEllipticOrbits Γ')

/-- Evaluating `fixedPermREquivOrderThreeEllipticOrbits` on `e (g Γ')` gives the orbit of
`g⁻¹ • ρ`. -/
@[simp]
theorem fixedPermREquivOrderThreeEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ))
    (hg : permR Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ')) :
    (fixedPermREquivOrderThreeEllipticOrbits Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • ρ) := by
  rw [fixedPermREquivOrderThreeEllipticOrbits, Equiv.trans_apply, fixedPermEquivFixed_mk,
    fixedCosetREquivOrderThreeEllipticOrbits_mk]

/-- Transporting fixed points between `(modularTriple Γ' e).σ0` and `permR Γ' e` via conjugation
by the involution `permS Γ' e`. -/
def fixedσ0EquivFixedPermR (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    {x : Fin n // (modularTriple Γ' e).σ0 x = x} ≃ {x : Fin n // permR Γ' e x = x} :=
  have hS_inv : (permS Γ' e)⁻¹ = permS Γ' e :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact modularTriple_σ1_sq Γ' e)
  have hS_idem (x : Fin n) : permS Γ' e (permS Γ' e x) = x := by
    rw [← Perm.mul_apply, ← sq, modularTriple_σ1_sq, Perm.one_apply]
  have hconj (x : Fin n) :
      permR Γ' e (permS Γ' e x) = permS Γ' e ((modularTriple Γ' e).σ0⁻¹ x) := by
    rw [permR_eq_permS_inv_mul_σ0_inv_mul_permS, Perm.mul_apply, Perm.mul_apply, hS_inv, hS_idem]
  have hiff (x : Fin n) :
      permR Γ' e (permS Γ' e x) = permS Γ' e x ↔ (modularTriple Γ' e).σ0 x = x := by
    rw [hconj, (permS Γ' e).injective.eq_iff, Perm.inv_eq_iff_eq, eq_comm]
  { toFun := fun ⟨x, hx⟩ ↦ ⟨permS Γ' e x, (hiff x).mpr hx⟩
    invFun := fun ⟨y, hy⟩ ↦ ⟨permS Γ' e y, (hiff (permS Γ' e y)).mp (by rwa [hS_idem])⟩
    left_inv := fun ⟨x, _⟩ ↦ Subtype.ext (hS_idem x)
    right_inv := fun ⟨y, _⟩ ↦ Subtype.ext (hS_idem y) }

/-- Evaluating `fixedσ0EquivFixedPermR` on `e (g Γ')` gives `e ((S * g) Γ')`. -/
@[simp]
theorem fixedσ0EquivFixedPermR_mk (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ))
    (hg : (modularTriple Γ' e).σ0 (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ')) :
    (fixedσ0EquivFixedPermR Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩).val =
      e ((((S : PSL(2, ℤ)) * g : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) := by
  simp only [fixedσ0EquivFixedPermR, Equiv.coe_fn_mk]
  dsimp only [permS]
  rw [modularTriple_σ1, Equiv.permutationRepresentation_apply, e.symm_apply_apply,
    MulAction.Quotient.smul_mk, smul_eq_mul]

/-- **Order-`3` elliptic orbits via fixed points of `σ0`.** The fixed points of
`(modularTriple Γ' e).σ0` are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on
`ℍ` having stabilizer order `3`: `e (g Γ')` maps to the orbit of `(S * g)⁻¹ • ρ`. -/
def fixedσ0EquivOrderThreeEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    {x : Fin n // (modularTriple Γ' e).σ0 x = x} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} :=
  (fixedσ0EquivFixedPermR Γ' e).trans (fixedPermREquivOrderThreeEllipticOrbits Γ' e)

/-- Evaluating `fixedσ0EquivOrderThreeEllipticOrbits` on `e (g Γ')` gives the orbit of
`((S : PSL(2, ℤ)) * g)⁻¹ • ρ`. -/
@[simp]
theorem fixedσ0EquivOrderThreeEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ))
    (hg : (modularTriple Γ' e).σ0 (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ')) :
    (fixedσ0EquivOrderThreeEllipticOrbits Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ)
        ((((S : PSL(2, ℤ)) * g)⁻¹ : PSL(2, ℤ)) • ρ) := by
  rw [fixedσ0EquivOrderThreeEllipticOrbits, Equiv.trans_apply]
  have hmk := fixedσ0EquivFixedPermR_mk Γ' e g hg
  have hprop := (fixedσ0EquivFixedPermR Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩).property
  rw [hmk] at hprop
  have heq : fixedσ0EquivFixedPermR Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩ =
      ⟨e ((((S : PSL(2, ℤ)) * g : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')), hprop⟩ :=
    Subtype.ext hmk
  rw [heq, fixedPermREquivOrderThreeEllipticOrbits_mk]

/-- The combinatorial count `ellipticTwo` equals the number of order-`2` elliptic orbits of
`Γ'.map psl2zToPSL2R` on `ℍ`. -/
theorem ellipticTwo_eq_card_orderTwoEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e =
      Nat.card {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
        cardStabilizerOnOrbit q = 2} := by
  rw [ellipticTwo_def, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
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
  let S (k : ℕ) : Set (orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ) :=
    {q | cardStabilizerOnOrbit q = k}
  have hunion : (Γ'.map psl2zToPSL2R).ellipticOrbits = S 2 ∪ S 3 := by
    ext q
    induction q using Quotient.inductionOn with | h z =>
    rw [Subgroup.quotientMk_mem_ellipticOrbits_iff, mem_freeLocus, ← Subgroup.card_eq_one,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq, cardStabilizerOnOrbit_mk,
      ← Γ'.map_liftSL_sl2zToPSL2R]
    refine ⟨fun hne ↦ ?_, fun h ↦ by rcases h with h2 | h3 <;> omega⟩
    rcases Γ'.liftSL.exists_smul_eq_of_card_stabilizer_ne_one hne with ⟨_, -, h2⟩ | ⟨_, -, h3⟩
    · exact Or.inl h2
    · exact Or.inr h3
  have hdisj : Disjoint (S 2) (S 3) :=
    Set.disjoint_left.mpr fun _ h2 h3 ↦ by rw [Set.mem_ofPred_eq] at h2 h3; omega
  have hfin₂ : (S 2).Finite :=
    Set.finite_coe_iff.mp (Finite.of_equiv _ (fixedPermSEquivOrderTwoEllipticOrbits Γ' e))
  have hfin₃ : (S 3).Finite :=
    Set.finite_coe_iff.mp (Finite.of_equiv _ (fixedPermREquivOrderThreeEllipticOrbits Γ' e))
  have hsum (k : ℕ) (hfin : (S k).Finite) :
      ∑ᶠ q ∈ S k, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) =
        (Nat.card (S k) : ℝ) * (1 - (k : ℝ)⁻¹) := by
    have hcongr : ∀ q ∈ S k, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) = (1 - (k : ℝ)⁻¹) :=
      fun q hq ↦ by rw [Set.mem_ofPred_eq] at hq; rw [hq]
    rw [finsum_mem_congr rfl hcongr, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
  have hcard2 : Nat.card (S 2) = ellipticTwo Γ' e :=
    (ellipticTwo_eq_card_orderTwoEllipticOrbits Γ' e).symm
  have hcard3 : Nat.card (S 3) = ellipticThree Γ' e :=
    (ellipticThree_eq_card_orderThreeEllipticOrbits Γ' e).symm
  rw [hunion, finsum_mem_union hdisj hfin₂ hfin₃, hsum 2 hfin₂, hsum 3 hfin₃, hcard2, hcard3]
  norm_num; ring

/-! ### Topological Euler characteristic and genus comparison -/

/-- **Comparison of Euler characteristics.** The finite-CW Euler characteristic of the
compactified modular curve `X(Γ')` equals the combinatorial Euler characteristic of the modular
triple `modularTriple Γ' e`. -/
theorem eulerChar_compactifiedQuotient_eq_eulerChar (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    letI := Γ'.finiteIndex_of_equiv e
    eulerChar (Γ'.map psl2zToPSL2R).CompactifiedQuotient = (modularTriple Γ' e).eulerChar := by
  let : Γ'.FiniteIndex := Γ'.finiteIndex_of_equiv e
  have : CompactSpace (Γ'.map psl2zToPSL2R).CompactifiedQuotient :=
    Γ'.compactSpace_compactifiedQuotient_map_psl2zToPSL2R
  have hle : Γ'.map psl2zToPSL2R ≤ psl2zToPSL2R.range := Γ'.map_le_range psl2zToPSL2R
  have hidx : ((Γ'.map psl2zToPSL2R).subgroupOf psl2zToPSL2R.range).index = n := by
    rw [← Subgroup.relIndex, Γ'.relIndex_map_psl2zToPSL2R, Γ'.index_eq_of_equiv e]
  have hRH := congrArg (Int.cast (R := ℝ))
    (TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree hle)
  rw [hidx, eulerChar_compactifiedQuotient] at hRH
  push_cast at hRH
  have hR := TauCeti.Fuchsian.ramificationDegree_eq_index_mul_cusps_add_elliptic_sub hle
    isCofinite_psl2zToPSL2RRange
  rw [hidx, Nat.card_unique, finsum_mem_ellipticOrbits_psl2zToPSL2RRange,
    ← cuspCount_eq_card_fuchsianCuspOrbit Γ' e,
    finsum_mem_ellipticOrbits_map_psl2zToPSL2R Γ' e] at hR
  have hcomb := congrArg (Int.cast (R := ℝ)) (six_mul_eulerChar_modularTriple Γ' e)
  push_cast at hcomb
  exact_mod_cast mul_left_cancel₀ (by norm_num : (6 : ℝ) ≠ 0) (by linarith :
    (6 : ℝ) * (eulerChar (Γ'.map psl2zToPSL2R).CompactifiedQuotient : ℝ) =
      (6 : ℝ) * ((modularTriple Γ' e).eulerChar : ℝ))

/-- **Comparison of combinatorial and topological genus.** For every finite-index subgroup
`Γ' ≤ PSL(2, ℤ)`, the combinatorial genus `genus Γ' e` agrees with the topological genus
`TauCeti.RiemannSurface.genus` of the compactified modular curve `X(Γ')`. -/
theorem genus_eq_riemannSurface_genus (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    letI := Γ'.finiteIndex_of_equiv e
    genus Γ' e = RiemannSurface.genus (Γ'.map psl2zToPSL2R).CompactifiedQuotient := by
  let : Γ'.FiniteIndex := Γ'.finiteIndex_of_equiv e
  exact (RiemannSurface.genus_eq_of_eulerChar_eq
    ((eulerChar_compactifiedQuotient_eq_eulerChar Γ' e).trans
      (two_sub_two_mul_genus Γ' e).symm)).symm

end TauCeti.ModularGroup
