/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic.Cusps
public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic.Elliptic
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
* **Elliptic orbits**: fixed points of `permS`, `permR`, and `σ0`
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
      TauCeti.Subgroup.integerCuspWidth ((ConjAct.toConjAct σ⁻¹ • Γ'.liftSL).map (mapGL ℝ)) := by
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
  obtain ⟨q, rfl⟩ := e.surjective i; obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g; exact ⟨σ⁻¹, by rwa [inv_inv]⟩

/-- The width at `∞` of each conjugate `σ⁻¹ (±Γ') σ`, the width of the cusp `σ ∞`, is one of the
cusp widths. -/
theorem integerCuspWidth_mem_cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (σ : SL(2, ℤ)) :
    TauCeti.Subgroup.integerCuspWidth ((ConjAct.toConjAct σ⁻¹ • Γ'.liftSL).map (mapGL ℝ)) ∈
      cuspWidths Γ' e := (mem_cuspWidths_iff Γ' e).mpr ⟨σ, rfl⟩

/-- The strict period subgroup of `Γ'.liftSL` in `GL(2, ℝ)` is generated by the `permT`-period of
the identity coset. -/
theorem strictPeriods_liftSL_eq_zmultiples (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Subgroup.strictPeriods (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples
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
  let gk : Γ'.map psl2zToPSL2R := ⟨sl2zToPSL2R (σ * _root_.ModularGroup.T ^ k * σ⁻¹), by
    rw [← psl2zToPSL2R_mk, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
      QuotientGroup.mk_inv]
    exact Subgroup.mem_map_of_mem psl2zToPSL2R hk⟩
  have hgk_conj : D.scaling * (gk : PSL(2, ℝ)) * D.scaling⁻¹ = upperRightHom (k : ℝ) := by
    dsimp only [gk]
    have hT : σ⁻¹ * (σ * _root_.ModularGroup.T ^ k * σ⁻¹) * σ = _root_.ModularGroup.T ^ k := by
      group
    rw [← psl2zToPSL2R_mk, conj_scaling_psl2zToPSL2R hσ, hT,
      TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow]
  have hgk_stab : gk ∈ stabilizer (Γ'.map psl2zToPSL2R) D.cusp := by
    rw [mem_stabilizer_iff]; apply MulAction.injective D.scaling; dsimp only
    rw [Subgroup.smul_def, ← mul_smul,
      ← inv_mul_cancel_right (D.scaling * (gk : PSL(2, ℝ))) D.scaling,
      mul_smul, D.scaling_smul_cusp, hgk_conj, upperRightHom_smul_infty]
  obtain ⟨r, hr⟩ := D.mem_stabilizer_iff_conj.mp hgk_stab
  exact ⟨r, (upperRightHom_injective (hgk_conj ▸ hr)).symm⟩

/-- At every cusp `σ • ∞`, the `permT`-period of `σ⁻¹ Γ'` equals `D.width` for any normalized
Fuchsian cusp datum `D` for `Γ'.map psl2zToPSL2R` with scaling `psl2zToPSL2R σ⁻¹`. -/
theorem natCast_minimalPeriod_permT_eq_cuspDatum_width (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ))
    (D : (Γ'.map psl2zToPSL2R).CuspDatum)
    (hσ : D.scaling = psl2zToPSL2R ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))) :
    (minimalPeriod (permT Γ' e)
      (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) = D.width := by
  set h := minimalPeriod (permT Γ' e) (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'))
  obtain ⟨g, hg, hgen⟩ := D.generator.property; obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  have hconj_eq : sl2zToPSL2R (σ⁻¹ * γ * σ) = upperRightHom D.width := by
    rw [← conj_scaling_psl2zToPSL2R hσ γ, hgen, D.scaling_mul_generator_mul_inv]
  have hc0 : (σ⁻¹ * γ * σ) 1 0 = 0 := by
    have h0 := (TauCeti.UpperHalfPlane.entries_of_coe_eq_upperRightHom
      ((sl2zToPSL2R_apply _).symm.trans hconj_eq)).1
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.map_apply,
      Int.coe_castRingHom] at h0; exact_mod_cast h0
  obtain ⟨k, hk⟩ := TauCeti.ModularGroup.exists_coe_eq_T_zpow_of_c_eq_zero hc0
  have hk_eq : (k : ℝ) = D.width := upperRightHom_injective <| by
    rw [← TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow, ← psl2zToPSL2R_mk, QuotientGroup.mk_zpow,
      ← hk, psl2zToPSL2R_mk, hconj_eq]
  have hk_mem : ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))⁻¹ * (T : PSL(2, ℤ)) ^ k *
      ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) ∈ Γ' := by
    rw [QuotientGroup.mk_inv, inv_inv, ← hk, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]; simpa [mul_assoc] using hg
  have hm_eq : (k.toNat : ℤ) = k :=
    Int.toNat_of_nonneg (by exact_mod_cast (hk_eq.symm ▸ D.width_pos : (0 : ℝ) < k).le)
  have hm_real : (k.toNat : ℝ) = D.width := by rw [← hk_eq]; exact_mod_cast hm_eq
  have hdvd1 : h ∣ k.toNat := by
    rw [minimalPeriod_permT_dvd_iff, ← zpow_natCast, hm_eq]; exact hk_mem
  have hTh_mem : (σ : PSL(2, ℤ)) * (T : PSL(2, ℤ)) ^ (h : ℤ) * (σ : PSL(2, ℤ))⁻¹ ∈ Γ' := by
    simpa [QuotientGroup.mk_inv, zpow_natCast] using
      (minimalPeriod_permT_dvd_iff Γ' e ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) h).mp dvd_rfl
  obtain ⟨r, hr_eq⟩ := cuspDatum_width_dvd_of_conj_T_zpow_mem hσ hTh_mem
  have hdvd2 : k.toNat ∣ h := Int.natCast_dvd_natCast.mp ⟨r, by
    rw [← hm_real] at hr_eq
    exact_mod_cast (by linear_combination -hr_eq : (h : ℝ) = k.toNat * r)⟩
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
  have hmul : D''.width =
      ((minimalPeriod (permT Γ'' e'')
          (e'' (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'')) /
        minimalPeriod (permT Γ' e')
          (e' (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℕ) : ℝ) * D'.width := by
    rw [← natCast_minimalPeriod_permT_eq_cuspDatum_width Γ'' e'' σ D'' hσ'',
      ← natCast_minimalPeriod_permT_eq_cuspDatum_width Γ' e' σ D' hσ', ← Nat.cast_mul,
      Nat.div_mul_cancel (minimalPeriod_permT_dvd_of_le h e'' e' ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)))]
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
@[simp] theorem permTCycleEquivFuchsianCuspOrbit_mk (Γ' : Subgroup PSL(2, ℤ))
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
@[simp] theorem permTCycleEquivFuchsianCuspOrbit_cuspCycleMapOfLE {Γ'' Γ' : Subgroup PSL(2, ℤ)}
    (h : Γ'' ≤ Γ') (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (q : Quotient (SameCycle.setoid (permT Γ'' e''))) :
    permTCycleEquivFuchsianCuspOrbit Γ' e' (cuspCycleMapOfLE h e'' e' q) =
      Subgroup.cuspOrbitMap (Subgroup.map_mono h) (permTCycleEquivFuchsianCuspOrbit Γ'' e'' q) :=
  cuspCycle_induction_on q fun g ↦ by
    rw [cuspCycleMapOfLE_mk, permTCycleEquivFuchsianCuspOrbit_mk,
      permTCycleEquivFuchsianCuspOrbit_mk, Subgroup.cuspOrbitMap_cuspOrbitMk]

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
@[simp] theorem permTCycleEquivCuspOrbits_mk (Γ' : Subgroup PSL(2, ℤ))
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
@[simp] theorem permTCycleEquivCuspOrbits_cuspCycleMapOfLE {Γ'' Γ' : Subgroup PSL(2, ℤ)}
    (h : Γ'' ≤ Γ') (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (q : Quotient (SameCycle.setoid (permT Γ'' e''))) :
    permTCycleEquivCuspOrbits Γ' e' (cuspCycleMapOfLE h e'' e' q) =
      CuspOrbits.map (Subgroup.map_mono (Subgroup.liftSL_le_liftSL_iff.mpr h))
        (permTCycleEquivCuspOrbits Γ'' e'' q) :=
  cuspCycle_induction_on q fun g ↦ by
    rw [cuspCycleMapOfLE_mk, permTCycleEquivCuspOrbits_mk, permTCycleEquivCuspOrbits_mk,
      CuspOrbits.map_mk]

/-! ### Elliptic orbits -/

/-- **Order-`2` elliptic orbits via fixed points of `permS`.** The fixed points of `permS Γ' e`
are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having stabilizer
order `2`: the fixed point `e (g Γ')` maps to the orbit of `g⁻¹ • i`. -/
def fixedPermSEquivOrderTwoEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    {x : Fin n // permS Γ' e x = x} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} :=
  (Equiv.subtypeEquivRight fun _ ↦ by rw [permS, modularTriple_σ1]).trans
    ((e.fixedPermutationRepresentationEquiv (S : PSL(2, ℤ))).trans
      (fixedCosetSEquivOrderTwoEllipticOrbits Γ'))

/-- Evaluating `fixedPermSEquivOrderTwoEllipticOrbits` on `e (g Γ')` gives the orbit of
`g⁻¹ • i`. -/
@[simp] theorem fixedPermSEquivOrderTwoEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ))
    (hg : permS Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ')) :
    (fixedPermSEquivOrderTwoEllipticOrbits Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • I) := by
  have hS : e.permutationRepresentation (S : PSL(2, ℤ)) (e (g : PSL(2, ℤ) ⧸ Γ')) =
      e (g : PSL(2, ℤ) ⧸ Γ') := by
    simpa [permS] using hg
  have hcoset :
      e.fixedPermutationRepresentationEquiv (S : PSL(2, ℤ)) ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hS⟩ =
        ⟨(g : PSL(2, ℤ) ⧸ Γ'), by
          rw [← MulAction.mem_stabilizer_iff,
            ← e.permutationRepresentation_apply_eq_self_iff]
          exact hS⟩ :=
    Subtype.ext (e.fixedPermutationRepresentationEquiv_apply (S : PSL(2, ℤ)) _ hS)
  rw [fixedPermSEquivOrderTwoEllipticOrbits, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.subtypeEquivRight_apply, hcoset, fixedCosetSEquivOrderTwoEllipticOrbits_mk]

/-- **Order-`3` elliptic orbits via fixed points of `permR`.** The fixed points of `permR Γ' e`
are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having stabilizer
order `3`: the fixed point `e (g Γ')` maps to the orbit of `g⁻¹ • ρ`. -/
def fixedPermREquivOrderThreeEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    {x : Fin n // permR Γ' e x = x} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} :=
  (Equiv.subtypeEquivRight fun _ ↦ by rw [permR_def]).trans
    ((e.fixedPermutationRepresentationEquiv (R : PSL(2, ℤ))).trans
      (fixedCosetREquivOrderThreeEllipticOrbits Γ'))

/-- Evaluating `fixedPermREquivOrderThreeEllipticOrbits` on `e (g Γ')` gives the orbit of
`g⁻¹ • ρ`. -/
@[simp] theorem fixedPermREquivOrderThreeEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ))
    (hg : permR Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ')) :
    (fixedPermREquivOrderThreeEllipticOrbits Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • ρ) := by
  have hR : e.permutationRepresentation (R : PSL(2, ℤ)) (e (g : PSL(2, ℤ) ⧸ Γ')) =
      e (g : PSL(2, ℤ) ⧸ Γ') := by
    simpa [permR_def] using hg
  have hcoset :
      e.fixedPermutationRepresentationEquiv (R : PSL(2, ℤ)) ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hR⟩ =
        ⟨(g : PSL(2, ℤ) ⧸ Γ'), by
          rw [← MulAction.mem_stabilizer_iff,
            ← e.permutationRepresentation_apply_eq_self_iff]
          exact hR⟩ :=
    Subtype.ext (e.fixedPermutationRepresentationEquiv_apply (R : PSL(2, ℤ)) _ hR)
  rw [fixedPermREquivOrderThreeEllipticOrbits, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.subtypeEquivRight_apply, hcoset, fixedCosetREquivOrderThreeEllipticOrbits_mk]

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
@[simp] theorem fixedσ0EquivOrderThreeEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ))
    (hg : (modularTriple Γ' e).σ0 (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ')) :
    (fixedσ0EquivOrderThreeEllipticOrbits Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ)
        ((((S : PSL(2, ℤ)) * g)⁻¹ : PSL(2, ℤ)) • ρ) := by
  have hmk : fixedσ0EquivFixedPermR Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩ =
      ⟨e ((((S : PSL(2, ℤ)) * g : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')), by
        rw [← fixedσ0EquivFixedPermR_mk Γ' e g hg]
        exact (fixedσ0EquivFixedPermR Γ' e ⟨e (g : PSL(2, ℤ) ⧸ Γ'), hg⟩).property⟩ :=
    Subtype.ext (fixedσ0EquivFixedPermR_mk Γ' e g hg)
  rw [fixedσ0EquivOrderThreeEllipticOrbits, Equiv.trans_apply, hmk,
    fixedPermREquivOrderThreeEllipticOrbits_mk]

/-- The combinatorial count `ellipticTwo` equals the number of order-`2` elliptic orbits of
`Γ'.map psl2zToPSL2R` on `ℍ`. -/
theorem ellipticTwo_eq_card_orderTwoEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e =
      Nat.card {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} := by
  rw [ellipticTwo_def, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    Nat.card_congr (fixedPermSEquivOrderTwoEllipticOrbits Γ' e)]

/-- The combinatorial count `ellipticThree` equals the number of order-`3` elliptic orbits of
`Γ'.map psl2zToPSL2R` on `ℍ`. -/
theorem ellipticThree_eq_card_orderThreeEllipticOrbits (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e =
      Nat.card {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} := by
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
    ext q; induction q using Quotient.inductionOn with | h z =>
    rw [Subgroup.quotientMk_mem_ellipticOrbits_iff, mem_freeLocus, ← Subgroup.card_eq_one,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq, cardStabilizerOnOrbit_mk,
      ← Γ'.map_liftSL_sl2zToPSL2R]
    refine ⟨fun hne ↦ ?_, fun h ↦ by rcases h with h2 | h3 <;> omega⟩
    rcases Γ'.liftSL.exists_smul_eq_of_card_stabilizer_ne_one hne with ⟨_, -, h2⟩ | ⟨_, -, h3⟩
    · exact Or.inl h2
    · exact Or.inr h3
  have hfin₂ : (S 2).Finite :=
    Set.finite_coe_iff.mp (Finite.of_equiv _ (fixedPermSEquivOrderTwoEllipticOrbits Γ' e))
  have hfin₃ : (S 3).Finite :=
    Set.finite_coe_iff.mp (Finite.of_equiv _ (fixedPermREquivOrderThreeEllipticOrbits Γ' e))
  have hsum (k : ℕ) (hfin : (S k).Finite) :
      ∑ᶠ q ∈ S k, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) =
        (Nat.card {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
          cardStabilizerOnOrbit q = k} : ℝ) * (1 - (k : ℝ)⁻¹) := by
    rw [finsum_mem_congr rfl fun q hq ↦ by rw [Set.mem_ofPred_eq.mp hq],
      finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul,
      ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
    dsimp only [S]
    rw [Set.coe_ofPred]
  rw [hunion, finsum_mem_union (Set.disjoint_left.mpr fun _ h2 h3 ↦ by
      rw [Set.mem_ofPred_eq] at h2 h3; omega) hfin₂ hfin₃, hsum 2 hfin₂, hsum 3 hfin₃,
    ← ellipticTwo_eq_card_orderTwoEllipticOrbits Γ' e,
    ← ellipticThree_eq_card_orderThreeEllipticOrbits Γ' e]
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
  have hle : Γ'.map psl2zToPSL2R ≤ psl2zToPSL2R.range := Γ'.map_le_range psl2zToPSL2R
  have hidx : ((Γ'.map psl2zToPSL2R).subgroupOf psl2zToPSL2R.range).index = n := by
    rw [← Subgroup.relIndex, Γ'.relIndex_map_psl2zToPSL2R, Γ'.index_eq_of_equiv e]
  have hRH := congrArg (Int.cast (R := ℝ))
    (TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree hle)
  rw [hidx, eulerChar_compactifiedQuotient] at hRH
  have hR := TauCeti.Fuchsian.ramificationDegree_eq_index_mul_cusps_add_elliptic_sub hle
    isCofinite_psl2zToPSL2RRange
  rw [hidx, Nat.card_unique, finsum_mem_ellipticOrbits_psl2zToPSL2RRange,
    ← cuspCount_eq_card_fuchsianCuspOrbit Γ' e,
    finsum_mem_ellipticOrbits_map_psl2zToPSL2R Γ' e] at hR
  have hcomb := congrArg (Int.cast (R := ℝ)) (six_mul_eulerChar_modularTriple Γ' e)
  push_cast at hRH hcomb
  exact_mod_cast mul_left_cancel₀ (by norm_num : (6 : ℝ) ≠ 0) (by linarith :
    (6 : ℝ) * (eulerChar (Γ'.map psl2zToPSL2R).CompactifiedQuotient : ℝ) =
      (6 : ℝ) * ((modularTriple Γ' e).eulerChar : ℝ))

/-- **Comparison of combinatorial and topological genus.** For every finite-index subgroup
`Γ' ≤ PSL(2, ℤ)`, the combinatorial genus `genus Γ' e` agrees with the topological genus
`TauCeti.RiemannSurface.genus` of the compactified modular curve `X(Γ')`. -/
theorem genus_eq_riemannSurface_genus (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    letI := Γ'.finiteIndex_of_equiv e
    genus Γ' e = RiemannSurface.genus (Γ'.map psl2zToPSL2R).CompactifiedQuotient := by
  let : Γ'.FiniteIndex := Γ'.finiteIndex_of_equiv e
  exact (RiemannSurface.genus_eq_of_eulerChar_eq <|
    (eulerChar_compactifiedQuotient_eq_eulerChar Γ' e).trans
      (two_sub_two_mul_genus Γ' e).symm).symm

end TauCeti.ModularGroup
