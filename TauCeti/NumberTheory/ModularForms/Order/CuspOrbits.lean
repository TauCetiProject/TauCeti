/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.NumberTheory.ModularForms.QExpansion.Irregular
import Mathlib.NumberTheory.ModularForms.NormTrace
import TauCeti.Analysis.Complex.Fuchsian.Cusp.ChangeScaling
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.NumberTheory.ModularForms.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Vanishing orders on cusp orbits of `Γ \ ∂ℍ`

For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, the cusps of the compactified modular curve
`(Γ.map sl2zToPSL2R).CompactifiedQuotient` are the cusp orbits `(Γ.map sl2zToPSL2R).CuspOrbit`.
Each normalized cusp datum `D` of `Γ.map sl2zToPSL2R` specifies a boundary cusp, a projective
scaling `σ ∈ PSL(2, ℝ)` sending that cusp to `∞`, and its projective width `D.width > 0`. Lifting
`σ` to `s ∈ SL(2, ℝ)` and reading `TauCeti.orderAtCusp D.width (f ∣[k] s⁻¹)` — half the order of
the `q₂`-expansion at period `2 * D.width`, matching `TauCeti.Subgroup.CuspDatum.automorphyUntwist`
— produces a `ℚ`-valued cusp order.

Two invariance facts let this order descend to `(Γ.map sl2zToPSL2R).CuspOrbit`:
1. Slashing an `h`-periodic function `g : ℍ → ℂ` by the inverse of an upper-triangular matrix
   `t ∈ SL(2, ℝ)` rescales its period to `t₀₀² * h` and multiplies its `cuspFunction` near `0` by
   `(t₁₁)^k` while rotating the `q`-coordinate by a nonzero constant, leaving both
   `qExpansionOrderAtCusp` and `orderAtCusp` unchanged.
2. At an integral representative `γ ∈ SL(2, ℤ)` with scaling `sl2zToPSL2R γ⁻¹`, the normalized
   cusp width `D.width` equals the projective width `widthInfty` of the conjugated arithmetic
   subgroup `γ⁻¹ Γ γ`. Comparing any cusp datum `D` and any lift `s` of `D.scaling` against an
   integral representative of `D.cuspOrbit` shows simultaneously that the order is independent of
   the lift `s`, of the scaling at the cusp, and of the cusp point chosen inside the `Γ`-orbit.

We also descend cusp regularity from `Subgroup.IsRegularAtInfty` on `γ⁻¹ Γ γ` to a representative-
independent predicate `IsRegularCusp Γ C` on `(Γ.map sl2zToPSL2R).CuspOrbit`, and record the
resulting parity dichotomy: `orderAtCuspOrbit f C` is a natural number at every regular cusp and in
every even weight, and has the form `m + 1 / 2` (`m : ℕ`) for a nonzero odd-weight form at an
irregular cusp.

## Main definitions

* `TauCeti.ModularForm.orderAtCuspDatum`: the `ℚ`-valued vanishing order of a slash-invariant form
  at a normalized cusp datum `D` of `Γ.map sl2zToPSL2R`.
* `TauCeti.ModularForm.orderAtCuspOrbit`: the `ℚ`-valued vanishing order descended to a cusp orbit
  `C : (Γ.map sl2zToPSL2R).CuspOrbit`.
* `TauCeti.ModularForm.IsRegularCusp`: regularity of a cusp orbit `C` of `Γ`.

## Main results

* `TauCeti.qExpansionOrderAtCusp_slash_mapGL_inv` and `TauCeti.orderAtCusp_slash_mapGL_inv`:
  invariance of `q`-expansion and rational cusp orders under upper-triangular `SL(2, ℝ)` scalings.
* `TauCeti.ModularForm.cuspDatum_width_eq_widthInfty`: at `D.scaling = sl2zToPSL2R γ⁻¹`, the datum
  width `D.width` equals the projective width `widthInfty` of `γ⁻¹ Γ γ`.
* `TauCeti.ModularForm.orderAtCuspDatum_eq_orderAtCusp_slash` and
  `TauCeti.ModularForm.orderAtCuspDatum_eq_of_cuspOrbit_eq`: independence of the `SL(2, ℝ)` lift,
  cusp scaling, and cusp-orbit representative.
* `TauCeti.ModularForm.orderAtCuspOrbit_cuspOrbit` and
  `TauCeti.ModularForm.orderAtCuspOrbit_cuspOrbitOfSL2Z`: evaluation at any cusp datum or integral
  matrix representative.
* `TauCeti.ModularForm.orderAtCuspOrbit_modularForm_mul`: additivity on products of nonzero forms.
* `TauCeti.ModularForm.exists_orderAtCuspOrbit_eq_natCast_of_isRegularCusp`,
  `TauCeti.ModularForm.exists_orderAtCuspOrbit_eq_natCast_of_even`, and
  `TauCeti.ModularForm.exists_orderAtCuspOrbit_eq_natCast_add_half_of_odd_of_not_isRegularCusp`:
  integrality and half-integrality of `orderAtCuspOrbit`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§2.4,
  3.2–3.3, 3.6, and the errata to pp. 74–75.
-/

public noncomputable section

open Complex Filter Function Matrix Matrix.SpecialLinearGroup Metric MulAction OnePoint
  UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise Topology

namespace TauCeti

section UpperTriangularScaling

variable {h : ℝ} {k : ℤ} {g : ℍ → ℂ} {t : SL(2, ℝ)}

private lemma coe_inv_smul_of_apply_one_zero_eq_zero (ht : t 1 0 = 0) (τ : ℍ) :
    ((t⁻¹ • τ : ℍ) : ℂ) = (t 1 1 : ℂ) ^ 2 * τ - t 0 1 * t 1 1 := by
  have hdet : (t 0 0 : ℂ) * t 1 1 = 1 := by
    have hd := t.det_coe
    rw [Matrix.det_fin_two, ht, mul_zero, sub_zero] at hd
    exact_mod_cast hd
  have hsmul := UpperHalfPlane.coe_smul_of_apply_zero_one_eq_zero ht (t⁻¹ • τ)
  rw [smul_inv_smul] at hsmul
  calc ((t⁻¹ • τ : ℍ) : ℂ)
      = 1 ^ 2 * (t⁻¹ • τ : ℍ) + (1 - 1) * (t 0 1 * t 1 1) := by ring
    _ = ((t 0 0 : ℂ) * t 1 1) ^ 2 * (t⁻¹ • τ : ℍ) +
          ((t 0 0 : ℂ) * t 1 1 - 1) * (t 0 1 * t 1 1) := by rw [hdet]
    _ = (t 1 1 : ℂ) ^ 2 * ((t 0 0 : ℂ) ^ 2 * (t⁻¹ • τ : ℍ) + t 0 0 * t 0 1) -
          t 0 1 * t 1 1 := by ring
    _ = (t 1 1 : ℂ) ^ 2 * τ - t 0 1 * t 1 1 := by rw [← hsmul]

private lemma slash_mapGL_inv_apply_of_apply_one_zero_eq_zero (ht : t 1 0 = 0) (g : ℍ → ℂ)
    (τ : ℍ) :
    (g ∣[k] mapGL ℝ t⁻¹) τ = (t 1 1 : ℂ) ^ k * g (t⁻¹ • τ) := by
  have h := Matrix.SpecialLinearGroup.slash_mapGL_inv_apply_smul t k g (t⁻¹ • τ)
  rw [smul_inv_smul] at h
  rw [h]
  simp [UpperHalfPlane.denom, mapGL_coe_matrix, ht]

/-- Slashing an `h`-periodic function by the inverse of an upper-triangular `t ∈ SL(2, ℝ)` produces
a function periodic of period `t₀₀² * h`. -/
lemma periodic_slash_mapGL_inv_of_apply_one_zero_eq_zero (ht : t 1 0 = 0)
    (hg_per : Periodic (g ∘ ofComplex) h) :
    Periodic ((g ∣[k] mapGL ℝ t⁻¹) ∘ ofComplex) (t 0 0 ^ 2 * h : ℝ) := by
  have hdet : (t 0 0 : ℂ) * t 1 1 = 1 := by
    have hd := t.det_coe
    rw [Matrix.det_fin_two, ht, mul_zero, sub_zero] at hd
    exact_mod_cast hd
  have hg' := TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff.mp hg_per
  refine TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff.mpr fun τ ↦ ?_
  have hshift : t⁻¹ • ((t 0 0 ^ 2 * h) +ᵥ τ) = h +ᵥ (t⁻¹ • τ) := by
    apply UpperHalfPlane.ext
    rw [coe_inv_smul_of_apply_one_zero_eq_zero ht, coe_vadd, coe_vadd,
      coe_inv_smul_of_apply_one_zero_eq_zero ht]
    push_cast
    linear_combination (h : ℂ) * ((t 0 0 : ℂ) * t 1 1 + 1) * hdet
  rw [slash_mapGL_inv_apply_of_apply_one_zero_eq_zero ht, hshift, hg',
    slash_mapGL_inv_apply_of_apply_one_zero_eq_zero ht]

/-- Near `q = 0`, slashing an `h`-periodic function by `t⁻¹` (`t ∈ SL(2, ℝ)` upper triangular)
multiplies its `cuspFunction` at period `t₀₀² * h` by `t₁₁ ^ k` and rotates the `q`-parameter by
`exp (-2πi t₀₁ t₁₁ / h)`. -/
lemma cuspFunction_slash_mapGL_inv_eventuallyEq (hh : 0 < h) (ht : t 1 0 = 0)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹) =ᶠ[𝓝 0] fun q : ℂ ↦
      (t 1 1 : ℂ) ^ k *
        cuspFunction h g (Complex.exp (-2 * Real.pi * Complex.I * (t 0 1 * t 1 1) / h) * q) := by
  have hdet : t 0 0 * t 1 1 = 1 := by
    have hd := t.det_coe
    rw [Matrix.det_fin_two, ht, mul_zero, sub_zero] at hd
    exact hd
  have ha0 : t 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hh' : 0 < t 0 0 ^ 2 * h := mul_pos (sq_pos_of_ne_zero ha0) hh
  have hper' := periodic_slash_mapGL_inv_of_apply_one_zero_eq_zero (k := k) ht hg_per
  set ζ : ℂ := Complex.exp (-2 * Real.pi * Complex.I * (t 0 1 * t 1 1) / h)
  have hne : cuspFunction (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹) =ᶠ[𝓝[≠] 0]
      fun q : ℂ ↦ (t 1 1 : ℂ) ^ k * cuspFunction h g (ζ * q) := by
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with q hq_ball hq_ne
    have him := Periodic.im_invQParam_pos_of_norm_lt_one hh' (mem_ball_zero_iff.mp hq_ball) hq_ne
    let τ : ℍ := ⟨Periodic.invQParam (t 0 0 ^ 2 * h) q, him⟩
    have hqτ : Periodic.qParam (t 0 0 ^ 2 * h) (τ : ℂ) = q :=
      Periodic.qParam_right_inv hh'.ne' hq_ne
    have hq_rel : Periodic.qParam h ((t⁻¹ • τ : ℍ) : ℂ) = ζ * q := by
      have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
      have haC : (t 0 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0
      have hdetC : (t 0 0 : ℂ) * t 1 1 = 1 := by exact_mod_cast hdet
      have hd_eq : (t 1 1 : ℂ) = (t 0 0 : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right hdetC
      rw [← hqτ, Periodic.qParam, Periodic.qParam, coe_inv_smul_of_apply_one_zero_eq_zero ht,
        ← Complex.exp_add]
      congr 1
      push_cast
      rw [hd_eq]
      field_simp
      ring
    rw [← hqτ, UpperHalfPlane.eq_cuspFunction τ hh'.ne' hper',
      slash_mapGL_inv_apply_of_apply_one_zero_eq_zero ht,
      ← UpperHalfPlane.eq_cuspFunction (t⁻¹ • τ) hh.ne' hg_per, hq_rel, hqτ]
  exact TauCeti.UpperHalfPlane.cuspFunction_eventuallyEq_nhds_of_continuousAt hne <|
    continuousAt_const.mul (hg.comp_of_eq (continuousAt_const.mul continuousAt_id) (mul_zero ζ))

/-- Analyticity at `q = 0` of `cuspFunction` is preserved under upper-triangular `SL(2, ℝ)`
scalings. -/
lemma analyticAt_cuspFunction_slash_mapGL_inv (hh : 0 < h) (ht : t 1 0 = 0)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    AnalyticAt ℂ (cuspFunction (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹)) 0 := by
  set ζ : ℂ := Complex.exp (-2 * Real.pi * Complex.I * (t 0 1 * t 1 1) / h)
  have han : AnalyticAt ℂ (fun q : ℂ ↦ (t 1 1 : ℂ) ^ k * cuspFunction h g (ζ * q)) 0 :=
    (analyticAt_const (v := (t 1 1 : ℂ) ^ k)).mul
      (hg.comp_of_eq ((analyticAt_const (v := ζ)).mul analyticAt_id) (mul_zero ζ))
  exact han.congr (cuspFunction_slash_mapGL_inv_eventuallyEq hh ht hg_per hg.continuousAt).symm

private lemma analyticOrderAt_const_mul_comp_const_mul {G : ℂ → ℂ} {c ζ : ℂ}
    (hG : AnalyticAt ℂ G 0) (hc : c ≠ 0) (hζ : ζ ≠ 0) :
    analyticOrderAt (fun q : ℂ ↦ c * G (ζ * q)) 0 = analyticOrderAt G 0 := by
  have hlin : AnalyticAt ℂ (fun q : ℂ ↦ ζ * q) 0 := analyticAt_const.mul analyticAt_id
  have hcomp : AnalyticAt ℂ (G ∘ fun q : ℂ ↦ ζ * q) 0 := hG.comp_of_eq hlin (mul_zero ζ)
  have hord_lin : analyticOrderAt (fun q : ℂ ↦ ζ * q - 0) 0 = 1 := by
    have heq : (fun q : ℂ ↦ ζ * q - 0) = (fun _ : ℂ ↦ ζ) * id := funext fun q ↦ by simp
    rw [heq, analyticOrderAt_mul analyticAt_const analyticAt_id,
      analyticAt_const.analyticOrderAt_eq_zero.mpr hζ, analyticOrderAt_id, zero_add]
  have hmul : (fun q : ℂ ↦ c * G (ζ * q)) = (fun _ : ℂ ↦ c) * (G ∘ fun q : ℂ ↦ ζ * q) := rfl
  rw [hmul, analyticOrderAt_mul analyticAt_const hcomp,
    analyticAt_const.analyticOrderAt_eq_zero.mpr hc, zero_add,
    AnalyticAt.analyticOrderAt_comp (by simpa using hG) hlin, mul_zero, hord_lin, mul_one]

/-- **Upper-triangular scaling invariance of `qExpansionOrderAtCusp`.** Slashing an `h`-periodic
function whose cusp function is analytic at `0` by `t⁻¹` (`t ∈ SL(2, ℝ)`, `t 1 0 = 0`) leaves its
`q`-expansion order unchanged when read at the rescaled width `t₀₀² * h`. -/
theorem qExpansionOrderAtCusp_slash_mapGL_inv (hh : 0 < h) (ht : t 1 0 = 0)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansionOrderAtCusp (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹) = qExpansionOrderAtCusp h g := by
  have hdet : t 0 0 * t 1 1 = 1 := by
    have hd := t.det_coe
    rw [Matrix.det_fin_two, ht, mul_zero, sub_zero] at hd
    exact hd
  have hd0 : (t 1 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (right_ne_zero_of_mul_eq_one hdet)
  rw [qExpansionOrderAtCusp_eq_analyticOrderAt
      (analyticAt_cuspFunction_slash_mapGL_inv hh ht hg_per hg),
    qExpansionOrderAtCusp_eq_analyticOrderAt hg,
    analyticOrderAt_congr (cuspFunction_slash_mapGL_inv_eventuallyEq hh ht hg_per hg.continuousAt),
    analyticOrderAt_const_mul_comp_const_mul hg (zpow_ne_zero k hd0) (Complex.exp_ne_zero _)]

/-- **Upper-triangular scaling invariance of `orderAtCusp`.** -/
theorem orderAtCusp_slash_mapGL_inv (hh : 0 < h) (ht : t 1 0 = 0)
    (hg_per : Periodic (g ∘ ofComplex) (2 * h : ℝ))
    (hg : AnalyticAt ℂ (cuspFunction (2 * h) g) 0) :
    orderAtCusp (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹) = orderAtCusp h g := by
  have hw : 2 * (t 0 0 ^ 2 * h) = t 0 0 ^ 2 * (2 * h) := by ring
  rw [orderAtCusp_def, orderAtCusp_def, hw,
    qExpansionOrderAtCusp_slash_mapGL_inv (by positivity) ht hg_per hg]

end UpperTriangularScaling

namespace ModularForm

private local instance isArithmeticConjMapGL {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
  simpa [← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv, map_mapGL]
    using Subgroup.IsArithmetic.conj (Γ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ γ)⁻¹

section IntegralCuspDatum

variable {Γ : Subgroup SL(2, ℤ)}

private lemma mapGL_transvection_eq_upperRightHom (w : ℝ) :
    mapGL ℝ (Matrix.SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) w) =
      Matrix.GeneralLinearGroup.upperRightHom w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mapGL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.GeneralLinearGroup.upperRightHom]

private lemma mapGL_neg_eq (A : SL(2, ℝ)) : mapGL ℝ (-A) = -mapGL ℝ A := by
  ext i j
  simp [mapGL_coe_matrix]

private lemma mapGL_map_intCast_eq (g : SL(2, ℤ)) :
    mapGL ℝ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) = mapGL ℝ g := by
  ext i j
  simp [mapGL_coe_matrix]

/-- If a normalized cusp datum `D` of `Γ.map sl2zToPSL2R` has scaling `sl2zToPSL2R γ⁻¹`, then its
cusp point is `sl2zToPSL2R γ • ∞`. -/
theorem cuspDatum_cusp_eq_of_scaling_eq {D : (Γ.map sl2zToPSL2R).CuspDatum} {γ : SL(2, ℤ)}
    (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    D.cusp = sl2zToPSL2R γ • (∞ : OnePoint ℝ) := by
  have h := D.scaling_smul_cusp
  rw [hσ, map_inv, inv_smul_eq_iff] at h
  exact h

private lemma cuspDatum_width_mem_periods {D : (Γ.map sl2zToPSL2R).CuspDatum} {γ : SL(2, ℤ)}
    (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    D.width ∈
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).periods := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  obtain ⟨g₀, hg₀, hg₀_eq⟩ := Subgroup.mem_map.mp D.generator.2
  have hconj : sl2zToPSL2R (γ⁻¹ * g₀ * γ) =
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom D.width := by
    simpa [map_mul, map_inv, hσ, hg₀_eq] using D.scaling_mul_generator_mul_inv
  rw [sl2zToPSL2R_apply, Matrix.ProjectiveSpecialLinearGroup.upperRightHom_apply,
    Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff] at hconj
  have hmem_conj : mapGL ℝ (γ⁻¹ * g₀ * γ) ∈ Γγ := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
      ConjAct.toConjAct_smul]
    simpa [map_mul, map_inv, mul_assoc] using Subgroup.mem_map_of_mem (mapGL ℝ) hg₀
  rw [← mapGL_map_intCast_eq (γ⁻¹ * g₀ * γ)] at hmem_conj
  rw [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff]
  rcases hconj with hpos | hneg
  · left
    rwa [← hpos, mapGL_transvection_eq_upperRightHom] at hmem_conj
  · right
    rwa [neg_eq_iff_eq_neg.mp hneg.symm, mapGL_neg_eq,
      mapGL_transvection_eq_upperRightHom] at hmem_conj

private lemma exists_mem_sl2zToPSL2R_conj_eq_upperRightHom_of_mem_periods {γ : SL(2, ℤ)} {w : ℝ}
    (hw : w ∈ (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).periods) :
    ∃ g₁ ∈ Γ, sl2zToPSL2R (γ⁻¹ * g₁ * γ) =
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom w := by
  rw [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff] at hw
  rcases hw with hp | hn
  · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
      ConjAct.toConjAct_smul] at hp
    obtain ⟨g₁, hg₁, hg₁_eq⟩ := Subgroup.mem_map.mp hp
    refine ⟨g₁, hg₁, ?_⟩
    have hM : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (γ⁻¹ * g₁ * γ) =
        Matrix.SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) w := by
      apply mapGL_injective (S := ℝ)
      rw [mapGL_map_intCast_eq, mapGL_transvection_eq_upperRightHom, map_mul, map_mul, map_inv,
        hg₁_eq]
      group
    rw [sl2zToPSL2R_apply, hM, Matrix.ProjectiveSpecialLinearGroup.upperRightHom_apply]
  · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
      ConjAct.toConjAct_smul] at hn
    obtain ⟨g₁, hg₁, hg₁_eq⟩ := Subgroup.mem_map.mp hn
    refine ⟨g₁, hg₁, ?_⟩
    have hM : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (γ⁻¹ * g₁ * γ) =
        -Matrix.SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) w := by
      apply mapGL_injective (S := ℝ)
      rw [mapGL_map_intCast_eq, mapGL_neg_eq, mapGL_transvection_eq_upperRightHom, map_mul,
        map_mul, map_inv, hg₁_eq]
      group
    rw [sl2zToPSL2R_apply, hM, Matrix.ProjectiveSpecialLinearGroup.mk_neg,
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom_apply]

private lemma widthInfty_mem_zmultiples_cuspDatum_width {D : (Γ.map sl2zToPSL2R).CuspDatum}
    {γ : SL(2, ℤ)} (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty ∈
      AddSubgroup.zmultiples D.width := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  obtain ⟨g₁, hg₁, hconj₁⟩ :=
    exists_mem_sl2zToPSL2R_conj_eq_upperRightHom_of_mem_periods Γγ.widthInfty_mem_periods
  have hconj₁' : D.scaling * sl2zToPSL2R g₁ * D.scaling⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom Γγ.widthInfty := by
    simpa [hσ, map_mul, map_inv] using hconj₁
  have hstab : (⟨sl2zToPSL2R g₁, Subgroup.mem_map_of_mem _ hg₁⟩ : Γ.map sl2zToPSL2R) ∈
      stabilizer (Γ.map sl2zToPSL2R) D.cusp := by
    rw [mem_stabilizer_iff, Subgroup.mk_smul]
    apply MulAction.injective D.scaling
    calc D.scaling • sl2zToPSL2R g₁ • D.cusp
        = (D.scaling * sl2zToPSL2R g₁ * D.scaling⁻¹) • D.scaling • D.cusp := by
            rw [mul_smul, mul_smul, inv_smul_smul]
      _ = D.scaling • D.cusp := by
            rw [hconj₁', D.scaling_smul_cusp,
              Matrix.ProjectiveSpecialLinearGroup.upperRightHom_smul_infty]
  obtain ⟨n, hn⟩ := D.mem_stabilizer_iff_conj.mp hstab
  rw [hconj₁'] at hn
  exact AddSubgroup.mem_zmultiples_iff.mpr
    ⟨n, by rw [zsmul_eq_mul, (Matrix.ProjectiveSpecialLinearGroup.upperRightHom_injective hn).symm]⟩

variable [Γ.FiniteIndex]

/-- If a normalized cusp datum `D` of `Γ.map sl2zToPSL2R` has scaling `sl2zToPSL2R γ⁻¹`, then its
cusp orbit is `Γ.cuspOrbitOfSL2Z γ`. -/
theorem cuspDatum_cuspOrbit_eq_of_scaling_eq {D : (Γ.map sl2zToPSL2R).CuspDatum} {γ : SL(2, ℤ)}
    (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    D.cuspOrbit = Γ.cuspOrbitOfSL2Z γ := by
  apply Subtype.ext
  rw [D.cuspOrbit_val, Γ.cuspOrbitOfSL2Z_val, cuspDatum_cusp_eq_of_scaling_eq hσ]

/-- **Compatibility of Fuchsian and arithmetic cusp widths.** At an integral scaling
`D.scaling = sl2zToPSL2R γ⁻¹`, the normalized Fuchsian cusp width `D.width` agrees with Mathlib's
projective width `widthInfty` of the conjugated arithmetic group `γ⁻¹ Γ γ`. -/
theorem cuspDatum_width_eq_widthInfty {D : (Γ.map sl2zToPSL2R).CuspDatum} {γ : SL(2, ℤ)}
    (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    D.width =
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (Γγ.periods_eq_zmultiples_widthInfty ▸ cuspDatum_width_mem_periods hσ)
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (widthInfty_mem_zmultiples_cuspDatum_width hσ)
  rw [zsmul_eq_mul] at hm hn
  have hmn : (m : ℝ) * n = 1 := mul_right_cancel₀ D.width_pos.ne' <| by
    calc (m : ℝ) * n * D.width
        = m * (n * D.width) := mul_assoc _ _ _
      _ = m * Γγ.widthInfty := by rw [hn]
      _ = 1 * D.width := by rw [hm, one_mul]
  have hm_pos : 0 ≤ m := by
    have : (0 : ℝ) < m * Γγ.widthInfty := hm ▸ D.width_pos
    exact_mod_cast (pos_of_mul_pos_left this Γγ.widthInfty_pos.le).le
  have hm1 : m = 1 := Int.eq_one_of_mul_eq_one_right hm_pos (by exact_mod_cast hmn)
  rw [← hm, hm1, Int.cast_one, one_mul]

end IntegralCuspDatum

private lemma slash_mapGL_ne_zero {k : ℤ} {g : ℍ → ℂ} (hg : g ≠ 0) (γ : SL(2, ℤ)) :
    (g ∣[k] mapGL ℝ γ) ≠ 0 := by
  intro h0
  have h1 := congrArg (· ∣[k] mapGL ℝ γ⁻¹) h0
  rw [← SlashAction.slash_mul, ← map_mul, mul_inv_cancel, map_one, SlashAction.slash_one,
    SlashAction.zero_slash] at h1
  exact hg h1

section OrderAtCuspOrbit

variable {Γ : Subgroup SL(2, ℤ)} {k k₁ k₂ : ℤ}
variable {F : Type*} [FunLike F ℍ ℂ]

/-- **The `ℚ`-valued vanishing order of a slash-invariant form at a normalized cusp datum `D` of
`Γ.map sl2zToPSL2R`.** It is `TauCeti.orderAtCusp D.width (f ∣[k] s⁻¹)` for a lift `s ∈ SL(2, ℝ)`
of `D.scaling`; for a modular form on finite-index `Γ`, `orderAtCuspDatum_eq_orderAtCusp_slash`
shows that every lift gives the same order. -/
def orderAtCuspDatum [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (D : (Γ.map sl2zToPSL2R).CuspDatum) (f : F) : ℚ :=
  TauCeti.orderAtCusp D.width
    ⇑(_root_.SlashInvariantForm.translate f
      (mapGL ℝ (QuotientGroup.mk_surjective D.scaling).choose⁻¹))

/-- **Simultaneous lift, scaling, and representative invariance.** For any normalized cusp datum `D`
of `Γ.map sl2zToPSL2R`, any lift `s ∈ SL(2, ℝ)` of `D.scaling`, and any integral matrix
`γ ∈ SL(2, ℤ)` representing `D.cuspOrbit`, the rational cusp order of `f ∣[k] s⁻¹` at width
`D.width` equals that of `f ∣[k] γ` at the projective width `widthInfty` of `γ⁻¹ Γ γ`. -/
theorem orderAtCusp_slash_scaling_inv_eq [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {D : (Γ.map sl2zToPSL2R).CuspDatum} {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling)
    {γ : SL(2, ℤ)} (hγ : Γ.cuspOrbitOfSL2Z γ = D.cuspOrbit) :
    TauCeti.orderAtCusp D.width (⇑f ∣[k] mapGL ℝ s⁻¹) =
      TauCeti.orderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) := by
  have : DiscreteTopology (Γ.map sl2zToPSL2R) := Γ.isCofinite_map_sl2zToPSL2R.discreteTopology
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  -- Compare `D` against an integral cusp datum `D₀` on the same orbit via `t = s * h₀ * s₀⁻¹`.
  obtain ⟨D₀, -, hD₀_scal⟩ :=
    (Γ.isCuspPoint_map_sl2zToPSL2R_smul_infty γ).exists_cuspDatum (σ := sl2zToPSL2R γ⁻¹)
      (by rw [map_inv, inv_smul_smul])
  have hD₀_orb : D₀.cuspOrbit = D.cuspOrbit :=
    (cuspDatum_cuspOrbit_eq_of_scaling_eq hD₀_scal).trans hγ
  obtain ⟨g₀, hg₀_cusp⟩ := mem_orbit_iff.mp ((D.cuspOrbit_eq_iff D₀).mp hD₀_orb.symm)
  obtain ⟨γ₀, hγ₀, hg₀_eq⟩ := Subgroup.mem_map.mp g₀.2
  set h₀ : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ₀
  set s₀ : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ⁻¹
  set t : SL(2, ℝ) := s * h₀ * s₀⁻¹ with ht_def
  have hcoe_t : ((t : SL(2, ℝ)) : PSL(2, ℝ)) = D.scaling * g₀ * D₀.scaling⁻¹ := by
    rw [ht_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs,
      ← sl2zToPSL2R_apply, hg₀_eq, ← sl2zToPSL2R_apply, hD₀_scal]
  have ht : t 1 0 = 0 := by
    have hfix : ((t : SL(2, ℝ)) : PSL(2, ℝ)) • (∞ : OnePoint ℝ) = ∞ := by
      rw [hcoe_t, mul_smul, mul_smul, inv_smul_eq_iff.mpr D₀.scaling_smul_cusp.symm,
        ← Subgroup.smul_def, hg₀_cusp, D.scaling_smul_cusp]
    rwa [OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hfix
  -- Read the width transformation off the scaling identity and apply upper-triangular invariance.
  have hσ (x : ℍ) : ((D.scaling • (g₀ : PSL(2, ℝ)) • x : ℍ) : ℂ) =
      (t 0 0 : ℂ) ^ 2 * (D₀.scaling • x : ℍ) + t 0 0 * t 0 1 := by
    rw [← UpperHalfPlane.coe_smul_of_apply_zero_one_eq_zero ht, ← UpperHalfPlane.pslMk_smul,
      hcoe_t, mul_smul, mul_smul, inv_smul_smul]
  have hw : D.width = t 0 0 ^ 2 * Γγ.widthInfty := by
    have hc := Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer g₀.2)
    have hw₀ := TauCeti.cuspDatum_width_eq_mul (D := D₀.conj hc) (D' := D)
      (by rw [_root_.Subgroup.CuspDatum.conj_cusp, ← hg₀_cusp, Subgroup.smul_def])
      (a := t 0 0 ^ 2) (b := t 0 0 * t 0 1) fun x ↦ by
        rw [_root_.Subgroup.CuspDatum.conj_scaling, mul_smul, Complex.ofReal_pow,
          Complex.ofReal_mul, ← hσ, smul_inv_smul]
    rwa [_root_.Subgroup.CuspDatum.conj_width, cuspDatum_width_eq_widthInfty hD₀_scal] at hw₀
  have hslash : ⇑f ∣[k] mapGL ℝ s⁻¹ = (⇑f ∣[k] mapGL ℝ γ) ∣[k] mapGL ℝ t⁻¹ := by
    have hs_inv : s⁻¹ = h₀ * s₀⁻¹ * t⁻¹ := by rw [ht_def]; group
    rw [hs_inv, map_mul, map_mul, mapGL_map_intCast_eq, map_inv, mapGL_map_intCast_eq, map_inv,
      inv_inv, SlashAction.slash_mul, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ₀)]
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hfγ_coe : ⇑fγ = ⇑f ∣[k] mapGL ℝ γ := rfl
  rw [hw, hslash, ← hfγ_coe]
  exact orderAtCusp_slash_mapGL_inv Γγ.widthInfty_pos ht
    (SlashInvariantFormClass.periodic_comp_ofComplex fγ Γγ.two_mul_widthInfty_mem_strictPeriods)
    (ModularFormClass.analyticAt_cuspFunction_zero fγ (mul_pos two_pos Γγ.widthInfty_pos)
      Γγ.two_mul_widthInfty_mem_strictPeriods)

/-- Every lift `s ∈ SL(2, ℝ)` of `D.scaling` computes `orderAtCuspDatum D f`. -/
theorem orderAtCuspDatum_eq_orderAtCusp_slash [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling) :
    orderAtCuspDatum D f = TauCeti.orderAtCusp D.width (⇑f ∣[k] mapGL ℝ s⁻¹) := by
  obtain ⟨γ, hγ⟩ := Γ.cuspOrbitOfSL2Z_surjective D.cuspOrbit
  rw [orderAtCuspDatum, _root_.SlashInvariantForm.coe_translate,
    orderAtCusp_slash_scaling_inv_eq f (QuotientGroup.mk_surjective D.scaling).choose_spec hγ,
    orderAtCusp_slash_scaling_inv_eq f hs hγ]

/-- Two normalized cusp data representing the same cusp orbit have the same vanishing order. -/
theorem orderAtCuspDatum_eq_of_cuspOrbit_eq [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {D D' : (Γ.map sl2zToPSL2R).CuspDatum} (h : D.cuspOrbit = D'.cuspOrbit) :
    orderAtCuspDatum D f = orderAtCuspDatum D' f := by
  obtain ⟨γ, hγ⟩ := Γ.cuspOrbitOfSL2Z_surjective D.cuspOrbit
  rw [orderAtCuspDatum, orderAtCuspDatum, _root_.SlashInvariantForm.coe_translate,
    _root_.SlashInvariantForm.coe_translate,
    orderAtCusp_slash_scaling_inv_eq f (QuotientGroup.mk_surjective D.scaling).choose_spec hγ,
    orderAtCusp_slash_scaling_inv_eq f (QuotientGroup.mk_surjective D'.scaling).choose_spec
      (hγ.trans h)]

/-- **The `ℚ`-valued vanishing order of a slash-invariant form on a cusp orbit
`C : (Γ.map sl2zToPSL2R).CuspOrbit`.** -/
def orderAtCuspOrbit [Γ.FiniteIndex] [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) : ℚ :=
  haveI : DiscreteTopology (Γ.map sl2zToPSL2R) := Γ.isCofinite_map_sl2zToPSL2R.discreteTopology
  orderAtCuspDatum C.cuspDatum f

/-- `orderAtCuspOrbit` evaluated on the cusp orbit of any normalized cusp datum `D` recovers
`orderAtCuspDatum D f`. -/
@[simp]
theorem orderAtCuspOrbit_cuspOrbit [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) :
    orderAtCuspOrbit f D.cuspOrbit = orderAtCuspDatum D f := by
  have : DiscreteTopology (Γ.map sl2zToPSL2R) := Γ.isCofinite_map_sl2zToPSL2R.discreteTopology
  exact orderAtCuspDatum_eq_of_cuspOrbit_eq f D.cuspOrbit.cuspOrbit_cuspDatum

/-- **Evaluation of `orderAtCuspOrbit` at an integral cusp representative `γ ∈ SL(2, ℤ)`.** The
order at `Γ.cuspOrbitOfSL2Z γ` is `TauCeti.orderAtCusp` of `f ∣[k] γ` at the projective width
`widthInfty` of `γ⁻¹ Γ γ`. -/
@[simp]
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (γ : SL(2, ℤ)) :
    orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) =
      TauCeti.orderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) := by
  have : DiscreteTopology (Γ.map sl2zToPSL2R) := Γ.isCofinite_map_sl2zToPSL2R.discreteTopology
  rw [orderAtCuspOrbit, orderAtCuspDatum, _root_.SlashInvariantForm.coe_translate]
  exact orderAtCusp_slash_scaling_inv_eq f
    (QuotientGroup.mk_surjective (Γ.cuspOrbitOfSL2Z γ).cuspDatum.scaling).choose_spec
    (Γ.cuspOrbitOfSL2Z γ).cuspOrbit_cuspDatum.symm

/-- The cusp order on every cusp orbit is nonnegative. -/
theorem orderAtCuspOrbit_nonneg [Γ.FiniteIndex]
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    0 ≤ orderAtCuspOrbit f C :=
  TauCeti.orderAtCusp_nonneg _ _

@[simp]
theorem orderAtCuspOrbit_zero [Γ.FiniteIndex] (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (0 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) C = 0 := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  simp [SlashAction.zero_slash, TauCeti.orderAtCusp_def]

/-- **Additivity on products at cusps**: for nonzero modular forms `f` and `g` on `Γ`, the cusp
order of `f.mul g` at every cusp orbit `C` is the sum of their cusp orders at `C`. -/
theorem orderAtCuspOrbit_modularForm_mul [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (f.mul g) C = orderAtCuspOrbit f C + orderAtCuspOrbit g C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k₁ := _root_.ModularForm.translate f (mapGL ℝ γ)
  let gγ : ModularForm Γγ k₂ := _root_.ModularForm.translate g (mapGL ℝ γ)
  have hfγ : (⇑fγ : ℍ → ℂ) ≠ 0 := slash_mapGL_ne_zero (fun h ↦ hf (DFunLike.ext' h)) γ
  have hgγ : (⇑gγ : ℍ → ℂ) ≠ 0 := slash_mapGL_ne_zero (fun h ↦ hg (DFunLike.ext' h)) γ
  have hfγ_coe : ⇑fγ = ⇑f ∣[k₁] mapGL ℝ γ := rfl
  have hgγ_coe : ⇑gγ = ⇑g ∣[k₂] mapGL ℝ γ := rfl
  have hprod : (⇑(f.mul g) ∣[k₁ + k₂] mapGL ℝ γ) = ⇑fγ * ⇑gγ := by
    rw [hfγ_coe, hgγ_coe]
    simp only [_root_.ModularForm.coe_mul, _root_.ModularForm.mul_slash, det_mapGL, Units.val_one,
      abs_one, one_smul]
  have h2w : 0 < 2 * Γγ.widthInfty := mul_pos two_pos Γγ.widthInfty_pos
  have hper := Γγ.two_mul_widthInfty_mem_strictPeriods
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, orderAtCuspOrbit_cuspOrbitOfSL2Z,
    orderAtCuspOrbit_cuspOrbitOfSL2Z, hprod]
  exact TauCeti.orderAtCusp_mul
    (ModularFormClass.analyticAt_cuspFunction_zero fγ h2w hper)
    (ModularFormClass.analyticAt_cuspFunction_zero gγ h2w hper)
    (analyticOrderAt_cuspFunction_ne_top h2w hper hfγ)
    (analyticOrderAt_cuspFunction_ne_top h2w hper hgγ)

/-- Since `(Γ.map sl2zToPSL2R).CuspOrbit` is finite for `[Γ.FiniteIndex]`, `orderAtCuspOrbit f` has
finite support. -/
theorem hasFiniteSupport_orderAtCuspOrbit [Γ.FiniteIndex]
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    Function.HasFiniteSupport (orderAtCuspOrbit (Γ := Γ) (k := k) f) :=
  Set.toFinite _

end OrderAtCuspOrbit

section RegularityAndParity

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}
variable {F : Type*} [FunLike F ℍ ℂ]

/-- **Regularity of a cusp orbit `C` of `Γ ≤ SL(2, ℤ)`.** A cusp orbit is regular when at every
integral matrix `γ ∈ SL(2, ℤ)` representing it, `∞` is a regular cusp of the conjugated subgroup
`γ⁻¹ Γ γ` (`Subgroup.IsRegularAtInfty`); `isRegularCusp_cuspOrbitOfSL2Z` shows that all
representatives agree. -/
def IsRegularCusp (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : Prop :=
  ∀ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C →
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty

private lemma isRegularAtInfty_conj_of_cuspOrbitOfSL2Z_eq {γ γ' : SL(2, ℤ)}
    (h : Γ.cuspOrbitOfSL2Z γ = Γ.cuspOrbitOfSL2Z γ') :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty ↔
      (ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty := by
  obtain ⟨g₀, hg₀, hc⟩ := (Γ.cuspOrbitOfSL2Z_eq_iff γ γ').mp h
  set m : SL(2, ℤ) := γ⁻¹ * g₀ * γ' with hm_def
  have hγ' : γ' = g₀⁻¹ * γ * m := by rw [hm_def]; group
  have hm_10 : (mapGL ℝ m) 1 0 = 0 := by
    simpa [mapGL_coe_matrix] using hc
  have hm_div : (mapGL ℝ m) 0 0 / (mapGL ℝ m) 1 1 = 1 := by
    have had : m 0 0 * m 1 1 = 1 := by
      simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using m.det_coe
    have heq : m 0 0 = m 1 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one had with h1 | h1
      · rw [h1, one_mul] at had
        rw [h1, had]
      · rw [h1, neg_one_mul, neg_eq_iff_eq_neg] at had
        rw [h1, had]
    have hd0 : ((m 1 1 : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast right_ne_zero_of_mul_eq_one had
    simpa [mapGL_coe_matrix, heq] using div_self hd0
  have hΓg₀ : ConjAct.toConjAct (mapGL ℝ g₀⁻¹)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) =
      (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [map_inv (mapGL ℝ), inv_inv]
    exact Subgroup.conjAct_pointwise_smul_eq_self
      (Subgroup.le_normalizer (Subgroup.mem_map_of_mem _ hg₀))
  have hconj : ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) =
      ConjAct.toConjAct (mapGL ℝ m)⁻¹ •
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) := by
    rw [hγ', map_mul, map_mul, _root_.mul_inv_rev, _root_.mul_inv_rev,
      ConjAct.toConjAct_mul, ConjAct.toConjAct_mul, mul_smul, mul_smul, hΓg₀]
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  have hsp : (ConjAct.toConjAct (mapGL ℝ m)⁻¹ • Γγ).strictPeriods = Γγ.strictPeriods := by
    ext x
    rw [Subgroup.mem_strictPeriods_conj_of_upperTriangular hm_10, hm_div, one_mul]
  have hp : (ConjAct.toConjAct (mapGL ℝ m)⁻¹ • Γγ).periods = Γγ.periods := by
    ext x
    rw [Subgroup.periods, Subgroup.periods, Subgroup.adjoinNegOne_conj,
      Subgroup.mem_strictPeriods_conj_of_upperTriangular hm_10, hm_div, one_mul]
  rw [hconj, Subgroup.IsRegularAtInfty, Subgroup.IsRegularAtInfty, hsp, hp]

/-- Regularity of `Γ.cuspOrbitOfSL2Z γ` is regularity at `∞` of `γ⁻¹ Γ γ`. -/
@[simp]
theorem isRegularCusp_cuspOrbitOfSL2Z (γ : SL(2, ℤ)) :
    IsRegularCusp Γ (Γ.cuspOrbitOfSL2Z γ) ↔
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty :=
  ⟨fun h ↦ h γ rfl, fun h _ hγ' ↦
    (isRegularAtInfty_conj_of_cuspOrbitOfSL2Z_eq hγ'.symm).mp h⟩

/-- When `-I ∈ Γ`, every cusp orbit of `Γ` is regular. -/
theorem isRegularCusp_of_neg_one_mem (h : (-1 : SL(2, ℤ)) ∈ Γ)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    IsRegularCusp Γ C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [isRegularCusp_cuspOrbitOfSL2Z]
  refine Subgroup.isRegularAtInfty_of_neg_one_mem ?_
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have hneg : (-1 : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [← Matrix.SpecialLinearGroup.mapGL_neg_one (R := ℤ)]
    exact Subgroup.mem_map_of_mem (mapGL ℝ) h
  simpa using hneg

/-- At a regular cusp `Γ.cuspOrbitOfSL2Z γ`, the rational cusp order equals the integral
`q`-expansion order at width `widthInfty`. -/
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_qExpansionOrderAtCusp_of_isRegularCusp
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) {γ : SL(2, ℤ)}
    (hreg : IsRegularCusp Γ (Γ.cuspOrbitOfSL2Z γ)) :
    orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) =
      (qExpansionOrderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) : ℚ) := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hw_mem : Γγ.widthInfty ∈ Γγ.strictPeriods :=
    Γγ.isRegularAtInfty_iff.mp ((isRegularCusp_cuspOrbitOfSL2Z γ).mp hreg)
  have : Fact (IsCusp OnePoint.infty Γγ) :=
    ⟨Γγ.isCusp_of_mem_strictPeriods Γγ.widthInfty_pos hw_mem⟩
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z]
  exact TauCeti.orderAtCusp_eq_qExpansionOrderAtCusp Γγ.widthInfty_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex fγ hw_mem)
    (ModularFormClass.bdd_at_infty fγ) (ModularFormClass.holo fγ)

/-- At a regular cusp orbit, `orderAtCuspOrbit f C` is a natural number regardless of the weight. -/
theorem exists_orderAtCuspOrbit_eq_natCast_of_isRegularCusp
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hreg : IsRegularCusp Γ C) :
    ∃ m : ℕ, orderAtCuspOrbit f C = m := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_qExpansionOrderAtCusp_of_isRegularCusp f hreg,
    qExpansionOrderAtCusp_def]
  exact ⟨_, Int.cast_natCast _⟩

/-- In even weight, `orderAtCuspOrbit f C` is a natural number at every cusp orbit, regular or
irregular. -/
theorem exists_orderAtCuspOrbit_eq_natCast_of_even
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hk : Even k)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    ∃ m : ℕ, orderAtCuspOrbit f C = m := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  let fγ : ModularForm _ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z]
  exact exists_orderAtCusp_eq_natCast_of_even fγ hk

/-- For a nonzero modular form of odd weight, the cusp order at an irregular cusp orbit is strictly
half-integral: `m + 1 / 2` for some `m : ℕ`. -/
theorem exists_orderAtCuspOrbit_eq_natCast_add_half_of_odd_of_not_isRegularCusp
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (hk : Odd k) {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hirr : ¬IsRegularCusp Γ C) :
    ∃ m : ℕ, orderAtCuspOrbit f C = (m : ℚ) + 1 / 2 := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [isRegularCusp_cuspOrbitOfSL2Z] at hirr
  let fγ : ModularForm _ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hfγ : (⇑fγ : ℍ → ℂ) ≠ 0 := slash_mapGL_ne_zero hf γ
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z]
  exact exists_orderAtCusp_eq_natCast_add_half_of_odd_of_not_isRegularAtInfty fγ hfγ hk hirr

end RegularityAndParity

end ModularForm

end TauCeti

end
