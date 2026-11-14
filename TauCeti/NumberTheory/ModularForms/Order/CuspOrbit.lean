/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Automorphy
public import TauCeti.NumberTheory.ModularForms.Order.AtCusp
import TauCeti.Analysis.Complex.Fuchsian.Cusp.ChangeScaling
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.NumberTheory.Modular.ConjugateTranslation
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.Irregular

/-!
# Geometric cusp orders on `(Γ.map sl2zToPSL2R).CuspOrbit`

For a finite-index subgroup `Γ ≤ SL(2, ℤ)` and its effective image `G = Γ.map sl2zToPSL2R ≤
PSL(2, ℝ)`, this file constructs the geometric `ℚ`-valued cusp order `orderAtCuspOrbit f C` on
`G.CuspOrbit`, links it to arbitrary Fuchsian cusp charts and to the local automorphy-sheaf chart
of `TauCeti/Analysis/Complex/Fuchsian/Cusp/Automorphy.lean`, and proves the exact integrality /
strict half-integrality dichotomy across regular and irregular cusps:

1. **Upper-triangular `SL(2, ℝ)` coordinate invariance**: slashing a bounded holomorphic periodic
   function on `ℍ` by `t⁻¹` for an upper-triangular `t ∈ SL(2, ℝ)` and rescaling the width by
   `t₀₀²` preserves both `qExpansionOrderAtCusp` and `orderAtCusp`.

2. **Normalized Fuchsian cusp data at integral representatives (`Subgroup.cuspDatumOfSL2Z`)**:
   every `γ ∈ SL(2, ℤ)` yields a normalized Fuchsian cusp datum of `G` at `γ • ∞` with scaling
   `(sl2zToPSL2R γ)⁻¹` whose Fuchsian width equals the projective cusp width `Γγ.widthInfty` of the
   conjugated group `Γγ = γ⁻¹ Γ γ`.

3. **Geometric cusp orders (`orderAtCuspOrbit`) and Fuchsian chart comparison**: the
   width-normalized `ℚ`-valued cusp order descends to `G.CuspOrbit`, agrees with
   `orderAtCusp D.width (f ∣[k] s⁻¹)` for *every* normalized Fuchsian cusp datum `D : G.CuspDatum`
   and lift `s ∈ SL(2, ℝ)` of `D.scaling`, and matches
   `(r : ℚ) / 2 + ord₀(automorphyDescent D s k r f)` in the local automorphy-sheaf chart.

4. **Regularity and half-integrality (`IsRegularCuspOrbit`)**: `Subgroup.IsRegularAtInfty` descends
   to `G.CuspOrbit`. For a nonzero form `f` of weight `k`, `orderAtCuspOrbit f C` is a natural
   number if and only if `k` is even or `C` is regular, and `m + 1 / 2` for a natural number `m` if
   and only if `k` is odd and `C` is irregular.

## Main declarations

* `TauCeti.qExpansionOrderAtCusp_slash_mapGL_inv_of_apply_one_zero_eq_zero` and
  `TauCeti.orderAtCusp_slash_mapGL_inv_of_apply_one_zero_eq_zero`: invariance of the cusp order
  under upper-triangular `SL(2, ℝ)` coordinate changes.
* `Subgroup.cuspDatumOfSL2Z`: the normalized Fuchsian cusp datum of `G` at `γ • ∞`, of width
  `(ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty`.
* `TauCeti.ModularForm.orderAtCuspOrbit`: the `ℚ`-valued cusp order on `G.CuspOrbit`, evaluated at
  integral representatives (`orderAtCuspOrbit_cuspOrbitOfSL2Z`), arbitrary Fuchsian cusp data
  (`orderAtCuspOrbit_cuspDatum`), and the automorphy-sheaf chart
  (`orderAtCuspOrbit_cuspDatum_eq_add_analyticOrderAt_automorphyDescent`).
* `TauCeti.ModularForm.IsRegularCuspOrbit`,
  `TauCeti.ModularForm.exists_nat_orderAtCuspOrbit_eq_iff`, and
  `TauCeti.ModularForm.exists_nat_orderAtCuspOrbit_eq_add_half_iff`: regularity of a cusp orbit and
  the exact integrality / strict half-integrality dichotomy.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§2.4,
  3.5–3.6 (with the errata to pp. 74–75 for irregular cusps in odd weight).
* [G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*][shimura1971], §2.1.
-/

public noncomputable section

open Complex Filter Function Matrix Matrix.SpecialLinearGroup Matrix.ProjectiveSpecialLinearGroup
  Metric MulAction OnePoint Subgroup UpperHalfPlane
open scoped Manifold MatrixGroups Modular ModularForm Pointwise Topology

namespace TauCeti

/-! ### Upper-triangular coordinate invariance of cusp orders -/

section UpperTriangularInvariance

private lemma denom_mapGL_inv_of_apply_one_zero_eq_zero {t : SL(2, ℝ)} (ht : t 1 0 = 0)
    (z : ℍ) : denom (mapGL ℝ t⁻¹) z = t 0 0 := by
  set s : SL(2, ℝ) := t⁻¹
  have hs10 : s 1 0 = 0 := by simp [s, ht]
  have hs11 : s 1 1 = t 0 0 := inv_apply_one_one t
  simp [denom, mapGL_coe_matrix, hs10, hs11]

private lemma slash_mapGL_inv_of_apply_one_zero_eq_zero_apply {g : ℍ → ℂ} {k : ℤ} {t : SL(2, ℝ)}
    (ht : t 1 0 = 0) (z : ℍ) :
    (g ∣[k] mapGL ℝ t⁻¹) z = g (t⁻¹ • z) * ((t 0 0 : ℝ) : ℂ) ^ (-k) := by
  rw [_root_.ModularForm.slash_apply, UpperHalfPlane.σ_eq_refl_of_det_pos (by simp),
    Matrix.SpecialLinearGroup.mapGL_smul, denom_mapGL_inv_of_apply_one_zero_eq_zero ht]
  simp [_root_.one_zpow]

/-- Upper-triangular coordinate change in `SL(2, ℝ)` rescales the `q`-parameter by a unit-modulus
phase while multiplying the width by `t₀₀²`. -/
private lemma qParam_inv_smul_of_apply_one_zero_eq_zero {h : ℝ} (hh : 0 < h) {t : SL(2, ℝ)}
    (ht : t 1 0 = 0) (z : ℍ) :
    Periodic.qParam h (t⁻¹ • z : ℍ) =
      Complex.exp (-2 * Real.pi * Complex.I * (t 1 1 * t 0 1) / h) *
        Periodic.qParam (t 0 0 ^ 2 * h) z := by
  have htinv10 : (t⁻¹ : SL(2, ℝ)) 1 0 = 0 := by simp [ht]
  have hdet : (t 0 0 : ℂ) * t 1 1 = 1 := by
    have hd := t.det_coe
    rw [Matrix.det_fin_two, ht, mul_zero, sub_zero] at hd
    exact_mod_cast hd
  have ht00 : (t 0 0 : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  rw [Periodic.qParam, Periodic.qParam, coe_smul_of_apply_zero_one_eq_zero htinv10,
    ← Complex.exp_add]
  simp only [inv_apply_zero_zero, inv_apply_zero_one]
  congr 1
  push_cast
  field_simp
  linear_combination (z : ℂ) * ((t 0 0 : ℂ) * t 1 1 + 1) * hdet

/-- Slashing a bounded function at `i∞` by the inverse of an upper-triangular `SL(2, ℝ)` matrix
preserves boundedness at `i∞`. -/
lemma isBoundedAtImInfty_slash_mapGL_inv_of_apply_one_zero_eq_zero {g : ℍ → ℂ} {k : ℤ}
    {t : SL(2, ℝ)} (ht : t 1 0 = 0) (hg : IsBoundedAtImInfty g) :
    IsBoundedAtImInfty (g ∣[k] mapGL ℝ t⁻¹) := by
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp hg
  have hdet : t 0 0 * t 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, ht, mul_zero, sub_zero] using t.det_coe
  have ht11 : 0 < t 1 1 ^ 2 := sq_pos_of_ne_zero (right_ne_zero_of_mul_eq_one hdet)
  have htinv10 : (t⁻¹ : SL(2, ℝ)) 1 0 = 0 := by simp [ht]
  refine isBoundedAtImInfty_iff.mpr ⟨‖((t 0 0 : ℝ) : ℂ) ^ (-k)‖ * max M 0, t 0 0 ^ 2 * max A 0,
    fun z hz ↦ ?_⟩
  have him : A ≤ (t⁻¹ • z).im := by
    have hcoe := congrArg Complex.im (coe_smul_of_apply_zero_one_eq_zero htinv10 z)
    simp only [inv_apply_zero_zero, inv_apply_zero_one, Complex.add_im, Complex.mul_im,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im, Complex.ofReal_re,
      zero_mul, add_zero, UpperHalfPlane.coe_im] at hcoe
    have hprod : t 1 1 ^ 2 * (t 0 0 ^ 2 * max A 0) = max A 0 := by
      have h1 : (t 1 1 * t 0 0) ^ 2 = 1 := by rw [mul_comm, hdet, one_pow]
      linear_combination max A 0 * h1
    have hle : max A 0 ≤ t 1 1 ^ 2 * z.im := by
      rw [← hprod]
      exact mul_le_mul_of_nonneg_left hz ht11.le
    linarith [le_max_left A 0]
  rw [slash_mapGL_inv_of_apply_one_zero_eq_zero_apply ht, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left ((hMA _ him).trans (le_max_left M 0)) (norm_nonneg _)

/-- Slashing an `h`-periodic function by the inverse of an upper-triangular `SL(2, ℝ)` matrix
produces a `(t₀₀² * h)`-periodic function. -/
lemma periodic_slash_mapGL_inv_of_apply_one_zero_eq_zero {h : ℝ} {g : ℍ → ℂ} {k : ℤ}
    {t : SL(2, ℝ)} (ht : t 1 0 = 0) (hg : Periodic (g ∘ ofComplex) h) :
    Periodic ((g ∣[k] mapGL ℝ t⁻¹) ∘ ofComplex) ((t 0 0 ^ 2 * h : ℝ)) := by
  refine _root_.UpperHalfPlane.periodic_comp_ofComplex fun z ↦ ?_
  have hdet : t 0 0 * t 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, ht, mul_zero, sub_zero] using t.det_coe
  have htinv10 : (t⁻¹ : SL(2, ℝ)) 1 0 = 0 := by simp [ht]
  have hsmul : t⁻¹ • ((t 0 0 ^ 2 * h) +ᵥ z) = h +ᵥ (t⁻¹ • z) := by
    apply UpperHalfPlane.ext
    rw [coe_smul_of_apply_zero_one_eq_zero htinv10, coe_vadd, coe_vadd,
      coe_smul_of_apply_zero_one_eq_zero htinv10]
    simp only [inv_apply_zero_zero, inv_apply_zero_one]
    push_cast
    have hdetC : (t 0 0 : ℂ) * t 1 1 = 1 := by exact_mod_cast hdet
    linear_combination (h : ℂ) * ((t 1 1 : ℂ) * t 0 0 + 1) * hdetC
  have hg_vadd : g (h +ᵥ (t⁻¹ • z)) = g (t⁻¹ • z) := by
    have hp := hg ((t⁻¹ • z : ℍ) : ℂ)
    rwa [Function.comp_apply, Function.comp_apply,
      show ((t⁻¹ • z : ℍ) : ℂ) + ↑h = ↑(h +ᵥ (t⁻¹ • z)) by rw [coe_vadd]; ring,
      ofComplex_apply, ofComplex_apply] at hp
  rw [slash_mapGL_inv_of_apply_one_zero_eq_zero_apply ht,
    slash_mapGL_inv_of_apply_one_zero_eq_zero_apply ht, hsmul, hg_vadd]

private lemma cuspFunction_slash_mapGL_inv_eventuallyEq_nhdsNE {h : ℝ} (hh : 0 < h)
    {g : ℍ → ℂ} {k : ℤ} {t : SL(2, ℝ)} (ht : t 1 0 = 0)
    (hg_per : Periodic (g ∘ ofComplex) h) :
    cuspFunction (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹) =ᶠ[𝓝[≠] 0]
      fun q ↦ ((t 0 0 : ℝ) : ℂ) ^ (-k) *
        cuspFunction h g (Complex.exp (-2 * Real.pi * Complex.I * (t 1 1 * t 0 1) / h) * q) := by
  have hdet : t 0 0 * t 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, ht, mul_zero, sub_zero] using t.det_coe
  have hw : 0 < t 0 0 ^ 2 * h := mul_pos (sq_pos_of_ne_zero (left_ne_zero_of_mul_eq_one hdet)) hh
  have hper' := periodic_slash_mapGL_inv_of_apply_one_zero_eq_zero (k := k) ht hg_per
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) one_pos)]
    with q hq0 hq
  rw [mem_ball_zero_iff] at hq
  set z : ℍ := ⟨Periodic.invQParam (t 0 0 ^ 2 * h) q,
    Periodic.im_invQParam_pos_of_norm_lt_one hw hq hq0⟩
  have hqz : Periodic.qParam (t 0 0 ^ 2 * h) z = q := Periodic.qParam_right_inv hw.ne' hq0
  change cuspFunction (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹) q =
    ((t 0 0 : ℝ) : ℂ) ^ (-k) *
      cuspFunction h g (Complex.exp (-2 * Real.pi * Complex.I * (t 1 1 * t 0 1) / h) * q)
  rw [← hqz, UpperHalfPlane.eq_cuspFunction z hw.ne' hper',
    slash_mapGL_inv_of_apply_one_zero_eq_zero_apply ht, mul_comm,
    ← qParam_inv_smul_of_apply_one_zero_eq_zero hh ht z,
    UpperHalfPlane.eq_cuspFunction (t⁻¹ • z) hh.ne' hg_per]

/-- **Upper-triangular invariance of `qExpansionOrderAtCusp`.** If `t ∈ SL(2, ℝ)` fixes `∞`
(`t 1 0 = 0`), slashing a bounded holomorphic `h`-periodic function by `t⁻¹` and rescaling the
width by `t₀₀²` preserves its `q`-expansion order at `∞`. -/
theorem qExpansionOrderAtCusp_slash_mapGL_inv_of_apply_one_zero_eq_zero {h : ℝ} (hh : 0 < h)
    {g : ℍ → ℂ} {k : ℤ} {t : SL(2, ℝ)} (ht : t 1 0 = 0)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg_bdd : IsBoundedAtImInfty g) (hg_mdiff : MDiff g) :
    qExpansionOrderAtCusp (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹) = qExpansionOrderAtCusp h g := by
  have hdet : t 0 0 * t 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, ht, mul_zero, sub_zero] using t.det_coe
  have ht00 : t 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hw : 0 < t 0 0 ^ 2 * h := mul_pos (sq_pos_of_ne_zero ht00) hh
  have han : AnalyticAt ℂ (cuspFunction h g) 0 :=
    analyticAt_cuspFunction_zero hh hg_per hg_mdiff hg_bdd
  have han' : AnalyticAt ℂ (cuspFunction (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹)) 0 :=
    analyticAt_cuspFunction_zero hw
      (periodic_slash_mapGL_inv_of_apply_one_zero_eq_zero ht hg_per)
      (hg_mdiff.slash k (mapGL ℝ t⁻¹))
      (isBoundedAtImInfty_slash_mapGL_inv_of_apply_one_zero_eq_zero ht hg_bdd)
  set ζ : ℂ := Complex.exp (-2 * Real.pi * Complex.I * (t 1 1 * t 0 1) / h)
  set c : ℂ := ((t 0 0 : ℝ) : ℂ) ^ (-k)
  have hc : c ≠ 0 := zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht00)
  have han_comp : AnalyticAt ℂ (fun q ↦ cuspFunction h g (ζ * q)) 0 :=
    han.comp_of_eq (by fun_prop) (mul_zero ζ)
  have heq : cuspFunction (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹) =ᶠ[𝓝 0]
      fun q ↦ c * cuspFunction h g (ζ * q) :=
    (han'.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (analyticAt_const.mul han_comp).continuousAt).mp
        (cuspFunction_slash_mapGL_inv_eventuallyEq_nhdsNE hh ht hg_per)
  have hcomp : analyticOrderAt (fun q ↦ cuspFunction h g (ζ * q)) 0 =
      analyticOrderAt (cuspFunction h g) 0 := by
    have hd : deriv (fun q : ℂ ↦ ζ * q) 0 ≠ 0 := by simp [ζ]
    simpa [Function.comp_def, mul_zero] using
      analyticOrderAt_comp_of_deriv_ne_zero (f := cuspFunction h g) (z₀ := (0 : ℂ))
        (by fun_prop) hd
  rw [qExpansionOrderAtCusp_eq_analyticOrderAt han', qExpansionOrderAtCusp_eq_analyticOrderAt han,
    analyticOrderAt_congr heq,
    show (fun q ↦ c * cuspFunction h g (ζ * q)) = (fun _ ↦ c) * fun q ↦ cuspFunction h g (ζ * q)
      from rfl,
    analyticOrderAt_mul analyticAt_const han_comp,
    analyticAt_const.analyticOrderAt_eq_zero.mpr hc, zero_add, hcomp]

/-- **Upper-triangular invariance of `orderAtCusp`.** Rescaling the width by `t₀₀²` after slashing
by `t⁻¹` for an upper-triangular `t ∈ SL(2, ℝ)` preserves the `ℚ`-valued cusp order. -/
theorem orderAtCusp_slash_mapGL_inv_of_apply_one_zero_eq_zero {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ}
    {k : ℤ} {t : SL(2, ℝ)} (ht : t 1 0 = 0) (hg_per : Periodic (g ∘ ofComplex) ((2 * h : ℝ)))
    (hg_bdd : IsBoundedAtImInfty g) (hg_mdiff : MDiff g) :
    orderAtCusp (t 0 0 ^ 2 * h) (g ∣[k] mapGL ℝ t⁻¹) = orderAtCusp h g := by
  have h2 : 2 * (t 0 0 ^ 2 * h) = t 0 0 ^ 2 * (2 * h) := by ring
  rw [orderAtCusp_def, orderAtCusp_def, h2,
    qExpansionOrderAtCusp_slash_mapGL_inv_of_apply_one_zero_eq_zero (by positivity) ht hg_per
      hg_bdd hg_mdiff]

end UpperTriangularInvariance

end TauCeti

/-! ### Normalized Fuchsian cusp data at integral representatives -/

namespace Subgroup

open TauCeti

section CuspDatumOfSL2Z

variable (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]

private local instance isArithmeticConjInv (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (H : Subgroup (GL (Fin 2) ℝ))).IsArithmetic :=
  Subgroup.isArithmetic_conj_of_mem (H := 𝒮ℒ) ⟨γ⁻¹, map_inv (mapGL ℝ) γ⟩

/-- The normalized Fuchsian cusp datum of `H.map sl2zToPSL2R` at `γ • ∞` with scaling
`(sl2zToPSL2R γ)⁻¹`. -/
def cuspDatumOfSL2Z (γ : SL(2, ℤ)) : (H.map sl2zToPSL2R).CuspDatum :=
  ((H.isCuspPoint_map_sl2zToPSL2R_smul_infty γ).exists_cuspDatum
    (inv_smul_smul (sl2zToPSL2R γ) (∞ : OnePoint ℝ))).choose

@[simp]
theorem cuspDatumOfSL2Z_cusp (γ : SL(2, ℤ)) :
    (H.cuspDatumOfSL2Z γ).cusp = sl2zToPSL2R γ • (∞ : OnePoint ℝ) :=
  ((H.isCuspPoint_map_sl2zToPSL2R_smul_infty γ).exists_cuspDatum
    (inv_smul_smul (sl2zToPSL2R γ) (∞ : OnePoint ℝ))).choose_spec.1

@[simp]
theorem cuspDatumOfSL2Z_scaling (γ : SL(2, ℤ)) :
    (H.cuspDatumOfSL2Z γ).scaling = (sl2zToPSL2R γ)⁻¹ :=
  ((H.isCuspPoint_map_sl2zToPSL2R_smul_infty γ).exists_cuspDatum
    (inv_smul_smul (sl2zToPSL2R γ) (∞ : OnePoint ℝ))).choose_spec.2

@[simp]
theorem cuspDatumOfSL2Z_cuspOrbit (γ : SL(2, ℤ)) :
    (H.cuspDatumOfSL2Z γ).cuspOrbit = H.cuspOrbitOfSL2Z γ := by
  apply Subtype.ext
  simp [CuspDatum.cuspOrbit_val, cuspDatumOfSL2Z_cusp]

private lemma sl2zToPSL2R_eq_upperRightHom_of_mapGL_eq {b : SL(2, ℤ)} {x : ℝ}
    (hmap : mapGL ℝ b = GeneralLinearGroup.upperRightHom x) :
    sl2zToPSL2R b = ProjectiveSpecialLinearGroup.upperRightHom x := by
  have h10 : b 1 0 = 0 := by
    have hR : (b 1 0 : ℝ) = 0 := by
      simpa [mapGL_coe_matrix, algebraMap_int_eq, GeneralLinearGroup.upperRightHom_apply] using
        congrArg (fun M : GL (Fin 2) ℝ ↦ (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0) hmap
    exact_mod_cast hR
  have h00 : b 0 0 = 1 := by
    have hR : (b 0 0 : ℝ) = 1 := by
      simpa [mapGL_coe_matrix, algebraMap_int_eq, GeneralLinearGroup.upperRightHom_apply] using
        congrArg (fun M : GL (Fin 2) ℝ ↦ (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0) hmap
    exact_mod_cast hR
  have h01 : (b 0 1 : ℝ) = x := by
    simpa [mapGL_coe_matrix, algebraMap_int_eq, GeneralLinearGroup.upperRightHom_apply] using
      congrArg (fun M : GL (Fin 2) ℝ ↦ (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hmap
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero h10 with hT | hT
  · rw [← h01]
    conv_lhs => rw [hT]
    exact TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow _
  · exfalso
    have hb00 : b 0 0 = -1 := by
      have := congrArg (fun M : SL(2, ℤ) ↦ (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0) hT
      simpa [ModularGroup.coe_T_zpow] using this
    omega

omit [H.FiniteIndex] in
/-- Every period of `γ⁻¹ H γ` is represented in `PSL(2, ℝ)` by `sl2zToPSL2R (γ⁻¹ * a * γ)` for
some `a ∈ H`. -/
private lemma exists_sl2zToPSL2R_eq_upperRightHom_of_mem_periods {γ : SL(2, ℤ)} {x : ℝ}
    (hx : x ∈ (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (H : Subgroup (GL (Fin 2) ℝ))).periods) :
    ∃ a ∈ H, sl2zToPSL2R (γ⁻¹ * a * γ) = ProjectiveSpecialLinearGroup.upperRightHom x := by
  simp only [Subgroup.periods, mem_strictPeriods_iff, mem_adjoinNegOne_iff,
    mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul, Subgroup.mem_map] at hx
  rcases hx with ⟨a, ha, ha_eq⟩ | ⟨a, ha, ha_eq⟩
  · refine ⟨a, ha, sl2zToPSL2R_eq_upperRightHom_of_mapGL_eq ?_⟩
    rw [map_mul, map_mul, map_inv, ha_eq]; group
  · refine ⟨a, ha, ?_⟩
    rw [← sl2zToPSL2R_neg]
    refine sl2zToPSL2R_eq_upperRightHom_of_mapGL_eq ?_
    have hneg1 : mapGL ℝ (-1 : SL(2, ℤ)) = -1 := mapGL_neg_one
    rw [← neg_one_mul (γ⁻¹ * a * γ), map_mul, hneg1, map_mul, map_mul, map_inv, ha_eq]
    simp [mul_assoc]

/-- Every integer multiple of `(H.cuspDatumOfSL2Z γ).width` belongs to the periods of `γ⁻¹ H γ`. -/
private lemma mem_periods_conj_inv_of_mem_zmultiples_width {γ : SL(2, ℤ)} {x : ℝ}
    (hx : x ∈ AddSubgroup.zmultiples (H.cuspDatumOfSL2Z γ).width) :
    x ∈ (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (H : Subgroup (GL (Fin 2) ℝ))).periods := by
  set D := H.cuspDatumOfSL2Z γ
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [zsmul_eq_mul]
  obtain ⟨a, ha, ha_eq⟩ := Subgroup.mem_map.mp (D.generator ^ n).2
  set b : SL(2, ℤ) := γ⁻¹ * a * γ with hb_def
  have hconj := D.scaling_mul_generator_zpow_mul_inv n
  rw [← Subgroup.coe_zpow, ← ha_eq, cuspDatumOfSL2Z_scaling, inv_inv, ← map_inv, ← map_mul,
    ← map_mul, ← hb_def] at hconj
  have h10 : b 1 0 = 0 :=
    (TauCeti.sl2zToPSL2R_smul_infty_eq_infty_iff _).mp
      (by rw [hconj, upperRightHom_smul_infty])
  simp only [Subgroup.periods, mem_strictPeriods_iff, mem_adjoinNegOne_iff,
    mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero h10 with hT | hT
  · left
    have hval : ((b 0 1 : ℤ) : ℝ) = n * D.width :=
      upperRightHom_injective (by
        rw [← TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow, ← hconj]; conv_rhs => rw [hT])
    rw [← hval, ← TauCeti.ModularGroup.mapGL_T_zpow_eq_upperRightHom, ← hT, hb_def]
    simpa [mul_assoc] using Subgroup.mem_map_of_mem (mapGL ℝ) ha
  · right
    set m : ℤ := -b 0 1
    have hTm : b = -ModularGroup.T ^ m := hT
    have hval : (m : ℝ) = n * D.width :=
      upperRightHom_injective (by
        rw [← TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow, ← hconj]
        conv_rhs => rw [hTm, sl2zToPSL2R_neg])
    rw [← hval, ← TauCeti.ModularGroup.mapGL_T_zpow_eq_upperRightHom]
    have h1 : a = -(γ * ModularGroup.T ^ m * γ⁻¹) := by
      have hgb : γ * b * γ⁻¹ = a := by rw [hb_def]; group
      rw [← hgb, hTm, mul_neg, neg_mul]
    have hmat : mapGL ℝ γ * -mapGL ℝ (ModularGroup.T ^ m) * (mapGL ℝ γ)⁻¹ = mapGL ℝ a := by
      have hneg1 : mapGL ℝ (-1 : SL(2, ℤ)) = -1 := mapGL_neg_one
      rw [h1, ← neg_one_mul (γ * ModularGroup.T ^ m * γ⁻¹), map_mul, hneg1, map_mul, map_mul,
        map_inv, mul_neg, neg_mul, neg_one_mul]
    rw [hmat]
    exact Subgroup.mem_map_of_mem (mapGL ℝ) ha

/-- **The Fuchsian width at `γ • ∞` in scaling `(sl2zToPSL2R γ)⁻¹` is the projective cusp width
`widthInfty` of `γ⁻¹ H γ`.** -/
@[simp]
theorem cuspDatumOfSL2Z_width (γ : SL(2, ℤ)) :
    (H.cuspDatumOfSL2Z γ).width =
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (H : Subgroup (GL (Fin 2) ℝ))).widthInfty := by
  set D := H.cuspDatumOfSL2Z γ
  symm
  refine Subgroup.strictWidthInfty_eq_of_strictPeriods_eq_zmultiples ?_ D.width_pos.le
  ext x
  refine ⟨fun hx ↦ ?_, mem_periods_conj_inv_of_mem_zmultiples_width H⟩
  obtain ⟨a, ha, hconj⟩ := exists_sl2zToPSL2R_eq_upperRightHom_of_mem_periods H hx
  have hstab : (⟨sl2zToPSL2R a, Subgroup.mem_map_of_mem _ ha⟩ : H.map sl2zToPSL2R) ∈
      stabilizer (H.map sl2zToPSL2R) D.cusp := by
    rw [mem_stabilizer_iff, Subgroup.smul_def, cuspDatumOfSL2Z_cusp]
    have hfix : sl2zToPSL2R (γ⁻¹ * a * γ) • (∞ : OnePoint ℝ) = ∞ := by
      rw [hconj, upperRightHom_smul_infty]
    rwa [map_mul, map_mul, map_inv, mul_smul, mul_smul, inv_smul_eq_iff] at hfix
  obtain ⟨n, hn⟩ := D.mem_stabilizer_iff_conj.mp hstab
  rw [cuspDatumOfSL2Z_scaling, inv_inv, ← map_inv, ← map_mul, ← map_mul, hconj] at hn
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by
    rw [zsmul_eq_mul, (upperRightHom_injective hn).symm]⟩

end CuspDatumOfSL2Z

end Subgroup

/-! ### Geometric cusp orders on `(Γ.map sl2zToPSL2R).CuspOrbit` -/

namespace TauCeti.ModularForm

section Cusps

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

private local instance isArithmeticConjInv (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic :=
  Subgroup.isArithmetic_conj_of_mem (H := 𝒮ℒ) ⟨γ⁻¹, map_inv (mapGL ℝ) γ⟩

omit [Γ.FiniteIndex] in
/-- Two normalized Fuchsian cusp data representing the same cusp orbit of `Γ.map sl2zToPSL2R` are
related by an upper-triangular `SL(2, ℝ)` matrix `t = s' * h * s⁻¹` whose `(0, 0)`-entry squared
rescales the width. -/
private lemma exists_upperTriangular_of_cuspOrbit_eq
    {D D' : (Γ.map sl2zToPSL2R).CuspDatum} (hDD' : D.cuspOrbit = D'.cuspOrbit)
    {s s' : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling) (hs' : (s' : PSL(2, ℝ)) = D'.scaling) :
    ∃ g ∈ Γ,
      let h : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g
      let t : SL(2, ℝ) := s' * h * s⁻¹
      t 1 0 = 0 ∧ D'.width = t 0 0 ^ 2 * D.width ∧
        mapGL ℝ s'⁻¹ = mapGL ℝ h * mapGL ℝ s⁻¹ * mapGL ℝ t⁻¹ := by
  obtain ⟨⟨_, g, hg, rfl⟩, hcusp⟩ := mem_orbit_iff.mp ((D'.cuspOrbit_eq_iff D).mp hDD'.symm)
  set h : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g
  have hh_psl : (h : PSL(2, ℝ)) = sl2zToPSL2R g := (sl2zToPSL2R_apply g).symm
  set γ_sub : Γ.map sl2zToPSL2R := ⟨sl2zToPSL2R g, Subgroup.mem_map_of_mem _ hg⟩
  set t : SL(2, ℝ) := s' * h * s⁻¹ with ht_def
  have ht_psl : (t : PSL(2, ℝ)) = D'.scaling * γ_sub * D.scaling⁻¹ := by
    rw [ht_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, hs', hh_psl]
  have ht10 : t 1 0 = 0 := by
    have hfix : (t : PSL(2, ℝ)) • (∞ : OnePoint ℝ) = ∞ := by
      rw [ht_psl, mul_smul, mul_smul, inv_smul_eq_iff.mpr D.scaling_smul_cusp.symm,
        ← Subgroup.smul_def, hcusp, D'.scaling_smul_cusp]
    rwa [OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff, coe_GL_coe_matrix] at hfix
  have hσ (x : ℍ) : ((D'.scaling • (γ_sub : PSL(2, ℝ)) • x : ℍ) : ℂ) =
      (t 0 0 : ℂ) ^ 2 * (D.scaling • x : ℍ) + t 0 0 * t 0 1 := by
    rw [← coe_smul_of_apply_zero_one_eq_zero ht10, ← UpperHalfPlane.pslMk_smul, ht_psl,
      mul_smul, mul_smul, inv_smul_smul]
  have hw : D'.width = t 0 0 ^ 2 * D.width := by
    have hc := Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer γ_sub.2)
    have hmul := TauCeti.cuspDatum_width_eq_mul (D := D.conj hc) (D' := D')
      (by rw [Subgroup.CuspDatum.conj_cusp, ← Subgroup.smul_def, hcusp])
      (a := t 0 0 ^ 2) (b := t 0 0 * t 0 1) fun x ↦ by
        rw [Subgroup.CuspDatum.conj_scaling, mul_smul, Complex.ofReal_pow, Complex.ofReal_mul,
          ← hσ, smul_inv_smul]
    rwa [Subgroup.CuspDatum.conj_width] at hmul
  have hrel : s'⁻¹ = h * s⁻¹ * t⁻¹ := by
    rw [ht_def]
    group
  refine ⟨g, hg, ht10, hw, ?_⟩
  rw [hrel, map_mul, map_mul]

/-- At an integral representative `γ ∈ SL(2, ℤ)`, `f ∣[k] mapGL ℝ γ` is `(2 * Γγ.widthInfty)`
periodic, bounded at `i∞`, and holomorphic. -/
private lemma slash_mapGL_int_cusp_props
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (γ : SL(2, ℤ)) :
    let Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
    Periodic ((⇑f ∣[k] mapGL ℝ γ) ∘ ofComplex) ((2 * Γγ.widthInfty : ℝ)) ∧
      IsBoundedAtImInfty (⇑f ∣[k] mapGL ℝ γ) ∧ MDiff (⇑f ∣[k] mapGL ℝ γ) := by
  intro Γγ
  set Fγ := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hcoe : (⇑Fγ : ℍ → ℂ) = ⇑f ∣[k] mapGL ℝ γ := _root_.ModularForm.coe_translate f (mapGL ℝ γ)
  have : Fact (IsCusp (∞ : OnePoint ℝ) Γγ) :=
    ⟨Γγ.isCusp_of_mem_strictPeriods (mul_pos two_pos Γγ.widthInfty_pos)
      Γγ.two_mul_widthInfty_mem_strictPeriods⟩
  exact ⟨hcoe ▸ SlashInvariantFormClass.periodic_comp_ofComplex Fγ
      Γγ.two_mul_widthInfty_mem_strictPeriods,
    hcoe ▸ ModularFormClass.bdd_at_infty Fγ,
    hcoe ▸ ModularFormClass.holo Fγ⟩

/-- Expresses `f ∣[k] mapGL ℝ s⁻¹` for an arbitrary normalized Fuchsian cusp datum `D` as an
upper-triangular coordinate change of `f ∣[k] mapGL ℝ γ` at an integral representative `γ` of
`D.cuspOrbit`. -/
private lemma exists_slash_cuspDatum_scaling_inv_eq
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling)
    {γ : SL(2, ℤ)} (hγ : Γ.cuspOrbitOfSL2Z γ = D.cuspOrbit) :
    ∃ t : SL(2, ℝ), t 1 0 = 0 ∧
      D.width = t 0 0 ^ 2 *
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty ∧
      ⇑f ∣[k] mapGL ℝ s⁻¹ = (⇑f ∣[k] mapGL ℝ γ) ∣[k] mapGL ℝ t⁻¹ := by
  set D₀ := Γ.cuspDatumOfSL2Z γ
  set s₀ : SL(2, ℝ) := (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)⁻¹
  have hs₀ : (s₀ : PSL(2, ℝ)) = D₀.scaling := by
    rw [cuspDatumOfSL2Z_scaling, QuotientGroup.mk_inv, sl2zToPSL2R_apply]
  obtain ⟨g, hg, ht10, hw, hrel⟩ := exists_upperTriangular_of_cuspOrbit_eq
    ((Γ.cuspDatumOfSL2Z_cuspOrbit γ).trans hγ) hs₀ hs
  have hs₀_inv : mapGL ℝ s₀⁻¹ = mapGL ℝ γ := by
    rw [inv_inv]; ext i j; simp [mapGL_coe_matrix, algebraMap_int_eq]
  have hg_mem : mapGL ℝ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) ∈
      (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    have heq : mapGL ℝ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) = mapGL ℝ g := by
      ext i j; simp [mapGL_coe_matrix, algebraMap_int_eq]
    exact heq ▸ Subgroup.mem_map_of_mem _ hg
  refine ⟨s * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g * s₀⁻¹, ht10, ?_, ?_⟩
  · rwa [cuspDatumOfSL2Z_width] at hw
  · rw [hrel, SlashAction.slash_mul, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f _ hg_mem, hs₀_inv]

/-- **For any Fuchsian cusp datum `D` of `Γ.map sl2zToPSL2R` and lift `s ∈ SL(2, ℝ)` of
`D.scaling`, the `ℚ`-valued cusp order of `f ∣[k] s⁻¹` matches that at any integral representative
of `D.cuspOrbit`.** -/
theorem orderAtCusp_cuspDatum_eq_of_cuspOrbitOfSL2Z_eq
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling)
    {γ : SL(2, ℤ)} (hγ : Γ.cuspOrbitOfSL2Z γ = D.cuspOrbit) :
    orderAtCusp D.width (⇑f ∣[k] mapGL ℝ s⁻¹) =
      orderAtCusp (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) := by
  obtain ⟨t, ht10, hw, hslash⟩ := exists_slash_cuspDatum_scaling_inv_eq f D hs hγ
  obtain ⟨hper, hbdd, hmdiff⟩ := slash_mapGL_int_cusp_props f γ
  rw [hw, hslash]
  exact orderAtCusp_slash_mapGL_inv_of_apply_one_zero_eq_zero
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty_pos ht10
    hper hbdd hmdiff

/-- For any normalized Fuchsian cusp datum `D` of `Γ.map sl2zToPSL2R` and lift `s ∈ SL(2, ℝ)` of
`D.scaling`, `f ∣[k] s⁻¹` is `(2 * D.width)`-periodic. -/
theorem periodic_slash_cuspDatum_scaling_inv
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling) :
    Periodic ((⇑f ∣[k] mapGL ℝ s⁻¹) ∘ ofComplex) ((2 * D.width : ℝ)) := by
  obtain ⟨γ, hγ⟩ := Γ.cuspOrbitOfSL2Z_surjective D.cuspOrbit
  obtain ⟨t, ht10, hw, hslash⟩ := exists_slash_cuspDatum_scaling_inv_eq f D hs hγ
  set wγ := (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
  have h2w : (2 * D.width : ℝ) = t 0 0 ^ 2 * (2 * wγ) := by rw [hw]; ring
  rw [hslash, h2w]
  exact periodic_slash_mapGL_inv_of_apply_one_zero_eq_zero ht10 (slash_mapGL_int_cusp_props f γ).1

/-- For any normalized Fuchsian cusp datum `D` of `Γ.map sl2zToPSL2R` and lift `s ∈ SL(2, ℝ)` of
`D.scaling`, `f ∣[k] s⁻¹` is bounded at `i∞`. -/
theorem isBoundedAtImInfty_slash_cuspDatum_scaling_inv
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling) :
    IsBoundedAtImInfty (⇑f ∣[k] mapGL ℝ s⁻¹) := by
  obtain ⟨γ, hγ⟩ := Γ.cuspOrbitOfSL2Z_surjective D.cuspOrbit
  obtain ⟨t, ht10, -, hslash⟩ := exists_slash_cuspDatum_scaling_inv_eq f D hs hγ
  rw [hslash]
  exact isBoundedAtImInfty_slash_mapGL_inv_of_apply_one_zero_eq_zero ht10
    (slash_mapGL_int_cusp_props f γ).2.1

/-- Representative invariance of the width-normalized cusp order across integral cusp
representatives `γ, γ' ∈ SL(2, ℤ)` of the same cusp orbit. -/
theorem orderAtCusp_eq_of_cuspOrbitOfSL2Z_eq
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) {γ γ' : SL(2, ℤ)}
    (h : Γ.cuspOrbitOfSL2Z γ = Γ.cuspOrbitOfSL2Z γ') :
    orderAtCusp (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) =
      orderAtCusp (ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ') := by
  set D := Γ.cuspDatumOfSL2Z γ
  set s : SL(2, ℝ) := (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)⁻¹
  have hs : (s : PSL(2, ℝ)) = D.scaling := by
    rw [cuspDatumOfSL2Z_scaling, QuotientGroup.mk_inv, sl2zToPSL2R_apply]
  have hs_inv : mapGL ℝ s⁻¹ = mapGL ℝ γ := by
    rw [inv_inv]; ext i j; simp [mapGL_coe_matrix, algebraMap_int_eq]
  rw [← cuspDatumOfSL2Z_width Γ γ, ← hs_inv]
  exact orderAtCusp_cuspDatum_eq_of_cuspOrbitOfSL2Z_eq f D hs
    (h.symm.trans (Γ.cuspDatumOfSL2Z_cuspOrbit γ).symm)

/-- **The geometric `ℚ`-valued vanishing order of `f` at `C ∈ (Γ.map sl2zToPSL2R).CuspOrbit`.**

Evaluated at any integral representative `γ ∈ SL(2, ℤ)` with `Γ.cuspOrbitOfSL2Z γ = C` it is
`orderAtCusp Γγ.widthInfty (f ∣[k] γ)` (`orderAtCuspOrbit_cuspOrbitOfSL2Z`), and at any normalized
Fuchsian cusp datum `D` representing `C` with scaling lift `s` it is
`orderAtCusp D.width (f ∣[k] s⁻¹)` (`orderAtCuspOrbit_cuspDatum`). -/
def orderAtCuspOrbit [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : ℚ :=
  let γ := Function.surjInv Γ.cuspOrbitOfSL2Z_surjective C
  orderAtCusp (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
    ⇑(_root_.SlashInvariantForm.translate f (mapGL ℝ γ))

lemma orderAtCuspOrbit_def [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit f C =
      orderAtCusp
        (ConjAct.toConjAct (mapGL ℝ (Function.surjInv Γ.cuspOrbitOfSL2Z_surjective C))⁻¹ •
          (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ (Function.surjInv Γ.cuspOrbitOfSL2Z_surjective C)) :=
  (rfl)

/-- **Integral-representative evaluation of `orderAtCuspOrbit`.** -/
@[simp]
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (γ : SL(2, ℤ)) :
    orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) =
      orderAtCusp (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) :=
  orderAtCusp_eq_of_cuspOrbitOfSL2Z_eq f (Function.surjInv_eq Γ.cuspOrbitOfSL2Z_surjective _)

/-- **Fuchsian cusp-chart evaluation of `orderAtCuspOrbit`.** At *any* normalized Fuchsian cusp
datum `D` of `Γ.map sl2zToPSL2R` and lift `s ∈ SL(2, ℝ)` of `D.scaling`, the geometric cusp order
agrees with `orderAtCusp D.width (f ∣[k] s⁻¹)`. -/
theorem orderAtCuspOrbit_cuspDatum
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling) :
    orderAtCuspOrbit f D.cuspOrbit = orderAtCusp D.width (⇑f ∣[k] mapGL ℝ s⁻¹) := by
  obtain ⟨γ, hγ⟩ := Γ.cuspOrbitOfSL2Z_surjective D.cuspOrbit
  rw [← hγ, orderAtCuspOrbit_cuspOrbitOfSL2Z,
    orderAtCusp_cuspDatum_eq_of_cuspOrbitOfSL2Z_eq f D hs hγ]

/-- For a nonzero modular form `f`, the doubled-width cusp function at any normalized Fuchsian cusp
datum `D` has finite analytic order at `0`. -/
private lemma analyticOrderAt_cuspFunction_slash_cuspDatum_ne_top
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling) :
    analyticOrderAt (cuspFunction (2 * D.width) (⇑f ∣[k] mapGL ℝ s⁻¹)) 0 ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hper := periodic_slash_cuspDatum_scaling_inv f D hs
  have hbdd := isBoundedAtImInfty_slash_cuspDatum_scaling_inv f D hs
  have hw2 : 0 < 2 * D.width := mul_pos two_pos D.width_pos
  have hmdiff : MDiff (⇑f ∣[k] mapGL ℝ s⁻¹) := (ModularFormClass.holo f).slash k (mapGL ℝ s⁻¹)
  have hdiff : DifferentiableOn ℂ (cuspFunction (2 * D.width) (⇑f ∣[k] mapGL ℝ s⁻¹)) (ball 0 1) :=
    differentiableOn_cuspFunction_ball hw2 hper hmdiff hbdd
  have heqOn : Set.EqOn (cuspFunction (2 * D.width) (⇑f ∣[k] mapGL ℝ s⁻¹)) 0 (ball 0 1) :=
    (hdiff.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball 0 1).isPreconnected (mem_ball_self one_pos) htop
  have hslash_zero : ⇑f ∣[k] mapGL ℝ s⁻¹ = 0 := by
    funext z
    rw [Pi.zero_apply, ← UpperHalfPlane.eq_cuspFunction (f := ⇑f ∣[k] mapGL ℝ s⁻¹) z hw2.ne' hper]
    exact heqOn (by
      rw [mem_ball_zero_iff]; exact_mod_cast Periodic.norm_qParam_lt_one hw2 z.im_pos)
  exact hf ((SlashAction.slash_eq_zero_iff k (mapGL ℝ s⁻¹) ⇑f).mp hslash_zero)

/-- **Comparison with the Fuchsian automorphy-sheaf chart (`Fuchsian/Cusp/Automorphy.lean`).**
For a nonzero modular form `f`, a normalized cusp datum `D`, lifts `s` of `D.scaling` and
`g ∈ Γ` of `D.generator`, and frame exponent `r < 2` satisfying the sign law
`((s * g * s⁻¹) 1 1) ^ k = (-1) ^ r`, the geometric cusp order `orderAtCuspOrbit f D.cuspOrbit`
is `(r : ℚ) / 2` plus the analytic order at `q = 0` of the local section coefficient
`automorphyDescent D s k r f`. -/
theorem orderAtCuspOrbit_cuspDatum_eq_add_analyticOrderAt_automorphyDescent
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling)
    {g : SL(2, ℤ)} (hgΓ : g ∈ Γ) (hg : sl2zToPSL2R g = D.generator) {r : ℕ} (hr : r < 2)
    (hk : ((s * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g * s⁻¹) 1 1 : ℝ) ^ k =
      (-1) ^ r) :
    orderAtCuspOrbit f D.cuspOrbit =
      (r : ℚ) / 2 +
        ((analyticOrderAt
          (TauCeti.Subgroup.CuspDatum.automorphyDescent D s k r ⇑f) 0).toNat : ℚ) := by
  set gR : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g
  have hgR : (gR : PSL(2, ℝ)) = D.generator := (sl2zToPSL2R_apply g).symm.trans hg
  have hlaw (τ : ℍ) (_ : τ ∈ TauCeti.Subgroup.CuspDatum.horodisc D 0) :
      f (gR • τ) = denom (mapGL ℝ gR) τ ^ k * f τ := by
    have hg_mem : mapGL ℝ gR ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := by
      have heq : mapGL ℝ gR = mapGL ℝ g := by
        ext i j; simp [gR, mapGL_coe_matrix, algebraMap_int_eq]
      exact heq ▸ Subgroup.mem_map_of_mem _ hgΓ
    exact Matrix.SpecialLinearGroup.mapGL_smul gR τ ▸
      SlashInvariantForm.slash_action_eqn'' f hg_mem τ
  have hbdd := isBoundedAtImInfty_slash_cuspDatum_scaling_inv f D hs
  have han : AnalyticAt ℂ (cuspFunction (2 * D.width) (⇑f ∣[k] mapGL ℝ s⁻¹)) 0 :=
    analyticAt_cuspFunction_zero (mul_pos two_pos D.width_pos)
      (periodic_slash_cuspDatum_scaling_inv f D hs)
      ((ModularFormClass.holo f).slash k (mapGL ℝ s⁻¹)) hbdd
  have hord := TauCeti.Subgroup.CuspDatum.analyticOrderAt_automorphyUntwist hs hgR hk hlaw
    (ModularFormClass.holo f).mdifferentiableOn hbdd le_rfl hr
  have hne_top : analyticOrderAt (TauCeti.Subgroup.CuspDatum.automorphyUntwist D s k ⇑f) 0 ≠ ⊤ := by
    rw [TauCeti.Subgroup.CuspDatum.automorphyUntwist_def]
    exact analyticOrderAt_cuspFunction_slash_cuspDatum_ne_top hf D hs
  have hd_ne_top : analyticOrderAt (TauCeti.Subgroup.CuspDatum.automorphyDescent D s k r ⇑f) 0 ≠
      ⊤ := fun hd ↦ hne_top (by rw [hord, hd]; simp)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hd_ne_top
  rw [orderAtCuspOrbit_cuspDatum f D hs, orderAtCusp_eq_half_analyticOrderAt han,
    ← TauCeti.Subgroup.CuspDatum.automorphyUntwist_def, hord, ← hm]
  have hcast : (r : ℕ∞) + (m : ℕ∞) * 2 = ((r + m * 2 : ℕ) : ℕ∞) := by norm_cast
  rw [hcast, ENat.toNat_natCast, ENat.toNat_natCast]
  push_cast
  ring

/-- Nonnegativity of `orderAtCuspOrbit`. -/
lemma orderAtCuspOrbit_nonneg [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : 0 ≤ orderAtCuspOrbit f C :=
  orderAtCusp_nonneg _ _

/-- Additivity of `orderAtCuspOrbit` on any form of weight `k₁ + k₂` whose underlying function is
the pointwise product of two nonzero modular forms of weights `k₁` and `k₂`. -/
theorem orderAtCuspOrbit_eq_add_of_coe_eq_mul {k₁ k₂ : ℤ}
    {F₁ F₂ F₃ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [SlashInvariantFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) (k₁ + k₂)]
    {f : F₁} {g : F₂} {fg : F₃} (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (hfg : (⇑fg : ℍ → ℂ) = ⇑f * ⇑g) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit fg C = orderAtCuspOrbit f C + orderAtCuspOrbit g C := by
  rw [orderAtCuspOrbit_def, orderAtCuspOrbit_def, orderAtCuspOrbit_def]
  set γ := Function.surjInv Γ.cuspOrbitOfSL2Z_surjective C
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  set fγ := _root_.ModularForm.translate f (mapGL ℝ γ)
  set gγ := _root_.ModularForm.translate g (mapGL ℝ γ)
  have hfγ : (⇑fγ : ℍ → ℂ) ≠ 0 := by
    rw [_root_.ModularForm.coe_translate f, ne_eq, SlashAction.slash_eq_zero_iff]; exact hf
  have hgγ : (⇑gγ : ℍ → ℂ) ≠ 0 := by
    rw [_root_.ModularForm.coe_translate g, ne_eq, SlashAction.slash_eq_zero_iff]; exact hg
  have hw2 : 0 < 2 * Γγ.widthInfty := mul_pos two_pos Γγ.widthInfty_pos
  have hper2 := Γγ.two_mul_widthInfty_mem_strictPeriods
  have : Fact (IsCusp (∞ : OnePoint ℝ) Γγ) := ⟨Γγ.isCusp_of_mem_strictPeriods hw2 hper2⟩
  have hprod : ⇑fg ∣[k₁ + k₂] mapGL ℝ γ = ⇑fγ * ⇑gγ := by
    rw [hfg, _root_.ModularForm.mul_slash, det_mapGL, Units.val_one, abs_one, one_smul,
      _root_.ModularForm.coe_translate, _root_.ModularForm.coe_translate]
  rw [hprod, ← _root_.ModularForm.coe_translate f, ← _root_.ModularForm.coe_translate g]
  exact orderAtCusp_mul (ModularFormClass.analyticAt_cuspFunction_zero fγ hw2 hper2)
    (ModularFormClass.analyticAt_cuspFunction_zero gγ hw2 hper2)
    (analyticOrderAt_cuspFunction_ne_top hw2 hper2 hfγ)
    (analyticOrderAt_cuspFunction_ne_top hw2 hper2 hgγ)

/-- Additivity of `orderAtCuspOrbit` on `ModularForm.mul`. -/
theorem _root_.ModularForm.orderAtCuspOrbit_mul {k₁ k₂ : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (f.mul g) C = orderAtCuspOrbit f C + orderAtCuspOrbit g C :=
  orderAtCuspOrbit_eq_add_of_coe_eq_mul hf hg (_root_.ModularForm.coe_mul f g) C

/-- Finite support of the cusp order divisor on `(Γ.map sl2zToPSL2R).CuspOrbit`. -/
theorem hasFiniteSupport_orderAtCuspOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (orderAtCuspOrbit (Γ := Γ) f).HasFiniteSupport :=
  Set.toFinite _

end Cusps

/-! ### Regularity and half-integrality of geometric cusp orbits -/

section Regularity

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

private local instance isArithmeticConjInv' (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic :=
  Subgroup.isArithmetic_conj_of_mem (H := 𝒮ℒ) ⟨γ⁻¹, map_inv (mapGL ℝ) γ⟩

private lemma exists_upperTriangular_conj_eq_of_cuspOrbitOfSL2Z_eq {γ γ' : SL(2, ℤ)}
    (h : Γ.cuspOrbitOfSL2Z γ = Γ.cuspOrbitOfSL2Z γ') :
    ∃ m : SL(2, ℤ), (mapGL ℝ m : GL (Fin 2) ℝ) 1 0 = 0 ∧
      ((mapGL ℝ m : GL (Fin 2) ℝ) 0 0 / (mapGL ℝ m : GL (Fin 2) ℝ) 1 1) = 1 ∧
      ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) =
        ConjAct.toConjAct (mapGL ℝ m)⁻¹ •
          (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) := by
  obtain ⟨g, hg, hc⟩ := (Γ.cuspOrbitOfSL2Z_eq_iff γ γ').mp h
  set m : SL(2, ℤ) := γ⁻¹ * g * γ'
  have hm10 : (mapGL ℝ m : GL (Fin 2) ℝ) 1 0 = 0 := by simp [mapGL_coe_matrix, hc]
  have hdiv : ((mapGL ℝ m : GL (Fin 2) ℝ) 0 0 / (mapGL ℝ m : GL (Fin 2) ℝ) 1 1) = 1 := by
    have had : m 0 0 * m 1 1 = 1 := by
      simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using m.det_coe
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨h00, h11⟩ | ⟨h00, h11⟩ <;>
      simp [mapGL_coe_matrix, algebraMap_int_eq, h00, h11]
  have hγ' : γ' = g⁻¹ * γ * m := by simp [m, mul_assoc]
  refine ⟨m, hm10, hdiv, ?_⟩
  have hinv_gl : (mapGL ℝ γ')⁻¹ = (mapGL ℝ m)⁻¹ * ((mapGL ℝ γ)⁻¹ * mapGL ℝ g) := by
    rw [hγ', map_mul, map_mul, map_inv]; group
  have hinv : ConjAct.toConjAct (mapGL ℝ γ')⁻¹ =
      ConjAct.toConjAct (mapGL ℝ m)⁻¹ *
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ * ConjAct.toConjAct (mapGL ℝ g)) := by
    rw [hinv_gl, ConjAct.toConjAct_mul, ConjAct.toConjAct_mul]
  rw [hinv, mul_smul, mul_smul,
    Subgroup.conjAct_pointwise_smul_eq_self
      (Subgroup.le_normalizer (Subgroup.mem_map_of_mem _ hg))]

/-- Equivalent integral cusp representatives yield conjugated subgroups with identical strict
periods. -/
theorem strictPeriods_conj_eq_of_cuspOrbitOfSL2Z_eq {γ γ' : SL(2, ℤ)}
    (h : Γ.cuspOrbitOfSL2Z γ = Γ.cuspOrbitOfSL2Z γ') :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods =
      (ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  obtain ⟨m, hm10, hdiv, hconj⟩ := exists_upperTriangular_conj_eq_of_cuspOrbitOfSL2Z_eq h
  ext x
  rw [hconj, Subgroup.mem_strictPeriods_conj_of_upperTriangular hm10, hdiv, one_mul]

/-- Equivalent integral cusp representatives yield conjugated subgroups with identical projective
cusp widths. -/
theorem widthInfty_conj_eq_of_cuspOrbitOfSL2Z_eq {γ γ' : SL(2, ℤ)}
    (h : Γ.cuspOrbitOfSL2Z γ = Γ.cuspOrbitOfSL2Z γ') :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty =
      (ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty := by
  obtain ⟨m, hm10, hdiv, hconj⟩ := exists_upperTriangular_conj_eq_of_cuspOrbitOfSL2Z_eq h
  rw [hconj, Subgroup.widthInfty_conj_of_upperTriangular _ hm10, hdiv, abs_one, div_one]

/-- Regularity at `∞` of the conjugated group `γ⁻¹ Γ γ` depends only on the cusp orbit of
`γ • ∞`. -/
theorem isRegularAtInfty_conj_iff_of_cuspOrbitOfSL2Z_eq {γ γ' : SL(2, ℤ)}
    (h : Γ.cuspOrbitOfSL2Z γ = Γ.cuspOrbitOfSL2Z γ') :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty ↔
      (ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty := by
  rw [Subgroup.isRegularAtInfty_iff, Subgroup.isRegularAtInfty_iff,
    strictPeriods_conj_eq_of_cuspOrbitOfSL2Z_eq h, widthInfty_conj_eq_of_cuspOrbitOfSL2Z_eq h]

/-- **Regularity of a geometric cusp orbit `C ∈ (Γ.map sl2zToPSL2R).CuspOrbit`.**

A cusp orbit `C` is regular when the conjugated subgroup `γ⁻¹ Γ γ` at any integral representative
`γ ∈ SL(2, ℤ)` of `C` is regular at `∞` (`strictPeriods = periods`, i.e., its minimal positive
period is achieved by a positive translation rather than only by a negative translation). -/
def IsRegularCuspOrbit (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : Prop :=
  let γ := Function.surjInv Γ.cuspOrbitOfSL2Z_surjective C
  (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty

lemma isRegularCuspOrbit_def (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    IsRegularCuspOrbit Γ C ↔
      (ConjAct.toConjAct (mapGL ℝ (Function.surjInv Γ.cuspOrbitOfSL2Z_surjective C))⁻¹ •
        (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty :=
  Iff.rfl

@[simp]
theorem isRegularCuspOrbit_cuspOrbitOfSL2Z (γ : SL(2, ℤ)) :
    IsRegularCuspOrbit Γ (Γ.cuspOrbitOfSL2Z γ) ↔
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty :=
  isRegularAtInfty_conj_iff_of_cuspOrbitOfSL2Z_eq
    (Function.surjInv_eq Γ.cuspOrbitOfSL2Z_surjective _)

/-- When `-I ∈ Γ`, every cusp orbit of `Γ` is regular. -/
theorem isRegularCuspOrbit_of_neg_one_mem (h : (-1 : SL(2, ℤ)) ∈ Γ)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : IsRegularCuspOrbit Γ C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [isRegularCuspOrbit_cuspOrbitOfSL2Z]
  apply Subgroup.isRegularAtInfty_of_neg_one_mem
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have hneg1 : mapGL ℝ (-1 : SL(2, ℤ)) = -1 := mapGL_neg_one
  have hneg : (-1 : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) :=
    hneg1 ▸ Subgroup.mem_map_of_mem (mapGL ℝ) h
  simpa using hneg

/-- **At a regular cusp, `orderAtCuspOrbit` agrees with the integer `q`-expansion order in the
projective cusp width `Γγ.widthInfty`.** -/
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z_of_isRegular
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) {γ : SL(2, ℤ)}
    (hreg : IsRegularCuspOrbit Γ (Γ.cuspOrbitOfSL2Z γ)) :
    orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) =
      (qExpansionOrderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) : ℚ) := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  set Fγ := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hw_mem : Γγ.widthInfty ∈ Γγ.strictPeriods :=
    Γγ.isRegularAtInfty_iff.mp ((isRegularCuspOrbit_cuspOrbitOfSL2Z γ).mp hreg)
  have : Fact (IsCusp (∞ : OnePoint ℝ) Γγ) :=
    ⟨Γγ.isCusp_of_mem_strictPeriods Γγ.widthInfty_pos hw_mem⟩
  have hper : Periodic ((⇑f ∣[k] mapGL ℝ γ) ∘ ofComplex) Γγ.widthInfty :=
    _root_.ModularForm.coe_translate f (mapGL ℝ γ) ▸
      SlashInvariantFormClass.periodic_comp_ofComplex Fγ hw_mem
  obtain ⟨-, hbdd, hmdiff⟩ := slash_mapGL_int_cusp_props f γ
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z]
  exact orderAtCusp_eq_qExpansionOrderAtCusp Γγ.widthInfty_pos hper hbdd hmdiff

/-- In even weight or at a regular cusp orbit, `orderAtCuspOrbit f C` is a natural number. -/
theorem exists_nat_orderAtCuspOrbit_eq_of_even_or_isRegular
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (h : Even k ∨ IsRegularCuspOrbit Γ C) :
    ∃ m : ℕ, orderAtCuspOrbit f C = m := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rcases h with hk | hreg
  · set Fγ := _root_.ModularForm.translate f (mapGL ℝ γ)
    rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
    exact exists_orderAtCusp_eq_natCast_of_even Fγ hk
  · set z := qExpansionOrderAtCusp
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
      (⇑f ∣[k] mapGL ℝ γ)
    refine ⟨z.toNat, ?_⟩
    rw [orderAtCuspOrbit_cuspOrbitOfSL2Z_of_isRegular f hreg, ← Int.cast_natCast,
      Int.toNat_of_nonneg (qExpansionOrderAtCusp_nonneg _ _)]

/-- For a nonzero odd-weight modular form at an irregular cusp orbit, `orderAtCuspOrbit f C` is
`m + 1 / 2` for some natural number `m` (in particular strictly positive). -/
theorem exists_nat_orderAtCuspOrbit_eq_add_half_of_odd_of_not_isRegular
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hk : Odd k) (hirr : ¬IsRegularCuspOrbit Γ C) :
    ∃ m : ℕ, orderAtCuspOrbit f C = (m : ℚ) + 1 / 2 := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set Fγ := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hFγ : (⇑Fγ : ℍ → ℂ) ≠ 0 := by
    rw [_root_.ModularForm.coe_translate f, ne_eq, SlashAction.slash_eq_zero_iff]; exact hf
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact exists_orderAtCusp_eq_natCast_add_half_of_odd_of_not_isRegularAtInfty Fγ hFγ hk
    (mt (isRegularCuspOrbit_cuspOrbitOfSL2Z γ).mpr hirr)

private lemma natCast_ne_natCast_add_half (n m : ℕ) : (n : ℚ) ≠ (m : ℚ) + 1 / 2 := by
  intro h
  have h2 : ((2 * n : ℕ) : ℚ) = ((2 * m + 1 : ℕ) : ℚ) := by
    push_cast
    linear_combination 2 * h
  exact absurd (Nat.cast_injective h2) (by omega)

/-- **Exact integrality criterion for `orderAtCuspOrbit`.** For a nonzero modular form `f` of
weight `k`, `orderAtCuspOrbit f C` is a natural number if and only if `k` is even or `C` is a
regular cusp orbit. -/
theorem exists_nat_orderAtCuspOrbit_eq_iff
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    (∃ m : ℕ, orderAtCuspOrbit f C = m) ↔ Even k ∨ IsRegularCuspOrbit Γ C := by
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, exists_nat_orderAtCuspOrbit_eq_of_even_or_isRegular f⟩
  by_contra hnot
  obtain ⟨hne, hnr⟩ := not_or.mp hnot
  obtain ⟨m, hm⟩ := exists_nat_orderAtCuspOrbit_eq_add_half_of_odd_of_not_isRegular f hf
    (Int.not_even_iff_odd.mp hne) hnr
  exact natCast_ne_natCast_add_half n m (hn.symm.trans hm)

/-- **Exact strict half-integrality criterion for `orderAtCuspOrbit`.** For a nonzero modular form
`f` of weight `k`, `orderAtCuspOrbit f C` is of the form `m + 1 / 2` (`m : ℕ`) if and only if `k`
is odd and `C` is an irregular cusp orbit. -/
theorem exists_nat_orderAtCuspOrbit_eq_add_half_iff
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    (∃ m : ℕ, orderAtCuspOrbit f C = (m : ℚ) + 1 / 2) ↔ Odd k ∧ ¬IsRegularCuspOrbit Γ C := by
  refine ⟨fun ⟨m, hm⟩ ↦ ?_,
    fun ⟨hk, hirr⟩ ↦ exists_nat_orderAtCuspOrbit_eq_add_half_of_odd_of_not_isRegular f hf hk hirr⟩
  by_contra hnot
  have hor : Even k ∨ IsRegularCuspOrbit Γ C := by
    by_cases hk : Odd k
    · exact Or.inr (Classical.not_not.mp fun hc ↦ hnot ⟨hk, hc⟩)
    · exact Or.inl (Int.not_odd_iff_even.mp hk)
  obtain ⟨n, hn⟩ := exists_nat_orderAtCuspOrbit_eq_of_even_or_isRegular f hor
  exact natCast_ne_natCast_add_half n m (hn.symm.trans hm)

end Regularity

end TauCeti.ModularForm

end
