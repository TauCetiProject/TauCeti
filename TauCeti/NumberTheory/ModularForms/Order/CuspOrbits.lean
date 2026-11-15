/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import TauCeti.NumberTheory.ModularForms.Cusps.Regularity
public import TauCeti.NumberTheory.ModularForms.QExpansion.Irregular
import Mathlib.NumberTheory.ModularForms.NormTrace
import TauCeti.Analysis.Complex.Fuchsian.Cusp.ChangeScaling
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj

/-!
# Vanishing orders on cusp orbits of `Γ \ ∂ℍ`

For a subgroup `Γ ≤ SL(2, ℤ)`, the cusps of the compactified modular curve
`(Γ.map sl2zToPSL2R).CompactifiedQuotient` are the cusp orbits `(Γ.map sl2zToPSL2R).CuspOrbit`.
Each normalized cusp datum `D` of `Γ.map sl2zToPSL2R` specifies a boundary cusp, a projective
scaling `σ ∈ PSL(2, ℝ)` sending that cusp to `∞`, and its projective width `D.width > 0`. Lifting
`σ` to `s ∈ SL(2, ℝ)` and reading `TauCeti.orderAtCusp D.width (f ∣[k] s⁻¹)` — half the order of
the `q₂`-expansion at period `2 * D.width`, matching `TauCeti.Subgroup.CuspDatum.automorphyUntwist`
— produces a `ℚ`-valued cusp order.

When `Γ` has finite index in `SL(2, ℤ)`, comparing any normalized cusp datum `D` and any lift `s`
of `D.scaling` against an integral representative `γ ∈ SL(2, ℤ)` of `D.cuspOrbit` (using
`TauCeti.orderAtCusp_slash_mapGL_inv` and `TauCeti.ModularForm.cuspDatum_width_eq_widthInfty`)
shows simultaneously that the rational cusp order is independent of the lift `s`, of the scaling at
the cusp, and of the cusp point chosen inside the `Γ`-orbit.

We also characterize vanishing at a cusp orbit (`0 < orderAtCuspOrbit f C`) and cuspidality
(`f ∈ ModularForm.cuspFormSubmodule _ k`) for nonzero modular forms, establish additivity and
power scaling on `[ModularFormClass]` and `ModularForm`/`CuspForm`, and record the parity
dichotomy governed by `Subgroup.IsRegularCusp`: `orderAtCuspOrbit f C` is a natural number at every
regular cusp and in every even weight, and has the form `m + 1 / 2` (`m : ℕ`) for a nonzero
odd-weight form at an irregular cusp.

## Main definitions

* `TauCeti.ModularForm.orderAtCuspDatum`: the `ℚ`-valued vanishing order of a slash-invariant form
  at a normalized cusp datum `D` of `Γ.map sl2zToPSL2R`.
* `TauCeti.ModularForm.orderAtCuspOrbit`: the `ℚ`-valued vanishing order descended to a cusp orbit
  `C : (Γ.map sl2zToPSL2R).CuspOrbit`.

## Main results

* `TauCeti.ModularForm.orderAtCuspDatum_eq_orderAtCusp_slash` and
  `TauCeti.ModularForm.orderAtCuspDatum_eq_of_cuspOrbit_eq`: independence of the `SL(2, ℝ)` lift,
  cusp scaling, and cusp-orbit representative.
* `TauCeti.ModularForm.orderAtCuspOrbit_cuspOrbit` and
  `TauCeti.ModularForm.orderAtCuspOrbit_cuspOrbitOfSL2Z`: evaluation at any cusp datum or integral
  matrix representative.
* `TauCeti.ModularForm.orderAtCuspOrbit_eq_zero_iff`,
  `TauCeti.ModularForm.orderAtCuspOrbit_pos_iff`, and
  `ModularForm.mem_cuspFormSubmodule_iff_forall_orderAtCuspOrbit_pos`: zero-detection at cusps and
  cuspidality characterization via positivity of all cusp orders.
* `TauCeti.ModularForm.orderAtCuspOrbit_eq_add_of_coe_eq_mul`,
  `ModularForm.orderAtCuspOrbit_mul`, and their power and finite-product counterparts: additivity
  and scaling on products and powers.
* `TauCeti.ModularForm.exists_orderAtCuspOrbit_eq_natCast_of_isRegularCusp`,
  `TauCeti.ModularForm.exists_orderAtCuspOrbit_eq_natCast_of_even`,
  `TauCeti.ModularForm.exists_orderAtCuspOrbit_eq_natCast_add_half_of_odd_of_not_isRegularCusp`,
  and the `[CuspFormClass]` lower bounds `1` vs `1 / 2`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§2.4,
  3.2–3.3, 3.6, and the errata to pp. 74–75.
-/

public noncomputable section

open Complex Filter Function Matrix Matrix.SpecialLinearGroup MulAction OnePoint UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

section OrderAtCuspOrbit

variable {Γ : Subgroup SL(2, ℤ)} {k k₁ k₂ : ℤ}
variable {F F₁ F₂ F₃ : Type*} [FunLike F ℍ ℂ] [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]

/-- **The `ℚ`-valued vanishing order of a slash-invariant form at a normalized cusp datum `D` of
`Γ.map sl2zToPSL2R`.** It is `TauCeti.orderAtCusp D.width (f ∣[k] s⁻¹)` for a lift `s ∈ SL(2, ℝ)`
of `D.scaling`; for a modular form on finite-index `Γ`, `orderAtCuspDatum_eq_orderAtCusp_slash`
shows that every lift gives the same order. -/
def orderAtCuspDatum [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (D : (Γ.map sl2zToPSL2R).CuspDatum) (f : F) : ℚ :=
  TauCeti.orderAtCusp D.width
    ⇑(_root_.SlashInvariantForm.translate f
      (mapGL ℝ (QuotientGroup.mk_surjective D.scaling).choose⁻¹))

/-- Unfolding `orderAtCuspDatum` across module boundaries. -/
theorem orderAtCuspDatum_def [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (D : (Γ.map sl2zToPSL2R).CuspDatum) (f : F) :
    orderAtCuspDatum D f =
      TauCeti.orderAtCusp D.width
        ⇑(_root_.SlashInvariantForm.translate f
          (mapGL ℝ (QuotientGroup.mk_surjective D.scaling).choose⁻¹)) :=
  (rfl)

/-- The cusp order at any normalized cusp datum is nonnegative. -/
theorem orderAtCuspDatum_nonneg [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (D : (Γ.map sl2zToPSL2R).CuspDatum) (f : F) :
    0 ≤ orderAtCuspDatum D f :=
  TauCeti.orderAtCusp_nonneg _ _

/-- The zero form has cusp order `0` at every normalized cusp datum. -/
@[simp]
theorem orderAtCuspDatum_zero
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [Zero F] [IsZeroApply F]
    (D : (Γ.map sl2zToPSL2R).CuspDatum) :
    orderAtCuspDatum D (0 : F) = 0 := by
  rw [orderAtCuspDatum_def, _root_.SlashInvariantForm.coe_translate, FunLike.coe_zero,
    SlashAction.zero_slash]
  simp [TauCeti.orderAtCusp_def]

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
    rw [hs_inv, map_mul, map_mul, mapGL_map_intCast (R := ℝ) (S := ℝ), map_inv,
      mapGL_map_intCast (R := ℝ) (S := ℝ), map_inv, inv_inv, SlashAction.slash_mul,
      SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ₀)]
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  rw [hw, hslash, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
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
  rw [orderAtCuspDatum_def, _root_.SlashInvariantForm.coe_translate,
    orderAtCusp_slash_scaling_inv_eq f (QuotientGroup.mk_surjective D.scaling).choose_spec hγ,
    orderAtCusp_slash_scaling_inv_eq f hs hγ]

/-- Two normalized cusp data representing the same cusp orbit have the same vanishing order. -/
theorem orderAtCuspDatum_eq_of_cuspOrbit_eq [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {D D' : (Γ.map sl2zToPSL2R).CuspDatum} (h : D.cuspOrbit = D'.cuspOrbit) :
    orderAtCuspDatum D f = orderAtCuspDatum D' f := by
  obtain ⟨γ, hγ⟩ := Γ.cuspOrbitOfSL2Z_surjective D.cuspOrbit
  rw [orderAtCuspDatum_def, orderAtCuspDatum_def, _root_.SlashInvariantForm.coe_translate,
    _root_.SlashInvariantForm.coe_translate,
    orderAtCusp_slash_scaling_inv_eq f (QuotientGroup.mk_surjective D.scaling).choose_spec hγ,
    orderAtCusp_slash_scaling_inv_eq f (QuotientGroup.mk_surjective D'.scaling).choose_spec
      (hγ.trans h)]

/-- **The `ℚ`-valued vanishing order of a slash-invariant form on a cusp orbit
`C : (Γ.map sl2zToPSL2R).CuspOrbit`.** -/
def orderAtCuspOrbit [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) : ℚ :=
  orderAtCuspDatum C.cuspDatum f

/-- Unfolding `orderAtCuspOrbit` across module boundaries. -/
theorem orderAtCuspOrbit_def [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit f C = orderAtCuspDatum C.cuspDatum f :=
  (rfl)

/-- The cusp order on every cusp orbit is nonnegative. -/
theorem orderAtCuspOrbit_nonneg [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    0 ≤ orderAtCuspOrbit f C :=
  orderAtCuspDatum_nonneg C.cuspDatum f

/-- The zero form has cusp order `0` at every cusp orbit. -/
@[simp]
theorem orderAtCuspOrbit_zero
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [Zero F] [IsZeroApply F]
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (0 : F) C = 0 := by
  rw [orderAtCuspOrbit_def, orderAtCuspDatum_zero]

/-- `orderAtCuspOrbit` evaluated on the cusp orbit of any normalized cusp datum `D` recovers
`orderAtCuspDatum D f`. -/
@[simp]
theorem orderAtCuspOrbit_cuspOrbit [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (D : (Γ.map sl2zToPSL2R).CuspDatum) :
    orderAtCuspOrbit f D.cuspOrbit = orderAtCuspDatum D f :=
  orderAtCuspDatum_eq_of_cuspOrbit_eq f D.cuspOrbit.cuspOrbit_cuspDatum

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
  rw [orderAtCuspOrbit_def, orderAtCuspDatum_def, _root_.SlashInvariantForm.coe_translate]
  exact orderAtCusp_slash_scaling_inv_eq f
    (QuotientGroup.mk_surjective (Γ.cuspOrbitOfSL2Z γ).cuspDatum.scaling).choose_spec
    (Γ.cuspOrbitOfSL2Z γ).cuspOrbit_cuspDatum.symm

/-- Scaling a modular form by a nonzero complex constant leaves its cusp order on each cusp orbit
unchanged. -/
@[simp]
theorem orderAtCuspOrbit_smul [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [SMul ℂ F] [IsSMulApply ℂ F]
    {c : ℂ} (hc : c ≠ 0) (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (c • f) C = orderAtCuspOrbit f C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, orderAtCuspOrbit_cuspOrbitOfSL2Z, FunLike.coe_smul,
    ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← _root_.ModularForm.SL_slash,
    _root_.ModularForm.SL_smul_slash, _root_.ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
    ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact TauCeti.orderAtCusp_smul
    (ModularFormClass.analyticAt_cuspFunction_zero fγ (mul_pos two_pos Γγ.widthInfty_pos)
      Γγ.two_mul_widthInfty_mem_strictPeriods) hc

/-- Scaling a modular form by a nonzero complex constant leaves its cusp order at any normalized
cusp datum unchanged. -/
@[simp]
theorem orderAtCuspDatum_smul [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [SMul ℂ F] [IsSMulApply ℂ F]
    {c : ℂ} (hc : c ≠ 0) (D : (Γ.map sl2zToPSL2R).CuspDatum) (f : F) :
    orderAtCuspDatum D (c • f) = orderAtCuspDatum D f := by
  rw [← orderAtCuspOrbit_cuspOrbit, ← orderAtCuspOrbit_cuspOrbit, orderAtCuspOrbit_smul hc]

/-- For a nonzero modular form `f`, the cusp order at `Γ.cuspOrbitOfSL2Z γ` is positive if and only
if `f ∣[k] γ` vanishes at `i∞`. -/
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (γ : SL(2, ℤ)) :
    0 < orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) ↔
      IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hfγ : (⇑fγ : ℍ → ℂ) ≠ 0 := by
    rw [_root_.ModularForm.coe_translate]
    exact (SlashAction.slash_eq_zero_iff k (mapGL ℝ γ) ⇑f).not.mpr hf
  have h2w : 0 < 2 * Γγ.widthInfty := mul_pos two_pos Γγ.widthInfty_pos
  have hper := Γγ.two_mul_widthInfty_mem_strictPeriods
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ),
    orderAtCusp_pos_iff Γγ.widthInfty_pos hper hfγ,
    UpperHalfPlane.cuspFunction_apply_zero h2w
      (ModularFormClass.analyticAt_cuspFunction_zero fγ h2w hper)
      (SlashInvariantFormClass.periodic_comp_ofComplex fγ hper)]
  exact ⟨_root_.ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero fγ,
    IsZeroAtImInfty.valueAtInfty_eq_zero⟩

/-- For a nonzero modular form `f`, the cusp order at `Γ.cuspOrbitOfSL2Z γ` vanishes if and only if
`f ∣[k] γ` does not vanish at `i∞`. -/
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_zero_iff [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (γ : SL(2, ℤ)) :
    orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) = 0 ↔
      ¬IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  rw [← (orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff hf γ).not, not_lt, le_antisymm_iff,
    and_iff_left (orderAtCuspOrbit_nonneg f _)]

/-- For a nonzero modular form `f`, the cusp order on a cusp orbit `C` vanishes if and only if
`f ∣[k] γ` is nonvanishing at `i∞` for every `γ ∈ SL(2, ℤ)` representing `C`. -/
theorem orderAtCuspOrbit_eq_zero_iff [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit f C = 0 ↔
      ∀ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C → ¬IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  obtain ⟨γ₀, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  refine ⟨fun h0 γ hγ ↦ ?_,
    fun h ↦ (orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_zero_iff hf γ₀).mpr (h γ₀ rfl)⟩
  rw [← orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_zero_iff hf γ, hγ]
  exact h0

/-- For a nonzero modular form `f`, the cusp order on a cusp orbit `C` is positive if and only if
`f ∣[k] γ` vanishes at `i∞` for some (equivalently, every) `γ ∈ SL(2, ℤ)` representing `C`. -/
theorem orderAtCuspOrbit_pos_iff [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    0 < orderAtCuspOrbit f C ↔
      ∃ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C ∧ IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  rw [(orderAtCuspOrbit_nonneg f C).lt_iff_ne, ne_comm]
  simpa only [not_forall, Classical.not_not, exists_prop] using
    (orderAtCuspOrbit_eq_zero_iff hf C).not

/-- **Cuspidality via cusp-orbit orders**: a nonzero modular form `f` on finite-index `Γ` belongs to
`ModularForm.cuspFormSubmodule` if and only if `0 < orderAtCuspOrbit f C` at every cusp orbit `C` of
`Γ`. -/
theorem _root_.ModularForm.mem_cuspFormSubmodule_iff_forall_orderAtCuspOrbit_pos [Γ.FiniteIndex]
    {f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k} (hf : f ≠ 0) :
    f ∈ _root_.ModularForm.cuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) k ↔
      ∀ C : (Γ.map sl2zToPSL2R).CuspOrbit, 0 < orderAtCuspOrbit f C := by
  have hf' : (⇑f : ℍ → ℂ) ≠ 0 := fun h ↦ hf (DFunLike.ext' h)
  rw [_root_.ModularForm.mem_cuspFormSubmodule_iff, _root_.ModularForm.isCuspForm_iff]
  refine ⟨fun hcusp C ↦ ?_, fun hpos c hc ↦ ?_⟩
  · obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    rw [orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff hf' γ]
    have hcγ : IsCusp (mapGL ℝ γ • ∞) (Γ : Subgroup (GL (Fin 2) ℝ)) :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
        (_root_.isCusp_SL2Z_iff'.mpr ⟨γ, rfl⟩)
    exact hcusp hcγ (mapGL ℝ γ) rfl
  · rw [OnePoint.isZeroAt_iff_forall_SL2Z ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)]
    intro γ _
    rw [_root_.ModularForm.SL_slash, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
    exact (orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff hf' γ).mp (hpos (Γ.cuspOrbitOfSL2Z γ))

/-- **Additivity on products at cusps (`ModularFormClass` form)**: if `fg` is a modular form of
weight `k₁ + k₂` with underlying function `f * g` for nonzero modular forms `f` and `g`, its cusp
order on each cusp orbit is the sum of their cusp orders. -/
theorem orderAtCuspOrbit_eq_add_of_coe_eq_mul [Γ.FiniteIndex]
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [ModularFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) (k₁ + k₂)]
    (f : F₁) (g : F₂) (fg : F₃) (hfg : ⇑fg = ⇑f * ⇑g)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit fg C = orderAtCuspOrbit f C + orderAtCuspOrbit g C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k₁ := _root_.ModularForm.translate f (mapGL ℝ γ)
  let gγ : ModularForm Γγ k₂ := _root_.ModularForm.translate g (mapGL ℝ γ)
  have hfγ : (⇑fγ : ℍ → ℂ) ≠ 0 := by
    rw [_root_.ModularForm.coe_translate]
    exact (SlashAction.slash_eq_zero_iff k₁ (mapGL ℝ γ) ⇑f).not.mpr hf
  have hgγ : (⇑gγ : ℍ → ℂ) ≠ 0 := by
    rw [_root_.ModularForm.coe_translate]
    exact (SlashAction.slash_eq_zero_iff k₂ (mapGL ℝ γ) ⇑g).not.mpr hg
  have hprod : (⇑fg ∣[k₁ + k₂] mapGL ℝ γ) = ⇑fγ * ⇑gγ := by
    simp only [hfg, _root_.ModularForm.mul_slash, det_mapGL, Units.val_one, abs_one, one_smul]
    rw [← _root_.ModularForm.coe_translate f (mapGL ℝ γ),
      ← _root_.ModularForm.coe_translate g (mapGL ℝ γ)]
  have h2w : 0 < 2 * Γγ.widthInfty := mul_pos two_pos Γγ.widthInfty_pos
  have hper := Γγ.two_mul_widthInfty_mem_strictPeriods
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, orderAtCuspOrbit_cuspOrbitOfSL2Z,
    orderAtCuspOrbit_cuspOrbitOfSL2Z, hprod,
    ← _root_.ModularForm.coe_translate f (mapGL ℝ γ),
    ← _root_.ModularForm.coe_translate g (mapGL ℝ γ)]
  exact TauCeti.orderAtCusp_mul
    (ModularFormClass.analyticAt_cuspFunction_zero fγ h2w hper)
    (ModularFormClass.analyticAt_cuspFunction_zero gγ h2w hper)
    (analyticOrderAt_cuspFunction_ne_top h2w hper hfγ)
    (analyticOrderAt_cuspFunction_ne_top h2w hper hgγ)

/-- **Power scaling at cusps (`ModularFormClass` form)**: if `fn` is a modular form of weight
`n * k` with underlying function `f ^ n`, its cusp order on each cusp orbit is `n` times that of
`f`. -/
theorem orderAtCuspOrbit_eq_mul_of_coe_eq_pow [Γ.FiniteIndex] {n : ℕ}
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) (n * k)]
    (f : F₁) (fn : F₂) (hfn : ⇑fn = ⇑f ^ n)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit fn C = n * orderAtCuspOrbit f C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hpow : (⇑fn ∣[(n : ℤ) * k] mapGL ℝ γ) = ⇑fγ ^ n := by
    simp only [hfn, _root_.ModularForm.pow_slash, det_mapGL, Units.val_one, abs_one,
      _root_.one_zpow, one_smul]
    rw [← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, orderAtCuspOrbit_cuspOrbitOfSL2Z, hpow,
    ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact TauCeti.orderAtCusp_pow n
    (ModularFormClass.analyticAt_cuspFunction_zero fγ (mul_pos two_pos Γγ.widthInfty_pos)
      Γγ.two_mul_widthInfty_mem_strictPeriods)

/-- **Finite-product additivity at cusps (`ModularFormClass` form)**: if `fp` is a modular form of
weight `∑ i ∈ s, kᵢ i` with underlying function `∏ i ∈ s, g i` for nonzero modular forms `g i`, its
cusp order on each cusp orbit is the sum of their cusp orders. -/
theorem orderAtCuspOrbit_eq_sum_of_coe_eq_prod [Γ.FiniteIndex] {ι : Type*} {s : Finset ι}
    {kᵢ : ι → ℤ} {G : ι → Type*} [∀ i, FunLike (G i) ℍ ℂ]
    [∀ i, ModularFormClass (G i) (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i)]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (hk : k = ∑ i ∈ s, kᵢ i)
    (g : (i : ι) → G i) (fp : F) (hfp : ⇑fp = ∏ i ∈ s, ⇑(g i))
    (hg : ∀ i ∈ s, (⇑(g i) : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit fp C = ∑ i ∈ s, orderAtCuspOrbit (g i) C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let gγ : (i : ι) → ModularForm Γγ (kᵢ i) := fun i ↦ _root_.ModularForm.translate (g i) (mapGL ℝ γ)
  have hgγ : ∀ i ∈ s, (⇑(gγ i) : ℍ → ℂ) ≠ 0 := fun i hi ↦ by
    rw [_root_.ModularForm.coe_translate]
    exact (SlashAction.slash_eq_zero_iff (kᵢ i) (mapGL ℝ γ) ⇑(g i)).not.mpr (hg i hi)
  have hprod : (⇑fp ∣[k] mapGL ℝ γ) = ∏ i ∈ s, ⇑(gγ i) := by
    subst hk
    simp only [hfp, _root_.ModularForm.prod_slash_sum_weights, det_mapGL, Units.val_one, abs_one,
      _root_.one_zpow, one_smul]
    exact Finset.prod_congr rfl fun i _ ↦ (_root_.ModularForm.coe_translate (g i) (mapGL ℝ γ)).symm
  have h2w : 0 < 2 * Γγ.widthInfty := mul_pos two_pos Γγ.widthInfty_pos
  have hper := Γγ.two_mul_widthInfty_mem_strictPeriods
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, hprod,
    TauCeti.orderAtCusp_prod s
      (fun i _ ↦ ModularFormClass.analyticAt_cuspFunction_zero (gγ i) h2w hper)
      (fun i hi ↦ analyticOrderAt_cuspFunction_ne_top h2w hper (hgγ i hi))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate (g i) (mapGL ℝ γ)]

/-- **Additivity on products at cusps**: for nonzero modular forms `f` and `g` on `Γ`, the cusp
order of `f.mul g` at every cusp orbit `C` is the sum of their cusp orders at `C`. -/
theorem _root_.ModularForm.orderAtCuspOrbit_mul [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (f.mul g) C = orderAtCuspOrbit f C + orderAtCuspOrbit g C :=
  orderAtCuspOrbit_eq_add_of_coe_eq_mul f g (f.mul g) (_root_.ModularForm.coe_mul f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) C

/-- Cusp orders scale under `ModularForm.pow`. -/
theorem _root_.ModularForm.orderAtCuspOrbit_pow [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (f.pow n) C = n * orderAtCuspOrbit f C :=
  orderAtCuspOrbit_eq_mul_of_coe_eq_pow f (f.pow n) (_root_.ModularForm.coe_pow f n) C

/-- Cusp orders sum over `ModularForm.prod` of nonzero forms. -/
theorem _root_.ModularForm.orderAtCuspOrbit_prod [Γ.FiniteIndex] {ι : Type*} {s : Finset ι}
    {kᵢ : ι → ℤ} (m : ℤ) (hm : m = ∑ i ∈ s, kᵢ i)
    (g : (i : ι) → ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i))
    (hg : ∀ i ∈ s, g i ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (_root_.ModularForm.prod m hm g) C =
      ∑ i ∈ s, orderAtCuspOrbit (g i) C :=
  orderAtCuspOrbit_eq_sum_of_coe_eq_prod hm g (_root_.ModularForm.prod m hm g) (by simp)
    (fun i hi h ↦ hg i hi (DFunLike.ext' h)) C

/-- Additivity on `CuspForm.mulModularForm` at cusps for nonzero forms. -/
theorem _root_.CuspForm.orderAtCuspOrbit_mulModularForm [Γ.FiniteIndex]
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (f.mulModularForm g) C = orderAtCuspOrbit f C + orderAtCuspOrbit g C :=
  orderAtCuspOrbit_eq_add_of_coe_eq_mul f g (f.mulModularForm g)
    (_root_.CuspForm.coe_mulModularForm f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) C

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

/-- At a regular cusp `Γ.cuspOrbitOfSL2Z γ`, the rational cusp order equals the integral
`q`-expansion order at width `widthInfty`. -/
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_qExpansionOrderAtCusp_of_isRegularCusp
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) {γ : SL(2, ℤ)}
    (hreg : Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)) :
    orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) =
      (qExpansionOrderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) : ℚ) := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hw_mem : Γγ.widthInfty ∈ Γγ.strictPeriods :=
    Γγ.isRegularAtInfty_iff.mp ((Γ.isRegularCusp_cuspOrbitOfSL2Z γ).mp hreg)
  have : Fact (IsCusp OnePoint.infty Γγ) :=
    ⟨Γγ.isCusp_of_mem_strictPeriods Γγ.widthInfty_pos hw_mem⟩
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact TauCeti.orderAtCusp_eq_qExpansionOrderAtCusp Γγ.widthInfty_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex fγ hw_mem)
    (ModularFormClass.bdd_at_infty fγ) (ModularFormClass.holo fγ)

/-- At a regular cusp orbit, `orderAtCuspOrbit f C` is a natural number regardless of the weight. -/
theorem exists_orderAtCuspOrbit_eq_natCast_of_isRegularCusp
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hreg : Γ.IsRegularCusp C) :
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
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact exists_orderAtCusp_eq_natCast_of_even fγ hk

/-- For a nonzero modular form of odd weight, the cusp order at an irregular cusp orbit is strictly
half-integral: `m + 1 / 2` for some `m : ℕ`. -/
theorem exists_orderAtCuspOrbit_eq_natCast_add_half_of_odd_of_not_isRegularCusp
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (hk : Odd k) {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hirr : ¬Γ.IsRegularCusp C) :
    ∃ m : ℕ, orderAtCuspOrbit f C = (m : ℚ) + 1 / 2 := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [Γ.isRegularCusp_cuspOrbitOfSL2Z] at hirr
  let fγ : ModularForm _ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hfγ : (⇑fγ : ℍ → ℂ) ≠ 0 := by
    rw [_root_.ModularForm.coe_translate]
    exact (SlashAction.slash_eq_zero_iff k (mapGL ℝ γ) ⇑f).not.mpr hf
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact exists_orderAtCusp_eq_natCast_add_half_of_odd_of_not_isRegularAtInfty fγ hfγ hk hirr

/-- Every nonzero cusp form has strictly positive vanishing order at every cusp orbit. -/
theorem orderAtCuspOrbit_pos [CuspFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    0 < orderAtCuspOrbit f C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  let fγ : CuspForm _ k := _root_.CuspForm.translate f (mapGL ℝ γ)
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff hf γ, ← _root_.CuspForm.coe_translate f (mapGL ℝ γ)]
  exact CuspFormClass.zero_at_infty fγ

/-- Every nonzero cusp form has vanishing order at least `1 / 2` at every cusp orbit (and at least
`1` at regular cusps or in even weight). -/
theorem one_div_two_le_orderAtCuspOrbit [CuspFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    1 / 2 ≤ orderAtCuspOrbit f C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  have hpos := orderAtCuspOrbit_pos hf (Γ.cuspOrbitOfSL2Z γ)
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, TauCeti.orderAtCusp_def] at hpos ⊢
  set n : ℤ := qExpansionOrderAtCusp
    (2 * (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty)
    (⇑f ∣[k] mapGL ℝ γ)
  have hpos' : (0 : ℚ) < n := by linarith
  have h1 : (1 : ℤ) ≤ n := Int.lt_iff_add_one_le.mp (by exact_mod_cast hpos')
  have h1q : (1 : ℚ) ≤ n := by exact_mod_cast h1
  linarith

/-- At a regular cusp orbit, every nonzero cusp form has vanishing order at least `1`. -/
theorem one_le_orderAtCuspOrbit_of_isRegularCusp
    [CuspFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hreg : Γ.IsRegularCusp C) :
    1 ≤ orderAtCuspOrbit f C := by
  obtain ⟨m, hm⟩ := exists_orderAtCuspOrbit_eq_natCast_of_isRegularCusp f hreg
  have hpos : (0 : ℚ) < m := hm ▸ orderAtCuspOrbit_pos hf C
  have hm1 : 1 ≤ m := Nat.succ_le_of_lt (by exact_mod_cast hpos)
  rw [hm]
  exact_mod_cast hm1

/-- In even weight, every nonzero cusp form has vanishing order at least `1` at every cusp orbit. -/
theorem one_le_orderAtCuspOrbit_of_even [CuspFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) (hk : Even k) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    1 ≤ orderAtCuspOrbit f C := by
  obtain ⟨m, hm⟩ := exists_orderAtCuspOrbit_eq_natCast_of_even f hk C
  have hpos : (0 : ℚ) < m := hm ▸ orderAtCuspOrbit_pos hf C
  have hm1 : 1 ≤ m := Nat.succ_le_of_lt (by exact_mod_cast hpos)
  rw [hm]
  exact_mod_cast hm1

end RegularityAndParity

end TauCeti.ModularForm

end
