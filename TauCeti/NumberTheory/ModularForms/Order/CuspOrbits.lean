/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import TauCeti.NumberTheory.ModularForms.Cusps.Regularity
public import TauCeti.NumberTheory.ModularForms.QExpansion.Irregular
import TauCeti.Analysis.Complex.Fuchsian.Cusp.ChangeScaling
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj
import TauCeti.NumberTheory.ModularForms.Cusps.Width

/-!
# Vanishing orders on cusp orbits of `Γ \ ∂ℍ`

For finite-index `Γ ≤ SL(2, ℤ)`, lifting a normalized cusp datum's scaling `σ ∈ PSL(2, ℝ)` to
`s ∈ SL(2, ℝ)` and reading `TauCeti.orderAtCusp D.width (f ∣[k] s⁻¹)` yields a `ℚ`-valued cusp
order `orderAtCuspOrbit f C` independent of lift, scaling, and orbit representative. We establish
zero-detection, cuspidality via cusp orders, product additivity, the regular/even vs
irregular/odd-weight parity dichotomy, and `[CuspFormClass]` lower bounds (`1` vs `1 / 2`).

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§2.4,
  3.2–3.3, 3.6, and the errata to pp. 74–75.
-/

public noncomputable section

open Complex Filter Function Matrix Matrix.SpecialLinearGroup MulAction OnePoint UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

variable {Γ : Subgroup SL(2, ℤ)} {k k₁ k₂ : ℤ}
variable {F F₁ F₂ F₃ : Type*} [FunLike F ℍ ℂ] [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]

section Slash

variable [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- The `ℚ`-valued vanishing order of a slash-invariant form at a normalized cusp datum `D`. -/
def orderAtCuspDatum (D : (Γ.map sl2zToPSL2R).CuspDatum) (f : F) : ℚ :=
  TauCeti.orderAtCusp D.width ⇑(_root_.SlashInvariantForm.translate f
    (mapGL ℝ (QuotientGroup.mk_surjective D.scaling).choose⁻¹))

/-- Unfolding `orderAtCuspDatum` across module boundaries. -/
theorem orderAtCuspDatum_def (D : (Γ.map sl2zToPSL2R).CuspDatum) (f : F) :
    orderAtCuspDatum D f = TauCeti.orderAtCusp D.width ⇑(_root_.SlashInvariantForm.translate f
      (mapGL ℝ (QuotientGroup.mk_surjective D.scaling).choose⁻¹)) := (rfl)

/-- The cusp order at any normalized cusp datum is nonnegative. -/
theorem orderAtCuspDatum_nonneg (D : (Γ.map sl2zToPSL2R).CuspDatum) (f : F) :
    0 ≤ orderAtCuspDatum D f := TauCeti.orderAtCusp_nonneg _ _

/-- The zero form has cusp order `0` at every normalized cusp datum. -/
@[simp] theorem orderAtCuspDatum_zero [Zero F] [IsZeroApply F]
    (D : (Γ.map sl2zToPSL2R).CuspDatum) : orderAtCuspDatum D (0 : F) = 0 := by
  rw [orderAtCuspDatum_def, _root_.SlashInvariantForm.coe_translate, FunLike.coe_zero,
    SlashAction.zero_slash, TauCeti.orderAtCusp_def]; simp

/-- The `ℚ`-valued vanishing order of a slash-invariant form on a cusp orbit. -/
def orderAtCuspOrbit (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) : ℚ :=
  orderAtCuspDatum C.cuspDatum f

/-- Unfolding `orderAtCuspOrbit` across module boundaries. -/
theorem orderAtCuspOrbit_def (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit f C = orderAtCuspDatum C.cuspDatum f := (rfl)

/-- The cusp order on every cusp orbit is nonnegative. -/
theorem orderAtCuspOrbit_nonneg (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    0 ≤ orderAtCuspOrbit f C := orderAtCuspDatum_nonneg C.cuspDatum f

/-- The zero form has cusp order `0` at every cusp orbit. -/
@[simp] theorem orderAtCuspOrbit_zero [Zero F] [IsZeroApply F]
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : orderAtCuspOrbit (0 : F) C = 0 := by
  rw [orderAtCuspOrbit_def, orderAtCuspDatum_zero]

/-- For finite-index `Γ`, `orderAtCuspOrbit f` has finite support. -/
theorem hasFiniteSupport_orderAtCuspOrbit [Γ.FiniteIndex] (f : F) :
    Function.HasFiniteSupport (orderAtCuspOrbit (Γ := Γ) (k := k) f) := Set.toFinite _

/-- The cusp order on every cusp orbit is a half-integer `m / 2` for some `m : ℕ`. -/
theorem exists_orderAtCuspOrbit_eq_natCast_div_two (f : F) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    ∃ m : ℕ, orderAtCuspOrbit f C = (m : ℚ) / 2 :=
  TauCeti.exists_orderAtCusp_eq_natCast_div_two _ _

end Slash

section Modular

variable [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- **Simultaneous lift, scaling, and representative invariance.** For any normalized cusp datum
`D`, lift `s ∈ SL(2, ℝ)` of `D.scaling`, and `γ ∈ SL(2, ℤ)` representing `D.cuspOrbit`, the cusp
order of `f ∣[k] s⁻¹` at width `D.width` equals that of `f ∣[k] γ` at `widthInfty` of `γ⁻¹ Γ γ`. -/
theorem orderAtCusp_slash_scaling_inv_eq (f : F) {D : (Γ.map sl2zToPSL2R).CuspDatum}
    {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling) {γ : SL(2, ℤ)}
    (hγ : Γ.cuspOrbitOfSL2Z γ = D.cuspOrbit) :
    TauCeti.orderAtCusp D.width (⇑f ∣[k] mapGL ℝ s⁻¹) =
      TauCeti.orderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  obtain ⟨D₀, -, hD₀_scal⟩ :=
    (Γ.isCuspPoint_map_sl2zToPSL2R_smul_infty γ).exists_cuspDatum (σ := sl2zToPSL2R γ⁻¹)
      (by rw [map_inv, inv_smul_smul])
  obtain ⟨g₀, hg₀_cusp⟩ := mem_orbit_iff.mp <| (D.cuspOrbit_eq_iff D₀).mp
    ((cuspDatum_cuspOrbit_eq_of_scaling_eq hD₀_scal).trans hγ).symm
  obtain ⟨γ₀, hγ₀, hg₀_eq⟩ := Subgroup.mem_map.mp g₀.property
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
  have hw : D.width = t 0 0 ^ 2 * Γγ.widthInfty := by
    have hw₀ := TauCeti.cuspDatum_width_eq_mul
      (D := D₀.conj (Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer g₀.property)))
      (D' := D) (by rw [_root_.Subgroup.CuspDatum.conj_cusp, ← hg₀_cusp, Subgroup.smul_def])
      (a := t 0 0 ^ 2) (b := t 0 0 * t 0 1) fun x ↦ by
        rw [_root_.Subgroup.CuspDatum.conj_scaling, mul_smul, Complex.ofReal_pow,
          Complex.ofReal_mul, ← UpperHalfPlane.coe_smul_of_apply_zero_one_eq_zero ht,
          ← UpperHalfPlane.pslMk_smul, hcoe_t, mul_smul, mul_smul, inv_smul_smul, smul_inv_smul]
    rwa [_root_.Subgroup.CuspDatum.conj_width, cuspDatum_width_eq_widthInfty hD₀_scal] at hw₀
  have hs_inv : s⁻¹ = h₀ * s₀⁻¹ * t⁻¹ := by rw [ht_def]; group
  have hslash : ⇑f ∣[k] mapGL ℝ s⁻¹ = (⇑f ∣[k] mapGL ℝ γ) ∣[k] mapGL ℝ t⁻¹ := by
    rw [hs_inv, map_mul, map_mul,
      mapGL_map_intCast (R := ℝ) (S := ℝ), map_inv, mapGL_map_intCast (R := ℝ) (S := ℝ), map_inv,
      inv_inv, SlashAction.slash_mul, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ₀)]
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  rw [hw, hslash, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact orderAtCusp_slash_mapGL_inv Γγ.widthInfty_pos ht
    (SlashInvariantFormClass.periodic_comp_ofComplex fγ Γγ.two_mul_widthInfty_mem_strictPeriods)
    (ModularFormClass.analyticAt_cuspFunction_zero fγ (mul_pos two_pos Γγ.widthInfty_pos)
      Γγ.two_mul_widthInfty_mem_strictPeriods)

/-- Every lift `s ∈ SL(2, ℝ)` of `D.scaling` computes `orderAtCuspDatum D f`. -/
theorem orderAtCuspDatum_eq_orderAtCusp_slash (f : F) (D : (Γ.map sl2zToPSL2R).CuspDatum)
    {s : SL(2, ℝ)} (hs : (s : PSL(2, ℝ)) = D.scaling) :
    orderAtCuspDatum D f = TauCeti.orderAtCusp D.width (⇑f ∣[k] mapGL ℝ s⁻¹) := by
  obtain ⟨γ, hγ⟩ := Γ.cuspOrbitOfSL2Z_surjective D.cuspOrbit
  rw [orderAtCuspDatum_def, _root_.SlashInvariantForm.coe_translate,
    orderAtCusp_slash_scaling_inv_eq f (QuotientGroup.mk_surjective D.scaling).choose_spec hγ,
    orderAtCusp_slash_scaling_inv_eq f hs hγ]

/-- Two normalized cusp data representing the same cusp orbit have the same vanishing order. -/
theorem orderAtCuspDatum_eq_of_cuspOrbit_eq (f : F) {D D' : (Γ.map sl2zToPSL2R).CuspDatum}
    (h : D.cuspOrbit = D'.cuspOrbit) : orderAtCuspDatum D f = orderAtCuspDatum D' f := by
  obtain ⟨γ, hγ⟩ := Γ.cuspOrbitOfSL2Z_surjective D.cuspOrbit
  rw [orderAtCuspDatum_eq_orderAtCusp_slash f D (QuotientGroup.mk_surjective _).choose_spec,
    orderAtCuspDatum_eq_orderAtCusp_slash f D' (QuotientGroup.mk_surjective _).choose_spec,
    orderAtCusp_slash_scaling_inv_eq f (QuotientGroup.mk_surjective _).choose_spec hγ,
    orderAtCusp_slash_scaling_inv_eq f (QuotientGroup.mk_surjective _).choose_spec (hγ.trans h)]

/-- `orderAtCuspOrbit` evaluated on `D.cuspOrbit` recovers `orderAtCuspDatum D f`. -/
@[simp] theorem orderAtCuspOrbit_cuspOrbit (f : F) (D : (Γ.map sl2zToPSL2R).CuspDatum) :
    orderAtCuspOrbit f D.cuspOrbit = orderAtCuspDatum D f :=
  orderAtCuspDatum_eq_of_cuspOrbit_eq f D.cuspOrbit.cuspOrbit_cuspDatum

/-- Evaluation at an integral representative `γ ∈ SL(2, ℤ)`. -/
@[simp] theorem orderAtCuspOrbit_cuspOrbitOfSL2Z (f : F) (γ : SL(2, ℤ)) :
    orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) =
      TauCeti.orderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) := by
  rw [orderAtCuspOrbit_def, orderAtCuspDatum_def, _root_.SlashInvariantForm.coe_translate]
  exact orderAtCusp_slash_scaling_inv_eq f
    (QuotientGroup.mk_surjective (Γ.cuspOrbitOfSL2Z γ).cuspDatum.scaling).choose_spec
    (Γ.cuspOrbitOfSL2Z γ).cuspOrbit_cuspDatum.symm

/-- Nonzero complex scalar multiples have the same cusp order on every cusp orbit. -/
@[simp] theorem orderAtCuspOrbit_smul [SMul ℂ F] [IsSMulApply ℂ F] {c : ℂ} (hc : c ≠ 0) (f : F)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : orderAtCuspOrbit (c • f) C = orderAtCuspOrbit f C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, orderAtCuspOrbit_cuspOrbitOfSL2Z, FunLike.coe_smul,
    ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← _root_.ModularForm.SL_slash,
    _root_.ModularForm.SL_smul_slash, _root_.ModularForm.SL_slash,
    Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact TauCeti.orderAtCusp_smul (ModularFormClass.analyticAt_cuspFunction_zero fγ
    (mul_pos two_pos Γγ.widthInfty_pos) Γγ.two_mul_widthInfty_mem_strictPeriods) hc

/-- Nonzero `f` has positive cusp order at `Γ.cuspOrbitOfSL2Z γ` iff `f ∣[k] γ` vanishes at `i∞`. -/
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) (γ : SL(2, ℤ)) :
    0 < orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) ↔ IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have h2w : 0 < 2 * Γγ.widthInfty := mul_pos two_pos Γγ.widthInfty_pos
  have hper := Γγ.two_mul_widthInfty_mem_strictPeriods
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ),
    orderAtCusp_pos_iff Γγ.widthInfty_pos hper (by
      rw [_root_.ModularForm.coe_translate]; exact (SlashAction.slash_eq_zero_iff ..).not.mpr hf),
    UpperHalfPlane.cuspFunction_apply_zero h2w
      (ModularFormClass.analyticAt_cuspFunction_zero fγ h2w hper)
      (SlashInvariantFormClass.periodic_comp_ofComplex fγ hper)]
  exact ⟨_root_.ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero fγ,
    IsZeroAtImInfty.valueAtInfty_eq_zero⟩

/-- Nonzero `f` has cusp order `0` at `Γ.cuspOrbitOfSL2Z γ` iff `f ∣[k] γ` is nonzero at `i∞`. -/
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_zero_iff {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (γ : SL(2, ℤ)) :
    orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) = 0 ↔ ¬IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  rw [← (orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff hf γ).not, not_lt, le_antisymm_iff,
    and_iff_left (orderAtCuspOrbit_nonneg f _)]

/-- Zero-detection for `orderAtCuspOrbit` of a nonzero modular form. -/
theorem orderAtCuspOrbit_eq_zero_iff {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit f C = 0 ↔
      ∀ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C → ¬IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  obtain ⟨γ₀, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  exact ⟨fun h0 γ hγ ↦ (orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_zero_iff hf γ).mp (hγ.symm ▸ h0),
    fun h ↦ (orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_zero_iff hf γ₀).mpr (h γ₀ rfl)⟩

/-- Positivity characterization for `orderAtCuspOrbit` of a nonzero modular form. -/
theorem orderAtCuspOrbit_pos_iff {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    0 < orderAtCuspOrbit f C ↔
      ∃ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C ∧ IsZeroAtImInfty (⇑f ∣[k] mapGL ℝ γ) := by
  rw [(orderAtCuspOrbit_nonneg f C).lt_iff_ne, ne_comm]
  simpa only [not_forall, Classical.not_not, exists_prop] using
    (orderAtCuspOrbit_eq_zero_iff hf C).not

/-- At a regular cusp `Γ.cuspOrbitOfSL2Z γ`, cusp order equals the `q`-expansion order. -/
theorem orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_qExpansionOrderAtCusp_of_isRegularCusp (f : F)
    {γ : SL(2, ℤ)} (hreg : Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ)) :
    orderAtCuspOrbit f (Γ.cuspOrbitOfSL2Z γ) =
      (qExpansionOrderAtCusp
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty
        (⇑f ∣[k] mapGL ℝ γ) : ℚ) := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k := _root_.ModularForm.translate f (mapGL ℝ γ)
  have hw_mem := Γγ.isRegularAtInfty_iff.mp ((Γ.isRegularCusp_cuspOrbitOfSL2Z γ).mp hreg)
  have : Fact (IsCusp OnePoint.infty Γγ) :=
    ⟨Γγ.isCusp_of_mem_strictPeriods Γγ.widthInfty_pos hw_mem⟩
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact TauCeti.orderAtCusp_eq_qExpansionOrderAtCusp Γγ.widthInfty_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex fγ hw_mem)
    (ModularFormClass.bdd_at_infty fγ) (ModularFormClass.holo fγ)

/-- At a regular cusp orbit, `orderAtCuspOrbit f C` is a natural number regardless of weight. -/
theorem exists_orderAtCuspOrbit_eq_natCast_of_isRegularCusp (f : F)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hreg : Γ.IsRegularCusp C) :
    ∃ m : ℕ, orderAtCuspOrbit f C = m := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z_eq_qExpansionOrderAtCusp_of_isRegularCusp f hreg,
    qExpansionOrderAtCusp_def]
  exact ⟨_, Int.cast_natCast _⟩

/-- In even weight, `orderAtCuspOrbit f C` is a natural number at every cusp orbit. -/
theorem exists_orderAtCuspOrbit_eq_natCast_of_even (f : F) (hk : Even k)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : ∃ m : ℕ, orderAtCuspOrbit f C = m := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact exists_orderAtCusp_eq_natCast_of_even (_root_.ModularForm.translate f (mapGL ℝ γ)) hk

/-- For nonzero modular `f` of odd weight, the order at an irregular cusp is `m + 1 / 2`. -/
theorem exists_orderAtCuspOrbit_eq_natCast_add_half_of_odd_of_not_isRegularCusp (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hk : Odd k) {C : (Γ.map sl2zToPSL2R).CuspOrbit}
    (hirr : ¬Γ.IsRegularCusp C) : ∃ m : ℕ, orderAtCuspOrbit f C = (m : ℚ) + 1 / 2 := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ)]
  exact exists_orderAtCusp_eq_natCast_add_half_of_odd_of_not_isRegularAtInfty
    (_root_.ModularForm.translate f (mapGL ℝ γ))
    (by rw [_root_.ModularForm.coe_translate]; exact (SlashAction.slash_eq_zero_iff ..).not.mpr hf)
    hk (mt (Γ.isRegularCusp_cuspOrbitOfSL2Z γ).mpr hirr)

end Modular

/-- **Cuspidality via cusp-orbit orders**: nonzero `f` belongs to `ModularForm.cuspFormSubmodule`
iff `0 < orderAtCuspOrbit f C` at every cusp orbit `C`. -/
theorem _root_.ModularForm.mem_cuspFormSubmodule_iff_forall_orderAtCuspOrbit_pos [Γ.FiniteIndex]
    {f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k} (hf : f ≠ 0) :
    f ∈ _root_.ModularForm.cuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) k ↔
      ∀ C : (Γ.map sl2zToPSL2R).CuspOrbit, 0 < orderAtCuspOrbit f C := by
  have hf' : (⇑f : ℍ → ℂ) ≠ 0 := FunLike.coe_zero_iff.not.mpr hf
  rw [_root_.ModularForm.mem_cuspFormSubmodule_iff, _root_.ModularForm.isCuspForm_iff]
  refine ⟨fun hcusp C ↦ ?_, fun hpos c hc ↦ ?_⟩
  · obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    exact (orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff hf' γ).mpr <|
      hcusp ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr (_root_.isCusp_SL2Z_iff'.mpr
        ⟨γ, rfl⟩)) (mapGL ℝ γ) rfl
  · rw [OnePoint.isZeroAt_iff_forall_SL2Z ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)]
    intro γ _
    rw [_root_.ModularForm.SL_slash, Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
    exact (orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff hf' γ).mp (hpos _)

/-- **Additivity on products at cusps (`ModularFormClass` form)**. -/
theorem orderAtCuspOrbit_eq_add_of_coe_eq_mul [Γ.FiniteIndex]
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [ModularFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) (k₁ + k₂)]
    (f : F₁) (g : F₂) (fg : F₃) (hfg : ⇑fg = ⇑f * ⇑g)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit fg C = orderAtCuspOrbit f C + orderAtCuspOrbit g C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  let fγ : ModularForm Γγ k₁ := _root_.ModularForm.translate f (mapGL ℝ γ)
  let gγ : ModularForm Γγ k₂ := _root_.ModularForm.translate g (mapGL ℝ γ)
  have h2w := mul_pos two_pos Γγ.widthInfty_pos
  have hper := Γγ.two_mul_widthInfty_mem_strictPeriods
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z, orderAtCuspOrbit_cuspOrbitOfSL2Z,
    orderAtCuspOrbit_cuspOrbitOfSL2Z, hfg, _root_.ModularForm.mul_slash, det_mapGL, Units.val_one,
    abs_one, one_smul, ← _root_.ModularForm.coe_translate f (mapGL ℝ γ),
    ← _root_.ModularForm.coe_translate g (mapGL ℝ γ)]
  refine TauCeti.orderAtCusp_mul (ModularFormClass.analyticAt_cuspFunction_zero fγ h2w hper)
    (ModularFormClass.analyticAt_cuspFunction_zero gγ h2w hper)
    (analyticOrderAt_cuspFunction_ne_top h2w hper ?_)
    (analyticOrderAt_cuspFunction_ne_top h2w hper ?_)
  · rw [_root_.ModularForm.coe_translate]; exact (SlashAction.slash_eq_zero_iff ..).not.mpr hf
  · rw [_root_.ModularForm.coe_translate]; exact (SlashAction.slash_eq_zero_iff ..).not.mpr hg

/-- Additivity of `orderAtCuspOrbit` on products of nonzero modular forms. -/
theorem _root_.ModularForm.orderAtCuspOrbit_mul [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    orderAtCuspOrbit (f.mul g) C = orderAtCuspOrbit f C + orderAtCuspOrbit g C :=
  orderAtCuspOrbit_eq_add_of_coe_eq_mul f g (f.mul g) (_root_.ModularForm.coe_mul f g)
    (FunLike.coe_zero_iff.not.mpr hf) (FunLike.coe_zero_iff.not.mpr hg) C

section Cusp

variable [Γ.FiniteIndex] [CuspFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- Every nonzero cusp form has strictly positive vanishing order at every cusp orbit. -/
theorem orderAtCuspOrbit_pos {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    0 < orderAtCuspOrbit f C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [orderAtCuspOrbit_cuspOrbitOfSL2Z_pos_iff hf γ, ← _root_.CuspForm.coe_translate f (mapGL ℝ γ)]
  exact CuspFormClass.zero_at_infty (_root_.CuspForm.translate f (mapGL ℝ γ))

/-- Every nonzero cusp form has vanishing order at least `1 / 2` at every cusp orbit. -/
theorem one_div_two_le_orderAtCuspOrbit {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : 1 / 2 ≤ orderAtCuspOrbit f C := by
  obtain ⟨m, hm⟩ := exists_orderAtCuspOrbit_eq_natCast_div_two f C
  have hpos := orderAtCuspOrbit_pos hf C
  rw [hm] at hpos ⊢
  have : (1 : ℚ) ≤ m := by
    exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast (by linarith : (0 : ℚ) < m) : 0 < m)
  linarith

/-- At a regular cusp orbit, every nonzero cusp form has vanishing order at least `1`. -/
theorem one_le_orderAtCuspOrbit_of_isRegularCusp {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    {C : (Γ.map sl2zToPSL2R).CuspOrbit} (hreg : Γ.IsRegularCusp C) : 1 ≤ orderAtCuspOrbit f C := by
  obtain ⟨m, hm⟩ := exists_orderAtCuspOrbit_eq_natCast_of_isRegularCusp f hreg
  rw [hm]; norm_cast; have : 0 < m := (by exact_mod_cast hm ▸ orderAtCuspOrbit_pos hf C); omega

/-- In even weight, every nonzero cusp form has vanishing order at least `1` at every cusp orbit. -/
theorem one_le_orderAtCuspOrbit_of_even {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) (hk : Even k)
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : 1 ≤ orderAtCuspOrbit f C := by
  obtain ⟨m, hm⟩ := exists_orderAtCuspOrbit_eq_natCast_of_even f hk C
  rw [hm]; norm_cast; have : 0 < m := (by exact_mod_cast hm ▸ orderAtCuspOrbit_pos hf C); omega

end Cusp

end TauCeti.ModularForm

end
