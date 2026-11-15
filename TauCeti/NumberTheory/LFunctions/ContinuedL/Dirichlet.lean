/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.ContinuedL.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Identification of the continued L-function of a primitive Dirichlet character

For a primitive Dirichlet character `χ` modulo `N`, `dirichletData χ hχ` packages Mathlib's
`χ.completedLFunction` multiplied by the conductor power `N^(s/2)`. At conductor `N = 1` the card
equals `riemannZetaData`, whose continued L-function is `riemannZeta = χ.LFunction`; at conductor
`N > 1` the card has `polarOrder = 0`, so multiplying by `N^(-s/2)` and `(χ.gammaFactor s)⁻¹`
recovers `χ.completedLFunction s / χ.gammaFactor s = χ.LFunction s` everywhere on `ℂ`, trivial zeros
and `s = 0` included.

For non-real characters (`χ ≠ χ⁻¹`), the dual card `dirichletData χ⁻¹ hχ.inv` has a distinct
continued L-function, confirming that the functional equation genuinely pairs `χ` with `χ⁻¹`.

## Main results

* `TauCeti.LFunctions.dirichletData_continuedL`: `(dirichletData χ hχ).continuedL = χ.LFunction`.
* `TauCeti.LFunctions.dirichletData_continuedL_eq_dual_continuedL_iff`:
  `(dirichletData χ hχ).continuedL = (dirichletData χ hχ).dual.continuedL ↔ χ = χ⁻¹`.
-/

public section

open Complex Filter Topology

namespace TauCeti.LFunctions

section Main

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- **The continued uncompleted L-function of `dirichletData χ hχ` is `χ.LFunction` everywhere on
`ℂ`**, for both principal (`N = 1`) and nonprincipal (`N > 1`) primitive characters, including at
`s = 0`, `s = 1`, and the trivial zeros. -/
@[simp]
theorem dirichletData_continuedL : (dirichletData χ hχ).continuedL = χ.LFunction := by
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne, riemannZetaData_continuedL, DirichletCharacter.LFunction_modOne_eq]
  · ext s
    have hp : (dirichletData χ hχ).polarOrder s = 0 := by simp [hN]
    have hpow : (N : ℂ) ^ (-s / 2) * (N : ℂ) ^ (s / 2) = 1 := by
      rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne N)), neg_div, neg_add_cancel, cpow_zero]
    rw [(dirichletData χ hχ).continuedL_of_polarOrder_eq_zero hp,
      (dirichletData χ hχ).invGammaFactor_def, dirichletData_conductor, PNat.mk_coe,
      dirichletData_completed, dirichletData_gammaFactor,
      χ.LFunction_eq_completed_div_gammaFactor s (.inr hN), div_eq_mul_inv]
    calc
      (N : ℂ) ^ (-s / 2) * ((N : ℂ) ^ (s / 2) * χ.completedLFunction s) *
          (χ.gammaFactor s)⁻¹ =
        ((N : ℂ) ^ (-s / 2) * (N : ℂ) ^ (s / 2)) *
          (χ.completedLFunction s * (χ.gammaFactor s)⁻¹) := by ring
      _ = χ.completedLFunction s * (χ.gammaFactor s)⁻¹ := by rw [hpow, one_mul]

/-- The continued L-functions of a primitive Dirichlet card and its dual coincide if and only if the
character is real (`χ = χ⁻¹`). -/
theorem dirichletData_continuedL_eq_dual_continuedL_iff :
    (dirichletData χ hχ).continuedL = (dirichletData χ hχ).dual.continuedL ↔ χ = χ⁻¹ := by
  rw [dirichletData_continuedL, dirichletData_dual, dirichletData_continuedL]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [← h]⟩
  have ha (ψ : DirichletCharacter ℂ N) : LSeries.abscissaOfAbsConv (ψ ·) < ⊤ :=
    (ψ.LSeriesSummable_of_one_lt_re (s := 2) (by norm_num)).abscissaOfAbsConv_le.trans_lt
      (EReal.coe_lt_top _)
  have hev : (fun x : ℝ ↦ LSeries (χ ·) x) =ᶠ[atTop] fun x : ℝ ↦ LSeries (χ⁻¹ ·) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : 1 < ((x : ℂ)).re := by simpa using hx
    rw [← χ.LFunction_eq_LSeries hx', ← χ⁻¹.LFunction_eq_LSeries hx', h]
  have hnat := fun {n : ℕ} (hn : n ≠ 0) ↦ LSeries.eq_of_LSeries_eventually_eq (ha χ) (ha χ⁻¹) hev hn
  ext a
  have hcast : (((ZMod.val (a : ZMod N) + N : ℕ) : ZMod N)) = (a : ZMod N) := by simp
  rw [← hcast]
  exact hnat (Nat.add_pos_right _ (NeZero.pos N)).ne'

end Main

section QuarticModFiveCheck

private def quarticVal : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | 2 => I
  | 3 => -I
  | _ => -1

private def quarticCharModFiveFun (a : ZMod 5) : ℂ := quarticVal a.val

private def quarticCharModFive : DirichletCharacter ℂ 5 where
  toFun := quarticCharModFiveFun
  map_one' := rfl
  map_mul' a b := by
    have : Fact (0 < 5) := ⟨by decide⟩
    simp only [quarticCharModFiveFun, ZMod.val_mul]
    have ha : a.val < 5 := a.val_lt
    have hb : b.val < 5 := b.val_lt
    interval_cases a.val <;> interval_cases b.val <;> norm_num [quarticVal]
  map_nonunit' a ha := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have ha0 : a = 0 := by
      by_contra h0
      exact ha (isUnit_iff_ne_zero.mpr h0)
    subst ha0
    rfl

private theorem quarticCharModFive_apply_two : quarticCharModFive 2 = I := rfl

private theorem quarticCharModFive_ne_one : quarticCharModFive ≠ 1 := by
  have h20 : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro h
  have h2 : quarticCharModFive 2 = (1 : DirichletCharacter ℂ 5) 2 := congrArg (· 2) h
  rw [quarticCharModFive_apply_two, MulChar.one_apply (isUnit_iff_ne_zero.mpr h20)] at h2
  have him := congrArg Complex.im h2
  norm_num at him

private theorem quarticCharModFive_isPrimitive : quarticCharModFive.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  exact ((Nat.prime_five.dvd_iff_eq
    (mt quarticCharModFive.eq_one_iff_conductor_eq_one.mpr quarticCharModFive_ne_one)).mp
      quarticCharModFive.conductor_dvd_level).symm

private theorem quarticCharModFive_ne_inv :
    quarticCharModFive ≠ quarticCharModFive⁻¹ := fun h ↦ by
  have hc := congrArg (fun d : AnalyticLFunctionData ↦ d.coeff 2)
    (dirichletData_dual quarticCharModFive quarticCharModFive_isPrimitive)
  simp only [AnalyticLFunctionData.dual_coeff,
    dirichletData_coeff_of_ne_zero _ _ (two_ne_zero (α := ℕ)), ← h] at hc
  rw [show ((2 : ℕ) : ZMod 5) = 2 from rfl, quarticCharModFive_apply_two] at hc
  have him := congrArg Complex.im hc
  norm_num at him

private theorem quarticCharModFive_gammaFactor_ne_zero {w : ℂ} (hw : w.im ≠ 0) :
    (dirichletData quarticCharModFive quarticCharModFive_isPrimitive).gammaFactor w ≠ 0 := by
  rw [dirichletData_gammaFactor]
  rcases quarticCharModFive.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    rintro h0
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h0
    exact hw (by simp [hn])
  · rw [ho.gammaFactor_def]
    rintro h0
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h0
    exact hw (by simpa using congrArg Complex.im hn)

-- For the quartic primitive character modulo `5`, `continuedL` is distinct from `dual.continuedL`,
-- and the functional equation fails if `d.dual` is replaced by `d` itself.
example : ∃ (χ : DirichletCharacter ℂ 5) (hχ : χ.IsPrimitive),
    let d := dirichletData χ hχ
    d.continuedL ≠ d.dual.continuedL ∧
      ∃ s : ℂ, d.polarOrder s = 0 ∧ d.gammaFactor s ≠ 0 ∧ d.gammaFactor (1 - s) ≠ 0 ∧
        d.gammaFactor s * d.continuedL s ≠
          d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
            d.gammaFactor (1 - s) * d.continuedL (1 - s) := by
  let χ := quarticCharModFive
  let hχ := quarticCharModFive_isPrimitive
  let d := dirichletData χ hχ
  have hneq : d.continuedL ≠ d.dual.continuedL :=
    (dirichletData_continuedL_eq_dual_continuedL_iff χ hχ).not.mpr quarticCharModFive_ne_inv
  refine ⟨χ, hχ, hneq, ?_⟩
  by_contra! hself
  apply hneq
  have hγ_dual : d.dual.gammaFactor = d.gammaFactor := by
    classical
    ext w
    rw [dirichletData_dual, dirichletData_gammaFactor, dirichletData_gammaFactor]
    simp only [DirichletCharacter.gammaFactor, DirichletCharacter.even_inv_iff]
  have heq_im {w : ℂ} (hw : w.im ≠ 0) : d.continuedL w = d.dual.continuedL w := by
    have hw' : (1 - w).im ≠ 0 := by simp [hw]
    have hp : d.polarOrder (1 - w) = 0 := by simp [d]
    have h1 := hself (1 - w) hp (quarticCharModFive_gammaFactor_ne_zero hw')
      (by rw [sub_sub_cancel]; exact quarticCharModFive_gammaFactor_ne_zero hw)
    have h2 := (dirichletData_hasFunctionalEquation χ hχ).gammaFactor_mul_continuedL hp
      (quarticCharModFive_gammaFactor_ne_zero hw')
      (by rw [hγ_dual, sub_sub_cancel]; exact quarticCharModFive_gammaFactor_ne_zero hw)
    rw [sub_sub_cancel] at h1 h2
    rw [hγ_dual] at h2
    have hε : d.rootNumber ≠ 0 := norm_ne_zero_iff.mp
      (by rw [(dirichletData_hasFunctionalEquation χ hχ).norm_rootNumber]; exact one_ne_zero)
    have hc : ((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - (1 - w)) ≠ 0 :=
      cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr d.conductor.ne_zero))
    exact mul_left_cancel₀
      (mul_ne_zero (mul_ne_zero hε hc) (quarticCharModFive_gammaFactor_ne_zero hw))
      (h1.symm.trans h2)
  have ha1 : AnalyticOnNhd ℂ d.continuedL Set.univ := fun z _ ↦
    dirichletData_continuedL χ hχ ▸
      (DirichletCharacter.differentiable_LFunction quarticCharModFive_ne_one).analyticAt z
  have ha2 : AnalyticOnNhd ℂ d.dual.continuedL Set.univ := fun z _ ↦ by
    rw [dirichletData_dual, dirichletData_continuedL]
    exact (DirichletCharacter.differentiable_LFunction
      (inv_ne_one.mpr quarticCharModFive_ne_one)).analyticAt z
  have hopen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  exact funext fun z ↦ ha1.eqOn_of_preconnected_of_eventuallyEq ha2 isPreconnected_univ
    (Set.mem_univ I) (Filter.eventually_of_mem (hopen.mem_nhds (by simp)) fun w hw ↦ heq_im hw)
    (Set.mem_univ z)

end QuarticModFiveCheck

end TauCeti.LFunctions
