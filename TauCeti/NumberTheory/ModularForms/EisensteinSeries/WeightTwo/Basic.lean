/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.E2.Bounds
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import TauCeti.NumberTheory.ModularForms.Cusps.Basic
public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.Cusps.Rat.Slash

/-!
# The corrected weight-two Eisenstein series

For a positive integer `t`, the function `E₂(z) - t E₂(tz)` is a holomorphic modular form
of weight two on `Γ₀(t)`. The anomalous transformation terms of Mathlib's normalized
`EisensteinSeries.E2` cancel under the integral conjugation attached to `diag(t, 1)`.
Its constant term is `1 - t`, so it is a noncuspidal modular form with nonzero constant
term whenever `t > 1`, while the correction at `t = 1` is zero.

The construction uses Mathlib's `EisensteinSeries.E2_slash_action` and its convergent
Fourier expansion, rather than introducing another definition of `E₂`.

## Main results

* `TauCeti.EisensteinSeries.correctedE2`: the corrected weight-two modular form on `Γ₀(t)`.
* `TauCeti.EisensteinSeries.coe_correctedE2`, `TauCeti.EisensteinSeries.correctedE2_apply`: its
  underlying function and values.
* `TauCeti.EisensteinSeries.hasSum_correctedE2`,
  `TauCeti.EisensteinSeries.qExpansion_coeff_correctedE2`: its convergent Fourier expansion and
  coefficient formula.
* `TauCeti.EisensteinSeries.correctedE2_eq_zero_iff`,
  `TauCeti.EisensteinSeries.correctedE2_mem_cuspFormSubmodule_iff`: the corrected form is zero or
  cuspidal exactly at level one.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Chapter 4.
* T. Miyake, *Modular Forms*, Chapter 4.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Filter Complex ModularForm

open scoped MatrixGroups ModularForm Manifold Topology ArithmeticFunction.sigma

namespace TauCeti.EisensteinSeries

open _root_.EisensteinSeries

variable (t : ℕ) [NeZero t]

private lemma D2_conjScale_slash (γ : SL(2, ℤ)) {c : ℤ} (hc : γ 1 0 = t * c) :
    _root_.EisensteinSeries.D2 (conjScale t γ c hc) ∣[(2 : ℤ)] scaleGL t =
      _root_.EisensteinSeries.D2 γ := by
  ext z
  have hc' : (γ 1 0 : ℂ) = (t : ℂ) * c := by exact_mod_cast hc
  simp [slash_scaleGL_apply, _root_.EisensteinSeries.D2, UpperHalfPlane.denom,
    coe_scaleGL_smul, hc']
  ring

private lemma correctedE2_slash (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 t) :
    (_root_.EisensteinSeries.E2 - _root_.EisensteinSeries.E2 ∣[(2 : ℤ)] scaleGL t)
      ∣[(2 : ℤ)] mapGL ℝ γ =
        _root_.EisensteinSeries.E2 - _root_.EisensteinSeries.E2 ∣[(2 : ℤ)] scaleGL t := by
  obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.mp hγ
  have H := _root_.EisensteinSeries.E2_slash_action γ
  have H' := _root_.EisensteinSeries.E2_slash_action (conjScale t γ c hc)
  rw [SL_slash, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL] at H H'
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, H,
    slash_scaleGL_slash_mapGL _ γ hc, H']
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.smul_slash,
    σ_eq_refl_of_det_pos val_det_scaleGL_pos, ContinuousAlgEquiv.refl_apply,
    D2_conjScale_slash t γ hc]
  abel

/-- The corrected weight-two Eisenstein series `E₂(z) - t E₂(tz)` on `Γ₀(t)`. -/
def correctedE2 : ModularForm ((Gamma0 t).map (mapGL ℝ)) 2 where
  toFun := _root_.EisensteinSeries.E2 - _root_.EisensteinSeries.E2 ∣[(2 : ℤ)] scaleGL t
  slash_action_eq' g hg := by
    obtain ⟨γ, hγ, rfl⟩ := hg
    exact correctedE2_slash t γ hγ
  holo' := _root_.E2_mdifferentiable.sub
    (_root_.E2_mdifferentiable.slash 2 (scaleGL t))
  bdd_at_cusps' hc := by
    have hle : (Gamma0 t).map (mapGL ℝ) ≤ 𝒮ℒ := by
      simpa [MonoidHom.range_eq_map] using Subgroup.map_mono (f := mapGL ℝ) (le_top (a := Gamma0 t))
    have hE := isBoundedAt_E2 (hc.mono hle)
    have hscale := OnePoint.isBoundedAt_rat_slash (Γ := 𝒮ℒ) 2 (scaleGLRat t)
      (fun _ hc ↦ isBoundedAt_E2 hc) (hc.mono hle)
    rw [ModularForm.rat_slash, map_ratCast_scaleGLRat] at hscale
    exact fun g hg ↦ by
      simpa only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash]
        using! (hE g hg).sub (hscale g hg)

/-- The underlying function of the corrected weight-two Eisenstein series. -/
lemma coe_correctedE2 :
    ⇑(correctedE2 t) =
      _root_.EisensteinSeries.E2 - _root_.EisensteinSeries.E2 ∣[(2 : ℤ)] scaleGL t := (rfl)

/-- Evaluation of the corrected weight-two Eisenstein series. -/
@[simp]
lemma correctedE2_apply (z : ℍ) :
    correctedE2 t z = _root_.EisensteinSeries.E2 z - t *
      _root_.EisensteinSeries.E2 (scaleGL t • z) := by
  rw [coe_correctedE2]
  simp [slash_scaleGL_apply]

/-- The convergent Fourier expansion of the corrected weight-two series. -/
theorem hasSum_correctedE2 (z : ℍ) :
    HasSum (fun n : ℕ ↦
      (if n = 0 then 1 - (t : ℂ) else
        -24 * ((σ 1 n : ℂ) - if t ∣ n then t * (σ 1 (n / t) : ℂ) else 0)) •
      Function.Periodic.qParam 1 z ^ n) (correctedE2 t z) := by
  let a : ℕ → ℂ := fun n ↦ if n = 0 then 1 else -24 * σ 1 n
  let b : ℕ → ℂ := fun n ↦ if t ∣ n then a (n / t) else 0
  have hE : HasSum (fun n ↦ a n • Function.Periodic.qParam 1 z ^ n)
      (_root_.EisensteinSeries.E2 z) := by
    simpa [a, Function.Periodic.qParam] using _root_.EisensteinSeries.hasSum_qExpansion_E2 (z := z)
  have hscale : HasSum (fun n ↦ b n • Function.Periodic.qParam 1 z ^ n)
      (_root_.EisensteinSeries.E2 (scaleGL t • z)) := by
    refine (Function.Injective.hasSum_iff (mul_right_injective₀ (NeZero.ne t)) ?_).mp ?_
    · intro n hn
      have hnt : ¬t ∣ n := fun ⟨m, hm⟩ ↦ hn ⟨m, hm.symm⟩
      simp [b, hnt]
    · have hE' : HasSum (fun n ↦ a n •
          Function.Periodic.qParam 1 (↑(scaleGL t • z : ℍ) : ℂ) ^ n)
          (_root_.EisensteinSeries.E2 (scaleGL t • z)) := by
        simpa [a, Function.Periodic.qParam] using
          _root_.EisensteinSeries.hasSum_qExpansion_E2 (z := scaleGL t • z)
      refine hE'.congr_fun fun n ↦ ?_
      simp only [Function.comp_apply, b, dvd_mul_right, ite_true,
        Nat.mul_div_right _ (Nat.pos_of_ne_zero (NeZero.ne t)), pow_mul,
        qParam_one_scaleGL_smul]
  rw [correctedE2_apply]
  convert hE.sub (hscale.const_smul (t : ℂ)) using 1
  ext n
  simp only [smul_eq_mul]
  by_cases hn : n = 0
  · subst n
    simp [a, b]
  · by_cases ht : t ∣ n
    · have hdiv : n / t ≠ 0 := by
        intro hzero
        have := Nat.div_mul_cancel ht
        exact hn (by simpa [hzero] using this.symm)
      simp only [a, b, ite_eq_right hn, ite_eq_left ht, ite_eq_right hdiv]
      ring
    · simp [a, b, hn, ht]

/-- The coefficient formula, with constant term `1 - t` and the divisor-sum correction
at positive indices. -/
@[simp]
theorem qExpansion_coeff_correctedE2 (n : ℕ) :
    (qExpansion 1 (correctedE2 t)).coeff n =
      if n = 0 then 1 - (t : ℂ) else
        -24 * ((σ 1 n : ℂ) - if t ∣ n then t * (σ 1 (n / t) : ℂ) else 0) := by
  exact (ModularFormClass.qExpansion_coeff_unique one_pos
    (by simp [CongruenceSubgroup.strictPeriods_Gamma0]) (hasSum_correctedE2 t) n).symm

/-- At level one the correction vanishes. -/
@[simp]
lemma correctedE2_one : correctedE2 1 = 0 := by
  ext z
  simp [correctedE2_apply]

/-- The corrected series vanishes exactly at level one. -/
@[simp]
lemma correctedE2_eq_zero_iff : correctedE2 t = 0 ↔ t = 1 := by
  constructor
  · intro h
    have H := qExpansion_coeff_correctedE2 t 0
    rw [h] at H
    simp only [FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero, ite_true] at H
    have ht : (t : ℂ) = 1 := (sub_eq_zero.mp H.symm).symm
    exact_mod_cast ht
  · rintro rfl
    exact correctedE2_one

/-- The correction is cuspidal exactly when it is the level-one zero form. Thus at every
level `t > 1` it is a noncuspidal modular form with nonzero constant term. -/
theorem correctedE2_mem_cuspFormSubmodule_iff :
    correctedE2 t ∈ ModularForm.cuspFormSubmodule ((Gamma0 t).map (mapGL ℝ)) 2 ↔ t = 1 := by
  constructor
  · rintro ⟨f, hf⟩
    have H := CuspFormClass.qExpansion_coeff_zero f one_pos
      (by simp [CongruenceSubgroup.strictPeriods_Gamma0])
    have heq : (f : ℍ → ℂ) = ⇑(correctedE2 t) := by
      rw [← hf, CuspForm.toModularFormₗ_eq_coe, ModularFormClass.coe_modularForm]
    rw [heq] at H
    have ht : (t : ℂ) = (1 : ℂ) := by
      simp only [qExpansion_coeff_correctedE2, ite_true] at H
      exact (sub_eq_zero.mp H).symm
    exact_mod_cast ht
  · rintro rfl
    rw [correctedE2_one]
    exact Submodule.zero_mem _

end TauCeti.EisensteinSeries
