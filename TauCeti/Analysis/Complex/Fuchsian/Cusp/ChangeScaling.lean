/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Coordinate

/-!
# Changing the scaling of a cusp

Two normalized data at the same cusp have the same positive primitive generator. Their scalings
are related by `σ' = aσ + b`, with `a > 0`, and their widths satisfy `w' = aw`. More generally, if
an element `k ∈ Γ` carries the cusp of one datum to the cusp of another, then `σ' k σ⁻¹` is such a
positive real affine transformation.
Consequently their exponential coordinates differ by the constant
`exp (2πib / (aw))`, of modulus one. This is the coordinate transition needed to compare cusp
charts on the upper half-plane.

The coordinate accessor `TauCeti.Subgroup.CuspDatum.coordinate` uses
`Function.Periodic.qParam`, so the statements apply before choosing a complex structure on the
cusp quotient. No discreteness hypothesis is needed once normalized cusp data
have been supplied.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Springer, 2005, §2.4.
-/

public section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane OnePoint
open scoped MatrixGroups

namespace TauCeti

variable {Γ : Subgroup PSL(2, ℝ)} {D D' : Γ.CuspDatum}

/-- The positive primitive generator depends only on the cusp, not on its scaling. -/
theorem cuspDatum_generator_eq (hc : D.cusp = D'.cusp) : D.generator = D'.generator := by
  let g := D'.scaling * D.scaling⁻¹
  have hg : g • (∞ : OnePoint ℝ) = ∞ := by
    dsimp only [g]
    rw [mul_smul, inv_smul_eq_iff.mpr D.scaling_smul_cusp.symm, hc,
      D'.scaling_smul_cusp]
  obtain ⟨t, ht, hconj⟩ := exists_conj_upperRightHom_of_smul_infty hg
  let E : Γ.CuspDatum :=
    { D with
      scaling := D'.scaling
      width := t ^ 2 * D.width
      width_pos := mul_pos (sq_pos_of_ne_zero ht) D.width_pos
      scaling_mul_generator_mul_inv := by
        rw [← hconj, ← D.scaling_mul_generator_mul_inv]
        dsimp only [g]
        group }
  have hE : E = D' := Subgroup.CuspDatum.ext rfl
  simpa only [E] using congrArg (fun F : Γ.CuspDatum ↦ F.generator) hE

/-- If `k ∈ Γ` carries the cusp of `D` to the cusp of `D'`, then `σ' k σ⁻¹` fixes `∞`, so it acts
on the upper half-plane by a positive real affine transformation. -/
theorem cuspDatum_exists_scaling_smul_eq_affine {k : Γ} (hk : k • D.cusp = D'.cusp) :
    ∃ a b : ℝ, 0 < a ∧ ∀ z : ℍ,
      (↑(D'.scaling • k • z) : ℂ) = a * (↑(D.scaling • z) : ℂ) + b := by
  have hg : (D'.scaling * (k : PSL(2, ℝ)) * D.scaling⁻¹) • (∞ : OnePoint ℝ) = ∞ := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr D.scaling_smul_cusp.symm, ← Subgroup.smul_def,
      hk, D'.scaling_smul_cusp]
  obtain ⟨g, hgeq⟩ := QuotientGroup.mk_surjective (D'.scaling * (k : PSL(2, ℝ)) * D.scaling⁻¹)
  rw [← hgeq, OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hg
  -- The affine normal form reuses Mathlib's
  -- `UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_eq_zero`.
  obtain ⟨a, b, hab⟩ := exists_SL2_smul_eq_of_apply_zero_one_eq_zero g hg
  refine ⟨a, b, a.property, fun z ↦ ?_⟩
  have heq : g • (D.scaling • z) = D'.scaling • k • z := by
    rw [← UpperHalfPlane.pslMk_smul, hgeq, mul_smul, mul_smul, inv_smul_smul, Subgroup.smul_def]
  rw [← heq, congrFun hab]
  simp only [Function.comp_apply, coe_vadd, coe_pos_real_smul, Complex.real_smul]
  ring

/-- Any two scalings at the same cusp differ by a positive real affine transformation. -/
theorem cuspDatum_exists_scaling_eq_affine (hc : D.cusp = D'.cusp) :
    ∃ a b : ℝ, 0 < a ∧ ∀ z : ℍ,
      (↑(D'.scaling • z) : ℂ) = a * (↑(D.scaling • z) : ℂ) + b := by
  simpa using cuspDatum_exists_scaling_smul_eq_affine (k := (1 : Γ)) (by simpa using hc)

/-- Under `σ' = aσ + b`, the cusp width changes from `w` to `aw`. -/
theorem cuspDatum_width_eq_mul (hc : D.cusp = D'.cusp) {a b : ℝ}
    (hσ : ∀ z : ℍ, (↑(D'.scaling • z) : ℂ) = a * (↑(D.scaling • z) : ℂ) + b) :
    D'.width = a * D.width := by
  have h := hσ ((D.generator : PSL(2, ℝ)) • UpperHalfPlane.I)
  rw [Subgroup.CuspDatum.coe_scaling_smul_generator D, cuspDatum_generator_eq hc,
    Subgroup.CuspDatum.coe_scaling_smul_generator D', hσ] at h
  have hw : (D'.width : ℂ) = (a : ℂ) * D.width := by linear_combination h
  exact_mod_cast hw

/-- The exact change-of-scaling formula for the exponential cusp coordinate. -/
theorem cuspDatum_coordinate_eq (hc : D.cusp = D'.cusp) {a b : ℝ}
    (hσ : ∀ z : ℍ, (↑(D'.scaling • z) : ℂ) = a * (↑(D.scaling • z) : ℂ) + b)
    (z : ℍ) :
    Subgroup.CuspDatum.coordinate D' z =
      Complex.exp (2 * Real.pi * Complex.I * b / (a * D.width)) *
        Subgroup.CuspDatum.coordinate D z := by
  have hw := cuspDatum_width_eq_mul hc hσ
  have ha : a ≠ 0 := by
    intro h
    have := D'.width_pos
    rw [hw, h, zero_mul] at this
    exact lt_irrefl _ this
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hw' : (D.width : ℂ) ≠ 0 := by exact_mod_cast D.width_pos.ne'
  simp only [Subgroup.CuspDatum.coordinate_apply, Function.Periodic.qParam, hσ, hw,
    Complex.ofReal_mul]
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring

/-- The modulus of the exponential cusp coordinate is independent of the normalized scaling. -/
theorem cuspDatum_norm_coordinate_eq (hc : D.cusp = D'.cusp) (z : ℍ) :
    ‖Subgroup.CuspDatum.coordinate D' z‖ = ‖Subgroup.CuspDatum.coordinate D z‖ := by
  obtain ⟨a, b, -, hσ⟩ := cuspDatum_exists_scaling_eq_affine hc
  rw [cuspDatum_coordinate_eq hc hσ, norm_mul, Complex.norm_exp]
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im]

section LiftTransition

variable {D' : Γ.CuspDatum} {s s' h : SL(2, ℝ)} {γ : Γ}

/-- The lift `s' * h * s⁻¹` of `σ' γ σ⁻¹` in `PSL(2, ℝ)`. -/
theorem coe_scaling_mul_mul_inv (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hs' : (s' : PSL(2, ℝ)) = D'.scaling) (hh : (h : PSL(2, ℝ)) = γ) :
    ((s' * h * s⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) = D'.scaling * γ * D.scaling⁻¹ := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, hs', hh]

/-- If `γ ∈ Γ` carries the cusp of `D` to that of `D'`, then `σ' γ σ⁻¹` fixes `∞`, so its lift
`s' * h * s⁻¹` is upper triangular. -/
theorem scaling_mul_mul_inv_apply_one_zero (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hs' : (s' : PSL(2, ℝ)) = D'.scaling) (hh : (h : PSL(2, ℝ)) = γ)
    (hγ : γ • D.cusp = D'.cusp) : (s' * h * s⁻¹) 1 0 = 0 := by
  have hg : ((s' * h * s⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) • (∞ : OnePoint ℝ) = ∞ := by
    rw [coe_scaling_mul_mul_inv hs hs' hh, mul_smul, mul_smul,
      inv_smul_eq_iff.mpr D.scaling_smul_cusp.symm, ← Subgroup.smul_def, hγ,
      D'.scaling_smul_cusp]
  rwa [OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hg

/-- If `γ ∈ Γ` carries the cusp of `D` to that of `D'`, with lifts `s`, `s'`, `h` of
`D.scaling`, `D'.scaling`, `γ`, then the widths satisfy
`D'.width = (s' * h * s⁻¹) 0 0 ^ 2 * D.width`. -/
theorem cuspDatum_width_eq_mul_of_smul (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hs' : (s' : PSL(2, ℝ)) = D'.scaling) (hh : (h : PSL(2, ℝ)) = γ)
    (hγ : γ • D.cusp = D'.cusp) :
    D'.width = (s' * h * s⁻¹) 0 0 ^ 2 * D.width := by
  set t : SL(2, ℝ) := s' * h * s⁻¹
  have ht : t 1 0 = 0 := scaling_mul_mul_inv_apply_one_zero hs hs' hh hγ
  have ht00 : t 0 0 ≠ 0 := by
    have h := t.det_coe
    rw [Matrix.det_fin_two, ht, mul_zero, sub_zero] at h
    exact left_ne_zero_of_mul_eq_one h
  let E : Γ.CuspDatum :=
    { cusp := D'.cusp
      scaling := D'.scaling
      generator := γ * D.generator * γ⁻¹
      width := t 0 0 ^ 2 * D.width
      width_pos := mul_pos (sq_pos_of_ne_zero ht00) D.width_pos
      zpowers_generator := by
        ext g
        simp only [Subgroup.mem_zpowers_iff]
        constructor
        · rintro ⟨n, rfl⟩
          have hgen : D.generator ^ n ∈ MulAction.stabilizer Γ D.cusp :=
            D.zpowers_generator ▸ Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
          rw [MulAction.mem_stabilizer_iff, conj_zpow, ← hγ, mul_smul, mul_smul, inv_smul_smul,
            MulAction.mem_stabilizer_iff.mp hgen]
        · intro hg
          have hmem : γ⁻¹ * g * γ ∈ MulAction.stabilizer Γ D.cusp := by
            rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hγ,
              MulAction.mem_stabilizer_iff.mp hg, ← hγ, inv_smul_smul]
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (D.zpowers_generator.symm ▸ hmem)
          exact ⟨n, by rw [conj_zpow, hn]; group⟩
      scaling_mul_generator_mul_inv := by
        have hconj : D'.scaling * ((γ * D.generator * γ⁻¹ : Γ) : PSL(2, ℝ)) * D'.scaling⁻¹ =
            (t : PSL(2, ℝ)) * upperRightHom D.width * (t : PSL(2, ℝ))⁻¹ := by
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
          rw [← D.scaling_mul_generator_mul_inv, coe_scaling_mul_mul_inv hs hs' hh]
          group
        rw [hconj]
        exact mk_mul_upperRightHom_mul_inv t ht D.width }
  have hE : E = D' := Subgroup.CuspDatum.ext rfl
  exact congrArg (fun F : Γ.CuspDatum ↦ F.width) hE.symm

end LiftTransition

end TauCeti
