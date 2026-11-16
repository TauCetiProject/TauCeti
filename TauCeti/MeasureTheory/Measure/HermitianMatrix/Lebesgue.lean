/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lebesgue measure on the complex Hermitian subspace

`TauCeti.hermitianLebesgue n` is the pushforward of product Lebesgue measure on the `n ^ 2` real
coordinates (diagonal entries and strictly upper-triangular real and imaginary parts) along
`(TauCeti.hermitianCoordinates n).symm`.

The Frobenius volume of `measureSpaceOfInnerProductSpace` is a Haar measure for the same topology
with a different normalization: each of the `n * (n - 1)` off-diagonal coordinate basis vectors
has Frobenius norm `√2`, so Frobenius volume is `2 ^ (n * (n - 1) / 2)` times
`TauCeti.hermitianLebesgue n`. Unitary conjugation `Matrix.unitaryGroup.hermitianConj U` is a
Frobenius isometry, so it preserves both Frobenius volume and `TauCeti.hermitianLebesgue n`.

## Main declarations

* `TauCeti.hermitianLebesgue` — Lebesgue measure on the complex Hermitian subspace, normalized by
  the diagonal and upper-triangular real/imaginary coordinates.
* `TauCeti.measurePreserving_hermitianCoordinates_symm` and
  `TauCeti.measurePreserving_hermitianCoordinates` — the coordinate equivalence preserves
  `hermitianLebesgue` and product Lebesgue measure.
* `TauCeti.hermitianLebesgueIsAddHaarMeasure` — `hermitianLebesgue n` is an additive Haar measure.
* `TauCeti.hermitianOrthonormalBasis` — the Frobenius-orthonormal basis obtained by rescaling
  off-diagonal vectors of `TauCeti.hermitianBasis` by `(√2)⁻¹`.
* `TauCeti.volume_hermitianMatrix_eq_smul_hermitianLebesgue` — comparison with Frobenius volume.
* `TauCeti.hermitianLebesgue_zero` — in dimension zero, `hermitianLebesgue` is the Dirac measure.
* `TauCeti.measurePreserving_hermitianFinOneEquiv` — in dimension one, `hermitianFinOneEquiv`
  carries `hermitianLebesgue 1` to Lebesgue measure on `ℝ`.
* `Matrix.unitaryGroup.measurePreserving_hermitianConj_volume` and
  `Matrix.unitaryGroup.measurePreserving_hermitianConj_hermitianLebesgue` — unitary conjugation
  preserves Frobenius volume and `hermitianLebesgue`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped RealInnerProductSpace

namespace TauCeti

/-- Lebesgue measure on the complex Hermitian subspace: the pushforward of product Lebesgue measure
on the `n ^ 2` real coordinates (diagonal entries and strictly upper-triangular real and imaginary
parts) along `(TauCeti.hermitianCoordinates n).symm`. -/
def hermitianLebesgue (n : ℕ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  (volume : Measure (Fin n × Fin n → ℝ)).map (hermitianCoordinates n).symm

/-- The coordinate reconstruction maps product Lebesgue measure to `hermitianLebesgue`. -/
theorem measurePreserving_hermitianCoordinates_symm (n : ℕ) :
    MeasurePreserving (hermitianCoordinates n).symm volume (hermitianLebesgue n) :=
  ⟨(hermitianCoordinates n).symm.continuous.measurable, rfl⟩

/-- The real Hermitian coordinates map `hermitianLebesgue` to product Lebesgue measure. -/
theorem measurePreserving_hermitianCoordinates (n : ℕ) :
    MeasurePreserving (hermitianCoordinates n) (hermitianLebesgue n) volume := by
  have h := measurePreserving_hermitianCoordinates_symm n
  rw [← hermitianCoordinatesMeasurableEquiv_symm_coe] at h
  have h' := h.symm (hermitianCoordinatesMeasurableEquiv n).symm
  rwa [MeasurableEquiv.symm_symm, hermitianCoordinatesMeasurableEquiv_coe] at h'

/-- `hermitianLebesgue` is an additive Haar measure. -/
instance hermitianLebesgueIsAddHaarMeasure (n : ℕ) :
    (hermitianLebesgue n).IsAddHaarMeasure :=
  ContinuousLinearEquiv.isAddHaarMeasure_map (hermitianCoordinates n).symm volume

/-! ### Comparison with the Frobenius volume -/

section comparison

private theorem hermitianLebesgue_eq_addHaar (n : ℕ) :
    hermitianLebesgue n = (hermitianBasis n).addHaar := by
  have hb : (Pi.basisFun ℝ (Fin n × Fin n)).map
      (hermitianCoordinates n).symm.toLinearEquiv = hermitianBasis n :=
    Basis.eq_of_apply_eq fun p => by simp [hermitianBasis_apply]
  rw [hermitianLebesgue, ← Module.Basis.addHaar_basisFun, Basis.map_addHaar, hb]

private theorem inner_hermitianBasis_eq (n : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (p : Fin n × Fin n) :
    ⟪A, hermitianBasis n p⟫ = (if p.1 = p.2 then 1 else 2) * hermitianCoordinates n A p := by
  obtain ⟨i, j⟩ := p
  rw [selfAdjoint.inner_eq_re_trace_mul]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [coe_hermitianBasis_offDiag_lt n h, Matrix.mul_add, Matrix.trace_add,
      Matrix.trace_mul_single, Matrix.trace_mul_single]
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_one,
      Complex.add_re, selfAdjoint.coe_apply_re_comm A i j,
      hermitianCoordinates_apply_of_le n A h.le, ite_eq_right h.ne]
    ring
  · rw [coe_hermitianBasis_diag, Matrix.trace_mul_single]
    simp [hermitianCoordinates_apply_of_le n A le_rfl]
  · rw [coe_hermitianBasis_offDiag_gt n h, Matrix.mul_sub, Matrix.trace_sub,
      Matrix.trace_mul_single, Matrix.trace_mul_single]
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Complex.sub_re,
      Complex.mul_I_re, selfAdjoint.coe_apply_im_comm A j i,
      hermitianCoordinates_apply_of_gt n A h, ite_eq_right h.ne']
    ring

/-- The rescaling that turns `TauCeti.hermitianBasis` into a Frobenius-orthonormal basis:
`1` on the diagonal and `(√2)⁻¹` off it. -/
private def hermScale (n : ℕ) (p : Fin n × Fin n) : ℝˣ :=
  if p.1 = p.2 then 1 else Units.mk0 (Real.sqrt 2)⁻¹ (by positivity)

private theorem hermScale_coe (n : ℕ) (p : Fin n × Fin n) :
    ((hermScale n p : ℝˣ) : ℝ) = if p.1 = p.2 then 1 else (Real.sqrt 2)⁻¹ := by
  rw [hermScale]
  split <;> simp

private theorem orthonormal_hermScaled (n : ℕ) :
    Orthonormal ℝ ⇑((hermitianBasis n).unitsSMul (hermScale n)) := by
  rw [orthonormal_iff_ite]
  intro p q
  rw [Basis.unitsSMul_apply, Basis.unitsSMul_apply, Units.smul_def, Units.smul_def,
    real_inner_smul_left, real_inner_smul_right, inner_hermitianBasis_eq]
  have hcoord : hermitianCoordinates n (hermitianBasis n p) q = if p = q then 1 else 0 := by
    rw [hermitianBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  rw [hcoord]
  by_cases hpq : p = q
  · subst hpq
    by_cases hd : p.1 = p.2
    · simp [hermScale_coe, hd]
    · simp only [hermScale_coe, hd, ↓reduceIte, mul_one]
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (by norm_num), inv_mul_cancel₀ two_ne_zero]
  · simp [hpq]

/-- The Frobenius-orthonormal basis of the complex Hermitian subspace obtained by rescaling the
off-diagonal vectors of `TauCeti.hermitianBasis` by `(√2)⁻¹`. -/
def hermitianOrthonormalBasis (n : ℕ) :
    OrthonormalBasis (Fin n × Fin n) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  ((hermitianBasis n).unitsSMul (hermScale n)).toOrthonormalBasis (orthonormal_hermScaled n)

/-- Each vector of `TauCeti.hermitianOrthonormalBasis` is `hermitianBasis` on the diagonal and
`(√2)⁻¹ • hermitianBasis` off it. -/
theorem hermitianOrthonormalBasis_apply (n : ℕ) (p : Fin n × Fin n) :
    hermitianOrthonormalBasis n p =
      if p.1 = p.2 then hermitianBasis n p else (Real.sqrt 2)⁻¹ • hermitianBasis n p := by
  rw [hermitianOrthonormalBasis, Basis.coe_toOrthonormalBasis, Basis.unitsSMul_apply,
    Units.smul_def, hermScale_coe]
  split_ifs <;> simp

private theorem addHaar_hermScaled (n : ℕ) :
    ((hermitianBasis n).unitsSMul (hermScale n)).addHaar =
      (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) := by
  rw [← Basis.toBasis_toOrthonormalBasis _ (orthonormal_hermScaled n),
    OrthonormalBasis.addHaar_eq_volume]

private theorem card_offDiag_fin_prod (n : ℕ) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2).card = n * (n - 1) := by
  have hdiag : (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2).card = n := by
    have hbij : (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2) =
        Finset.univ.image fun i : Fin n => (i, i) := by
      ext ⟨i, j⟩
      simp [eq_comm]
    rw [hbij, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Finset.card_fin]
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n × Fin n)))
    (p := fun p => p.1 = p.2)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hdiag, ← ne_eq] at hsum
  rcases n with _ | k
  · simp
  · rw [Nat.add_sub_cancel]
    have : (k + 1) * (k + 1) = (k + 1) + (k + 1) * k := by ring
    omega

private theorem prod_hermScale_inv (n : ℕ) :
    (((∏ p, hermScale n p)⁻¹ : ℝˣ) : ℝ) = (2 : ℝ) ^ (n * (n - 1) / 2) := by
  have hprod : ((∏ p, hermScale n p : ℝˣ) : ℝ) = (Real.sqrt 2)⁻¹ ^ (n * (n - 1)) := by
    rw [← Units.coeHom_apply, map_prod]
    simp only [Units.coeHom_apply, hermScale_coe]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, card_offDiag_fin_prod]
  rw [Units.val_inv_eq_inv_val, hprod, inv_pow, inv_inv]
  conv_lhs =>
    rw [← Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd, pow_mul,
      Real.sq_sqrt (by norm_num)]

private theorem volume_parallelepiped_hermitianBasis (n : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)))
        (hermitianBasis n).parallelepiped =
      ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2)) := by
  rw [Basis.coe_parallelepiped, ← addHaar_hermScaled n, Measure.addHaar_parallelepiped,
    Basis.det_unitsSMul]
  simp only [_root_.smul_apply, Basis.det_self, smul_eq_mul, mul_one]
  rw [prod_hermScale_inv]
  exact congrArg ENNReal.ofReal (abs_of_nonneg (by positivity))

end comparison

/-- The Frobenius volume of the complex Hermitian subspace is `2 ^ (n * (n - 1) / 2)` times
`TauCeti.hermitianLebesgue n`: each of the `n * (n - 1)` off-diagonal coordinate directions has
Frobenius norm `√2`. -/
theorem volume_hermitianMatrix_eq_smul_hermitianLebesgue (n : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) =
      ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2)) • hermitianLebesgue n := by
  rw [hermitianLebesgue_eq_addHaar, Basis.addHaar_def, ← volume_parallelepiped_hermitianBasis]
  exact Measure.addHaarMeasure_unique _ _

/-- In dimension zero, the complex Hermitian subspace is a single point and `hermitianLebesgue` is
the Dirac measure there. -/
theorem hermitianLebesgue_zero : hermitianLebesgue 0 = Measure.dirac 0 := by
  have : IsEmpty (Fin 0 × Fin 0) := ⟨fun p => p.1.elim0⟩
  rw [hermitianLebesgue, volume_pi, Measure.pi_of_empty _ 0, Measure.map_dirac, map_zero]

/-- In dimension one, reading the single real diagonal entry carries `hermitianLebesgue 1` to
Lebesgue measure on `ℝ`. -/
theorem measurePreserving_hermitianFinOneEquiv :
    MeasurePreserving hermitianFinOneEquiv (hermitianLebesgue 1) volume := by
  let _ : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ => Subsingleton.elim _ _⟩
  have h : (hermitianFinOneEquiv : _ → ℝ) =
      MeasurableEquiv.funUnique (Fin 1 × Fin 1) ℝ ∘ hermitianCoordinates 1 := by
    funext A
    have hdefault : (default : Fin 1 × Fin 1) = (0, 0) := Subsingleton.elim _ _
    simp [Function.comp_apply, hdefault]
  rw [h]
  exact (volume_preserving_funUnique (Fin 1 × Fin 1) ℝ).comp
    (measurePreserving_hermitianCoordinates 1)

end TauCeti

/-! ### Unitary invariance of Frobenius volume and coordinate Lebesgue measure -/

namespace Matrix.unitaryGroup

variable {n : ℕ}

/-- Unitary conjugation preserves Frobenius volume on the complex Hermitian subspace. -/
theorem measurePreserving_hermitianConj_volume (U : Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (hermitianConj U) volume volume :=
  (hermitianConj U).measurePreserving

/-- Unitary conjugation preserves `TauCeti.hermitianLebesgue n` on the complex Hermitian
subspace. -/
theorem measurePreserving_hermitianConj_hermitianLebesgue (U : Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (hermitianConj U) (TauCeti.hermitianLebesgue n)
      (TauCeti.hermitianLebesgue n) := by
  refine ⟨(hermitianConj U).continuous.measurable, ?_⟩
  set c : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2))
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsmul : c • (TauCeti.hermitianLebesgue n).map (hermitianConj U) =
      c • TauCeti.hermitianLebesgue n := by
    rw [← Measure.map_smul, ← TauCeti.volume_hermitianMatrix_eq_smul_hermitianLebesgue n,
      (measurePreserving_hermitianConj_volume U).map_eq]
    exact (hermitianConj U).continuous.measurable.aemeasurable
  refine Measure.ext fun s _ => (ENNReal.mul_right_inj hc0 hcTop).1 ?_
  have h := congrArg (fun μ : Measure _ => μ s) hsmul
  simpa only [_root_.smul_apply, smul_eq_mul] using h

end Matrix.unitaryGroup
