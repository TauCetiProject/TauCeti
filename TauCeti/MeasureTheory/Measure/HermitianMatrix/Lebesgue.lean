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

`TauCeti.hermitianLebesgue p` is the pushforward of product Lebesgue measure on `Fin p × Fin p → ℝ`
along `(TauCeti.hermitianCoordinates p).symm`: product Lebesgue measure in the `p` diagonal real
coordinates `(A i i).re` and the `p * (p - 1)` upper off-diagonal real and imaginary coordinates
`(A i j).re` and `(A i j).im` (`i < j`).

Parallel to `TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue`, this file compares
`hermitianLebesgue p` with the trace-inner-product volume of `measureSpaceOfInnerProductSpace`:
each of the `p * (p - 1)` off-diagonal basis directions `Eᵢⱼ + Eⱼᵢ` and `I • (Eⱼᵢ - Eᵢⱼ)` has
Frobenius norm `√2`, so trace-inner-product `volume` is `2 ^ (p * (p - 1) / 2)` times
`hermitianLebesgue p`. Unitary conjugation preserves both measures.

## Main declarations

* `TauCeti.hermitianLebesgue` — coordinate Lebesgue measure on the complex Hermitian subspace.
* `TauCeti.measurePreserving_hermitianCoordinates_symm`,
  `TauCeti.measurePreserving_hermitianCoordinates` — coordinate reconstruction and extraction are
  measure preserving.
* `TauCeti.hermitianLebesgueIsAddHaarMeasure` — `hermitianLebesgue p` is an additive Haar measure.
* `TauCeti.hermitianOrthonormalBasis` — the Frobenius orthonormal basis obtained by rescaling the
  off-diagonal coordinate basis vectors by `(√2)⁻¹`.
* `TauCeti.volume_hermitianMatrix_eq_smul_hermitianLebesgue` — comparison with trace-inner-product
  `volume`.
* `TauCeti.hermitianLebesgue_zero` — in dimension zero, `hermitianLebesgue` is the Dirac mass at
  zero.
* `TauCeti.measurePreserving_hermitianFinOneEquiv` — in dimension one, reading the single real
  entry carries `hermitianLebesgue 1` to Lebesgue measure on `ℝ`.
* `Matrix.unitaryGroup.measurePreserving_hermitianConj_volume`,
  `Matrix.unitaryGroup.measurePreserving_hermitianConj_hermitianLebesgue` — unitary conjugation
  preserves both `volume` and `hermitianLebesgue`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5.1.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate ENNReal RealInnerProductSpace

namespace TauCeti

/-- Coordinate Lebesgue measure on the complex Hermitian subspace: the pushforward of product
Lebesgue measure in the diagonal real and upper off-diagonal real and imaginary coordinates along
`(TauCeti.hermitianCoordinates p).symm`. -/
def hermitianLebesgue (p : ℕ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (volume : Measure (Fin p × Fin p → ℝ)).map (hermitianCoordinates p).symm

/-- Defining formula for `TauCeti.hermitianLebesgue`. -/
theorem hermitianLebesgue_def (p : ℕ) :
    hermitianLebesgue p =
      (volume : Measure (Fin p × Fin p → ℝ)).map (hermitianCoordinates p).symm :=
  (rfl)

/-- The coordinate reconstruction maps product Lebesgue measure to `hermitianLebesgue`. -/
theorem measurePreserving_hermitianCoordinates_symm (p : ℕ) :
    MeasurePreserving (hermitianCoordinates p).symm volume (hermitianLebesgue p) :=
  ⟨(hermitianCoordinates p).symm.continuous.measurable, rfl⟩

/-- `TauCeti.hermitianCoordinates` maps `hermitianLebesgue` to product Lebesgue measure. -/
theorem measurePreserving_hermitianCoordinates (p : ℕ) :
    MeasurePreserving (hermitianCoordinates p) (hermitianLebesgue p) volume := by
  have h := measurePreserving_hermitianCoordinates_symm p
  rw [← hermitianCoordinatesMeasurableEquiv_symm_coe] at h
  have h' := h.symm (hermitianCoordinatesMeasurableEquiv p).symm
  rwa [MeasurableEquiv.symm_symm, hermitianCoordinatesMeasurableEquiv_coe] at h'

/-- `hermitianLebesgue` is an additive Haar measure. -/
instance hermitianLebesgueIsAddHaarMeasure (p : ℕ) :
    (hermitianLebesgue p).IsAddHaarMeasure :=
  ContinuousLinearEquiv.isAddHaarMeasure_map (hermitianCoordinates p).symm volume

/-! ### Comparison with the trace-inner-product volume -/

section comparison

private theorem hermitianLebesgue_eq_addHaar (p : ℕ) :
    hermitianLebesgue p = (hermitianBasis p).addHaar := by
  have hb : (Pi.basisFun ℝ (Fin p × Fin p)).map
      (hermitianCoordinates p).symm.toLinearEquiv = hermitianBasis p :=
    Basis.eq_of_apply_eq fun ij ↦ by simp [hermitianBasis_apply]
  rw [hermitianLebesgue, ← Module.Basis.addHaar_basisFun, Basis.map_addHaar, hb]

/-- Pairing a Hermitian matrix with the coordinate basis vector `hermitianBasis p kl` reads off
its `kl` coordinate, doubled off the diagonal. -/
private theorem inner_hermitianBasis (p : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) (kl : Fin p × Fin p) :
    ⟪A, hermitianBasis p kl⟫ =
      (if kl.1 = kl.2 then 1 else 2) * hermitianCoordinates p A kl := by
  obtain ⟨k, l⟩ := kl
  rw [selfAdjoint.inner_eq_re_trace_mul]
  rcases lt_trichotomy k l with h | rfl | h
  · rw [coe_hermitianBasis_of_lt p h, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul,
      Matrix.trace_single_mul, one_smul, one_smul, ← selfAdjoint.coe_apply_conj A l k,
      hermitianCoordinates_apply_of_le p A h.le]
    simp only [h.ne, ↓reduceIte, Complex.add_re, Complex.conj_re]
    ring
  · rw [coe_hermitianBasis_diag, Matrix.trace_single_mul, one_smul,
      hermitianCoordinates_apply_of_le p A le_rfl]
    simp
  · rw [coe_hermitianBasis_of_gt p h, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_single_mul,
      Matrix.trace_single_mul, ← selfAdjoint.coe_apply_conj A k l,
      hermitianCoordinates_apply_of_gt p A h]
    simp only [h.ne', ↓reduceIte, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.conj_im]
    ring

private def hermScale (p : ℕ) (ij : Fin p × Fin p) : ℝˣ :=
  if ij.1 = ij.2 then 1 else Units.mk0 (Real.sqrt 2)⁻¹ (by positivity)

private theorem hermScale_coe (p : ℕ) (ij : Fin p × Fin p) :
    ((hermScale p ij : ℝˣ) : ℝ) = if ij.1 = ij.2 then 1 else (Real.sqrt 2)⁻¹ := by
  rw [hermScale]
  split <;> simp

private theorem orthonormal_hermScaled (p : ℕ) :
    Orthonormal ℝ ⇑((hermitianBasis p).unitsSMul (hermScale p)) := by
  rw [orthonormal_iff_ite]
  intro ij kl
  rw [Basis.unitsSMul_apply, Basis.unitsSMul_apply, Units.smul_def, Units.smul_def,
    real_inner_smul_left, real_inner_smul_right, inner_hermitianBasis, hermitianBasis_apply,
    ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply]
  by_cases h : ij = kl
  · subst h
    by_cases hd : ij.1 = ij.2
    · simp [hermScale_coe, hd]
    · simp only [hermScale_coe, hd, ↓reduceIte, mul_one]
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (by norm_num), inv_mul_cancel₀ two_ne_zero]
  · simp [h, Ne.symm h]

/-- The orthonormal basis of the complex Hermitian subspace obtained by rescaling the off-diagonal
vectors of `TauCeti.hermitianBasis` by `(√2)⁻¹`: `Eᵢᵢ` at `(i, i)`, `(Eᵢⱼ + Eⱼᵢ) / √2` at `(i, j)`
for `i < j`, and `I • (Eⱼᵢ - Eᵢⱼ) / √2` at `(i, j)` for `j < i`. -/
def hermitianOrthonormalBasis (p : ℕ) :
    OrthonormalBasis (Fin p × Fin p) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  ((hermitianBasis p).unitsSMul (hermScale p)).toOrthonormalBasis (orthonormal_hermScaled p)

/-- Each vector of `TauCeti.hermitianOrthonormalBasis` is the coordinate basis vector
`TauCeti.hermitianBasis` scaled by `1` on the diagonal and `(√2)⁻¹` off the diagonal. -/
theorem hermitianOrthonormalBasis_apply (p : ℕ) (ij : Fin p × Fin p) :
    hermitianOrthonormalBasis p ij =
      (if ij.1 = ij.2 then (1 : ℝ) else (Real.sqrt 2)⁻¹) • hermitianBasis p ij := by
  rw [hermitianOrthonormalBasis, Basis.coe_toOrthonormalBasis, Basis.unitsSMul_apply,
    Units.smul_def, hermScale_coe]

private theorem addHaar_hermScaled (p : ℕ) :
    ((hermitianBasis p).unitsSMul (hermScale p)).addHaar =
      (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) := by
  rw [← Basis.toBasis_toOrthonormalBasis _ (orthonormal_hermScaled p),
    OrthonormalBasis.addHaar_eq_volume]

private theorem card_hermOffDiag (p : ℕ) :
    ((Finset.univ.filter fun ij : Fin p × Fin p ↦ ij.1 ≠ ij.2).card : ℝ) =
      (p : ℝ) * ((p : ℝ) - 1) := by
  have hdiag : (Finset.univ.filter fun ij : Fin p × Fin p ↦ ij.1 = ij.2) =
      Finset.univ.image fun i : Fin p ↦ (i, i) := by
    ext ⟨i, j⟩
    simp [eq_comm]
  have hcard_diag : (Finset.univ.filter fun ij : Fin p × Fin p ↦ ij.1 = ij.2).card = p := by
    rw [hdiag, Finset.card_image_of_injective _ fun a b h ↦ (Prod.mk.inj h).1, Finset.card_fin]
  have hsum : (Finset.univ.filter fun ij : Fin p × Fin p ↦ ij.1 = ij.2).card +
      (Finset.univ.filter fun ij : Fin p × Fin p ↦ ij.1 ≠ ij.2).card = p * p := by
    simpa [Fintype.card_prod, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun ij : Fin p × Fin p ↦ ij.1 = ij.2)
  rw [hcard_diag] at hsum
  have hcast : (p : ℝ) + ((Finset.univ.filter fun ij : Fin p × Fin p ↦ ij.1 ≠ ij.2).card : ℝ) =
      (p : ℝ) * (p : ℝ) := by
    exact_mod_cast hsum
  linarith

private theorem prod_hermScale_inv (p : ℕ) :
    (((∏ ij, hermScale p ij)⁻¹ : ℝˣ) : ℝ) =
      (2 : ℝ) ^ (((p : ℝ) * ((p : ℝ) - 1)) / 2) := by
  set N : ℕ := (Finset.univ.filter fun ij : Fin p × Fin p ↦ ij.1 ≠ ij.2).card with hN
  have hprod : ((∏ ij, hermScale p ij : ℝˣ) : ℝ) = (Real.sqrt 2)⁻¹ ^ N := by
    rw [← Units.coeHom_apply, map_prod]
    simp only [Units.coeHom_apply, hermScale_coe]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [Units.val_inv_eq_inv_val, hprod, inv_pow, inv_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast ((2 : ℝ) ^ (1 / 2 : ℝ)) N, ← Real.rpow_mul (by norm_num)]
  congr 1
  rw [hN, card_hermOffDiag]
  ring

private theorem volume_parallelepiped_hermitianBasis (p : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)))
        (hermitianBasis p).parallelepiped =
      ENNReal.ofReal ((2 : ℝ) ^ (((p : ℝ) * ((p : ℝ) - 1)) / 2)) := by
  rw [Basis.coe_parallelepiped, ← addHaar_hermScaled p, Measure.addHaar_parallelepiped,
    Basis.det_unitsSMul]
  simp only [_root_.smul_apply, Basis.det_self, smul_eq_mul, mul_one]
  rw [prod_hermScale_inv]
  exact congrArg ENNReal.ofReal (abs_of_nonneg (Real.rpow_nonneg (by norm_num) _))

end comparison

/-- The trace-inner-product `volume` on the complex Hermitian subspace is
`2 ^ (p * (p - 1) / 2)` times `hermitianLebesgue p`: each of the `p * (p - 1)` off-diagonal real
and imaginary coordinate directions has Frobenius norm `√2`. -/
theorem volume_hermitianMatrix_eq_smul_hermitianLebesgue (p : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) =
      ENNReal.ofReal ((2 : ℝ) ^ (((p : ℝ) * ((p : ℝ) - 1)) / 2)) • hermitianLebesgue p := by
  rw [hermitianLebesgue_eq_addHaar, Basis.addHaar_def, ← volume_parallelepiped_hermitianBasis]
  exact Measure.addHaarMeasure_unique _ _

/-- Conversely, `hermitianLebesgue p` is `2 ^ (-(p * (p - 1) / 2))` times trace-inner-product
`volume`. -/
theorem hermitianLebesgue_eq_smul_volume (p : ℕ) :
    hermitianLebesgue p =
      ENNReal.ofReal ((2 : ℝ) ^ (-(((p : ℝ) * ((p : ℝ) - 1)) / 2))) •
        (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) := by
  rw [volume_hermitianMatrix_eq_smul_hermitianLebesgue, smul_smul,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    ← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_smul]

/-- In dimension zero, `hermitianLebesgue` is the Dirac mass at zero. -/
theorem hermitianLebesgue_zero : hermitianLebesgue 0 = Measure.dirac 0 := by
  have : IsEmpty (Fin 0 × Fin 0) := ⟨fun ij ↦ ij.1.elim0⟩
  rw [hermitianLebesgue, volume_pi, Measure.pi_of_empty _ 0, Measure.map_dirac, map_zero]

/-- In dimension one, reading the single real entry carries `hermitianLebesgue 1` to Lebesgue
measure on `ℝ`. -/
theorem measurePreserving_hermitianFinOneEquiv :
    MeasurePreserving hermitianFinOneEquiv (hermitianLebesgue 1) volume := by
  let _ : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have h : (hermitianFinOneEquiv : _ → ℝ) =
      MeasurableEquiv.funUnique (Fin 1 × Fin 1) ℝ ∘ hermitianCoordinates 1 := by
    funext A
    simp only [Function.comp_apply, hermitianFinOneEquiv_apply, MeasurableEquiv.funUnique_apply]
    have hd : (default : Fin 1 × Fin 1) = (0, 0) := Subsingleton.elim _ _
    rw [hd, hermitianCoordinates_apply_of_le 1 A le_rfl]
  rw [h]
  exact (volume_preserving_funUnique (Fin 1 × Fin 1) ℝ).comp
    (measurePreserving_hermitianCoordinates 1)

end TauCeti

namespace Matrix.unitaryGroup

open TauCeti

/-- Unitary conjugation preserves the trace-inner-product `volume` on the complex Hermitian
subspace. -/
theorem measurePreserving_hermitianConj_volume {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ) :
    MeasurePreserving (hermitianConj U) volume volume :=
  (hermitianConj U).measurePreserving

/-- Unitary conjugation preserves coordinate Lebesgue measure `TauCeti.hermitianLebesgue`. -/
theorem measurePreserving_hermitianConj_hermitianLebesgue {p : ℕ}
    (U : Matrix.unitaryGroup (Fin p) ℂ) :
    MeasurePreserving (hermitianConj U) (hermitianLebesgue p) (hermitianLebesgue p) := by
  rw [hermitianLebesgue_eq_smul_volume]
  exact (measurePreserving_hermitianConj_volume U).smul_measure _

end Matrix.unitaryGroup
