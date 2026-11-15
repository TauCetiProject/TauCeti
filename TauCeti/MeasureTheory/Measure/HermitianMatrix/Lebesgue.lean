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
along `(TauCeti.hermitianCoordinates p).symm`, that is, product Lebesgue measure in the `p`
diagonal real coordinates `(A i i).re`, the `p * (p - 1) / 2` strictly upper-triangular real
coordinates `(A i j).re` (`i < j`), and the `p * (p - 1) / 2` strictly upper-triangular imaginary
coordinates `(A i j).im` (`i < j`).

For the real Frobenius inner product `⟪A, B⟫ = Re tr (B * A)`, the `p` diagonal coordinate basis
vectors `Eᵢᵢ` have norm `1` while the `p * (p - 1)` off-diagonal basis vectors `Eᵢⱼ + Eⱼᵢ` and
`I • Eᵢⱼ - I • Eⱼᵢ` (`i < j`) each have norm `√2`. Rescaling the off-diagonal vectors by `(√2)⁻¹`
gives the orthonormal basis `TauCeti.hermitianOrthonormalBasis p`, and the Frobenius volume is
`2 ^ (p * (p - 1) / 2)` times `hermitianLebesgue p`. Unitary conjugation preserves both measures.

## Main declarations

* `TauCeti.hermitianLebesgue` — coordinate Lebesgue measure on the complex Hermitian subspace.
* `TauCeti.measurePreserving_hermitianCoordinates_symm` and
  `TauCeti.measurePreserving_hermitianCoordinates` — measure preservation of the coordinate
  identifications.
* `TauCeti.hermitianLebesgueIsAddHaarMeasure` — `hermitianLebesgue p` is an additive Haar measure.
* `TauCeti.hermitianOrthonormalBasis` — the Frobenius-orthonormal basis obtained by rescaling the
  off-diagonal vectors of `TauCeti.hermitianBasis` by `(√2)⁻¹`.
* `TauCeti.volume_hermitianMatrix_eq_smul_hermitianLebesgue` — comparison with the real Frobenius
  volume: `volume = 2 ^ (p * (p - 1) / 2) • hermitianLebesgue p`.
* `TauCeti.hermitianLebesgue_zero` and `TauCeti.measurePreserving_hermitianFinOneEquiv` — low
  dimensions `p = 0` and `p = 1`.
* `Matrix.UnitaryGroup.map_hermitianConj_hermitianLebesgue` and
  `Matrix.UnitaryGroup.measurePreserving_hermitianConj_hermitianLebesgue` — unitary conjugation
  preserves `hermitianLebesgue p`.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate InnerProductSpace Matrix RealInnerProductSpace

namespace TauCeti

/-- Coordinate Lebesgue measure on the complex Hermitian subspace: the pushforward of product
Lebesgue measure in diagonal real and strictly upper-triangular real and imaginary coordinates. -/
def hermitianLebesgue (p : ℕ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (volume : Measure (Fin p × Fin p → ℝ)).map (hermitianCoordinates p).symm

/-- Reconstructing a Hermitian matrix from its real coordinates carries product Lebesgue measure
to `TauCeti.hermitianLebesgue`. -/
theorem measurePreserving_hermitianCoordinates_symm (p : ℕ) :
    MeasurePreserving (hermitianCoordinates p).symm volume (hermitianLebesgue p) :=
  ⟨(hermitianCoordinates p).symm.continuous.measurable, rfl⟩

/-- Reading off the real coordinates of a Hermitian matrix carries `TauCeti.hermitianLebesgue` to
product Lebesgue measure. -/
theorem measurePreserving_hermitianCoordinates (p : ℕ) :
    MeasurePreserving (hermitianCoordinates p) (hermitianLebesgue p) volume := by
  have h := measurePreserving_hermitianCoordinates_symm p
  rw [← hermitianCoordinatesMeasurableEquiv_symm_coe] at h
  have h' := h.symm (hermitianCoordinatesMeasurableEquiv p).symm
  rwa [MeasurableEquiv.symm_symm, hermitianCoordinatesMeasurableEquiv_coe] at h'

/-- `TauCeti.hermitianLebesgue` is an additive Haar measure. -/
instance hermitianLebesgueIsAddHaarMeasure (p : ℕ) :
    (hermitianLebesgue p).IsAddHaarMeasure :=
  ContinuousLinearEquiv.isAddHaarMeasure_map (hermitianCoordinates p).symm volume

/-! ### Orthonormal basis and comparison with the Frobenius volume -/

section comparison

private theorem hermitianLebesgue_eq_addHaar (p : ℕ) :
    hermitianLebesgue p = (hermitianBasis p).addHaar := by
  have hb : (Pi.basisFun ℝ (Fin p × Fin p)).map
      (hermitianCoordinates p).symm.toLinearEquiv = hermitianBasis p :=
    Basis.eq_of_apply_eq fun ab ↦ by simp [hermitianBasis_apply]
  rw [hermitianLebesgue, ← Module.Basis.addHaar_basisFun, Basis.map_addHaar, hb]

private theorem trace_single_mul (p : ℕ) (M : Matrix (Fin p) (Fin p) ℂ) (k l : Fin p) (z : ℂ) :
    (Matrix.single k l z * M).trace = z * M l k := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/-- Pairing any Hermitian matrix with `hermitianBasis p ab` extracts `hermitianCoordinates p A ab`,
doubled off the diagonal. -/
private theorem inner_hermitianBasis (p : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) (ab : Fin p × Fin p) :
    ⟪A, hermitianBasis p ab⟫ =
      (if ab.1 = ab.2 then 1 else 2) * hermitianCoordinates p A ab := by
  obtain ⟨i, j⟩ := ab
  rw [selfAdjoint.inner_eq_re_trace_mul]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [coe_hermitianBasis_of_lt p h, Matrix.add_mul, Matrix.trace_add, trace_single_mul,
      trace_single_mul, hermitianCoordinates_apply_of_le p A h.le, ite_eq_right h.ne,
      ← selfAdjoint.coe_apply_conj A i j]
    simp
    ring
  · rw [coe_hermitianBasis_diag p i, trace_single_mul, hermitianCoordinates_apply_self]
    simp
  · rw [coe_hermitianBasis_of_gt p h, Matrix.sub_mul, Matrix.trace_sub, trace_single_mul,
      trace_single_mul, hermitianCoordinates_apply_of_gt p A h, ite_eq_right h.ne',
      ← selfAdjoint.coe_apply_conj A j i]
    simp
    ring

private def hermScale (p : ℕ) (ab : Fin p × Fin p) : ℝˣ :=
  if ab.1 = ab.2 then 1 else Units.mk0 (Real.sqrt 2)⁻¹ (by positivity)

private theorem hermScale_coe (p : ℕ) (ab : Fin p × Fin p) :
    ((hermScale p ab : ℝˣ) : ℝ) = if ab.1 = ab.2 then 1 else (Real.sqrt 2)⁻¹ := by
  rw [hermScale]
  split <;> simp

private theorem orthonormal_hermScaled (p : ℕ) :
    Orthonormal ℝ ⇑((hermitianBasis p).unitsSMul (hermScale p)) := by
  rw [orthonormal_iff_ite]
  intro ab cd
  rw [Basis.unitsSMul_apply, Basis.unitsSMul_apply, Units.smul_def, Units.smul_def,
    real_inner_smul_left, real_inner_smul_right, inner_hermitianBasis,
    ← hermitianBasis_repr, Basis.repr_self, Finsupp.single_apply]
  by_cases h : ab = cd
  · subst h
    by_cases hd : ab.1 = ab.2
    · simp [hermScale_coe, hd]
    · simp only [hermScale_coe, hd, ↓reduceIte, mul_one]
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (by norm_num), inv_mul_cancel₀ two_ne_zero]
  · simp [h]

/-- The Frobenius-orthonormal basis of the complex Hermitian subspace obtained from
`TauCeti.hermitianBasis` by rescaling the `p * (p - 1)` off-diagonal basis vectors by `(√2)⁻¹`. -/
def hermitianOrthonormalBasis (p : ℕ) :
    OrthonormalBasis (Fin p × Fin p) ℝ
      (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  ((hermitianBasis p).unitsSMul (hermScale p)).toOrthonormalBasis (orthonormal_hermScaled p)

@[simp]
theorem coe_hermitianOrthonormalBasis_apply (p : ℕ) (ab : Fin p × Fin p) :
    (hermitianOrthonormalBasis p ab :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) =
      (if ab.1 = ab.2 then (1 : ℝ) else (Real.sqrt 2)⁻¹) • hermitianBasis p ab := by
  rw [hermitianOrthonormalBasis, Basis.coe_toOrthonormalBasis, Basis.unitsSMul_apply,
    Units.smul_def, hermScale_coe]

private theorem addHaar_hermScaled (p : ℕ) :
    ((hermitianBasis p).unitsSMul (hermScale p)).addHaar =
      (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) := by
  rw [← Basis.toBasis_toOrthonormalBasis _ (orthonormal_hermScaled p),
    OrthonormalBasis.addHaar_eq_volume]

private theorem card_hermitian_offDiag (p : ℕ) :
    ((Finset.univ.filter fun ab : Fin p × Fin p ↦ ab.1 ≠ ab.2).card : ℝ) =
      (p : ℝ) * ((p : ℝ) - 1) := by
  have hdiag : (Finset.univ.filter fun ab : Fin p × Fin p ↦ ab.1 = ab.2).card = p := by
    rw [show (Finset.univ.filter fun ab : Fin p × Fin p ↦ ab.1 = ab.2) =
      Finset.univ.image (fun i : Fin p ↦ (i, i)) by ext ⟨a, b⟩; simp [eq_comm],
      Finset.card_image_of_injective _ fun _ _ h ↦ (Prod.mk.inj h).1, Finset.card_fin]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin p × Fin p))) (fun ab ↦ ab.1 = ab.2)
  simp only [hdiag, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hsum
  linarith [show (p : ℝ) + ((Finset.univ.filter fun ab : Fin p × Fin p ↦ ab.1 ≠ ab.2).card : ℝ) =
    (p : ℝ) * p from mod_cast hsum]

private theorem prod_hermScale_inv (p : ℕ) :
    (((∏ ab, hermScale p ab)⁻¹ : ℝˣ) : ℝ) =
      Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 2) := by
  set N : ℕ := (Finset.univ.filter fun ab : Fin p × Fin p ↦ ab.1 ≠ ab.2).card with hN
  have hprod : ((∏ ab, hermScale p ab : ℝˣ) : ℝ) = (Real.sqrt 2)⁻¹ ^ N := by
    rw [← Units.coeHom_apply, map_prod]
    simp only [Units.coeHom_apply, hermScale_coe]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [Units.val_inv_eq_inv_val, hprod, inv_pow, inv_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast ((2 : ℝ) ^ (1 / 2 : ℝ)) N, ← Real.rpow_mul (by norm_num)]
  congr 1; rw [hN, card_hermitian_offDiag]; ring

private theorem volume_parallelepiped_hermitianBasis (p : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)))
        (hermitianBasis p).parallelepiped =
      ENNReal.ofReal (Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 2)) := by
  rw [Basis.coe_parallelepiped, ← addHaar_hermScaled p, Measure.addHaar_parallelepiped,
    Basis.det_unitsSMul]
  simp only [_root_.smul_apply, Basis.det_self, smul_eq_mul, mul_one, prod_hermScale_inv]
  exact congrArg ENNReal.ofReal (abs_of_nonneg (Real.rpow_nonneg (by norm_num) _))

end comparison

/-- The Frobenius volume of the complex Hermitian subspace is `2 ^ (p * (p - 1) / 2)` times
`TauCeti.hermitianLebesgue`: each of the `p * (p - 1)` off-diagonal real coordinate directions
`Eᵢⱼ + Eⱼᵢ` and `I • Eᵢⱼ - I • Eⱼᵢ` (`i < j`) has Frobenius norm `√2`. -/
theorem volume_hermitianMatrix_eq_smul_hermitianLebesgue (p : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) =
      ENNReal.ofReal (Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 2)) • hermitianLebesgue p := by
  rw [hermitianLebesgue_eq_addHaar, Basis.addHaar_def, ← volume_parallelepiped_hermitianBasis]
  exact Measure.addHaarMeasure_unique _ _

/-- In dimension zero, `TauCeti.hermitianLebesgue` is the Dirac measure at `0`. -/
theorem hermitianLebesgue_zero : hermitianLebesgue 0 = Measure.dirac 0 := by
  have : IsEmpty (Fin 0 × Fin 0) := ⟨fun ab ↦ ab.1.elim0⟩
  rw [hermitianLebesgue, volume_pi, Measure.pi_of_empty _ 0, Measure.map_dirac, map_zero]

/-- In dimension one, reading the real part of the single entry carries `hermitianLebesgue 1` to
Lebesgue measure on `ℝ`. -/
theorem measurePreserving_hermitianFinOneEquiv :
    MeasurePreserving hermitianFinOneEquiv (hermitianLebesgue 1) volume := by
  let _ : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have h : (hermitianFinOneEquiv : _ → ℝ) =
      MeasurableEquiv.funUnique (Fin 1 × Fin 1) ℝ ∘ hermitianCoordinates 1 := by
    funext A
    simp [MeasurableEquiv.funUnique, Subsingleton.elim (default : Fin 1 × Fin 1) (0, 0)]
  rw [h]
  exact (volume_preserving_funUnique _ ℝ).comp (measurePreserving_hermitianCoordinates 1)

end TauCeti

namespace Matrix.UnitaryGroup

open TauCeti

variable {p : ℕ}

/-- Unitary conjugation pushes `TauCeti.hermitianLebesgue` forward to itself. -/
@[simp]
theorem map_hermitianConj_hermitianLebesgue (U : Matrix.unitaryGroup (Fin p) ℂ) :
    (hermitianLebesgue p).map (hermitianConj U) = hermitianLebesgue p := by
  have hvol := (hermitianConj U).measurePreserving.map_eq
  rw [volume_hermitianMatrix_eq_smul_hermitianLebesgue p,
    Measure.map_smul _ (hermitianConj U).continuous.aemeasurable] at hvol
  set c : ENNReal := ENNReal.ofReal (Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 2))
  have hc : c⁻¹ * c = 1 := ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos two_pos _)).ne' ENNReal.ofReal_ne_top
  simpa [smul_smul, hc] using congrArg (c⁻¹ • ·) hvol

/-- Unitary conjugation preserves `TauCeti.hermitianLebesgue`. -/
theorem measurePreserving_hermitianConj_hermitianLebesgue (U : Matrix.unitaryGroup (Fin p) ℂ) :
    MeasurePreserving (hermitianConj U) (hermitianLebesgue p) (hermitianLebesgue p) :=
  ⟨(hermitianConj U).continuous.measurable, map_hermitianConj_hermitianLebesgue U⟩

end Matrix.UnitaryGroup
