/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

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

/-- Pairing any Hermitian matrix with `hermitianBasis p ab` extracts `hermitianCoordinates p A ab`,
doubled off the diagonal. -/
private theorem inner_hermitianBasis (p : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) (ab : Fin p × Fin p) :
    ⟪A, hermitianBasis p ab⟫ =
      (if ab.1 = ab.2 then 1 else 2) * hermitianCoordinates p A ab := by
  obtain ⟨i, j⟩ := ab
  rw [selfAdjoint.inner_eq_re_trace_mul]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [coe_hermitianBasis_of_lt p h, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul,
      Matrix.trace_single_mul, smul_eq_mul, smul_eq_mul,
      hermitianCoordinates_apply_of_le p A h.le, ite_eq_right h.ne,
      ← selfAdjoint.coe_apply_conj A i j]
    simp
    ring
  · rw [coe_hermitianBasis_diag p i, Matrix.trace_single_mul, smul_eq_mul,
      hermitianCoordinates_apply_self]
    simp
  · rw [coe_hermitianBasis_of_gt p h, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_single_mul,
      Matrix.trace_single_mul, smul_eq_mul, smul_eq_mul,
      hermitianCoordinates_apply_of_gt p A h, ite_eq_right h.ne',
      ← selfAdjoint.coe_apply_conj A j i]
    simp
    ring

private theorem inner_hermitianBasis_self (p : ℕ) (ab cd : Fin p × Fin p) :
    ⟪hermitianBasis p ab, hermitianBasis p cd⟫ =
      if ab = cd then (if ab.1 = ab.2 then 1 else 2) else 0 := by
  rw [inner_hermitianBasis, ← hermitianBasis_repr, Basis.repr_self, Finsupp.single_apply]
  by_cases h : ab = cd
  · subst h; simp
  · simp [h]

/-- The Frobenius-orthonormal basis of the complex Hermitian subspace obtained from
`TauCeti.hermitianBasis` by rescaling the `p * (p - 1)` off-diagonal basis vectors by `(√2)⁻¹`. -/
def hermitianOrthonormalBasis (p : ℕ) :
    OrthonormalBasis (Fin p × Fin p) ℝ
      (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  ((hermitianBasis p).unitsSMul fun ab ↦
      if ab.1 = ab.2 then 1 else Units.mk0 (Real.sqrt 2)⁻¹ (by positivity)).toOrthonormalBasis <| by
    rw [orthonormal_iff_ite]
    intro ab cd
    rw [Basis.unitsSMul_apply, Basis.unitsSMul_apply, Units.smul_def, Units.smul_def,
      real_inner_smul_left, real_inner_smul_right, inner_hermitianBasis_self]
    by_cases h : ab = cd
    · subst h
      by_cases hd : ab.1 = ab.2
      · simp [hd]
      · simp only [hd, ↓reduceIte, Units.val_mk0]
        rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (by norm_num), inv_mul_cancel₀ two_ne_zero]
    · simp [h]

@[simp]
theorem coe_hermitianOrthonormalBasis_apply (p : ℕ) (ab : Fin p × Fin p) :
    (hermitianOrthonormalBasis p ab :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) =
      (if ab.1 = ab.2 then (1 : ℝ) else (Real.sqrt 2)⁻¹) • hermitianBasis p ab := by
  rw [hermitianOrthonormalBasis, Basis.coe_toOrthonormalBasis, Basis.unitsSMul_apply,
    Units.smul_def]
  split_ifs <;> simp

end comparison

/-- The Frobenius volume of the complex Hermitian subspace is `2 ^ (p * (p - 1) / 2)` times
`TauCeti.hermitianLebesgue`: each of the `p * (p - 1)` off-diagonal real coordinate directions
`Eᵢⱼ + Eⱼᵢ` and `I • Eᵢⱼ - I • Eⱼᵢ` (`i < j`) has Frobenius norm `√2`. -/
theorem volume_hermitianMatrix_eq_smul_hermitianLebesgue (p : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) =
      ENNReal.ofReal (Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 2)) • hermitianLebesgue p := by
  rw [hermitianLebesgue_eq_addHaar, (hermitianBasis p).volume_eq_smul_addHaar]
  congr 2
  have hgram : Matrix.gram ℝ (hermitianBasis p) =
      Matrix.diagonal fun ab : Fin p × Fin p ↦ if ab.1 = ab.2 then (1 : ℝ) else 2 := by
    ext ab cd
    simp only [Matrix.gram_apply, Matrix.diagonal_apply, inner_hermitianBasis_self]
  rw [hgram, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const]
  have hcard : ((Finset.univ.filter fun ab : Fin p × Fin p ↦ ¬ab.1 = ab.2).card : ℝ) =
      (p : ℝ) * ((p : ℝ) - 1) := by
    have hfilt : (Finset.univ.filter fun ab : Fin p × Fin p ↦ ¬ab.1 = ab.2) =
        (Finset.univ : Finset (Fin p)).offDiag := by
      ext ⟨a, b⟩; simp
    rw [hfilt, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.le_mul_self p), Nat.cast_mul]
    ring
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hcard,
    Real.rpow_eq_pow]
  congr 1; ring

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
    (hermitianLebesgue p).map (hermitianConj U) = hermitianLebesgue p :=
  (hermitianConj U).map_addHaar (hermitianLebesgue p)

/-- Unitary conjugation preserves `TauCeti.hermitianLebesgue`. -/
theorem measurePreserving_hermitianConj_hermitianLebesgue (U : Matrix.unitaryGroup (Fin p) ℂ) :
    MeasurePreserving (hermitianConj U) (hermitianLebesgue p) (hermitianLebesgue p) :=
  (hermitianConj U).measurePreserving_addHaar (hermitianLebesgue p)

end Matrix.UnitaryGroup
