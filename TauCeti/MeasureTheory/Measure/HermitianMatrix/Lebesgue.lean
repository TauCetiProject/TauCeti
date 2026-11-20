/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Normalize
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lebesgue measure on the complex Hermitian subspace

`TauCeti.hermitianLebesgue p` is the pushforward of product Lebesgue measure on `Fin p × Fin p → ℝ`
along `(TauCeti.hermitianCoordinates p).symm`: product Lebesgue measure in `(A i i).re` and the
`p * (p - 1)` off-diagonal coordinates `(A i j).re`, `(A i j).im` (`i < j`). Because each
off-diagonal basis direction has Frobenius norm `√2`, trace-inner-product `volume` is
`2 ^ (p * (p - 1) / 2)` times `hermitianLebesgue p`, and unitary conjugation preserves both.

## Main declarations

* `TauCeti.hermitianLebesgue`, `TauCeti.hermitianLebesgueIsAddHaarMeasure`,
  `TauCeti.measurePreserving_hermitianCoordinates_symm`,
  `TauCeti.measurePreserving_hermitianCoordinates`.
* `TauCeti.hermitianOrthonormalBasis`, `TauCeti.volume_hermitianMatrix_eq_smul_hermitianLebesgue`,
  `TauCeti.hermitianLebesgue_eq_smul_volume`, `TauCeti.hermitianLebesgue_zero`,
  `TauCeti.measurePreserving_hermitianFinOneEquiv`.
* `Matrix.UnitaryGroup.measurePreserving_hermitianConj_volume`,
  `Matrix.UnitaryGroup.measurePreserving_hermitianConj_hermitianLebesgue`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, §2.5.1.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate ENNReal RealInnerProductSpace

namespace TauCeti

/-- Coordinate Lebesgue measure on the complex Hermitian subspace: the pushforward of product
Lebesgue measure along `(TauCeti.hermitianCoordinates p).symm`. -/
def hermitianLebesgue (p : ℕ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (volume : Measure (Fin p × Fin p → ℝ)).map (hermitianCoordinates p).symm

/-- Defining formula for `TauCeti.hermitianLebesgue`. -/
theorem hermitianLebesgue_def (p : ℕ) :
    hermitianLebesgue p =
      (volume : Measure (Fin p × Fin p → ℝ)).map (hermitianCoordinates p).symm := (rfl)

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
instance hermitianLebesgueIsAddHaarMeasure (p : ℕ) : (hermitianLebesgue p).IsAddHaarMeasure :=
  ContinuousLinearEquiv.isAddHaarMeasure_map (hermitianCoordinates p).symm volume

section comparison

private theorem hermitianLebesgue_eq_addHaar (p : ℕ) :
    hermitianLebesgue p = (hermitianBasis p).addHaar := by
  have hb : (Pi.basisFun ℝ (Fin p × Fin p)).map (hermitianCoordinates p).symm.toLinearEquiv =
      hermitianBasis p :=
    Basis.eq_of_apply_eq fun ij ↦ by simp [hermitianBasis_apply]
  rw [hermitianLebesgue, ← Module.Basis.addHaar_basisFun, Basis.map_addHaar, hb]

/-- Pairing `A` with `hermitianBasis p kl` gives its `kl` coordinate, doubled off the diagonal. -/
theorem inner_hermitianBasis (p : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) (kl : Fin p × Fin p) :
    ⟪A, hermitianBasis p kl⟫ =
      (if kl.1 = kl.2 then 1 else 2) * hermitianCoordinates p A kl := by
  obtain ⟨k, l⟩ := kl; rw [selfAdjoint.inner_eq_re_trace_mul]
  rcases lt_trichotomy k l with h | rfl | h
  · rw [coe_hermitianBasis_of_lt p h, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul,
      Matrix.trace_single_mul, one_smul, one_smul, ← selfAdjoint.conj_coe_apply A l k,
      hermitianCoordinates_apply_of_le p A h.le]
    simp only [h.ne, ↓reduceIte, Complex.add_re, Complex.conj_re]; ring
  · rw [coe_hermitianBasis_diag, Matrix.trace_single_mul, one_smul,
      hermitianCoordinates_apply_of_le p A le_rfl]; simp
  · rw [coe_hermitianBasis_of_gt p h, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_single_mul,
      Matrix.trace_single_mul, ← selfAdjoint.conj_coe_apply A k l,
      hermitianCoordinates_apply_of_gt p A h]
    simp only [h.ne', ↓reduceIte, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.conj_im]; ring

/-- The coordinate basis vectors of `TauCeti.hermitianBasis` are pairwise orthogonal in the
real Frobenius inner product. -/
theorem pairwise_inner_hermitianBasis (p : ℕ) :
    Pairwise fun ij kl ↦ ⟪hermitianBasis p ij, hermitianBasis p kl⟫ = 0 := by
  intro ij kl hne
  rw [inner_hermitianBasis, hermitianBasis_apply, ContinuousLinearEquiv.apply_symm_apply,
    Pi.single_apply, ite_eq_right hne.symm, mul_zero]

/-- Each vector of `TauCeti.hermitianBasis` has Frobenius norm `1` on the diagonal and `√2` off
it. -/
theorem norm_hermitianBasis (p : ℕ) (ij : Fin p × Fin p) :
    ‖hermitianBasis p ij‖ = if ij.1 = ij.2 then 1 else Real.sqrt 2 := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_hermitianBasis,
    hermitianBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  split_ifs <;> simp

/-- The orthonormal basis of the complex Hermitian subspace obtained by rescaling the off-diagonal
vectors of `TauCeti.hermitianBasis` by `(√2)⁻¹`. -/
def hermitianOrthonormalBasis (p : ℕ) :
    OrthonormalBasis (Fin p × Fin p) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (hermitianBasis p).toOrthonormalBasisOfOrthogonal (pairwise_inner_hermitianBasis p)

/-- Each vector of `TauCeti.hermitianOrthonormalBasis` rescales `TauCeti.hermitianBasis` by `1` on
the diagonal and `(√2)⁻¹` off the diagonal. -/
theorem hermitianOrthonormalBasis_apply (p : ℕ) (ij : Fin p × Fin p) :
    hermitianOrthonormalBasis p ij =
      (if ij.1 = ij.2 then (1 : ℝ) else (Real.sqrt 2)⁻¹) • hermitianBasis p ij := by
  rw [hermitianOrthonormalBasis, Basis.toOrthonormalBasisOfOrthogonal_apply, norm_hermitianBasis]
  split_ifs <;> simp

/-- Coordinates in `TauCeti.hermitianOrthonormalBasis` rescale off-diagonal coordinates by `√2`. -/
@[simp] theorem hermitianOrthonormalBasis_repr (p : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) (ij : Fin p × Fin p) :
    (hermitianOrthonormalBasis p).repr A ij =
      (if ij.1 = ij.2 then 1 else Real.sqrt 2) * hermitianCoordinates p A ij := by
  rw [hermitianOrthonormalBasis, Basis.toOrthonormalBasisOfOrthogonal_repr_apply,
    norm_hermitianBasis, hermitianBasis_repr, RCLike.ofReal_real_eq_id, id_eq]

private theorem card_hermOffDiag (p : ℕ) :
    ((Finset.univ.filter fun ij : Fin p × Fin p ↦ ij.1 ≠ ij.2).card : ℝ) =
      (p : ℝ) * ((p : ℝ) - 1) := by
  have hoff : (Finset.univ.filter fun ij : Fin p × Fin p ↦ ij.1 ≠ ij.2) =
      (Finset.univ : Finset (Fin p)).offDiag := by
    ext; simp [Finset.mem_offDiag]
  rw [hoff, Finset.offDiag_card, Finset.card_fin, Nat.cast_sub (Nat.le_mul_self p), Nat.cast_mul]
  ring

end comparison

/-- The trace-inner-product `volume` on the complex Hermitian subspace is
`2 ^ (p * (p - 1) / 2)` times `hermitianLebesgue p`. -/
theorem volume_hermitianMatrix_eq_smul_hermitianLebesgue (p : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) =
      ENNReal.ofReal ((2 : ℝ) ^ (((p : ℝ) * ((p : ℝ) - 1)) / 2)) • hermitianLebesgue p := by
  rw [hermitianLebesgue_eq_addHaar,
    (hermitianBasis p).volume_eq_smul_addHaar_of_pairwise_inner_eq_zero
      (pairwise_inner_hermitianBasis p)]
  congr 2
  simp_rw [norm_hermitianBasis]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), card_hermOffDiag]
  exact congrArg _ (by ring)

/-- Conversely, `hermitianLebesgue p` is `2 ^ (-(p * (p - 1) / 2))` times `volume`. -/
theorem hermitianLebesgue_eq_smul_volume (p : ℕ) :
    hermitianLebesgue p =
      ENNReal.ofReal ((2 : ℝ) ^ (-(((p : ℝ) * ((p : ℝ) - 1)) / 2))) •
        (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) := by
  rw [volume_hermitianMatrix_eq_smul_hermitianLebesgue, smul_smul,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    ← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_smul]

/-- In dimension zero, `hermitianLebesgue` is the Dirac mass at zero. -/
theorem hermitianLebesgue_zero : hermitianLebesgue 0 = Measure.dirac 0 := by
  rw [hermitianLebesgue_eq_addHaar, Module.Basis.addHaar_eq_dirac]

/-- In dimension one, `hermitianFinOneEquiv` carries `hermitianLebesgue 1` to `volume` on `ℝ`. -/
theorem measurePreserving_hermitianFinOneEquiv :
    MeasurePreserving hermitianFinOneEquiv (hermitianLebesgue 1) volume := by
  let : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have hcomp : ⇑hermitianFinOneEquiv =
      ⇑(MeasurableEquiv.funUnique (Fin 1 × Fin 1) ℝ) ∘ ⇑(hermitianCoordinates 1) :=
    funext fun A ↦ by
      simp [Subsingleton.elim default ((0, 0) : Fin 1 × Fin 1)]
  rw [hcomp]
  exact (volume_preserving_funUnique (Fin 1 × Fin 1) ℝ).comp
    (measurePreserving_hermitianCoordinates 1)

end TauCeti

namespace Matrix.UnitaryGroup
open TauCeti

/-- Unitary conjugation preserves `volume` on the complex Hermitian subspace. -/
theorem measurePreserving_hermitianConj_volume {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ) :
    MeasurePreserving (hermitianConj U) volume volume := measurePreserving_selfAdjointConj_volume U

/-- Unitary conjugation preserves coordinate Lebesgue measure `TauCeti.hermitianLebesgue`. -/
theorem measurePreserving_hermitianConj_hermitianLebesgue {p : ℕ}
    (U : Matrix.unitaryGroup (Fin p) ℂ) :
    MeasurePreserving (hermitianConj U) (hermitianLebesgue p) (hermitianLebesgue p) := by
  rw [hermitianLebesgue_eq_smul_volume]
  exact (measurePreserving_hermitianConj_volume U).smul_measure _

end Matrix.UnitaryGroup
