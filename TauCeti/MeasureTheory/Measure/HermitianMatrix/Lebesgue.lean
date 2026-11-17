/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Normalize
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Lebesgue measure on the complex Hermitian subspace

`TauCeti.hermitianLebesgue n` is the pushforward of product Lebesgue measure on the `n ^ 2` real
coordinates (diagonal entries and strictly upper-triangular real and imaginary parts) along
`(TauCeti.hermitianCoordinates n).symm`.

The Frobenius volume of `measureSpaceOfInnerProductSpace` is a Haar measure for the same topology
with a different normalization: each of the `n * (n - 1)` off-diagonal coordinate basis vectors
has Frobenius norm `√2`, so Frobenius volume is `2 ^ (n * (n - 1) / 2)` times
`TauCeti.hermitianLebesgue n`. Unitary conjugation `Matrix.UnitaryGroup.selfAdjointConj U` is a
Frobenius isometry, so `Matrix.UnitaryGroup.measurePreserving_selfAdjointConj` directly gives
invariance of both Frobenius volume and `TauCeti.hermitianLebesgue n`.

## Main declarations

* `TauCeti.hermitianLebesgue` — Lebesgue measure on the complex Hermitian subspace, normalized by
  the diagonal and upper-triangular real/imaginary coordinates.
* `TauCeti.measurePreserving_hermitianCoordinates_symm` and
  `TauCeti.measurePreserving_hermitianCoordinates` — the coordinate equivalence preserves
  `hermitianLebesgue` and product Lebesgue measure.
* `TauCeti.hermitianLebesgueIsAddHaarMeasure` — `hermitianLebesgue n` is an additive Haar measure.
* `TauCeti.pairwise_inner_hermitianBasis` and `TauCeti.norm_hermitianBasis` — orthogonality and
  Frobenius norms of `TauCeti.hermitianBasis`.
* `TauCeti.hermitianOrthonormalBasis` — the Frobenius-orthonormal basis obtained by rescaling
  off-diagonal vectors of `TauCeti.hermitianBasis` by `(√2)⁻¹`, with coordinate lemma
  `TauCeti.hermitianOrthonormalBasis_repr_apply`.
* `TauCeti.volume_hermitianMatrix_eq_smul_hermitianLebesgue` — comparison with Frobenius volume.
* `TauCeti.hermitianLebesgue_zero` — in dimension zero, `hermitianLebesgue` is the Dirac measure.
* `TauCeti.measurePreserving_hermitianFinOneEquiv` — in dimension one, `hermitianFinOneEquiv`
  carries `hermitianLebesgue 1` to Lebesgue measure on `ℝ`.

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
  rw [selfAdjoint.inner_eq_re_trace_mul, RCLike.re_to_complex]
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

/-- The coordinate basis vectors of `TauCeti.hermitianBasis` are pairwise orthogonal in the real
Frobenius inner product. -/
theorem pairwise_inner_hermitianBasis (n : ℕ) :
    Pairwise fun p q ↦ ⟪hermitianBasis n p, hermitianBasis n q⟫ = 0 := by
  intro p q hpq
  rw [inner_hermitianBasis_eq, hermitianBasis_apply, ContinuousLinearEquiv.apply_symm_apply,
    Pi.single_eq_of_ne hpq.symm, mul_zero]

/-- Each vector of `TauCeti.hermitianBasis` has Frobenius norm `1` on the diagonal and `√2` off
it. -/
theorem norm_hermitianBasis (n : ℕ) (p : Fin n × Fin n) :
    ‖hermitianBasis n p‖ = if p.1 = p.2 then 1 else Real.sqrt 2 := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_hermitianBasis_eq,
    hermitianBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  split_ifs <;> simp

/-- The Frobenius-orthonormal basis of the complex Hermitian subspace obtained by rescaling the
off-diagonal vectors of `TauCeti.hermitianBasis` by `(√2)⁻¹`. -/
def hermitianOrthonormalBasis (n : ℕ) :
    OrthonormalBasis (Fin n × Fin n) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  (hermitianBasis n).toOrthonormalBasisOfOrthogonal (pairwise_inner_hermitianBasis n)

/-- Each vector of `TauCeti.hermitianOrthonormalBasis` is `hermitianBasis` on the diagonal and
`(√2)⁻¹ • hermitianBasis` off it. -/
theorem hermitianOrthonormalBasis_apply (n : ℕ) (p : Fin n × Fin n) :
    hermitianOrthonormalBasis n p =
      if p.1 = p.2 then hermitianBasis n p else (Real.sqrt 2)⁻¹ • hermitianBasis n p := by
  rw [hermitianOrthonormalBasis, Basis.toOrthonormalBasisOfOrthogonal_apply, norm_hermitianBasis]
  split_ifs <;> simp

/-- The `p`-th coordinate of `A` in `TauCeti.hermitianOrthonormalBasis` is
`hermitianCoordinates n A p` on the diagonal and `√2 * hermitianCoordinates n A p` off it. -/
@[simp]
theorem hermitianOrthonormalBasis_repr_apply (n : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (p : Fin n × Fin n) :
    (hermitianOrthonormalBasis n).repr A p =
      (if p.1 = p.2 then 1 else Real.sqrt 2) * hermitianCoordinates n A p := by
  rw [hermitianOrthonormalBasis, Basis.toOrthonormalBasisOfOrthogonal_repr_apply,
    norm_hermitianBasis, hermitianBasis_repr, RCLike.ofReal_real_eq_id, id_eq]

private theorem card_offDiag_fin_prod (n : ℕ) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2).card = n * (n - 1) := by
  have h : (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2) =
      (Finset.univ : Finset (Fin n)).offDiag := by
    ext ⟨i, j⟩
    simp
  rw [h, Finset.offDiag_card, Finset.card_fin, Nat.mul_sub_left_distrib, mul_one]

end comparison

/-- The Frobenius volume of the complex Hermitian subspace is `2 ^ (n * (n - 1) / 2)` times
`TauCeti.hermitianLebesgue n`: each of the `n * (n - 1)` off-diagonal coordinate directions has
Frobenius norm `√2`. -/
theorem volume_hermitianMatrix_eq_smul_hermitianLebesgue (n : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) =
      ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2)) • hermitianLebesgue n := by
  rw [hermitianLebesgue_eq_addHaar,
    (hermitianBasis n).volume_eq_smul_addHaar_of_pairwise_inner_eq_zero
      (pairwise_inner_hermitianBasis n)]
  congr 2
  simp_rw [norm_hermitianBasis]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, card_offDiag_fin_prod]
  conv_lhs =>
    rw [← Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd, pow_mul,
      Real.sq_sqrt (by norm_num)]

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
