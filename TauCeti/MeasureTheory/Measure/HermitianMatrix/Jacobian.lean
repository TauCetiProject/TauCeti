/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Hermitian.Congruence
public import TauCeti.MeasureTheory.Measure.Haar.Matrix.Complex
public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Lebesgue
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.MeasureTheory.Integral.Dilation
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Lebesgue Jacobians on complex and Hermitian matrices

This file computes two Jacobians for Lebesgue measure on complex Hermitian matrices, part of the
bookkeeping behind the polar formula for the Gram map `Y ↦ Yᴴ J Y`; the third, for two-sided
multiplication `Y ↦ P * Y * Q` of complex matrices, is
`MeasureTheory.lintegral_eq_enorm_det_pow_mul_enorm_det_pow_mul_lintegral_comp_matrix_mul_mul`
in `TauCeti.MeasureTheory.Measure.Haar.Matrix.Complex`. Complex matrices carry the product
Lebesgue measure `dZ` of the real and imaginary parts of their entries, and the Hermitian
matrices of size `p` carry `TauCeti.hermitianLebesgue p`, the product of the Lebesgue measures of
the entries on and above the diagonal.

* `MeasureTheory.lintegral_comp_selfAdjointConjugate`: for invertible `C`, the congruence
  `T ↦ C * T * Cᴴ` of Hermitian `n × n` matrices has Jacobian `|det C| ^ (2 n)`, for every
  additive Haar measure, and
  `MeasureTheory.lintegral_eq_enorm_det_pow_mul_lintegral_comp_selfAdjointConjugate_conjTranspose`
  states it in the form `∫⁻ T, g T = ‖C.det‖ₑ ^ (2 n) * ∫⁻ T, g (Cᴴ * T * C)`.
* `TauCeti.lintegral_eq_lintegral_hermitianLebesgue_I_smul_add`: writing a square complex matrix
  of size `p` as `Z = i S + T / 2`, with `S` and `T` Hermitian, so that `i S` is its
  skew-Hermitian and `T / 2` its Hermitian part, Lebesgue measure is `dZ = 2 ^ (-p) dS dT`.

The first is a linear change of variables with the determinant
`Matrix.det_selfAdjointConjugate_complex`. For the second, the real trace form
`Re tr(Xᴴ Y)` is the dot product of the real coordinates of the entries, and for Hermitian `S`,
`S'`, `T`, `T'` it gives `⟪i S + T, i S' + T'⟫ = ⟪S, S'⟫ + ⟪T, T'⟫`, since `tr(S T')` is real.
So `(S, T) ↦ i S + T` carries a product of orthonormal bases of the Hermitian matrices to a
family whose coordinate matrix is orthogonal, and it carries the product of the trace-form
volumes to `dZ`. The comparison `TauCeti.volume_hermitianMatrix_eq_smul_hermitianLebesgue` of
the trace-form volume with `hermitianLebesgue p` and the dilation `T ↦ T / 2` give the constant.

## Provenance

The two statements are adapted from `New.lintegral_eq_det_mul_comp_congruence` and
`New.lintegral_eq_skewOfReal_add_hermOfReal` in
`src/Lib/DiscreteSeries/Haar/GramCoordinates.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). There they are
stated in real coordinates `hermOfReal`, `skewOfReal` of their own; here they use the Hermitian
submodule with `TauCeti.hermitianLebesgue`, and the second is proved through orthonormal bases
rather than through the explicit scaling of entries used there.
-/

public section

noncomputable section

open MeasureTheory Module Complex
open scoped Matrix ComplexConjugate ENNReal RealInnerProductSpace

namespace MeasureTheory

/-- **Change of variables for the congruence of Hermitian matrices**: for an invertible complex
matrix `C` and an additive Haar measure `μ` on the Hermitian matrices of size `p`, the
substitution `T ↦ C * T * Cᴴ` has the real Jacobian `|det C| ^ (2 p)`. -/
theorem lintegral_comp_selfAdjointConjugate {p : ℕ}
    (μ : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) [μ.IsAddHaarMeasure]
    {C : Matrix (Fin p) (Fin p) ℂ} (hC : C.det ≠ 0)
    (g : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) → ℝ≥0∞) :
    ∫⁻ T, g (Matrix.selfAdjointConjugate ℝ C T) ∂μ =
      ENNReal.ofReal ((‖C.det‖ ^ (2 * p))⁻¹) * ∫⁻ T, g T ∂μ := by
  have h_det : LinearMap.det (Matrix.selfAdjointConjugate ℝ C) = ‖C.det‖ ^ (2 * p) := by
    rw [Matrix.det_selfAdjointConjugate_complex, Complex.normSq_eq_norm_sq, Fintype.card_fin,
      pow_mul]
  have h_pos : 0 < ‖C.det‖ ^ (2 * p) := pow_pos (norm_pos_iff.2 hC) _
  rw [lintegral_comp_linearMap μ (h_det.trans_ne h_pos.ne') g, h_det,
    abs_of_pos (inv_pos.2 h_pos)]

/-- **Change of variables for the congruence of Hermitian matrices**, in the form
`∫⁻ T, G T = |det C| ^ (2 p) * ∫⁻ T, G (Cᴴ * T * C)` for an invertible complex matrix `C` and
an additive Haar measure on the Hermitian matrices of size `p`. -/
theorem lintegral_eq_enorm_det_pow_mul_lintegral_comp_selfAdjointConjugate_conjTranspose {p : ℕ}
    (μ : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) [μ.IsAddHaarMeasure]
    {C : Matrix (Fin p) (Fin p) ℂ} (hC : C.det ≠ 0)
    (g : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) → ℝ≥0∞) :
    ∫⁻ T, g T ∂μ = ‖C.det‖ₑ ^ (2 * p) *
      ∫⁻ T, g (Matrix.selfAdjointConjugate ℝ Cᴴ T) ∂μ := by
  have hC' : Cᴴ.det ≠ 0 := by rwa [Matrix.det_conjTranspose, star_ne_zero]
  -- The Jacobian cancels against the inverse factor of `lintegral_comp_selfAdjointConjugate`.
  rw [lintegral_comp_selfAdjointConjugate μ hC', Matrix.det_conjTranspose, norm_star, ← mul_assoc,
    ENNReal.ofReal_inv_of_pos (pow_pos (norm_pos_iff.2 hC) _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
    ENNReal.mul_inv_cancel (by simp [hC]) (by simp), one_mul]

end MeasureTheory

namespace TauCeti

/-! ### Skew-Hermitian and Hermitian parts -/

section Decomposition

variable {p : ℕ}

/-- The real basis of `Fin p → Fin p → ℂ` given by the real and imaginary parts of the entries. -/
private def entryBasis (p : ℕ) :
    Module.Basis (Σ _ : Fin p, Σ _ : Fin p, Fin 2) ℝ (Fin p → Fin p → ℂ) :=
  Pi.basis fun _ ↦ Pi.basis fun _ ↦ Complex.basisOneI

private theorem entryBasis_repr (Z : Fin p → Fin p → ℂ) (σ : Σ _ : Fin p, Σ _ : Fin p, Fin 2) :
    (entryBasis p).repr Z σ = ![(Z σ.1 σ.2.1).re, (Z σ.1 σ.2.1).im] σ.2.2 := by
  simp [entryBasis]

/-- The dot product of the coordinates of `entryBasis` is the real trace form. -/
private theorem sum_entryBasis_repr_mul (X Y : Fin p → Fin p → ℂ) :
    ∑ σ, (entryBasis p).repr X σ * (entryBasis p).repr Y σ =
      ∑ i, ∑ j, (conj (X i j) * Y i j).re := by
  simp only [Fintype.sum_sigma, entryBasis_repr, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The product Lebesgue measure on `Fin p → Fin p → ℂ` is the Haar measure of `entryBasis`. -/
private theorem entryBasis_addHaar :
    (entryBasis p).addHaar = (volume : Measure (Fin p → Fin p → ℂ)) := by
  simp only [entryBasis, Module.Basis.addHaar_pi, Complex.addHaar_basisOneI, volume_pi]

/-- The real trace form of `i S + T` and `i S' + T'`, for Hermitian `S`, `T`, `S'`, `T'`, is
`⟪S, S'⟫ + ⟪T, T'⟫`: the cross terms vanish because the trace of a product of Hermitian matrices
is real. -/
private theorem sum_re_conj_mul_I_smul_add
    (S T S' T' : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ∑ i, ∑ j, (conj ((I • (S : Matrix (Fin p) (Fin p) ℂ) + T) i j) *
      (I • (S' : Matrix (Fin p) (Fin p) ℂ) + T') i j).re = ⟪S, S'⟫ + ⟪T, T'⟫ := by
  have h (i j : Fin p) : (conj ((I • (S : Matrix (Fin p) (Fin p) ℂ) + T) i j) *
      (I • (S' : Matrix (Fin p) (Fin p) ℂ) + T') i j).re =
      (conj ((S : Matrix (Fin p) (Fin p) ℂ) i j) * (S' : Matrix (Fin p) (Fin p) ℂ) i j).re +
      (conj ((T : Matrix (Fin p) (Fin p) ℂ) i j) * (T' : Matrix (Fin p) (Fin p) ℂ) i j).re +
      (conj ((S : Matrix (Fin p) (Fin p) ℂ) i j) * (T' : Matrix (Fin p) (Fin p) ℂ) i j).im -
      (conj ((T : Matrix (Fin p) (Fin p) ℂ) i j) * (S' : Matrix (Fin p) (Fin p) ℂ) i j).im := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_I,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Complex.re_sum,
    ← Complex.im_sum, selfAdjoint.sum_conj_mul_eq_trace, selfAdjoint.im_trace_mul, sub_zero,
    add_zero,
    selfAdjoint.inner_eq_re_trace_mul]
  rw [Matrix.trace_mul_comm (S : Matrix (Fin p) (Fin p) ℂ),
    Matrix.trace_mul_comm (T : Matrix (Fin p) (Fin p) ℂ)]

variable (p) in
/-- The real linear map `(S, T) ↦ i S + T` from pairs of Hermitian matrices to complex arrays. -/
private def iSMulAdd :
    (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) →ₗ[ℝ] (Fin p → Fin p → ℂ) where
  toFun x :=
    Matrix.of.symm (I • (x.1 : Matrix (Fin p) (Fin p) ℂ) + (x.2 : Matrix (Fin p) (Fin p) ℂ))
  map_add' x y := by
    ext i j
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add, Matrix.of_symm_apply,
      Matrix.add_apply, Pi.add_apply]
    ring
  map_smul' c x := by
    ext i j
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Matrix.of_symm_apply,
      Matrix.add_apply, Matrix.smul_apply, RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      Complex.real_smul]
    ring

private theorem iSMulAdd_apply
    (x : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    iSMulAdd p x =
      Matrix.of.symm (I • (x.1 : Matrix (Fin p) (Fin p) ℂ) + (x.2 : Matrix (Fin p) (Fin p) ℂ)) :=
  rfl

/-- `(S, T) ↦ i S + T` carries the sum of the trace forms to the real trace form. -/
private theorem sum_entryBasis_repr_iSMulAdd
    (x y : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ∑ σ, (entryBasis p).repr (iSMulAdd p x) σ * (entryBasis p).repr (iSMulAdd p y) σ =
      ⟪x.1, y.1⟫ + ⟪x.2, y.2⟫ := by
  simp only [sum_entryBasis_repr_mul, iSMulAdd_apply, Matrix.of_symm_apply,
    sum_re_conj_mul_I_smul_add]

private theorem injective_iSMulAdd : Function.Injective (iSMulAdd p) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have h := sum_entryBasis_repr_iSMulAdd x x
  simp only [hx, map_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    real_inner_self_eq_norm_sq] at h
  have h₁ : ‖x.1‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖]
  have h₂ : ‖x.2‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖]
  exact Prod.ext (by simpa using h₁) (by simpa using h₂)

private theorem finrank_prod_hermitianMatrix_eq :
    finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) = finrank ℝ (Fin p → Fin p → ℂ) := by
  rw [Module.finrank_prod, finrank_hermitianMatrix, Module.finrank_eq_card_basis (entryBasis p)]
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  ring

variable (p) in
/-- `(S, T) ↦ i S + T` as a continuous real linear equivalence. -/
private def iSMulAddEquiv :
    (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) ≃L[ℝ] (Fin p → Fin p → ℂ) :=
  ((iSMulAdd p).linearEquivOfInjective injective_iSMulAdd
    finrank_prod_hermitianMatrix_eq).toContinuousLinearEquiv

private theorem iSMulAddEquiv_apply
    (x : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    iSMulAddEquiv p x = iSMulAdd p x := by
  simp [iSMulAddEquiv, LinearMap.linearEquivOfInjective_apply]

variable (p) in
/-- The product of two copies of the orthonormal basis `hermitianOrthonormalBasis p`. -/
private def prodBasis :
    Module.Basis ((Fin p × Fin p) ⊕ (Fin p × Fin p)) ℝ
      (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ×
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (hermitianOrthonormalBasis p).toBasis.prod (hermitianOrthonormalBasis p).toBasis

private theorem inner_prodBasis (a b : (Fin p × Fin p) ⊕ (Fin p × Fin p)) :
    ⟪(prodBasis p a).1, (prodBasis p b).1⟫ + ⟪(prodBasis p a).2, (prodBasis p b).2⟫ =
      if a = b then 1 else 0 := by
  have h := orthonormal_iff_ite.1 (hermitianOrthonormalBasis p).orthonormal
  rcases a with a | a <;> rcases b with b | b <;>
    simp [prodBasis, h]

/-- The image of `prodBasis p` under `(S, T) ↦ i S + T` spans a parallelepiped of volume one. -/
private theorem volume_parallelepiped_iSMulAdd :
    volume (parallelepiped fun a ↦ iSMulAdd p (prodBasis p a)) = 1 := by
  obtain ⟨ε⟩ : Nonempty ((Σ _ : Fin p, Σ _ : Fin p, Fin 2) ≃
      (Fin p × Fin p) ⊕ (Fin p × Fin p)) := by
    refine Fintype.card_eq.1 ?_
    simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Fintype.card_sum, Fintype.card_prod]
    ring
  rw [← parallelepiped_comp_equiv _ ε, ← entryBasis_addHaar, Measure.addHaar_parallelepiped,
    Module.Basis.det_apply]
  set M := (entryBasis p).toMatrix ((fun a ↦ iSMulAdd p (prodBasis p a)) ∘ ε)
  have hM : Mᵀ * M = 1 := by
    ext τ τ'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, M, Module.Basis.toMatrix_apply,
      Function.comp_apply]
    rw [sum_entryBasis_repr_iSMulAdd, inner_prodBasis, Matrix.one_apply]
    simp [ε.injective.eq_iff]
  have h_det : |M.det| * |M.det| = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    rw [← abs_mul, h, abs_one]
  rw [(mul_self_eq_one_iff.1 h_det).resolve_right (by linarith [abs_nonneg M.det]),
    ENNReal.ofReal_one]

/-- `(S, T) ↦ i S + T` carries the product of the trace-form volumes of the Hermitian matrices
to the product Lebesgue measure. -/
private theorem map_iSMulAddEquiv_volume :
    Measure.map (iSMulAddEquiv p) (volume : Measure (selfAdjoint.submodule ℝ
      (Matrix (Fin p) (Fin p) ℂ) × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) =
      volume := by
  have hb : (prodBasis p).addHaar = (volume : Measure (selfAdjoint.submodule ℝ
      (Matrix (Fin p) (Fin p) ℂ) × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))) := by
    rw [prodBasis, Module.Basis.prod_addHaar, OrthonormalBasis.addHaar_eq_volume,
      Measure.volume_eq_prod]
  rw [← hb, Module.Basis.map_addHaar, Module.Basis.addHaar_eq_iff, Module.Basis.coe_parallelepiped,
    Module.Basis.coe_map]
  exact volume_parallelepiped_iSMulAdd

/-- The constant of the decomposition: `c ^ 2 / 2 ^ (p ^ 2) = 2 ^ (-p)`, where
`c = 2 ^ (p (p - 1) / 2)` compares the trace-form volume with `hermitianLebesgue p`. -/
private theorem decomposition_const :
    ENNReal.ofReal ((2 : ℝ) ^ (((p : ℝ) * ((p : ℝ) - 1)) / 2)) *
      (ENNReal.ofReal ((2 : ℝ) ^ (((p : ℝ) * ((p : ℝ) - 1)) / 2)) *
        (ENNReal.ofReal |(2 : ℝ) ^ finrank ℝ (selfAdjoint.submodule ℝ
          (Matrix (Fin p) (Fin p) ℂ))|)⁻¹) = (2 ^ p)⁻¹ := by
  -- Move everything into `ENNReal.ofReal` of a real power of `2` and compare exponents.
  rw [finrank_hermitianMatrix, abs_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos
    (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow zero_le_two,
    ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  simp only [← Real.rpow_natCast, ← Real.rpow_neg zero_le_two, ← Real.rpow_add two_pos]
  congr 1
  push_cast
  ring

/-- **Lebesgue measure on square matrices in skew-Hermitian and Hermitian coordinates.** Writing a
complex matrix of size `p` as `Z = i S + T / 2`, with `S` and `T` Hermitian, so that `i S` is its
skew-Hermitian and `T / 2` its Hermitian part,
`dZ = 2 ^ (-p) dS dT` for the coordinate Lebesgue measures `hermitianLebesgue p` in `S` and `T`. -/
theorem lintegral_eq_lintegral_hermitianLebesgue_I_smul_add {g : Matrix (Fin p) (Fin p) ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ Z, g Z = (2 ^ p)⁻¹ * ∫⁻ T, ∫⁻ S, g (I • (S : Matrix (Fin p) (Fin p) ℂ) +
      (2⁻¹ : ℝ) • (T : Matrix (Fin p) (Fin p) ℂ)) ∂hermitianLebesgue p ∂hermitianLebesgue p := by
  have hg' : Measurable fun x : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
        g (I • (x.1 : Matrix (Fin p) (Fin p) ℂ) + (x.2 : Matrix (Fin p) (Fin p) ℂ)) :=
    hg.comp ((Matrix.ofMeasurableEquiv _ _ ℂ).measurable.comp
      (iSMulAddEquiv p).continuous.measurable)
  have h_arrays : ∫⁻ Z, g Z = ∫⁻ x : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ), g (I • (x.1 : Matrix (Fin p) (Fin p) ℂ) +
      (x.2 : Matrix (Fin p) (Fin p) ℂ)) := by
    rw [← (Matrix.volume_preserving_ofMeasurableEquiv _ _ ℂ).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _), ← map_iSMulAddEquiv_volume]
    rw [lintegral_map (f := fun a ↦ g (Matrix.ofMeasurableEquiv _ _ ℂ a))
      (hg.comp (Matrix.ofMeasurableEquiv _ _ ℂ).measurable)
      (iSMulAddEquiv p).continuous.measurable]
    simp only [iSMulAddEquiv_apply, iSMulAdd_apply, Matrix.ofMeasurableEquiv_apply,
      Equiv.apply_symm_apply]
  rw [h_arrays, Measure.volume_eq_prod, lintegral_prod_symm _ hg'.aemeasurable]
  simp_rw [volume_hermitianMatrix_eq_smul_hermitianLebesgue, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← decomposition_const, mul_assoc,
    mul_assoc]
  congr 2
  have h := Measure.lintegral_comp_inv_smul (hermitianLebesgue p)
    (fun T : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
      ∫⁻ S, g (I • (S : Matrix (Fin p) (Fin p) ℂ) + (T : Matrix (Fin p) (Fin p) ℂ))
        ∂hermitianLebesgue p) (two_ne_zero (α := ℝ))
  simp only [Submodule.coe_smul] at h
  rw [h, ← mul_assoc, ENNReal.inv_mul_cancel (by simp) ENNReal.ofReal_ne_top, one_mul]

end Decomposition

end TauCeti
