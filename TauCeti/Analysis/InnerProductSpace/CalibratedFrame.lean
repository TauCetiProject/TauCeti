/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family

/-!
# Calibrated frames of alternating forms

Let `E` be a real inner product space and `φ : E [⋀^Fin k]→L[ℝ] ℝ` be a continuous alternating
`k`-form. An ordered `k`-tuple `v : Fin k → E` is *calibrated* by `φ` (`TauCeti.IsCalibratedFrame`)
when `v` is orthonormal and `φ v = 1`. When `φ` has comass `‖φ‖ ≤ 1`, any calibrated frame forces
`‖φ‖ = 1` and realizes the equality case of the linear calibration inequality
`|φ v| ≤ ‖φ‖ * ‖v₁ ∧ ⋯ ∧ vₖ‖`: calibrated frames are the positively oriented orthonormal frames of
the equality `k`-planes of `φ`.

This file develops the linear-algebraic properties of calibrated frames:

* **Comass lower bound and nonexistence**: a calibrated frame implies `1 ≤ ‖φ‖`
  (`TauCeti.IsCalibratedFrame.one_le_norm`), so a form with `‖φ‖ < 1` admits no calibrated frames
  (`TauCeti.not_isCalibratedFrame_of_norm_lt_one`).
* **Orthogonal and special orthogonal frame changes**: combining `v` on the right with a `k × k`
  matrix `A` scales `φ` by `A.det` (`ContinuousAlternatingMap.apply_sum_smul_col_eq_det_mul`).
  Consequently `TauCeti.IsCalibratedFrame φ` is invariant under right multiplication by
  `Matrix.specialOrthogonalGroup (Fin k) ℝ`
  (`TauCeti.isCalibratedFrame_sum_smul_specialOrthogonalGroup_iff`), while an orthogonal matrix of
  determinant `-1` (or a odd permutation, swap, or single-slot negation in positive degree) carries
  calibrated frames of `φ` to calibrated frames of `-φ`.
* **Isometric invariance**: pulling `φ` back along a linear isometry `f : E →ₗᵢ[ℝ] F` pulls back
  its calibrated frames (`TauCeti.isCalibratedFrame_comp_linearIsometry_iff`).
* **Volume forms and simple calibrations**: on an oriented `k`-dimensional space, `o.volumeFormL`
  has comass `1` (`Orientation.norm_volumeFormL`) and calibrates an orthonormal basis `b` if and
  only if `b` is positively oriented (`TauCeti.isCalibratedFrame_volumeFormL_orthonormalBasis_iff`).
  More generally, for any orthonormal frame `u : Fin k → E` in a finite-dimensional space, the
  simple form `alternatingFormEquiv E k (ιMulti ℝ k u)` has comass `1` and calibrates `v` if and
  only if `v` is orthonormal with `ιMulti ℝ k v = ιMulti ℝ k u`
  (`TauCeti.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff`).

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157, §II.3–4.
* D. Joyce, *Lectures on Special Lagrangian Geometry*, arXiv:math/0111111 (2001), §2.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace Matrix

namespace ContinuousAlternatingMap

section MatrixCombinations

variable {R E ι : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [Fintype ι] [DecidableEq ι]

/-- Evaluating an alternating form on column-combinations `j ↦ ∑ i, A i j • v i` of a family `v`
multiplies `φ v` by `A.det`. -/
theorem apply_sum_smul_col_eq_det_mul (φ : E [⋀^ι]→L[R] R) (v : ι → E) (A : Matrix ι ι R) :
    φ (fun j ↦ ∑ i, A i j • v i) = A.det * φ v := by
  let L : (ι → R) →ₗ[R] E := Fintype.linearCombination R v
  let e : Module.Basis ι R (ι → R) := Pi.basisFun R ι
  let ψ : (ι → R) [⋀^ι]→ₗ[R] R := φ.toAlternatingMap.compLinearMap L
  have hψ := DFunLike.congr_fun (ψ.eq_smul_basis_det e) (fun j i ↦ A i j)
  have he : ψ e = φ v := by
    simp [ψ, L, e]
  have hL : ψ (fun j i ↦ A i j) = φ (fun j ↦ ∑ i, A i j • v i) := by
    simp [ψ, L, Fintype.linearCombination_apply]
  have hdet : e.det (fun j i ↦ A i j) = A.det := by
    rw [Pi.basisFun_det_apply]
    exact A.det_transpose
  calc φ (fun j ↦ ∑ i, A i j • v i)
      _ = ψ (fun j i ↦ A i j) := hL.symm
      _ = φ v * A.det := by rw [hψ, _root_.smul_apply, he, hdet, smul_eq_mul]
      _ = A.det * φ v := mul_comm _ _

/-- Evaluating an alternating form on row-combinations `j ↦ ∑ i, A j i • v i` of a family `v`
multiplies `φ v` by `A.det`. -/
theorem apply_sum_smul_row_eq_det_mul (φ : E [⋀^ι]→L[R] R) (v : ι → E) (A : Matrix ι ι R) :
    φ (fun j ↦ ∑ i, A j i • v i) = A.det * φ v := by
  simpa only [Matrix.transpose_apply, Matrix.det_transpose] using
    φ.apply_sum_smul_col_eq_det_mul v Aᵀ

end MatrixCombinations

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- Negating one vector of an orthonormal family preserves orthonormality. -/
protected theorem orthonormal_update_neg {ι : Type*} [DecidableEq ι] {v : ι → E}
    (hv : Orthonormal ℝ v) (i : ι) :
    Orthonormal ℝ (Function.update v i (-v i)) := by
  rw [orthonormal_iff_ite]
  intro a b
  obtain rfl | ha := eq_or_ne i a <;> obtain rfl | hb := eq_or_ne i b
  · simp [hv.1 i]
  · simp [hb, hb.symm, hv.2 hb]
  · simp [ha.symm, hv.2 ha.symm]
  · simp [ha.symm, hb.symm, orthonormal_iff_ite.1 hv a b]

/-- In positive degree, a nonnegative comass bound `‖φ‖ ≤ C` on a real alternating `k`-form is
equivalent to the one-sided bound `φ v ≤ C` on all orthonormal frames `v`, since negating the
first vector of an orthonormal frame preserves orthonormality and negates `φ v`. -/
theorem opNorm_le_iff_apply_le_orthonormal {φ : E [⋀^Fin k]→L[ℝ] ℝ} (hk : 1 ≤ k) {C : ℝ}
    (hC : 0 ≤ C) :
    ‖φ‖ ≤ C ↔ ∀ v : Fin k → E, Orthonormal ℝ v → φ v ≤ C := by
  rw [φ.opNorm_le_iff_le_orthonormal hC]
  refine ⟨fun h v hv ↦ (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h v hv),
    fun h v hv ↦ ?_⟩
  rw [Real.norm_eq_abs, abs_le]
  refine ⟨?_, h v hv⟩
  let i₀ : Fin k := ⟨0, hk⟩
  have hneg : φ (Function.update v i₀ (-v i₀)) = -φ v := by
    simpa [neg_one_smul] using φ.map_update_smul v i₀ (-1 : ℝ) (v i₀)
  linarith [h _ (ContinuousAlternatingMap.orthonormal_update_neg hv i₀)]

end General

end ContinuousAlternatingMap

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n)]

/-- The continuous oriented volume form on an `n`-dimensional real inner product space has comass
`1` in every dimension `n`, including `n = 0`. -/
@[simp]
theorem norm_volumeFormL (o : Orientation ℝ E (Fin n)) : ‖o.volumeFormL‖ = 1 := by
  rcases n with _ | m
  · have hle : ‖o.volumeFormL‖ ≤ 1 :=
      (o.volumeFormL.opNorm_le_iff_le_orthonormal zero_le_one).2 fun v hv ↦ by
        rw [Real.norm_eq_abs, volumeFormL_apply, o.abs_volumeForm_apply_eq_sqrt_det_gram,
          Matrix.gram_eq_one_iff_orthonormal.2 hv, Matrix.det_one, Real.sqrt_one]
    have horth : Orthonormal ℝ (![] : Fin 0 → E) := orthonormal_iff_ite.2 fun i ↦ i.elim0
    have hge : 1 ≤ ‖o.volumeFormL‖ := by
      simpa [Real.norm_eq_abs, volumeFormL_apply, o.abs_volumeForm_apply_eq_sqrt_det_gram] using
        (o.volumeFormL.opNorm_le_iff_le_orthonormal (norm_nonneg _)).1 le_rfl ![] horth
    exact le_antisymm hle hge
  · have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ m
    let b : OrthonormalBasis (Fin (m + 1)) ℝ E :=
      (stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)
    rw [o.volumeFormL.norm_eq_norm_apply_orthonormalBasis b, Real.norm_eq_abs, volumeFormL_apply,
      o.abs_volumeForm_apply_eq_sqrt_det_gram, Matrix.gram_eq_one_iff_orthonormal.2 b.orthonormal,
      Matrix.det_one, Real.sqrt_one]

end Orientation

namespace TauCeti

section General

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k : ℕ}

/-- An ordered frame `v` is calibrated by the `k`-form `φ` when it is orthonormal and `φ v = 1`;
for a form of comass at most one these are the positively oriented equality planes of `φ`. -/
def IsCalibratedFrame (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) : Prop :=
  Orthonormal ℝ v ∧ φ v = 1

/-- Unfolding `IsCalibratedFrame` into orthonormality and unit pairing. -/
theorem isCalibratedFrame_def (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    IsCalibratedFrame φ v ↔ Orthonormal ℝ v ∧ φ v = 1 :=
  Iff.rfl

/-- A calibrated frame is orthonormal. -/
theorem IsCalibratedFrame.orthonormal {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) : Orthonormal ℝ v :=
  h.1

/-- A calibrated frame evaluates `φ` to `1`. -/
theorem IsCalibratedFrame.apply_eq_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) : φ v = 1 :=
  h.2

/-- Any form admitting a calibrated frame has comass at least `1`. -/
theorem IsCalibratedFrame.one_le_norm {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) : 1 ≤ ‖φ‖ := by
  have hle :=
    (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal (norm_nonneg φ)).1 le_rfl v h.orthonormal
  simpa only [Real.norm_eq_abs, h.apply_eq_one, abs_one] using hle

/-- A form of comass at most `1` that admits a calibrated frame has comass `1`. -/
theorem IsCalibratedFrame.norm_eq_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) (hφ : ‖φ‖ ≤ 1) : ‖φ‖ = 1 :=
  le_antisymm hφ h.one_le_norm

/-- A form with comass strictly less than `1` admits no calibrated frames. -/
theorem not_isCalibratedFrame_of_norm_lt_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} (hφ : ‖φ‖ < 1)
    (v : Fin k → E) : ¬IsCalibratedFrame φ v :=
  fun h ↦ hφ.not_ge h.one_le_norm

/-- The zero `k`-form admits no calibrated frames. -/
@[simp]
theorem not_isCalibratedFrame_zero (v : Fin k → E) :
    ¬IsCalibratedFrame (0 : E [⋀^Fin k]→L[ℝ] ℝ) v :=
  not_isCalibratedFrame_of_norm_lt_one (by simp) v

/-- A form admitting a calibrated frame is nonzero. -/
theorem IsCalibratedFrame.ne_zero {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) : φ ≠ 0 := by
  rintro rfl
  exact not_isCalibratedFrame_zero v h

/-- In degree zero, the unique empty frame is calibrated by `φ` if and only if `φ ![] = 1`. -/
@[simp]
theorem isCalibratedFrame_zero_iff (φ : E [⋀^Fin 0]→L[ℝ] ℝ) (v : Fin 0 → E) :
    IsCalibratedFrame φ v ↔ φ ![] = 1 := by
  rw [isCalibratedFrame_def, Matrix.empty_eq v]
  exact and_iff_right (orthonormal_iff_ite.2 fun i ↦ i.elim0)

/-- Pulling a form back along a linear isometry pulls back calibrated frames: `w` is calibrated by
`f* φ` if and only if `f ∘ w` is calibrated by `φ`. -/
@[simp]
theorem isCalibratedFrame_comp_linearIsometry_iff (φ : F [⋀^Fin k]→L[ℝ] ℝ) (f : E →ₗᵢ[ℝ] F)
    (w : Fin k → E) :
    IsCalibratedFrame (φ.compContinuousLinearMap f.toContinuousLinearMap) w ↔
      IsCalibratedFrame φ (f ∘ w) := by
  simp only [isCalibratedFrame_def, f.orthonormal_comp_iff,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rfl

/-- Pulling a form back along a linear isometric equivalence (coerced via
`LinearIsometryEquiv.toContinuousLinearEquiv`) pulls back calibrated frames. -/
@[simp]
theorem isCalibratedFrame_comp_linearIsometryEquiv_iff (φ : F [⋀^Fin k]→L[ℝ] ℝ) (f : E ≃ₗᵢ[ℝ] F)
    (w : Fin k → E) :
    IsCalibratedFrame (φ.compContinuousLinearMap (f.toContinuousLinearEquiv : E →L[ℝ] F)) w ↔
      IsCalibratedFrame φ (f ∘ w) :=
  isCalibratedFrame_comp_linearIsometry_iff φ f.toLinearIsometry w

/-- Reordering a calibrated frame by an even permutation preserves calibration. -/
theorem IsCalibratedFrame.comp_perm_of_sign_eq_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) {σ : Equiv.Perm (Fin k)} (hσ : Equiv.Perm.sign σ = 1) :
    IsCalibratedFrame φ (v ∘ σ) := by
  refine ⟨h.orthonormal.comp σ σ.injective, ?_⟩
  have hp := φ.toAlternatingMap.map_perm v σ
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, hσ, one_smul] at hp
  rw [hp, h.apply_eq_one]

/-- An even permutation of the slots preserves `IsCalibratedFrame`. -/
theorem isCalibratedFrame_comp_perm_iff_of_sign_eq_one (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E)
    {σ : Equiv.Perm (Fin k)} (hσ : Equiv.Perm.sign σ = 1) :
    IsCalibratedFrame φ (v ∘ σ) ↔ IsCalibratedFrame φ v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_perm_of_sign_eq_one hσ⟩
  have h' := h.comp_perm_of_sign_eq_one (σ := σ⁻¹) (by simp [hσ])
  simpa [Function.comp_def] using h'

/-- Reordering a calibrated frame of `φ` by an odd permutation yields a calibrated frame of
`-φ`. -/
theorem IsCalibratedFrame.neg_comp_perm_of_sign_eq_neg_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) {σ : Equiv.Perm (Fin k)} (hσ : Equiv.Perm.sign σ = -1) :
    IsCalibratedFrame (-φ) (v ∘ σ) := by
  refine ⟨h.orthonormal.comp σ σ.injective, ?_⟩
  have hp := φ.toAlternatingMap.map_perm v σ
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, hσ, Units.neg_smul, one_smul] at hp
  rw [ContinuousAlternatingMap.neg_apply, hp, neg_neg, h.apply_eq_one]

/-- An odd permutation exchanges calibrated frames of `φ` and calibrated frames of `-φ`. -/
theorem isCalibratedFrame_neg_comp_perm_iff_of_sign_eq_neg_one (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (v : Fin k → E) {σ : Equiv.Perm (Fin k)} (hσ : Equiv.Perm.sign σ = -1) :
    IsCalibratedFrame (-φ) (v ∘ σ) ↔ IsCalibratedFrame φ v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.neg_comp_perm_of_sign_eq_neg_one hσ⟩
  have h' := h.neg_comp_perm_of_sign_eq_neg_one (σ := σ⁻¹) (by simp [hσ])
  simpa [Function.comp_def] using h'

/-- Swapping two distinct vectors in a frame exchanges calibrated frames of `φ` and calibrated
frames of `-φ`. -/
theorem isCalibratedFrame_neg_comp_swap_iff (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) {i j : Fin k}
    (hij : i ≠ j) :
    IsCalibratedFrame (-φ) (v ∘ Equiv.swap i j) ↔ IsCalibratedFrame φ v :=
  isCalibratedFrame_neg_comp_perm_iff_of_sign_eq_neg_one φ v (Equiv.Perm.sign_swap hij)

/-- Negating one vector of a frame (which exists whenever `1 ≤ k`) exchanges calibrated frames of
`φ` and calibrated frames of `-φ`. -/
theorem isCalibratedFrame_neg_update_neg_iff (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) (i : Fin k) :
    IsCalibratedFrame (-φ) (Function.update v i (-v i)) ↔ IsCalibratedFrame φ v := by
  have hinv : Function.update (Function.update v i (-v i)) i (-Function.update v i (-v i) i) =
      v := by
    ext j
    obtain rfl | hj := eq_or_ne i j
    · simp
    · simp [hj.symm]
  have hneg : φ (Function.update v i (-v i)) = -φ v := by
    simpa [neg_one_smul] using φ.map_update_smul v i (-1 : ℝ) (v i)
  refine ⟨fun ⟨hw, hval⟩ ↦ ⟨?_, ?_⟩,
    fun ⟨hv, hval⟩ ↦ ⟨ContinuousAlternatingMap.orthonormal_update_neg hv i, ?_⟩⟩
  · simpa only [hinv] using ContinuousAlternatingMap.orthonormal_update_neg hw i
  · rw [ContinuousAlternatingMap.neg_apply, hneg, neg_neg] at hval
    exact hval
  · rw [ContinuousAlternatingMap.neg_apply, hneg, neg_neg, hval]

private theorem sum_smul_sum_smul_of_mul_eq_one (v : Fin k → E) {A B : Matrix (Fin k) (Fin k) ℝ}
    (hAB : A * B = 1) :
    (fun j ↦ ∑ l, B l j • ∑ i, A i l • v i) = v := by
  ext j
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hcoeff (i : Fin k) : ∑ l, B l j * A i l = (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
    rw [← hAB, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _
  simp_rw [← Finset.sum_smul, hcoeff, Matrix.one_apply]
  simp

/-- Right multiplication of a frame `v` by an orthogonal matrix `A ∈ O(k)` of determinant `1`
preserves `IsCalibratedFrame`. -/
theorem IsCalibratedFrame.sum_smul_of_mem_specialOrthogonalGroup {φ : E [⋀^Fin k]→L[ℝ] ℝ}
    {v : Fin k → E} (h : IsCalibratedFrame φ v) {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin k) ℝ) :
    IsCalibratedFrame φ (fun j ↦ ∑ i, A i j • v i) := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff'] at hA
  refine ⟨?_, ?_⟩
  · have horth : Aᵀ * (Aᵀ)ᴴ = 1 := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
        hA.1
    simpa only [Matrix.transpose_apply] using (h.orthonormal.orthonormal_sum_smul_iff Aᵀ).2 horth
  · rw [φ.apply_sum_smul_col_eq_det_mul, hA.2, one_mul, h.apply_eq_one]

/-- **Special orthogonal invariance of calibrated frames**: for `g ∈ SO(k)`, the right-transformed
frame `j ↦ ∑ i, g i j • v i` is calibrated by `φ` if and only if `v` is calibrated by `φ`. -/
@[simp]
theorem isCalibratedFrame_sum_smul_specialOrthogonalGroup_iff (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (v : Fin k → E) (g : Matrix.specialOrthogonalGroup (Fin k) ℝ) :
    IsCalibratedFrame φ (fun j ↦ ∑ i, (g : Matrix (Fin k) (Fin k) ℝ) i j • v i) ↔
      IsCalibratedFrame φ v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.sum_smul_of_mem_specialOrthogonalGroup g.2⟩
  have h' := h.sum_smul_of_mem_specialOrthogonalGroup (g⁻¹).2
  have hmul : (g : Matrix (Fin k) (Fin k) ℝ) *
      (g⁻¹ : Matrix.specialOrthogonalGroup (Fin k) ℝ) = 1 := by
    change (↑(g * g⁻¹) : Matrix (Fin k) (Fin k) ℝ) = 1
    rw [mul_inv_cancel, Submonoid.coe_one]
  rwa [sum_smul_sum_smul_of_mul_eq_one v hmul] at h'

/-- Right multiplication of a frame `v` by an orientation-reversing orthogonal matrix `A ∈ O(k)`
(`A.det = -1`) exchanges calibrated frames of `φ` and calibrated frames of `-φ`. -/
theorem isCalibratedFrame_neg_sum_smul_iff_of_det_eq_neg_one (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (v : Fin k → E) {A : Matrix (Fin k) (Fin k) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin k) ℝ)
    (hdet : A.det = -1) :
    IsCalibratedFrame (-φ) (fun j ↦ ∑ i, A i j • v i) ↔ IsCalibratedFrame φ v := by
  have step {ψ : E [⋀^Fin k]→L[ℝ] ℝ} {w : Fin k → E} {B : Matrix (Fin k) (Fin k) ℝ}
      (hB : B ∈ Matrix.orthogonalGroup (Fin k) ℝ) (hd : B.det = -1) (hw : IsCalibratedFrame ψ w) :
      IsCalibratedFrame (-ψ) (fun j ↦ ∑ i, B i j • w i) := by
    rw [Matrix.mem_orthogonalGroup_iff'] at hB
    refine ⟨?_, ?_⟩
    · have horth : Bᵀ * (Bᵀ)ᴴ = 1 := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
          hB
      simpa only [Matrix.transpose_apply] using (hw.orthonormal.orthonormal_sum_smul_iff Bᵀ).2 horth
    · rw [ContinuousAlternatingMap.neg_apply, ψ.apply_sum_smul_col_eq_det_mul, hd, hw.apply_eq_one]
      ring
  refine ⟨fun h ↦ ?_, step hA hdet⟩
  have hmul : A * Aᵀ = 1 := by rwa [Matrix.mem_orthogonalGroup_iff] at hA
  have hAT : Aᵀ ∈ Matrix.orthogonalGroup (Fin k) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_transpose]
    rwa [Matrix.mem_orthogonalGroup_iff'] at hA
  simpa only [neg_neg, sum_smul_sum_smul_of_mul_eq_one v hmul] using
    step hAT (by rw [Matrix.det_transpose, hdet]) h

/-- On an oriented `k`-dimensional real inner product space, a frame `v : Fin k → E` is calibrated
by `o.volumeFormL` if and only if `v` is orthonormal and `0 < o.volumeForm v`. -/
theorem isCalibratedFrame_volumeFormL_iff_pos [Fact (Module.finrank ℝ E = k)]
    (o : Orientation ℝ E (Fin k)) (v : Fin k → E) :
    IsCalibratedFrame o.volumeFormL v ↔ Orthonormal ℝ v ∧ 0 < o.volumeForm v := by
  rw [isCalibratedFrame_def, Orientation.volumeFormL_apply]
  refine and_congr_right fun hv ↦ ⟨fun h ↦ by linarith, fun hpos ↦ ?_⟩
  have habs : |o.volumeForm v| = 1 := by
    rw [o.abs_volumeForm_apply_eq_sqrt_det_gram, Matrix.gram_eq_one_iff_orthonormal.2 hv,
      Matrix.det_one, Real.sqrt_one]
  rwa [abs_of_pos hpos] at habs

/-- On an oriented `k`-dimensional real inner product space, an orthonormal basis `b` is calibrated
by `o.volumeFormL` if and only if `b` is positively oriented for `o`. -/
@[simp]
theorem isCalibratedFrame_volumeFormL_orthonormalBasis_iff [Fact (Module.finrank ℝ E = k)]
    (o : Orientation ℝ E (Fin k)) (b : OrthonormalBasis (Fin k) ℝ E) :
    IsCalibratedFrame o.volumeFormL b ↔ b.toBasis.orientation = o := by
  rw [isCalibratedFrame_volumeFormL_iff_pos, and_iff_right b.orthonormal,
    ← OrthonormalBasis.coe_toBasis, Orientation.volumeForm_apply_pos_iff]

end General

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}

/-- The simple `k`-form `v ↦ ⟪u₁ ∧ ⋯ ∧ uₖ, v₁ ∧ ⋯ ∧ vₖ⟫` of an orthonormal frame `u` calibrates
`u` itself. -/
theorem _root_.Orthonormal.isCalibratedFrame_alternatingFormEquiv_ιMulti {u : Fin k → E}
    (hu : Orthonormal ℝ u) :
    IsCalibratedFrame (alternatingFormEquiv E k (ιMulti ℝ k u)) u := by
  refine ⟨hu, ?_⟩
  rw [alternatingFormEquiv_apply, real_inner_self_eq_norm_sq, hu.norm_ιMulti, one_pow]

/-- The simple `k`-form `alternatingFormEquiv E k (ιMulti ℝ k u)` associated to an orthonormal
frame `u` has comass `1`. -/
@[simp]
theorem _root_.Orthonormal.norm_alternatingFormEquiv_ιMulti {u : Fin k → E}
    (hu : Orthonormal ℝ u) :
    ‖alternatingFormEquiv E k (ιMulti ℝ k u)‖ = 1 :=
  hu.isCalibratedFrame_alternatingFormEquiv_ιMulti.norm_eq_one
    ((norm_alternatingFormEquiv_le _).trans_eq hu.norm_ιMulti)

/-- **Equality planes of a simple calibration**: for an orthonormal frame `u : Fin k → E`, the
simple `k`-form `alternatingFormEquiv E k (ιMulti ℝ k u)` calibrates `v` if and only if `v` is
orthonormal and spans the same oriented `k`-plane as `u` (`ιMulti ℝ k v = ιMulti ℝ k u`). -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti_iff {u : Fin k → E} (hu : Orthonormal ℝ u)
    (v : Fin k → E) :
    IsCalibratedFrame (alternatingFormEquiv E k (ιMulti ℝ k u)) v ↔
      Orthonormal ℝ v ∧ ιMulti ℝ k v = ιMulti ℝ k u := by
  rw [isCalibratedFrame_def, alternatingFormEquiv_apply]
  refine and_congr_right fun hv ↦ ⟨fun hinner ↦ ?_, fun heq ↦ ?_⟩
  · have hnorm : ‖ιMulti ℝ k v - ιMulti ℝ k u‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hv.norm_ιMulti, hu.norm_ιMulti, real_inner_comm, hinner]
      ring
    exact sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 hnorm))
  · rw [heq, real_inner_self_eq_norm_sq, hu.norm_ιMulti, one_pow]

end FiniteDimensional

end TauCeti
