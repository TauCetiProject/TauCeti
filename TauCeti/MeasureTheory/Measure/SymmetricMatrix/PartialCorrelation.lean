/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Correlation
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The Jacobian of partial-correlation coordinates

Partial correlations in the open cube parametrize positive-definite correlation matrices.
This file computes the Jacobian of that parametrization in the strictly lower matrix
coordinates.  If `zᵢⱼ` is the partial correlation in row `i` and column `j`, the absolute
Jacobian is

`∏ i > j, (1 - zᵢⱼ ^ 2) ^ ((p - j - 2) / 2)`.

The calculation orders the coordinates by row and then column.  The correlation entry in
position `(i, j)` depends only on earlier coordinates in this order, while its derivative with
respect to `zᵢⱼ` is the product of the residual square roots in rows `i` and `j`.  Thus the
derivative matrix is triangular, and regrouping its diagonal factors gives the formula above.
This is the change-of-variables factor used to normalize the LKJ density.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open scoped BigOperators
open Set

namespace TauCeti

variable {p : ℕ}

/-- The product of the residual square roots in row `i` before column `j`. -/
private def partialCorrelationPrefix (z : strictLowerTriangle p → ℝ) (i j : Fin p) : ℝ :=
  ∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < j,
    Real.sqrt (1 - z ij ^ 2)

private theorem partialCorrelationCholesky_apply_eq_prefix
    (z : strictLowerTriangle p → ℝ) {i j : Fin p} (hji : j < i) :
    partialCorrelationCholesky z i j =
      z ⟨(i, j), hji⟩ * partialCorrelationPrefix z i j := by
  rw [partialCorrelationCholesky_apply_of_gt z hji]
  rfl

private theorem partialCorrelationCholesky_apply_self_eq_prefix
    (z : strictLowerTriangle p → ℝ) (i : Fin p) :
    partialCorrelationCholesky z i i = partialCorrelationPrefix z i i := by
  rw [partialCorrelationCholesky_apply_self]
  unfold partialCorrelationPrefix
  congr 1
  ext ij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨h, h ▸ ij.2⟩
  · exact And.left

/-- A strictly lower Gram entry isolates its newest partial correlation linearly. -/
private theorem correlationCoordinatesOfPartialCorrelation_apply_eq_sum_add
    (z : strictLowerTriangle p → ℝ) (ij : strictLowerTriangle p) :
    correlationCoordinatesOfPartialCorrelation z ij =
      (∑ k ∈ Finset.Iio ij.1.2,
        partialCorrelationCholesky z ij.1.1 k *
          partialCorrelationCholesky z ij.1.2 k) +
      z ij * partialCorrelationPrefix z ij.1.1 ij.1.2 *
        partialCorrelationPrefix z ij.1.2 ij.1.2 := by
  obtain ⟨⟨i, j⟩, hji⟩ := ij
  rw [correlationCoordinatesOfPartialCorrelation_apply]
  -- Expose the matrix entry after destructuring its subtype index.
  change partialCorrelationGram z i j = _
  rw [partialCorrelationGram_def]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hsum :
      (∑ k, partialCorrelationCholesky z i k * partialCorrelationCholesky z j k) =
        ∑ k ∈ Finset.Iic j,
          partialCorrelationCholesky z i k * partialCorrelationCholesky z j k := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦ ?_
    simp only [Finset.mem_Iic, not_le] at hk
    rw [partialCorrelationCholesky_apply_of_lt z hk, mul_zero]
  rw [hsum, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  · rw [partialCorrelationCholesky_apply_eq_prefix z hji,
      partialCorrelationCholesky_apply_self_eq_prefix]
    ring

private theorem partialCorrelationPrefix_add_single_of_not_mem
    (z : strictLowerTriangle p → ℝ) (t : ℝ) (kl : strictLowerTriangle p) (i j : Fin p)
    (hkl : ¬(kl.1.1 = i ∧ kl.1.2 < j)) :
    partialCorrelationPrefix (z + t • Pi.single kl 1) i j =
      partialCorrelationPrefix z i j := by
  unfold partialCorrelationPrefix
  apply Finset.prod_congr rfl
  intro ab hab
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
  have hne : kl ≠ ab := by
    intro h
    apply hkl
    simpa [h] using hab
  simp [hne]

private theorem partialCorrelationCholesky_add_single_of_not_mem
    (z : strictLowerTriangle p → ℝ) (t : ℝ) (kl : strictLowerTriangle p)
    (i k : Fin p) (hki : k ≤ i)
    (hkl : ¬(kl.1.1 = i ∧ kl.1.2 ≤ k)) :
    partialCorrelationCholesky (z + t • Pi.single kl 1) i k =
      partialCorrelationCholesky z i k := by
  rcases hki.eq_or_lt with rfl | hki
  · rw [partialCorrelationCholesky_apply_self_eq_prefix,
      partialCorrelationCholesky_apply_self_eq_prefix,
      partialCorrelationPrefix_add_single_of_not_mem]
    intro h
    exact hkl ⟨h.1, h.2.le⟩
  · rw [partialCorrelationCholesky_apply_eq_prefix _ hki,
      partialCorrelationCholesky_apply_eq_prefix _ hki,
      partialCorrelationPrefix_add_single_of_not_mem]
    · have hne : kl ≠ (⟨(i, k), hki⟩ : strictLowerTriangle p) := by
        intro h
        apply hkl
        simp [h]
      simp [hne]
    · intro h
      exact hkl ⟨h.1, h.2.le⟩

/-- Changing a coordinate later in row-then-column order does not change an earlier correlation
coordinate. -/
private theorem correlationCoordinatesOfPartialCorrelation_add_single_of_lt
    (z : strictLowerTriangle p → ℝ) (t : ℝ) {ij kl : strictLowerTriangle p}
    (h : toLex (ij.1.1, ij.1.2) < toLex (kl.1.1, kl.1.2)) :
    correlationCoordinatesOfPartialCorrelation (z + t • Pi.single kl 1) ij =
      correlationCoordinatesOfPartialCorrelation z ij := by
  have hkey := h
  rw [correlationCoordinatesOfPartialCorrelation_apply_eq_sum_add,
    correlationCoordinatesOfPartialCorrelation_apply_eq_sum_add]
  rw [Prod.Lex.toLex_lt_toLex] at h
  have hnot_i (k : Fin p) (hkj : k ≤ ij.1.2) :
      ¬(kl.1.1 = ij.1.1 ∧ kl.1.2 ≤ k) := by
    rintro ⟨hrow, hcol⟩
    rcases h with hrow' | ⟨_, hcol'⟩
    · exact (hrow ▸ hrow').false
    · exact (not_lt_of_ge (hcol.trans hkj)) hcol'
  have hnot_j (k : Fin p) (hkj : k ≤ ij.1.2) :
      ¬(kl.1.1 = ij.1.2 ∧ kl.1.2 ≤ k) := by
    rintro ⟨hrow, _⟩
    rcases h with hrow' | ⟨hrow', _⟩
    · exact (not_lt_of_ge ij.2.le) (by simpa [hrow] using hrow')
    · exact ij.2.ne (hrow'.trans hrow).symm
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k hk
    have hkj := (Finset.mem_Iio.1 hk).le
    rw [partialCorrelationCholesky_add_single_of_not_mem _ _ _ _ _
        (hkj.trans ij.2.le) (hnot_i k hkj),
      partialCorrelationCholesky_add_single_of_not_mem _ _ _ _ _ hkj (hnot_j k hkj)]
  · have hne : kl ≠ ij := by
      intro heq
      subst kl
      exact (lt_irrefl _ hkey)
    rw [partialCorrelationPrefix_add_single_of_not_mem,
      partialCorrelationPrefix_add_single_of_not_mem]
    · simp [hne]
    · intro hmem
      exact hnot_j ij.1.2 le_rfl ⟨hmem.1, hmem.2.le⟩
    · intro hmem
      exact hnot_i ij.1.2 le_rfl ⟨hmem.1, hmem.2.le⟩

/-- Varying `zᵢⱼ` changes the corresponding correlation coordinate affinely, with slope the
product of the residual square roots in rows `i` and `j`. -/
private theorem correlationCoordinatesOfPartialCorrelation_add_single_self
    (z : strictLowerTriangle p → ℝ) (t : ℝ) (ij : strictLowerTriangle p) :
    correlationCoordinatesOfPartialCorrelation (z + t • Pi.single ij 1) ij =
      correlationCoordinatesOfPartialCorrelation z ij +
        t * (partialCorrelationPrefix z ij.1.1 ij.1.2 *
          partialCorrelationPrefix z ij.1.2 ij.1.2) := by
  rw [correlationCoordinatesOfPartialCorrelation_apply_eq_sum_add,
    correlationCoordinatesOfPartialCorrelation_apply_eq_sum_add]
  have hnot_i (k : Fin p) (hkj : k < ij.1.2) :
      ¬(ij.1.1 = ij.1.1 ∧ ij.1.2 ≤ k) := fun h ↦ (not_le_of_gt hkj) h.2
  have hnot_j (k : Fin p) (hkj : k ≤ ij.1.2) :
      ¬(ij.1.1 = ij.1.2 ∧ ij.1.2 ≤ k) := fun h ↦ ij.2.ne h.1.symm
  have hsum :
      (∑ k ∈ Finset.Iio ij.1.2,
        partialCorrelationCholesky (z + t • Pi.single ij 1) ij.1.1 k *
          partialCorrelationCholesky (z + t • Pi.single ij 1) ij.1.2 k) =
      ∑ k ∈ Finset.Iio ij.1.2,
        partialCorrelationCholesky z ij.1.1 k *
          partialCorrelationCholesky z ij.1.2 k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := Finset.mem_Iio.1 hk
    rw [partialCorrelationCholesky_add_single_of_not_mem _ _ _ _ _
        (hkj.le.trans ij.2.le) (hnot_i k hkj),
      partialCorrelationCholesky_add_single_of_not_mem _ _ _ _ _ hkj.le
        (hnot_j k hkj.le)]
  rw [hsum, partialCorrelationPrefix_add_single_of_not_mem,
    partialCorrelationPrefix_add_single_of_not_mem]
  · simp
    ring
  · intro h
    exact ij.2.ne h.1.symm
  · exact fun h ↦ (not_lt_of_ge h.2.le) h.2

private theorem fderiv_apply_eq_of_add_smul_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x v : E} {w : F} (hf : DifferentiableAt ℝ f x)
    (h : ∀ t : ℝ, f (x + t • v) = f x + t • w) :
    (fderiv ℝ f x) v = w := by
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const v).const_add x
  have hcomp : HasDerivAt (fun t : ℝ ↦ f (x + t • v)) ((fderiv ℝ f x) v) 0 := by
    have hfat : HasFDerivAt f (fderiv ℝ f x) ((fun t : ℝ ↦ x + t • v) 0) := by
      simpa using hf.hasFDerivAt
    exact hfat.comp_hasDerivAt 0 hline
  have hrhs : HasDerivAt (fun t : ℝ ↦ f x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const w).const_add (f x)
  exact (hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ (h t).symm)).unique hrhs

private theorem fderiv_coord_apply {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Finite ι] {f : E → ι → ℝ} {x v : E} (hf : DifferentiableAt ℝ f x) (i : ι) :
    (fderiv ℝ (fun y ↦ f y i) x) v = (fderiv ℝ f x v) i := by
  let _ := Fintype.ofFinite ι
  have hcomp := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp x hf.hasFDerivAt
  have heq : (fun y ↦ f y i) = (ContinuousLinearMap.proj (R := ℝ) i) ∘ f := rfl
  rw [heq, hcomp.fderiv]
  rfl

private def strictLowerTriangleKey (ij : strictLowerTriangle p) : Fin p ×ₗ Fin p :=
  toLex (ij.1.1, ij.1.2)

private theorem strictLowerTriangleKey_injective :
    Function.Injective (strictLowerTriangleKey (p := p)) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ h
  simp only [strictLowerTriangleKey, toLex_inj, Prod.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

private theorem differentiableAt_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    DifferentiableAt ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z :=
  (contDiffOn_correlationCoordinatesOfPartialCorrelation.differentiableOn
      (by simp)).differentiableAt
    (by
      have hopen : IsOpen {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1} := by
        have hopen_eq : {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1} =
            Set.univ.pi (fun _ ↦ Ioo (-1) 1) := by
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioo]
          exact forall_congr' fun _ ↦ abs_lt
        rw [hopen_eq]
        exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo
      exact hopen.mem_nhds hz)

private theorem toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation_of_lt
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1)
    {ij kl : strictLowerTriangle p}
    (h : strictLowerTriangleKey ij < strictLowerTriangleKey kl) :
    LinearMap.toMatrix (Pi.basisFun ℝ (strictLowerTriangle p))
        (Pi.basisFun ℝ (strictLowerTriangle p))
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z) ij kl = 0 := by
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  rw [← fderiv_coord_apply
    (differentiableAt_correlationCoordinatesOfPartialCorrelation hz) ij]
  exact fderiv_apply_eq_of_add_smul_eq
    (by
      -- Expose evaluation as composition with the continuous coordinate projection.
      change DifferentiableAt ℝ
        ((ContinuousLinearMap.proj (R := ℝ) ij) ∘
          correlationCoordinatesOfPartialCorrelation) z
      exact (ContinuousLinearMap.proj (R := ℝ) ij).differentiableAt.comp z
        (differentiableAt_correlationCoordinatesOfPartialCorrelation hz))
    (v := Pi.single kl 1) (w := 0) fun t ↦ by
      simpa using correlationCoordinatesOfPartialCorrelation_add_single_of_lt z t h

private theorem blockTriangular_toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    (LinearMap.toMatrix (Pi.basisFun ℝ (strictLowerTriangle p))
      (Pi.basisFun ℝ (strictLowerTriangle p))
      (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z)).BlockTriangular
      (OrderDual.toDual ∘ strictLowerTriangleKey) := by
  intro ij kl h
  exact toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation_of_lt hz
    (by simpa only [Function.comp_apply, OrderDual.toDual_lt_toDual] using h)

private theorem toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation_diag
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1)
    (ij : strictLowerTriangle p) :
    LinearMap.toMatrix (Pi.basisFun ℝ (strictLowerTriangle p))
        (Pi.basisFun ℝ (strictLowerTriangle p))
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z) ij ij =
      partialCorrelationPrefix z ij.1.1 ij.1.2 *
        partialCorrelationPrefix z ij.1.2 ij.1.2 := by
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  rw [← fderiv_coord_apply
    (differentiableAt_correlationCoordinatesOfPartialCorrelation hz) ij]
  exact fderiv_apply_eq_of_add_smul_eq
    (by
      -- Expose evaluation as composition with the continuous coordinate projection.
      change DifferentiableAt ℝ
        ((ContinuousLinearMap.proj (R := ℝ) ij) ∘
          correlationCoordinatesOfPartialCorrelation) z
      exact (ContinuousLinearMap.proj (R := ℝ) ij).differentiableAt.comp z
        (differentiableAt_correlationCoordinatesOfPartialCorrelation hz))
    (v := Pi.single ij 1)
    (w := partialCorrelationPrefix z ij.1.1 ij.1.2 *
      partialCorrelationPrefix z ij.1.2 ij.1.2)
    (correlationCoordinatesOfPartialCorrelation_add_single_self z · ij)

private theorem card_strictLowerTriangle_row_eq_col_gt (ab : strictLowerTriangle p) :
    ((Finset.univ : Finset (strictLowerTriangle p)).filter
      fun ij ↦ ij.1.1 = ab.1.1 ∧ ab.1.2 < ij.1.2).card =
      (Finset.Ioo ab.1.2 ab.1.1).card := by
  apply Finset.card_bij (fun ij _ ↦ ij.1.2)
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    exact Finset.mem_Ioo.2 ⟨hij.2, hij.1 ▸ ij.2⟩
  · intro ij₁ hij₁ ij₂ hij₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij₁ hij₂
    exact Subtype.ext (Prod.ext (hij₁.1.trans hij₂.1.symm) heq)
  · intro j hj
    let ij : strictLowerTriangle p := ⟨(ab.1.1, j), (Finset.mem_Ioo.1 hj).2⟩
    refine ⟨ij, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨rfl, (Finset.mem_Ioo.1 hj).1⟩

private theorem card_strictLowerTriangle_col_eq (ab : strictLowerTriangle p) :
    ((Finset.univ : Finset (strictLowerTriangle p)).filter
      fun ij ↦ ij.1.2 = ab.1.1).card = (Finset.Ioi ab.1.1).card := by
  apply Finset.card_bij (fun ij _ ↦ ij.1.1)
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    exact Finset.mem_Ioi.2 (hij ▸ ij.2)
  · intro ij₁ hij₁ ij₂ hij₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij₁ hij₂
    exact Subtype.ext (Prod.ext heq (hij₁.trans hij₂.symm))
  · intro i hi
    refine ⟨⟨(i, ab.1.1), Finset.mem_Ioi.1 hi⟩, ?_, rfl⟩
    simp

private theorem prod_partialCorrelationPrefix_first (z : strictLowerTriangle p → ℝ) :
    ∏ ij : strictLowerTriangle p, partialCorrelationPrefix z ij.1.1 ij.1.2 =
      ∏ ab : strictLowerTriangle p,
        Real.sqrt (1 - z ab ^ 2) ^ (ab.1.1.val - ab.1.2.val - 1) := by
  unfold partialCorrelationPrefix
  calc
    (∏ ij : strictLowerTriangle p,
        ∏ ab : strictLowerTriangle p with ab.1.1 = ij.1.1 ∧ ab.1.2 < ij.1.2,
          Real.sqrt (1 - z ab ^ 2)) =
        ∏ ij : strictLowerTriangle p, ∏ ab : strictLowerTriangle p,
          if ab.1.1 = ij.1.1 ∧ ab.1.2 < ij.1.2 then
            Real.sqrt (1 - z ab ^ 2) else 1 := by
      apply Finset.prod_congr rfl
      intro ij _
      rw [Finset.prod_ite]
      simp
    _ = ∏ ab : strictLowerTriangle p, ∏ ij : strictLowerTriangle p,
          if ab.1.1 = ij.1.1 ∧ ab.1.2 < ij.1.2 then
            Real.sqrt (1 - z ab ^ 2) else 1 := Finset.prod_comm
    _ = ∏ ab : strictLowerTriangle p,
          Real.sqrt (1 - z ab ^ 2) ^
            ((Finset.univ : Finset (strictLowerTriangle p)).filter
              fun ij ↦ ij.1.1 = ab.1.1 ∧ ab.1.2 < ij.1.2).card := by
      apply Finset.prod_congr rfl
      intro ab _
      have hfilter : (Finset.univ : Finset (strictLowerTriangle p)).filter
          (fun ij ↦ ab.1.1 = ij.1.1 ∧ ab.1.2 < ij.1.2) =
          Finset.univ.filter
            (fun ij ↦ ij.1.1 = ab.1.1 ∧ ab.1.2 < ij.1.2) := by
        ext ij
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_congr eq_comm Iff.rfl
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, hfilter, Finset.prod_const]
    _ = ∏ ab : strictLowerTriangle p,
          Real.sqrt (1 - z ab ^ 2) ^ (ab.1.1.val - ab.1.2.val - 1) := by
      apply Finset.prod_congr rfl
      intro ab _
      rw [card_strictLowerTriangle_row_eq_col_gt, Fin.card_Ioo]

private theorem prod_partialCorrelationPrefix_second (z : strictLowerTriangle p → ℝ) :
    ∏ ij : strictLowerTriangle p, partialCorrelationPrefix z ij.1.2 ij.1.2 =
      ∏ ab : strictLowerTriangle p,
        Real.sqrt (1 - z ab ^ 2) ^ (p - 1 - ab.1.1.val) := by
  unfold partialCorrelationPrefix
  calc
    (∏ ij : strictLowerTriangle p,
        ∏ ab : strictLowerTriangle p with ab.1.1 = ij.1.2 ∧ ab.1.2 < ij.1.2,
          Real.sqrt (1 - z ab ^ 2)) =
        ∏ ij : strictLowerTriangle p, ∏ ab : strictLowerTriangle p,
          if ab.1.1 = ij.1.2 ∧ ab.1.2 < ij.1.2 then
            Real.sqrt (1 - z ab ^ 2) else 1 := by
      apply Finset.prod_congr rfl
      intro ij _
      rw [Finset.prod_ite]
      simp
    _ = ∏ ab : strictLowerTriangle p, ∏ ij : strictLowerTriangle p,
          if ab.1.1 = ij.1.2 ∧ ab.1.2 < ij.1.2 then
            Real.sqrt (1 - z ab ^ 2) else 1 := Finset.prod_comm
    _ = ∏ ab : strictLowerTriangle p,
          Real.sqrt (1 - z ab ^ 2) ^
            ((Finset.univ : Finset (strictLowerTriangle p)).filter
              fun ij ↦ ij.1.2 = ab.1.1).card := by
      apply Finset.prod_congr rfl
      intro ab _
      have hfilter : (Finset.univ : Finset (strictLowerTriangle p)).filter
          (fun ij ↦ ab.1.1 = ij.1.2 ∧ ab.1.2 < ij.1.2) =
          Finset.univ.filter (fun ij ↦ ij.1.2 = ab.1.1) := by
        ext ij
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h ↦ h.1.symm
        · intro h
          exact ⟨h.symm, h ▸ ab.2⟩
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, hfilter, Finset.prod_const]
    _ = ∏ ab : strictLowerTriangle p,
          Real.sqrt (1 - z ab ^ 2) ^ (p - 1 - ab.1.1.val) := by
      apply Finset.prod_congr rfl
      intro ab _
      rw [card_strictLowerTriangle_col_eq, Fin.card_Ioi]

private theorem prod_partialCorrelationPrefix (z : strictLowerTriangle p → ℝ) :
    ∏ ij : strictLowerTriangle p,
        (partialCorrelationPrefix z ij.1.1 ij.1.2 *
          partialCorrelationPrefix z ij.1.2 ij.1.2) =
      ∏ ij : strictLowerTriangle p,
        Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.val - 2) := by
  rw [Finset.prod_mul_distrib, prod_partialCorrelationPrefix_first,
    prod_partialCorrelationPrefix_second, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ij _
  rw [← pow_add]
  congr 1
  omega

private theorem abs_det_fderiv_correlationCoordinatesOfPartialCorrelation_eq_prod_sqrt
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    |(fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).det| =
      ∏ ij : strictLowerTriangle p,
        Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.val - 2) := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (Pi.basisFun ℝ (strictLowerTriangle p))]
  have htri :
      (LinearMap.toMatrix (Pi.basisFun ℝ (strictLowerTriangle p))
        (Pi.basisFun ℝ (strictLowerTriangle p))
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z)).BlockTriangular
        (OrderDual.toDual ∘ strictLowerTriangleKey) :=
    blockTriangular_toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation hz
  rw [htri.det_eq_prod_diag
      (OrderDual.toDual.injective.comp strictLowerTriangleKey_injective),
    Finset.prod_congr rfl fun ij (_ : ij ∈ Finset.univ) ↦
      toMatrix_fderiv_correlationCoordinatesOfPartialCorrelation_diag hz ij,
    abs_of_pos, prod_partialCorrelationPrefix]
  exact Finset.prod_pos fun ij _ ↦ mul_pos
    (Finset.prod_pos fun ab hab ↦ Real.sqrt_pos.2 <| sub_pos.2 <|
      (sq_lt_one_iff_abs_lt_one _).2 (hz ab))
    (Finset.prod_pos fun ab hab ↦ Real.sqrt_pos.2 <| sub_pos.2 <|
      (sq_lt_one_iff_abs_lt_one _).2 (hz ab))

/-- **The Jacobian of partial-correlation coordinates.** On the open cube, the absolute
Jacobian determinant of the map to strictly lower correlation-matrix entries is the product
`∏ i > j, (1 - zᵢⱼ²) ^ ((p - j - 2) / 2)`.  The exponent uses real division. -/
theorem abs_det_fderiv_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    |(fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).det| =
      ∏ ij : strictLowerTriangle p,
        (1 - z ij ^ 2) ^ (((p - ij.1.2.val - 2 : ℕ) : ℝ) / 2) := by
  rw [abs_det_fderiv_correlationCoordinatesOfPartialCorrelation_eq_prod_sqrt hz]
  apply Finset.prod_congr rfl
  intro ij _
  have hbase : 0 < 1 - z ij ^ 2 := sub_pos.2 <|
    (sq_lt_one_iff_abs_lt_one _).2 (hz ij)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
  congr 1
  ring

end TauCeti
