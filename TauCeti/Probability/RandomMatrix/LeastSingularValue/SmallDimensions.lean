/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Process.Basic
import TauCeti.MeasureTheory.MeasurableSpace.Pi.SplitAt
import TauCeti.Probability.Independence.Integration
import TauCeti.Analysis.Matrix.MeasurableSpace
import TauCeti.Probability.Moments.SubGaussian.AntiConcentration
import TauCeti.Probability.Moments.SubGaussian.Basic
import TauCeti.Probability.Moments.SubGaussian.Matrix

/-!
# Uniform invertibility in bounded dimension

A single-entry anti-concentration bound gives a lower bound on the chance of a large
determinant, by induction on a principal minor. Together with the sub-Gaussian operator-norm
tail it gives a positive chance of a uniformly positive least singular value when the
dimension is bounded.
-/

public section

noncomputable section

open MeasureTheory Matrix Real Set
open scoped Matrix.Norms.L2Operator NNReal

namespace ProbabilityTheory.iIndepFun

private abbrev EntriesExceptTopLeft (n : ℕ) :=
  {ij : Fin (n + 1) × Fin (n + 1) // ij ≠ (0, 0)} → ℝ

/-- Reassemble the matrix by inserting its top-left entry. -/
private def fillTopLeft {n : ℕ} (p : EntriesExceptTopLeft n × ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j ↦ (MeasurableEquiv.piSplitAt (0, 0) (fun _ ↦ ℝ)).symm (p.2, p.1) (i, j)

private theorem submatrix_fillTopLeft {n : ℕ} (x : EntriesExceptTopLeft n) (z : ℝ)
    (f : Fin n → Fin (n + 1)) :
    (fillTopLeft (x, z)).submatrix Fin.succ f = (fillTopLeft (x, 0)).submatrix Fin.succ f := by
  ext i j
  have hne : (i.succ, f j) ≠ ((0, 0) : Fin (n + 1) × Fin (n + 1)) :=
    fun h ↦ Fin.succ_ne_zero i (congrArg Prod.fst h)
  simp only [fillTopLeft, submatrix_apply, Matrix.of_apply]
  rw [MeasurableEquiv.piSplitAt_symm_apply_ne _ _ _ hne,
    MeasurableEquiv.piSplitAt_symm_apply_ne _ _ _ hne]

private theorem det_fillTopLeft {n : ℕ} (x : EntriesExceptTopLeft n) (z : ℝ) :
    (fillTopLeft (x, z)).det =
      z * ((fillTopLeft (x, 0)).submatrix Fin.succ Fin.succ).det + (fillTopLeft (x, 0)).det := by
  have hfirst (v : ℝ) : fillTopLeft (x, v) 0 0 = v := by
    simpa only [fillTopLeft, Matrix.of_apply] using
      MeasurableEquiv.piSplitAt_symm_apply_self
        (α := fun _ : Fin (n + 1) × Fin (n + 1) ↦ ℝ) (0, 0) (v, x)
  have hrest (j : Fin n) : fillTopLeft (x, z) 0 j.succ = fillTopLeft (x, 0) 0 j.succ := by
    have hne : ((0 : Fin (n + 1)), j.succ) ≠ (0, 0) :=
      fun h ↦ Fin.succ_ne_zero j (congrArg Prod.snd h)
    simp only [fillTopLeft, Matrix.of_apply]
    rw [MeasurableEquiv.piSplitAt_symm_apply_ne _ _ _ hne,
      MeasurableEquiv.piSplitAt_symm_apply_ne _ _ _ hne]
  rw [Matrix.det_succ_row_zero (fillTopLeft (x, z)), Matrix.det_succ_row_zero (fillTopLeft (x, 0)),
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [submatrix_fillTopLeft, hfirst, hrest, Fin.val_zero, pow_zero, one_mul, zero_mul,
    zero_add, Fin.succAbove_zero]

private theorem mul_measureReal_abs_det_submatrix_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {A : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hind : iIndepFun (fun ij : Fin (n + 1) × Fin (n + 1) ↦ fun ω ↦ A ω ij.1 ij.2) P)
    (hA : AEMeasurable A P) {b r u : ℝ} (hu : 0 < u)
    (h : ∀ v : ℝ, b ≤ P.real {ω | r ≤ |A ω 0 0 - v|}) :
    b * P.real {ω | u ≤ |((A ω).submatrix Fin.succ Fin.succ).det|} ≤
      P.real {ω | r * u ≤ |(A ω).det|} := by
  have := hind.isProbabilityMeasure
  let ι := Fin (n + 1) × Fin (n + 1)
  let k : ι := (0, 0)
  let S := {j : ι // j ≠ k}
  let X (ω : Ω) (j : S) := A ω j.val.1 j.val.2
  let Y (ω : Ω) := A ω 0 0
  have hm (ij : ι) : AEMeasurable (fun ω ↦ A ω ij.1 ij.2) P :=
    Matrix.measurable_apply.comp_aemeasurable hA
  have hind' : IndepFun X Y P := by
    have hS : Disjoint {j | j ≠ k} {k} := by simp [disjoint_singleton_right]
    exact (hind.indepFun_set₀ hS hm).comp measurable_id
      (measurable_pi_apply ⟨k, mem_singleton k⟩)
  have hM : Measurable (@fillTopLeft n) := by
    apply Measurable.of_eval_matrix
    intro i j
    exact (measurable_pi_apply (i, j)).comp
      ((MeasurableEquiv.piSplitAt k (fun _ ↦ ℝ)).symm.measurable.comp measurable_swap)
  have heq (ω : Ω) : fillTopLeft (X ω, Y ω) = A ω := by
    ext i j
    let e := MeasurableEquiv.piSplitAt k (fun _ ↦ ℝ)
    have h : (Y ω, X ω) = e (fun ij ↦ A ω ij.1 ij.2) := by
      rw [show e = MeasurableEquiv.piSplitAt k (fun _ ↦ ℝ) from rfl,
        MeasurableEquiv.piSplitAt_apply]
    exact congrFun (e.symm_apply_eq.mpr h) (i, j)
  let a (x : S → ℝ) := ((fillTopLeft (x, 0)).submatrix Fin.succ Fin.succ).det
  let F : Set ((S → ℝ) × ℝ) := {p | r * u ≤ |(fillTopLeft p).det|}
  let G : Set (S → ℝ) := {x | u ≤ |a x|}
  have hF : MeasurableSet F := measurableSet_le measurable_const
    (by simpa only [Real.norm_eq_abs] using (Measurable.matrix_det hM).norm)
  have hG : MeasurableSet G := by
    apply measurableSet_le measurable_const
    have h : Measurable a :=
      (continuous_id.matrix_submatrix Fin.succ Fin.succ).matrix_det.measurable.comp
        (hM.comp (measurable_id.prodMk measurable_const))
    simpa only [Real.norm_eq_abs] using h.norm
  have hG_eq : X ⁻¹' G = {ω | u ≤ |((A ω).submatrix Fin.succ Fin.succ).det|} := by
    ext ω
    have he := submatrix_fillTopLeft (X ω) (Y ω) Fin.succ
    rw [heq] at he
    simp only [G, mem_preimage, mem_ofPred_eq, a, ← he]
  have hF_eq : (fun ω ↦ (X ω, Y ω)) ⁻¹' F = {ω | r * u ≤ |(A ω).det|} := by
    ext ω
    simp [F, heq]
  rw [← hG_eq, ← hF_eq]
  refine hind'.mul_measureReal_preimage_le (.of_eval fun j ↦ hm j) (hm k) hF hG ?_
  intro x hx
  have hax : u ≤ |a x| := hx
  have hax0 : a x ≠ 0 := abs_pos.mp (hu.trans_le hax)
  let v := -(fillTopLeft (x, 0)).det / a x
  refine (h v).trans (measureReal_mono ?_)
  intro ω hω
  have hfactor : Y ω * a x + (fillTopLeft (x, 0)).det = (Y ω - v) * a x := by
    dsimp [v]
    field_simp
    ring
  rw [mem_preimage, mem_preimage, mem_ofPred_eq, det_fillTopLeft, hfactor, abs_mul]
  exact mul_le_mul hω hax hu.le (abs_nonneg _)

/-- If every entry of an independent real square matrix has probability at least `b` of
lying outside any open interval of radius `r`, its determinant has absolute value at least
`r ^ n` with probability at least `b ^ n`. -/
theorem pow_le_measureReal_abs_det_ge {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {A : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hind : iIndepFun (fun ij : Fin n × Fin n ↦ fun ω ↦ A ω ij.1 ij.2) P)
    (hA : AEMeasurable A P) {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r)
    (h : ∀ i j v, b ≤ P.real {ω | r ≤ |A ω i j - v|}) :
    b ^ n ≤ P.real {ω | r ^ n ≤ |(A ω).det|} := by
  have := hind.isProbabilityMeasure
  induction n with
  | zero => simp
  | succ n ih =>
    let B (ω : Ω) := (A ω).submatrix Fin.succ Fin.succ
    have hB : AEMeasurable B P :=
      (continuous_id.matrix_submatrix Fin.succ Fin.succ).measurable.comp_aemeasurable hA
    have hBi : iIndepFun (fun ij : Fin n × Fin n ↦ fun ω ↦ B ω ij.1 ij.2) P :=
      hind.precomp (g := fun p : Fin n × Fin n ↦ (p.1.succ, p.2.succ))
        ((Fin.succ_injective n).prodMap (Fin.succ_injective n))
    rw [pow_succ', pow_succ']
    exact (mul_le_mul_of_nonneg_left (ih hBi hB fun i j v ↦ h i.succ j.succ v) hb).trans
      (mul_measureReal_abs_det_submatrix_le hind hA (pow_pos hr _) (h 0 0))

private theorem le_measureReal_abs_det_ge_of_subgaussian
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {P : Measure Ω} {A : Ω → Matrix n n ℝ} {K : ℝ≥0}
    (hind : iIndepFun (fun ij : n × n ↦ fun ω ↦ A ω ij.1 ij.2) P)
    (hA : ∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P)
    (hvar : ∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) :
    let b := min (1 / 2) ((1 - (1 / 2 : ℝ) ^ 2) ^ 2 / (256 * √2 * ((K : ℝ) + 1) ^ 2))
    b ^ Fintype.card n ≤ P.real {ω | (1 / 2 : ℝ) ^ Fintype.card n ≤ |(A ω).det|} := by
  intro b
  have := hind.isProbabilityMeasure
  let e := (Fintype.equivFin n).symm
  let B (ω : Ω) := (A ω).submatrix e e
  have hB : AEMeasurable B P :=
    .of_eval fun i ↦ .of_eval fun j ↦ (hA (e i) (e j)).aemeasurable
  have hBi : iIndepFun (fun ij : Fin (Fintype.card n) × Fin (Fintype.card n) ↦
      fun ω ↦ B ω ij.1 ij.2) P :=
    hind.precomp (g := fun ij : Fin (Fintype.card n) × Fin (Fintype.card n) ↦ (e ij.1, e ij.2))
      (e.injective.prodMap e.injective)
  have hBdet (ω : Ω) : (B ω).det = (A ω).det := Matrix.det_submatrix_equiv_self e _
  simp_rw [← hBdet]
  refine hBi.pow_le_measureReal_abs_det_ge hB (by dsimp [b]; positivity) (by norm_num)
    fun i j v ↦ ?_
  let Z (ω : Ω) := A ω (e i) (e j)
  let E : Set Ω := {ω | |Z ω - v| ≤ 1 / 2}
  have hm : NullMeasurableSet E P :=
    nullMeasurableSet_le (by simpa only [Real.norm_eq_abs] using
      ((hA (e i) (e j)).aemeasurable.sub_const v).norm) aemeasurable_const
  have hsub := (hA (e i) (e j)).mono (le_add_of_nonneg_right zero_le_one)
  have hle := hsub.measureReal_abs_sub_le_le_one_sub_div (hvar (e i) (e j)) v
    (r := 1 / 2) (by norm_num)
  have hle' : P.real E ≤ 1 - b := by
    refine hle.trans (sub_le_sub_left ?_ 1)
    push_cast
    exact min_le_right _ _
  have hb' : b ≤ P.real Eᶜ := by
    rw [measureReal_compl₀ hm, probReal_univ]
    exact le_sub_comm.mp hle'
  refine hb'.trans (measureReal_mono fun ω hω ↦ ?_)
  have ht : ¬ |Z ω - v| ≤ 1 / 2 := hω
  exact (not_le.mp ht).le

private theorem abs_det_le_l2_opNorm_pow_mul_singularValues
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hn : 0 < Fintype.card n) :
    |A.det| ≤ ‖A‖ ^ (Fintype.card n - 1) *
      (toEuclideanLin A).singularValues (Fintype.card n - 1) := by
  have h := (toEuclideanLin A).normDet_le_norm_pow_mul_minimalStretch
    (by simpa only [finrank_euclideanSpace] using hn)
  rw [LinearMap.minimalStretch_def, finrank_euclideanSpace] at h
  have heq : (toEuclideanLin A).normDet = |A.det| := by
    rw [(toEuclideanLin A).normDet_eq_norm_det_toMatrix
      (EuclideanSpace.basisFun n ℝ) (EuclideanSpace.basisFun n ℝ),
      Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin, Real.norm_eq_abs]
  rw [heq] at h
  simpa only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] using h

/-- For independent real sub-Gaussian entries of second moments at least one, square matrices
of positive size at most `N` have a uniformly positive probability of a least singular value
bounded below by a positive constant. No equality of entry laws is required. -/
theorem exists_le_measureReal_singularValues_card_sub_one_ge_of_card_le (K : ℝ≥0) (N : ℕ) :
    ∃ u p : ℝ, 0 < u ∧ 0 < p ∧ p < 1 ∧
      ∀ {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] {P : Measure Ω}
        {A : Ω → Matrix n n ℝ},
        iIndepFun (fun ij : n × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        0 < Fintype.card n → Fintype.card n ≤ N →
        p ≤ P.real {ω | u ≤ (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1)} := by
  let b := min (1 / 2) ((1 - (1 / 2 : ℝ) ^ 2) ^ 2 / (256 * √2 * ((K : ℝ) + 1) ^ 2))
  have hb : 0 < b := by dsimp [b]; positivity
  have hb₁ : b ≤ 1 := (min_le_left _ _).trans (by norm_num)
  let p := b ^ N / 2
  have hp : 0 < p := by dsimp [p]; positivity
  have hp' : p < 1 := by
    have h := pow_le_one₀ hb.le hb₁ (n := N)
    dsimp [p]
    linarith
  let t := √(log (2 / p))
  have ht₂ : t ^ 2 = log (2 / p) :=
    sq_sqrt (log_nonneg ((le_div_iff₀ hp).2 (by linarith)))
  have htail : 2 * exp (-(t ^ 2)) = p := by
    rw [ht₂, exp_neg, exp_log (by positivity)]
    field_simp
  let R := max 1 (8 * ((K : ℝ) + 1) * (√N + √N + t))
  have hR : 1 ≤ R := le_max_left _ _
  let u := (1 / 2 : ℝ) ^ N / R ^ (N - 1)
  refine ⟨u, p, by dsimp [u]; positivity, hp, hp', ?_⟩
  intro Ω n _ _ _ P A hind hA hvar hn hN
  have := hind.isProbabilityMeasure
  let d := Fintype.card n
  have hK : K ≤ (K + 1) ^ 2 := by
    exact_mod_cast (show (K : ℝ) ≤ ((K : ℝ) + 1) ^ 2 by nlinarith [K.coe_nonneg])
  let G : Set Ω := {ω | (1 / 2 : ℝ) ^ d ≤ |(A ω).det|}
  let E : Set Ω := {ω | R < ‖A ω‖}
  have hG : b ^ d ≤ P.real G := le_measureReal_abs_det_ge_of_subgaussian hind hA hvar
  have hE : P.real E ≤ p := by
    refine (measureReal_mono (s₂ := {ω | 8 * ((K : ℝ) + 1) * (√d + √d + t) < ‖A ω‖})
      ?_ (measure_ne_top _ _)).trans ?_
    · intro ω hω
      have hdN : √(d : ℝ) ≤ √N := sqrt_le_sqrt (by exact_mod_cast hN)
      have h : 8 * ((K : ℝ) + 1) * (√d + √d + t) ≤
          8 * ((K : ℝ) + 1) * (√N + √N + t) := by gcongr
      exact (h.trans (le_max_right _ _)).trans_lt hω
    · simpa only [NNReal.coe_add, NNReal.coe_one, htail] using
        hind.measureReal_matrix_l2_opNorm_gt_le (fun i j ↦ (hA i j).mono hK)
          (t := t) (sqrt_nonneg _)
  have hsmall : G \ E ⊆ {ω | u ≤ (toEuclideanLin (A ω)).singularValues (d - 1)} := by
    rintro ω ⟨hω, hωE⟩
    have hnorm : ‖A ω‖ ≤ R := le_of_not_gt hωE
    have hdet := abs_det_le_l2_opNorm_pow_mul_singularValues (A ω) hn
    have hpow : ‖A ω‖ ^ (d - 1) ≤ R ^ (N - 1) :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm _).trans
        (pow_le_pow_right₀ hR (Nat.sub_le_sub_right hN _))
    apply (div_le_iff₀ (by positivity : 0 < R ^ (N - 1))).2
    rw [mul_comm]
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hN).trans
      ((mem_ofPred.mp hω).trans (hdet.trans
        (mul_le_mul_of_nonneg_right hpow (LinearMap.singularValues_nonneg _ _))))
  refine le_trans ?_ ((le_measureReal_sdiff (s₁ := G) (s₂ := E)).trans
    (measureReal_mono hsmall))
  have hbd : b ^ N ≤ b ^ d := pow_le_pow_of_le_one hb.le hb₁ hN
  dsimp [p] at hE ⊢
  linarith

end ProbabilityTheory.iIndepFun
