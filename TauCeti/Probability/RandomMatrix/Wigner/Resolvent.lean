/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Probability.RandomMatrix.QuadraticForm
public import TauCeti.Analysis.Matrix.Resolvent.SelfConsistency
public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence
import TauCeti.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The Wigner resolvent equation

For Wigner matrices with independent directionally sub-Gaussian upper entries, the Schur
complement expresses each diagonal resolvent entry in terms of an independent quadratic form.
Hanson–Wright concentration bounds the error simultaneously over the deleted columns, and the
imaginary part of the resolvent trace selects the stable root of the semicircle equation.

## References

* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology NNReal ENNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}

section Fluctuations

variable {K v : ℝ≥0}
  (hξ : ∀ ij (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * ξ ij ω).re) (‖u‖₊ ^ 2 * K) P)

include hξ in
private theorem hasSubgaussianMGF_wignerMatrix_apply_of_ne {n : ℕ} {i j : Fin (n + 1)}
    (hij : i ≠ j) (u : ℂ) :
    HasSubgaussianMGF (fun ω ↦ (star u * wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j).re)
      (‖u‖₊ ^ 2 * (K / (n + 1 : ℝ≥0))) P := by
  have hproxy (w : ℂ) : NNReal.mk ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ ^ 2) (sq_nonneg _) *
      (‖w‖₊ ^ 2 * K) =
      ‖w‖₊ ^ 2 * (K / (n + 1 : ℝ≥0)) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
      NNReal.coe_mk, inv_pow, Nat.cast_add, Nat.cast_one]
    rw [Real.sq_sqrt (by positivity)]
    ring
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · have hf := (hξ ⟨(i.val, j.val), h⟩ u).const_mul (√((n + 1 : ℕ) : ℝ))⁻¹
    simpa only [wignerMatrix_apply_of_lt _ _ _ h, ← Complex.ofReal_inv, mul_left_comm,
      Complex.re_ofReal_mul] using hf.mono (hproxy u).le
  · have hre (ω : Ω) :
        (star u * star (ξ ⟨(j.val, i.val), h⟩ ω)).re =
          (star (star u) * ξ ⟨(j.val, i.val), h⟩ ω).re := by
      simp [Complex.mul_re]
    have hf := (hξ ⟨(j.val, i.val), h⟩ (star u)).const_mul (√((n + 1 : ℕ) : ℝ))⁻¹
    simpa only [wignerMatrix_apply_of_gt _ _ _ h, ← Complex.ofReal_inv, mul_left_comm,
      Complex.re_ofReal_mul, hre, nnNorm_star] using hf.mono (hproxy (star u)).le

private def wignerMinorResolvent {n : ℕ} (i : Fin (n + 1)) (z : ℂ) (ω : Ω) :
    Matrix {j // j ≠ i} {j // j ≠ i} ℂ :=
  ((wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).submatrix (↑) (↑) - z • 1)⁻¹

private def wignerQuadraticError {n : ℕ} (i : Fin (n + 1)) (z : ℂ) (v : ℝ≥0) (ω : Ω) : ℂ :=
  let a : {j // j ≠ i} → ℂ := fun j ↦ wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω j i
  star a ⬝ᵥ wignerMinorResolvent (ξ := ξ) i z ω *ᵥ a -
    ((v : ℂ) / ((n + 1 : ℕ) : ℂ)) * (wignerMinorResolvent (ξ := ξ) i z ω).trace

include hξ in
private theorem wignerQuadraticError_tail (hind : iIndepFun ξ P)
    (hv : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = v) {n : ℕ} (i : Fin (n + 1))
    {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    P.real {ω | t < ‖wignerQuadraticError (ξ := ξ) i z v ω‖} ≤
      2 * Real.exp (-(1 / 150528) *
        min (t ^ 2 * z.im ^ 2 / (K : ℝ) ^ 2) (t * z.im / (K : ℝ)) * (n + 1)) := by
  let a (j : {j // j ≠ i}) (ω : Ω) := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω j i
  let A (ω : Ω) : Matrix {j // j ≠ i} {j // j ≠ i} ℂ :=
    (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).submatrix (↑) (↑)
  have hm (ij : StrictUpper) := (integrable_of_hasSubgaussianMGF_re_star_mul (hξ ij)).aemeasurable
  have hW := aemeasurable_wignerMatrix (n := n + 1) (η := fun _ _ ↦ 0) (fun ij _ ↦ hm ij)
    (fun _ _ ↦ aemeasurable_const)
  have hA : AEMeasurable A P := .of_eval fun j ↦ .of_eval fun k ↦
    (Matrix.measurable_apply (i := j.val) (j := k.val)).comp_aemeasurable hW
  have hi : IndepFun A (fun ω j ↦ a j ω) P :=
    indepFun_submatrix_wignerMatrix_zero_column hind hm i
  have hia : iIndepFun a P := iIndepFun_wignerMatrix_apply_of_ne Subtype.val (fun _ ↦ i)
    Subtype.property (fun j k h ↦ Subtype.ext (((Sym2.eq_iff.mp h).resolve_right
      fun he ↦ j.property he.1).1)) (hind.precomp Subtype.val_injective)
  have ha (j : {j // j ≠ i}) : ∫ ω, ‖a j ω‖ ^ 2 ∂P = (v : ℝ) / (n + 1) := by
    simp only [a, norm_wignerMatrix_apply_sq_of_ne _ _ _ j.property, integral_const_mul,
      hv, Nat.cast_add, Nat.cast_one]
    ring
  have hcard : (Fintype.card {j // j ≠ i} : ℝ) ≤ n + 1 := by
    have hc := Fintype.card_le_of_injective (Subtype.val : {j // j ≠ i} → Fin (n + 1))
      Subtype.val_injective
    exact_mod_cast hc.trans_eq (Fintype.card_fin (n + 1))
  have htail := hia.measureReal_norm_star_dotProduct_inv_sub_smul_one_mulVec_sub_smul_trace_gt_le
    (fun j ↦ hasSubgaussianMGF_wignerMatrix_apply_of_ne hξ j.property) ha hA
    (.of_forall fun ω ↦ (wignerMatrix_isHermitian ξ _ ω _).submatrix _) hi z 1 hcard (t := t)
  simp only [Complex.ofReal_one, one_mul, one_pow, abs_one, abs_of_pos hz] at htail
  have hd : 0 < (n + 1 : ℝ) := by positivity
  have hr₁ : t ^ 2 / (((K : ℝ) / (n + 1)) ^ 2 * (n + 1) * z.im⁻¹ ^ 2) =
      t ^ 2 * z.im ^ 2 / (K : ℝ) ^ 2 * (n + 1) := by
    by_cases hK : (K : ℝ) = 0
    · simp [hK]
    field_simp [hd.ne', hz.ne']
  have hr₂ : t / (((K : ℝ) / (n + 1)) * z.im⁻¹) =
      t * z.im / (K : ℝ) * (n + 1) := by
    by_cases hK : (K : ℝ) = 0
    · simp [hK]
    field_simp [hd.ne', hz.ne']
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
    ← mul_assoc] at htail
  rw [hr₁, hr₂, ← min_mul_of_nonneg _ _ hd.le, ← mul_assoc] at htail
  simpa only [wignerQuadraticError, a, A, wignerMinorResolvent, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Nat.cast_add, Nat.cast_one]
    using htail

omit [MeasurableSpace Ω] in
private theorem norm_wignerTransform_sub_le {n : ℕ} {z : ℂ} (hz : 0 < z.im)
    (ω : Ω) (v : ℝ≥0) (t : ℝ)
    (ht : ∀ i : Fin (n + 1), ‖wignerQuadraticError (ξ := ξ) i z v ω‖ ≤ t) :
    let A := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
    let hA := wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
      resolventTransform (semicircleReal 0 v) z‖ ≤
      (t + 3 * (v : ℝ) / ((n + 1) * z.im)) / z.im ^ 2 := by
  intro A hA
  let m := resolventTransform (A.spectralMeasure hA : Measure ℝ) z
  let R := (A - z • 1)⁻¹
  have hm : m = (((n + 1 : ℕ) : ℂ))⁻¹ * R.trace := by
    simpa only [Fintype.card_fin] using
      resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hz.ne')
  have hbound (i : Fin (n + 1)) :
      ‖(v : ℂ) / ((n + 1 : ℕ) : ℂ) * (wignerMinorResolvent (ξ := ξ) i z ω).trace -
        (v : ℂ) * m‖ ≤ 3 * (v : ℝ) / ((n + 1) * z.im) := by
    rw [hm, div_eq_mul_inv, ← mul_assoc, ← mul_sub, norm_mul, norm_mul, norm_inv,
      Complex.norm_natCast]
    have h := hA.norm_trace_inv_sub_smul_one_sub_trace_submatrix_le i hz.ne'
    rw [abs_of_pos hz, ← norm_sub_rev] at h
    simp only [R, A, wignerMinorResolvent, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg v.coe_nonneg, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ((v : ℝ) * (n + 1 : ℝ)⁻¹) * (3 / z.im) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by simp only [div_eq_mul_inv, _root_.mul_inv_rev]; ring
  have hentry (i : Fin (n + 1)) :
      ‖(v : ℂ) * m - star (fun j : {j // j ≠ i} ↦ A j i) ⬝ᵥ
        (wignerMinorResolvent (ξ := ξ) i z ω *ᵥ fun j : {j // j ≠ i} ↦ A j i)‖ ≤
        t + 3 * (v : ℝ) / ((n + 1) * z.im) := by
    rw [norm_sub_rev]
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (ht i) (hbound i))
  have hres := hA.norm_resolventTransform_spectralMeasure_quadratic_le hz (v : ℂ)
  dsimp only at hres
  have hs := norm_sub_resolventTransform_semicircleReal_le (a := 0) (v := v) hz
    (w := m) (im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz).le
  rw [Complex.ofReal_zero, sub_zero] at hs
  have hquad : ‖(v : ℂ) * (m * m) + z * m + 1‖ ≤
      (t + 3 * (v : ℝ) / ((n + 1) * z.im)) / z.im := hres.trans (by
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ (z.im * (n + 1))⁻¹ * ∑ _ : Fin (n + 1), (t + 3 * (v : ℝ) / ((n + 1) * z.im)) := by
        gcongr with i _
        simpa only [A, wignerMatrix_apply_self, Complex.ofReal_zero, mul_zero, zero_add,
          wignerMinorResolvent] using hentry i
      _ = (t + 3 * (v : ℝ) / ((n + 1) * z.im)) / z.im := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_one, _root_.mul_inv_rev, div_eq_mul_inv]
        field_simp)
  exact hs.trans ((div_le_div_of_nonneg_right hquad hz.le).trans_eq (by rw [div_div, sq]))

include hξ in
/-- At a fixed upper-half-plane parameter, the Wigner transform deviates from the
semicircle transform with exponentially small probability. The threshold includes the
deterministic principal-minor trace correction. The bound allows varying upper-entry laws. -/
theorem measureReal_norm_resolventTransform_wignerMatrix_zero_sub_semicircleReal_gt_le
    (hind : iIndepFun ξ P) (hv : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = v) (n : ℕ)
    {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    P.real {ω | (t + 3 * (v : ℝ) / ((n + 1) * z.im)) / z.im ^ 2 <
      ‖resolventTransform ((wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z -
        resolventTransform (semicircleReal 0 v) z‖} ≤
      2 * (n + 1) * Real.exp (-(1 / 150528) *
        min (t ^ 2 * z.im ^ 2 / (K : ℝ) ^ 2) (t * z.im / (K : ℝ)) * (n + 1)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let E (i : Fin (n + 1)) := {ω | t < ‖wignerQuadraticError (ξ := ξ) i z v ω‖}
  refine (measureReal_mono (s₂ := ⋃ i, E i) ?_).trans ((measureReal_iUnion_fintype_le E).trans ?_)
  · intro ω hω
    by_contra hnone
    have hi (i : Fin (n + 1)) : ‖wignerQuadraticError (ξ := ξ) i z v ω‖ ≤ t :=
      le_of_not_gt fun hi ↦ hnone (Set.mem_iUnion.2 ⟨i, hi⟩)
    exact (not_lt_of_ge (norm_wignerTransform_sub_le hz ω v t hi)) hω
  · refine (Finset.sum_le_sum fun i _ ↦ wignerQuadraticError_tail hξ hind hv i hz t).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    ring

include hξ in
/-- The fixed-parameter Wigner resolvent transforms converge almost surely for independent
directionally sub-Gaussian upper entries of common second moment. -/
theorem ae_tendsto_resolventTransform_wignerMatrix_zero_of_hasSubgaussianMGF
    (hind : iIndepFun ξ P) (hv : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = v) {z : ℂ} (hz : 0 < z.im) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      resolventTransform ((wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z)
      atTop (𝓝 (resolventTransform (semicircleReal 0 v) z)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let L : ℝ≥0 := max K 1
  have hL : 0 < (L : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast le_max_right K 1)
  have hXL ij u := (hξ ij u).mono (mul_le_mul_of_nonneg_left (le_max_left K 1) (by positivity))
  let s := resolventTransform (semicircleReal 0 v) z
  let m (n : ℕ) (ω : Ω) := resolventTransform
    ((wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z
  have hsmall : Tendsto (fun n : ℕ ↦ 3 * (v : ℝ) / ((n + 1) * z.im)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using
      tendsto_const_nhds.div_atTop (hn.atTop_mul_const hz)
  have hbc (j : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ‖m n ω - s‖ ≤ (j + 1 : ℝ)⁻¹ := by
    let t := (j + 1 : ℝ)⁻¹ * z.im ^ 2 / 2
    have ht : 0 < t := by positivity
    let c := (1 / 150528 : ℝ) *
      min (t ^ 2 * z.im ^ 2 / (L : ℝ) ^ 2) (t * z.im / (L : ℝ))
    have hc : 0 < c :=
      mul_pos (by norm_num) (lt_min (div_pos (by positivity) (sq_pos_of_pos hL))
        (div_pos (mul_pos ht hz) hL))
    have hs : Summable (fun n : ℕ ↦ 2 * (n + 1 : ℝ) * Real.exp (-c * (n + 1))) := by
      simpa only [pow_one, Nat.cast_add, Nat.cast_one, mul_assoc] using
        ((summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul 1 hc)).mul_left 2
    let E (n : ℕ) := {ω | (j + 1 : ℝ)⁻¹ < ‖m n ω - s‖}
    have htail : Summable (fun n ↦ P.real (E n)) := by
      apply hs.of_norm_bounded_eventually_nat
      filter_upwards [hsmall.eventually (eventually_lt_nhds ht)] with n hn
      have hthreshold : (t + 3 * (v : ℝ) / ((n + 1) * z.im)) / z.im ^ 2 ≤ (j + 1 : ℝ)⁻¹ := by
        rw [div_le_iff₀ (by positivity)]
        dsimp [t] at *
        linarith
      rw [Real.norm_of_nonneg measureReal_nonneg]
      have h := measureReal_norm_resolventTransform_wignerMatrix_zero_sub_semicircleReal_gt_le
        hXL hind hv n hz t
      exact (measureReal_mono (fun _ h ↦ hthreshold.trans_lt h) (measure_ne_top _ _)).trans
        (by simpa only [c, neg_mul] using h)
    have hfinite : (∑' n, P (E n)) ≠ ∞ := by
      simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        htail.tsum_ofReal_ne_top
    simpa only [E, Set.mem_ofPred_eq, not_lt] using ae_eventually_notMem hfinite
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω j] with n hn
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using
    hn.trans_lt (by simpa only [one_div] using hj)

include hξ in
/-- The Wigner empirical spectral measures converge weakly almost surely for independent
directionally sub-Gaussian upper entries with common second absolute moment `v`. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_zero_of_hasSubgaussianMGF
    (hind : iIndepFun ξ P) (hv : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = v) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))) atTop
      (𝓝 (⟨semicircleReal 0 v, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  ProbabilityMeasure.ae_tendsto_of_ae_tendsto_resolventTransform fun _ hz ↦
    ae_tendsto_resolventTransform_wignerMatrix_zero_of_hasSubgaussianMGF hξ hind hv hz

end Fluctuations

end TauCeti.Probability
