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
import TauCeti.Analysis.Convex.FiniteMean
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

namespace Matrix.IsHermitian

/-- The difference from the semicircle transform is controlled by the mean absolute
leave-one-out error and the principal-minor trace correction. This is the averaged form of
the uniform-threshold estimate in the original sub-Gaussian Wigner resolvent argument. -/
theorem norm_resolventTransform_spectralMeasure_sub_semicircleReal_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hd : ∀ i, A i i = 0) {z : ℂ} (hz : 0 < z.im) (v : ℝ≥0) :
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
      resolventTransform (TauCeti.Probability.semicircleReal 0 v) z‖ ≤
      z.im⁻¹ ^ 2 * (TauCeti.finiteMean ℝ (fun i ↦ ‖A.minorQuadraticError i z v‖) +
        3 * (v : ℝ) / ((Fintype.card ι : ℝ) * z.im)) := by
  let m := resolventTransform (A.spectralMeasure hA : Measure ℝ) z
  let c := 3 * (v : ℝ) / ((Fintype.card ι : ℝ) * z.im)
  have hs := TauCeti.Probability.norm_sub_resolventTransform_semicircleReal_le
    (a := 0) (v := v) hz (w := m)
    (im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz).le
  rw [Complex.ofReal_zero, sub_zero] at hs
  have hentry (i : ι) :
      ‖(v : ℂ) * m - star (fun j : {j // j ≠ i} ↦ A j i) ⬝ᵥ
        (A.minorResolvent i z *ᵥ fun j : {j // j ≠ i} ↦ A j i)‖ ≤
      ‖A.minorQuadraticError i z v‖ + c := by
    rw [minorQuadraticError_def, norm_sub_rev]
    refine (norm_sub_le_norm_sub_add_norm_sub _
      (((v : ℂ) / (Fintype.card ι : ℂ)) * (A.minorResolvent i z).trace) _).trans
      (add_le_add le_rfl ?_)
    rw [div_eq_mul_inv, mul_assoc, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg v.coe_nonneg]
    have h := hA.norm_normalized_minor_trace_sub_resolventTransform_le hz.ne' i
    rw [abs_of_pos hz] at h
    exact (mul_le_mul_of_nonneg_left h v.coe_nonneg).trans_eq (by unfold c; ring)
  have hres := hA.norm_resolventTransform_spectralMeasure_quadratic_le hz (v : ℂ)
  simp only [hd, zero_add] at hres
  have hbound := hres.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ ↦ hentry i) (by positivity))
  refine hs.trans ((div_le_div_of_nonneg_right hbound hz.le).trans_eq ?_)
  rw [← TauCeti.finiteMean_add_const, TauCeti.finiteMean_eq_inv_smul_sum, smul_eq_mul]
  ring

end Matrix.IsHermitian

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

include hξ in
private theorem wignerQuadraticError_tail (hind : iIndepFun ξ P)
    (hv : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = v) {n : ℕ} (i : Fin (n + 1))
    {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    P.real {ω | t < ‖(wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).minorQuadraticError i z v‖} ≤
      2 * Real.exp (-(1 / 150528) *
        min (t ^ 2 * z.im ^ 2 / (K : ℝ) ^ 2) (t * z.im / (K : ℝ)) * (n + 1)) := by
  have hm (ij : StrictUpper) := (integrable_of_hasSubgaussianMGF_re_star_mul (hξ ij)).aemeasurable
  obtain ⟨hA, hi, hia, ha⟩ := wignerMatrix_zero_minor_column
    (hind.precomp Subtype.val_injective) (fun ij _ ↦ hm ij) (fun ij _ ↦ hv ij) i
  have hcard : (Fintype.card {j // j ≠ i} : ℝ) ≤ n + 1 := by
    exact_mod_cast (Fintype.card_subtype_le (fun j : Fin (n + 1) ↦ j ≠ i)).trans_eq
      (Fintype.card_fin (n + 1))
  have htail := hia.measureReal_norm_star_dotProduct_inv_sub_smul_one_mulVec_sub_smul_trace_gt_le
    (fun j ↦ hasSubgaussianMGF_wignerMatrix_apply_of_ne hξ j.property)
    (fun j ↦ by simpa only [Nat.cast_succ] using ha j) hA
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
  simpa only [Matrix.minorQuadraticError_def, Matrix.minorResolvent_def, Fintype.card_fin,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Nat.cast_add, Nat.cast_one]
    using htail

omit [MeasurableSpace Ω] in
private theorem norm_wignerTransform_sub_le {n : ℕ} {z : ℂ} (hz : 0 < z.im)
    (ω : Ω) (v : ℝ≥0) (t : ℝ)
    (ht : ∀ i : Fin (n + 1),
      ‖(wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).minorQuadraticError i z v‖ ≤ t) :
    let A := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
    let hA := wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
      resolventTransform (semicircleReal 0 v) z‖ ≤
      (t + 3 * (v : ℝ) / ((n + 1) * z.im)) / z.im ^ 2 := by
  intro A hA
  have h := hA.norm_resolventTransform_spectralMeasure_sub_semicircleReal_le
    (by simp) hz v
  have hmean : finiteMean ℝ (fun i ↦ ‖A.minorQuadraticError i z v‖) ≤ t := by
    refine (finiteMean_mono (g := fun _ ↦ t) ht).trans_eq ?_
    rw [finiteMean_def]
    exact Finset.centerMass_const (by simpa using (show (0 : ℝ) < n + 1 by positivity).ne') t
  have h' := h.trans (mul_le_mul_of_nonneg_left (add_le_add hmean le_rfl) (sq_nonneg _))
  simpa only [Fintype.card_fin, Nat.cast_succ, inv_pow, div_eq_inv_mul] using h'

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
  let E (i : Fin (n + 1)) :=
    {ω | t < ‖(wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).minorQuadraticError i z v‖}
  refine (measureReal_mono (s₂ := ⋃ i, E i) ?_).trans ((measureReal_iUnion_fintype_le E).trans ?_)
  · intro ω hω
    by_contra hnone
    have hi (i : Fin (n + 1)) :
        ‖(wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).minorQuadraticError i z v‖ ≤ t :=
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
