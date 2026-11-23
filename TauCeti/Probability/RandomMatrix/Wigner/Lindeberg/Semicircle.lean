/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Lindeberg.Basic
public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
public import TauCeti.Analysis.Matrix.Resolvent.SelfConsistency
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Probability.Moments.QuadraticForm.SecondMoment
import TauCeti.Probability.RandomMatrix.Wigner.Diagonal
import TauCeti.Analysis.Matrix.Resolvent.Semicircle
import TauCeti.Analysis.Matrix.Resolvent.Measurable
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Matrix.SpectralMeasure.ResolventStability
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.ResolventTransform.InProbability

/-!
# The Wigner semicircle law for Lindeberg arrays

For triangular Wigner arrays, the resolvent trace is controlled by the average of the absolute
leave-one-out quadratic-form errors and a minor-trace correction that vanishes as the dimension
grows. Off-diagonal products are bounded
using only second moments. The truncation of the squared entries controls the diagonal
part of each quadratic form, and its discarded second moments appear in the Lindeberg sum.
A diagonal with vanishing normalized mean-square norm contributes a separate error.

The sample spaces can vary with the size of the matrix.
`MeasureTheory.ProbabilityMeasure.tendsto_measure_integral_iff_resolventTransform`
turns the transform bounds into weak convergence in probability.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices,
  a review*, Statistica Sinica 9 (1999), §2.1, Theorem 2.4.
* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter Finset
open scoped BigOperators Topology NNReal ENNReal Matrix.Norms.L2Operator BoundedContinuousFunction

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

variable {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {n : ℕ}

private abbrev zeroDiagonalWigner (ξ : StrictUpper → Ω → ℂ) (N : ℕ) :=
  wignerMatrix ξ (fun _ _ ↦ 0) N

private theorem wigner_minor_secondMoment_terms_le {m N : ℝ} (hN : 0 < N) (hm : m ≤ N)
    (r : ℝ≥0) :
    2 * N⁻¹ * Real.sqrt m + Real.sqrt ((r : ℝ) * m * N⁻¹) ≤
      2 / Real.sqrt N + Real.sqrt r := by
  apply add_le_add
  · calc
      _ ≤ 2 * N⁻¹ * Real.sqrt N := by gcongr
      _ = _ := by rw [mul_assoc, inv_mul_eq_div, Real.sqrt_div_self, div_eq_mul_inv]
  · rw [mul_assoc, ← div_eq_mul_inv]
    exact Real.sqrt_le_sqrt (mul_le_of_le_one_right r.coe_nonneg ((div_le_one hN).2 hm))

/-- For a zero-diagonal Wigner corner, the minor quadratic error is integrable. Its mean norm
is bounded by the matrix-size term, the squared-norm cutoff term and the discarded second
moments of the deleted column. -/
theorem integrable_and_integral_norm_wignerMatrix_zero_minorQuadraticError_le
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ ij.val) P)
    (hLp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) 2 P)
    (hc : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (i : Fin (n + 1)) {z : ℂ} (hz : 0 < z.im) (r : ℝ≥0) :
    let a := fun (j : {j // j ≠ i}) ω ↦ wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω j i
    let Q := fun ω ↦ (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).minorQuadraticError i z 1
    Integrable Q P ∧ (∫ ω, ‖Q ω‖ ∂P) ≤ z.im⁻¹ *
      (2 / Real.sqrt (n + 1) + Real.sqrt r +
        2 * ∑ j : {j // j ≠ i},
          ∫ ω, {ω | (r : ℝ) < ‖a j ω‖ ^ 2}.indicator (fun ω ↦ ‖a j ω‖ ^ 2) ω ∂P) := by
  intro a Q
  let R := fun ω ↦ (zeroDiagonalWigner ξ (n + 1) ω).minorResolvent i z
  have := hind.isProbabilityMeasure
  let B (ω : Ω) : Matrix {j // j ≠ i} {j // j ≠ i} ℂ :=
    (zeroDiagonalWigner ξ (n + 1) ω).submatrix (↑) (↑)
  let S (M : Matrix {j // j ≠ i} {j // j ≠ i} ℂ) := (M - z • 1)⁻¹
  have hm (ij : StrictUpper) (hij : ij.val.2 < n + 1) := (hLp ij hij).aemeasurable
  have hS : Measurable S := by dsimp only [S]; fun_prop
  have hR_eq : R = S ∘ B := funext fun ω ↦ Matrix.minorResolvent_def _ i z
  have hR : AEMeasurable R P := (Matrix.measurable_minorResolvent i z).comp_aemeasurable
    (aemeasurable_wignerMatrix hm (fun _ _ ↦ aemeasurable_const))
  have hi : IndepFun B (fun ω j ↦ a j ω) P :=
    indepFun_submatrix_wignerMatrix_zero_column hind hm i
  have hiR : IndepFun R (fun ω j ↦ a j ω) P := by
    rw [hR_eq]
    simpa only [Function.id_comp] using hi.comp hS measurable_id
  have hia := iIndepFun_wignerMatrix_offDiag_column (η := fun _ _ ↦ 0) i hind
  have hRbound : ∀ᵐ ω ∂P, ‖R ω‖ ≤ z.im⁻¹ := .of_forall fun ω ↦ by
    simpa only [R, RCLike.im_eq_complex_im, abs_of_pos hz] using
      (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)).l2_opNorm_minorResolvent_le hz.ne' i
  have hmoment (j : {j // j ≠ i}) : ∫ ω, ‖a j ω‖ ^ 2 ∂P = (n + 1 : ℝ)⁻¹ := by
    simpa only [Nat.cast_succ, mul_one] using
      integral_norm_wignerMatrix_apply_sq_of_ne (η := fun _ _ ↦ 0) hv j.property
  have hRi : Integrable (fun ω ↦ ‖R ω‖) P :=
    Integrable.of_bound hR.norm.aestronglyMeasurable _ (by simpa using hRbound)
  have hRm : (∫ ω, ‖R ω‖ ∂P) ≤ z.im⁻¹ := by
    simpa using integral_mono_ae hRi (integrable_const _) hRbound
  have h := hia.integrable_and_integral_norm_star_dotProduct_mulVec_sub_sum_diag_le_of_indepFun
    (fun j ↦ memLp_wignerMatrix_apply hLp (fun _ _ ↦ memLp_const 0) j i)
    (fun j ↦ integral_wignerMatrix_apply_eq_zero hc (by simp) j i) hR hiR hRi
    (fun j ↦ (hmoment j).le) r
  have hQ : Q = fun ω ↦ star (fun j ↦ a j ω) ⬝ᵥ R ω *ᵥ (fun j ↦ a j ω) -
      ∑ j, R ω j j * ((∫ y, ‖a j y‖ ^ 2 ∂P : ℝ) : ℂ) := by
    funext ω
    simp only [Q, Matrix.minorQuadraticError_eq_sub_sum_diag, Fintype.card_fin, Nat.cast_succ,
      NNReal.coe_one, one_div, hmoment, R, a]
    congr 1
    exact sum_congr rfl fun j _ ↦ mul_comm _ _
  rw [hQ]
  refine ⟨h.1, h.2.trans ?_⟩
  have hcard : (Fintype.card {j // j ≠ i} : ℝ) ≤ n + 1 := by
    exact_mod_cast (Fintype.card_subtype_le (fun j : Fin (n + 1) ↦ j ≠ i)).trans_eq
      (Fintype.card_fin (n + 1))
  have hscale := wigner_minor_secondMoment_terms_le (by positivity) hcard r
  refine mul_le_mul hRm (add_le_add hscale le_rfl) ?_ (inv_nonneg.mpr hz.le)
  refine add_nonneg (by positivity) (mul_nonneg (by norm_num) (sum_nonneg fun _ _ ↦ ?_))
  exact integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _

private theorem integrable_wignerTransform_error [IsFiniteMeasure P]
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n + 1, AEMeasurable (η i) P) {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun ω ↦
      resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z -
        resolventTransform (semicircleReal 0 1) z) P :=
  ((aemeasurable_wignerMatrix hξ hη).integrable_resolventTransform_spectralMeasure
    (fun ω ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) hz.ne').sub (integrable_const _)

private theorem integral_norm_resolventTransform_wignerMatrix_zero_sub_semicircleReal_le
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ ij.val) P)
    (hLp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) 2 P)
    (hc : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    {z : ℂ} (hz : 0 < z.im) (r : ℝ≥0) :
    (∫ ω, ‖resolventTransform
      ((wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z -
        resolventTransform (semicircleReal 0 1) z‖ ∂P) ≤ z.im⁻¹ ^ 2 *
      (z.im⁻¹ * (2 / Real.sqrt (n + 1) + Real.sqrt r +
        2 * (wignerLindebergSum (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1)) P r).toReal) +
        3 / ((n + 1) * z.im)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let A := zeroDiagonalWigner ξ (n + 1)
  let Q (i : Fin (n + 1)) (ω : Ω) := (A ω).minorQuadraticError i z 1
  have hq i :=
    integrable_and_integral_norm_wignerMatrix_zero_minorQuadraticError_le hind hLp hc hv i hz r
  have hi (i : Fin (n + 1)) : Integrable (fun ω ↦ ‖Q i ω‖) P := (hq i).1.norm
  have htest := (integrable_wignerTransform_error (η := fun _ _ ↦ 0)
    (fun ij hij ↦ (hLp ij hij).aemeasurable) (fun _ _ ↦ aemeasurable_const) hz).norm
  let c := 3 / ((n + 1 : ℝ) * z.im)
  have hm : Integrable (fun ω ↦ 𝔼 i, ‖Q i ω‖) P := integrable_expect fun i _ ↦ hi i
  have hmajor : Integrable (fun ω ↦ z.im⁻¹ ^ 2 * ((𝔼 i, ‖Q i ω‖) + c)) P :=
    (hm.add (integrable_const c)).const_mul _
  have hpoint (ω : Ω) :=
    (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))
      |>.norm_resolventTransform_spectralMeasure_sub_semicircleReal_le_of_diag_eq_zero
        (diag_wignerMatrix_zero ξ ω) hz 1
  refine (integral_mono htest hmajor (fun ω ↦ by
    simpa only [Q, c, Fintype.card_fin, Nat.cast_succ, NNReal.coe_one, mul_one] using
      hpoint ω)).trans ?_
  rw [integral_const_mul, integral_add hm (integrable_const c),
    integral_expect fun i _ ↦ hi i, integral_const, probReal_univ, one_smul]
  let b := 2 / Real.sqrt (n + 1) + Real.sqrt r
  let T (i : Fin (n + 1)) := ∑ j : {j // j ≠ i},
    ∫ ω, {ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω ∂P
  let U (i : Fin (n + 1)) := z.im⁻¹ * (b + 2 * T i)
  have hU (i : Fin (n + 1)) : (∫ ω, ‖Q i ω‖ ∂P) ≤ U i := by
    simpa only [U, T, b, A] using (hq i).2
  have htail : (wignerLindebergSum A P r).toReal = 𝔼 i, T i := by
    rw [Fintype.expect_eq_sum_div_card, div_eq_inv_mul, Fintype.card_fin,
      wignerLindebergSum_toReal A r (fun i j ↦ by
        have hsq := (memLp_wignerMatrix_apply hLp (fun _ _ ↦ memLp_const 0)
          j.val i).integrable_norm_pow (by decide : 2 ≠ 0)
        exact hsq.indicator₀ (nullMeasurableSet_lt aemeasurable_const hsq.aemeasurable)),
      Fintype.card_fin]
  have hscaled : (𝔼 i, U i) = z.im⁻¹ * (b + 2 * (wignerLindebergSum A P r).toReal) := by
    dsimp only [U]
    rw [← Finset.mul_expect, Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect,
      ← htail]
  have hmean := Finset.expect_le_expect fun i (_ : i ∈ Finset.univ) ↦ hU i
  refine (mul_le_mul_of_nonneg_left (add_le_add hmean le_rfl) (sq_nonneg _)).trans_eq ?_
  simp only [hscaled, b, c, A, zeroDiagonalWigner]

/-- At each upper-half-plane parameter, the mean absolute error of a Wigner resolvent
transform is controlled by the matrix size, the off-diagonal Lindeberg sum and the
diagonal second moments. Independence and the moment conditions concern the entries
in the corner of size `n + 1` and ensure that the Lindeberg sum is finite. -/
theorem integral_norm_resolventTransform_wignerMatrix_sub_semicircleReal_le
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ ij.val) P)
    (hm : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hc : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hd : ∀ i < n + 1, MemLp (η i) 2 P) {z : ℂ} (hz : 0 < z.im) (r : ℝ≥0) :
    (∫ ω, ‖resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z -
      resolventTransform (semicircleReal 0 1) z‖ ∂P) ≤ z.im⁻¹ ^ 2 *
      (z.im⁻¹ * (2 / Real.sqrt (n + 1) + Real.sqrt r +
        2 * (wignerLindebergSum (wignerMatrix ξ η (n + 1)) P r).toReal) +
        3 / ((n + 1) * z.im) + Real.sqrt ((n + 1 : ℝ)⁻¹ ^ 2 *
          ∑ i : Fin (n + 1), ∫ ω, η i ω ^ 2 ∂P)) := by
  have := hind.isProbabilityMeasure
  have ha := integrable_wignerTransform_error hm (fun i hi ↦ (hd i hi).aemeasurable) hz
  have hb := integrable_wignerTransform_error hm
    (η := fun _ _ ↦ 0) (fun _ _ ↦ aemeasurable_const) hz
  have h := integral_norm_resolventTransform_wignerMatrix_zero_sub_semicircleReal_le
    hind (fun ij hij ↦ (hm ij hij).aestronglyMeasurable.memLp_two_of_integral_norm_sq_ne_zero
      ((hv ij hij).trans_ne one_ne_zero)) hc hv hz r
  rw [wignerLindebergSum_wignerMatrix_eq_replace_diag ξ _ η] at h
  have hab := integral_norm_resolventTransform_wignerMatrix_sub_wignerMatrix_zero_le hm hd hz.ne'
  have hd' := (ha.sub hb).congr (.of_forall fun _ ↦ sub_sub_sub_cancel_right _ _ _)
  let L (ω : Ω) := resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
    (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z
  let L₀ (ω : Ω) := resolventTransform ((zeroDiagonalWigner ξ (n + 1) ω).spectralMeasure
    (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z
  let m := resolventTransform (semicircleReal 0 1) z
  have hsplit (ω : Ω) : L ω - m = (L₀ ω - m) + (L ω - L₀ ω) := by abel
  have htriangle := hb.integral_norm_add_le hd'
  calc
    _ = ∫ ω, ‖(L₀ ω - m) + (L ω - L₀ ω)‖ ∂P :=
      integral_congr_ae (.of_forall fun ω ↦ congrArg norm (hsplit ω))
    _ ≤ _ := htriangle.trans ((add_le_add h hab).trans_eq (by ring))


end TauCeti.Probability

namespace TauCeti.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
  {ξ : ∀ n, StrictUpper → Ω n → ℂ} {η : ∀ n, ℕ → Ω n → ℝ}

/-- For triangular Wigner arrays with centered independent upper entries of unit second
absolute moment, the Lindeberg condition and a vanishing diagonal contribution imply
mean absolute convergence of the transforms at each upper-half-plane parameter. The
sample spaces may vary with the dimension. -/
theorem tendsto_integral_norm_resolventTransform_wignerMatrix_sub_semicircleReal_of_lindeberg
    (hind : ∀ n, iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ n ij.val) (P n))
    (hm : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → AEMeasurable (ξ n ij) (P n))
    (hc : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hv : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hd : ∀ n i, i < n + 1 → MemLp (η n i) 2 (P n))
    (hdiag : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ ^ 2 *
      ∑ i : Fin (n + 1), ∫ ω, η n i ω ^ 2 ∂P n) atTop (𝓝 0))
    (hL : ∀ r : ℝ≥0, 0 < r → Tendsto (fun n ↦
      wignerLindebergSum (wignerMatrix (ξ n) (η n) (n + 1)) (P n) r) atTop (𝓝 0))
    {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun n ↦ ∫ ω, ‖resolventTransform
      ((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ) z -
      resolventTransform (semicircleReal 0 1) z‖ ∂P n) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    simpa only [Nat.cast_succ, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hsize : Tendsto (fun n : ℕ ↦ 2 / Real.sqrt (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hN)
  have hminor : Tendsto (fun n : ℕ ↦ 3 / ((n + 1 : ℝ) * z.im)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hN.atTop_mul_const hz)
  apply tendsto_order.2
  refine ⟨fun ε hε ↦ .of_forall fun n ↦ hε.trans_le
    (integral_nonneg fun _ ↦ norm_nonneg _), ?_⟩
  intro ε hε
  let C := z.im⁻¹ ^ 2 * z.im⁻¹
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  let r : ℝ≥0 := ⟨δ ^ 2, sq_nonneg _⟩
  have hr : 0 < r := sq_pos_of_pos hδ
  have htail : Tendsto (fun n ↦
      (wignerLindebergSum (wignerMatrix (ξ n) (η n) (n + 1)) (P n) r).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hL r hr)
  have hlim := ((((hsize.add_const (Real.sqrt r)).add (htail.const_mul 2)).const_mul
    z.im⁻¹).add hminor |>.add hdiag.sqrt).const_mul (z.im⁻¹ ^ 2)
  have hlim' : z.im⁻¹ ^ 2 * (z.im⁻¹ * (0 + Real.sqrt (r : ℝ) + 2 * 0) + 0 + Real.sqrt 0)
      = ε / 2 := by
    have hr' : (r : ℝ) = δ ^ 2 := rfl
    simp only [hr', Real.sqrt_sq hδ.le, Real.sqrt_zero, mul_zero, zero_add, add_zero]
    simp only [← mul_assoc, C, δ]
    field_simp [hz.ne']
  rw [hlim'] at hlim
  filter_upwards [hlim.eventually_lt_const (u := ε) (by linarith)] with n hn
  exact (integral_norm_resolventTransform_wignerMatrix_sub_semicircleReal_le
    (hind n) (hm n) (hc n) (hv n) (hd n) hz r).trans_lt hn

/-- **Semicircle law in probability for triangular Wigner arrays.** Centered independent
upper entries have unit second absolute moment before division by the square root of the
dimension. The diagonal is real with negligible normalized mean-square size. Under the
Lindeberg condition, each bounded continuous test integral converges in probability to
its standard semicircle integral, including when the sample spaces vary. -/
theorem wigner_semicircle_in_probability_of_lindeberg
    (hind : ∀ n, iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ n ij.val) (P n))
    (hm : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → AEMeasurable (ξ n ij) (P n))
    (hc : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hv : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hd : ∀ n i, i < n + 1 → MemLp (η n i) 2 (P n))
    (hdiag : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ ^ 2 *
      ∑ i : Fin (n + 1), ∫ ω, η n i ω ^ 2 ∂P n) atTop (𝓝 0))
    (hL : ∀ r : ℝ≥0, 0 < r → Tendsto (fun n ↦
      wignerLindebergSum (wignerMatrix (ξ n) (η n) (n + 1)) (P n) r) atTop (𝓝 0))
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω |
      ε ≤ |(∫ x, f x ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
        ∫ x, f x ∂semicircleReal 0 1|}) atTop (𝓝 0) := by
  let μ : ProbabilityMeasure ℝ := ⟨semicircleReal 0 1, inferInstance⟩
  let L (n : ℕ) (ω : Ω n) := (wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
    (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1))
  refine (ProbabilityMeasure.tendsto_measure_integral_iff_resolventTransform P L atTop μ).2
    (fun z hz t ht ↦ ?_) f ε hε
  let E (n : ℕ) (ω : Ω n) :=
    resolventTransform (L n ω : Measure ℝ) z - resolventTransform (semicircleReal 0 1) z
  have hlim : Tendsto (fun n ↦ ∫ ω, ‖E n ω‖ ∂P n) atTop (𝓝 0) :=
    tendsto_integral_norm_resolventTransform_wignerMatrix_sub_semicircleReal_of_lindeberg
      hind hm hc hv hd hdiag hL hz
  exact tendsto_measure_norm_ge_of_tendsto_integral_norm
    (.of_forall fun n ↦ by
      have := (hind n).isProbabilityMeasure
      exact (integrable_wignerTransform_error (hm n) (fun i hi ↦ (hd n i hi).aemeasurable) hz).norm)
    hlim ht

end TauCeti.Probability
