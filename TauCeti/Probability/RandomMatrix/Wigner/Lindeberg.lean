/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
import TauCeti.Probability.Moments.QuadraticForm.SecondMoment
import TauCeti.Probability.Independence.Basic
import TauCeti.Analysis.Matrix.Resolvent.SelfConsistency
import TauCeti.Analysis.Matrix.SpectralMeasure.ResolventStability
import TauCeti.Analysis.Matrix.MeasurableSpace
import TauCeti.MeasureTheory.Measure.ResolventTransform.InProbability

/-!
# The Wigner semicircle law for Lindeberg arrays

For triangular Wigner arrays, the average of the absolute leave-one-out quadratic-form
errors is sufficient to control the resolvent trace. Off-diagonal products are bounded
using only second moments. The truncation of the squared entries controls the diagonal
part of each quadratic form, and its discarded second moments appear in the Lindeberg sum.
A diagonal with vanishing normalized mean-square norm contributes a separate error.

The sample spaces can vary with the size of the matrix.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices,
  a review*, Statistica Sinica 9 (1999), §2.1, Theorem 2.4.
* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter Finset
open scoped Topology NNReal ENNReal Matrix.Norms.L2Operator BoundedContinuousFunction

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The average squared off-diagonal tail integral above the squared-modulus cutoff.
The sum takes the value `⊤` when any of the discarded second moments is infinite.
Here the matrix entries already include the Wigner normalization. For a matrix of size
`N`, cutoff `r` thus corresponds to the unnormalized modulus cutoff `√(r * N)`
and an overall factor `1 / N²` in the sum of the unnormalized second moments. -/
def wignerLindebergSum {N : ℕ} (A : Ω → Matrix (Fin N) (Fin N) ℂ) (P : Measure Ω)
    (r : ℝ≥0) : ℝ≥0∞ :=
  (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N, ∑ j : {j : Fin N // j ≠ i},
    ∫⁻ ω, ENNReal.ofReal
      ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω) ∂P

/-- For integrable discarded second moments, the real value of the Lindeberg sum is the
average of the corresponding Bochner integrals. -/
theorem wignerLindebergSum_toReal {N : ℕ} (A : Ω → Matrix (Fin N) (Fin N) ℂ) (r : ℝ≥0)
    (hA : ∀ (i : Fin N) (j : {j : Fin N // j ≠ i}),
      Integrable ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2)) P) :
    (wignerLindebergSum A P r).toReal =
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : {j : Fin N // j ≠ i},
        ∫ ω, {ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω ∂P := by
  have hnonneg (i : Fin N) (j : {j : Fin N // j ≠ i}) (ω : Ω) :
      0 ≤ {ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω :=
    Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  simp_rw [wignerLindebergSum, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← ofReal_integral_eq_lintegral_ofReal (hA _ _) (.of_forall (hnonneg _ _))]
  rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (integral_nonneg (hnonneg _ _))]

variable {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {n : ℕ}

private abbrev zeroDiagonalWigner (ξ : StrictUpper → Ω → ℂ) (N : ℕ) :=
  wignerMatrix ξ (fun _ _ ↦ 0) N

private theorem second_moment_wignerMatrix_apply_of_ne
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    {i j : Fin (n + 1)} (hij : i ≠ j) :
    ∫ ω, ‖wignerMatrix ξ η (n + 1) ω i j‖ ^ 2 ∂P = (n + 1 : ℝ)⁻¹ := by
  simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ hij, integral_const_mul, Nat.cast_succ]
  rw [hv _ (max_lt i.isLt j.isLt), mul_one]

private theorem quadraticForm_wigner_minor_bound (hind : iIndepFun ξ P)
    (hLp : ∀ ij, MemLp (ξ ij) 2 P)
    (hc : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (i : Fin (n + 1)) {z : ℂ} (hz : 0 < z.im) (r : ℝ≥0) :
    let a := fun (j : {j // j ≠ i}) ω ↦ zeroDiagonalWigner ξ (n + 1) ω j i
    let R := fun ω ↦ (((zeroDiagonalWigner ξ (n + 1) ω).submatrix (↑) (↑) :
      Matrix {j // j ≠ i} {j // j ≠ i} ℂ) - z • 1)⁻¹
    let Q := fun ω ↦ star (fun j ↦ a j ω) ⬝ᵥ R ω *ᵥ (fun j ↦ a j ω) -
      ((n + 1 : ℕ) : ℂ)⁻¹ * (R ω).trace
    Integrable Q P ∧ (∫ ω, ‖Q ω‖ ∂P) ≤ z.im⁻¹ *
      (2 / Real.sqrt (n + 1) + Real.sqrt r +
        2 * ∑ j : {j // j ≠ i},
          ∫ ω, {ω | (r : ℝ) < ‖a j ω‖ ^ 2}.indicator (fun ω ↦ ‖a j ω‖ ^ 2) ω ∂P) := by
  intro a R Q
  have := hind.isProbabilityMeasure
  let B (ω : Ω) : Matrix {j // j ≠ i} {j // j ≠ i} ℂ :=
    (zeroDiagonalWigner ξ (n + 1) ω).submatrix (↑) (↑)
  have hW := aemeasurable_wignerMatrix (n := n + 1) (η := fun _ _ ↦ 0)
    (fun ij _ ↦ (hLp ij).aemeasurable) (fun _ _ ↦ aemeasurable_const)
  have hB : AEMeasurable B P := .of_eval fun j ↦ .of_eval fun k ↦
    (Matrix.measurable_apply (i := j.val) (j := k.val)).comp_aemeasurable hW
  have hres : Measurable (fun M : Matrix {j // j ≠ i} {j // j ≠ i} ℂ ↦ (M - z • 1)⁻¹) := by
    fun_prop
  have hR : AEMeasurable R P := hres.comp_aemeasurable hB
  have hi : IndepFun R (fun ω j ↦ a j ω) P :=
    (indepFun_submatrix_wignerMatrix_zero_column hind (fun ij ↦ (hLp ij).aemeasurable) i).comp
      hres measurable_id
  have hia : iIndepFun a P := iIndepFun_wignerMatrix_apply_of_ne Subtype.val (fun _ ↦ i)
    Subtype.property (fun j k h ↦ Subtype.ext (((Sym2.eq_iff.mp h).resolve_right
      fun he ↦ j.property he.1).1)) (hind.precomp Subtype.val_injective)
  have hRbound : ∀ᵐ ω ∂P, ‖R ω‖ ≤ z.im⁻¹ := .of_forall fun ω ↦ by
    simpa only [R, RCLike.im_eq_complex_im, abs_of_pos hz] using
      ((wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)).submatrix
        (Subtype.val : {j // j ≠ i} → Fin (n + 1))).l2_opNorm_inv_sub_smul_one_le hz.ne'
  have ha (j : {j // j ≠ i}) : ∫ ω, ‖a j ω‖ ^ 2 ∂P = (n + 1 : ℝ)⁻¹ :=
    second_moment_wignerMatrix_apply_of_ne hv j.property
  have h := hia.integral_norm_star_dotProduct_mulVec_sub_sum_diag_le_of_indepFun
    (fun j ↦ memLp_wignerMatrix_apply (fun ij _ ↦ hLp ij) (fun _ _ ↦ memLp_const 0) j i)
    (fun j ↦ integral_wignerMatrix_apply_eq_zero hc (by simp) j i) hR hi hRbound
    (fun j ↦ (ha j).le) r
  have he (ω : Ω) : ∑ j, R ω j j * ((∫ y, ‖a j y‖ ^ 2 ∂P : ℝ) : ℂ) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * (R ω).trace := by
    simp only [ha, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one, Nat.cast_succ, Matrix.trace, Matrix.diag, Finset.mul_sum]
    exact sum_congr rfl fun j _ ↦ mul_comm _ _
  simp only [he] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hcard : (Fintype.card {j // j ≠ i} : ℝ) ≤ n + 1 := by
    exact_mod_cast (Fintype.card_le_of_injective _ Subtype.val_injective).trans_eq
      (Fintype.card_fin (n + 1))
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have h₁ : 2 * (n + 1 : ℝ)⁻¹ * Real.sqrt (Fintype.card {j // j ≠ i}) ≤
      2 / Real.sqrt (n + 1) := by
    calc
      _ ≤ 2 * (n + 1 : ℝ)⁻¹ * Real.sqrt (n + 1) := by gcongr
      _ = _ := by field_simp; nlinarith [Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)]
  have h₂ : Real.sqrt ((r : ℝ) * Fintype.card {j // j ≠ i} * (n + 1 : ℝ)⁻¹) ≤ Real.sqrt r := by
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ (r : ℝ) * (n + 1) * (n + 1 : ℝ)⁻¹ := by gcongr
      _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add h₁ h₂) le_rfl) (inv_nonneg.mpr hz.le)

private theorem norm_normalized_minor_trace_sub_resolventTransform_le {N : ℕ} [NeZero N]
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i : Fin N) :
    ‖(N : ℂ)⁻¹ * (((A.submatrix (↑) (↑) : Matrix {j // j ≠ i} {j // j ≠ i} ℂ) -
        z • 1)⁻¹).trace - resolventTransform (A.spectralMeasure hA : Measure ℝ) z‖ ≤
      3 / ((N : ℝ) * z.im) := by
  rw [resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hz.ne'),
    Fintype.card_fin, ← mul_sub, norm_mul, norm_inv, Complex.norm_natCast, norm_sub_rev]
  have h := hA.norm_trace_inv_sub_smul_one_sub_trace_submatrix_le i hz.ne'
  rw [abs_of_pos hz] at h
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

private theorem norm_wignerTransform_sub_le_mean_quadraticError {N : ℕ} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian) (hd : ∀ i, A i i = 0)
    {z : ℂ} (hz : 0 < z.im) :
    let m := resolventTransform (A.spectralMeasure hA : Measure ℝ) z
    let R (i : Fin N) :=
      ((A.submatrix (↑) (↑) : Matrix {j // j ≠ i} {j // j ≠ i} ℂ) - z • 1)⁻¹
    let a (i : Fin N) (j : {j // j ≠ i}) := A j i
    let Q (i : Fin N) := star (a i) ⬝ᵥ R i *ᵥ a i - (N : ℂ)⁻¹ * (R i).trace
    ‖m - resolventTransform (semicircleReal 0 1) z‖ ≤ z.im⁻¹ ^ 2 *
      ((N : ℝ)⁻¹ * ∑ i, ‖Q i‖ + 3 / ((N : ℝ) * z.im)) := by
  intro m R a Q
  have hp := im_resolventTransform_pos (μ := (A.spectralMeasure hA : Measure ℝ))
    (IsProbabilityMeasure.ne_zero _) hz
  have hs := norm_sub_resolventTransform_semicircleReal_le (a := 0) (v := 1) hz hp.le
  simp only [NNReal.coe_one, Complex.ofReal_one, Complex.ofReal_zero, sub_zero, one_mul] at hs
  have hres := hA.norm_resolventTransform_spectralMeasure_quadratic_le hz (1 : ℂ)
  have hres' : ‖m * m + z * m + 1‖ ≤ (z.im * N)⁻¹ *
      ∑ i : Fin N, ‖m - star (a i) ⬝ᵥ R i *ᵥ a i‖ := by
    simpa only [Fintype.card_fin, hd, zero_add, one_mul] using hres
  have hentry (i : Fin N) : ‖m - star (a i) ⬝ᵥ R i *ᵥ a i‖ ≤
      ‖Q i‖ + 3 / ((N : ℝ) * z.im) := by
    rw [norm_sub_rev]
    exact (norm_sub_le_norm_sub_add_norm_sub _ ((N : ℂ)⁻¹ * (R i).trace) _).trans
      (add_le_add le_rfl (norm_normalized_minor_trace_sub_resolventTransform_le hA hz i))
  have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin N))) ↦ hentry i
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  refine hs.trans ((div_le_div_of_nonneg_right (hres'.trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))) hz.le).trans_eq ?_)
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private theorem integrable_wignerTransform_error [IsProbabilityMeasure P]
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n + 1, AEMeasurable (η i) P) {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun ω ↦
      resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z -
        resolventTransform (semicircleReal 0 1) z) P := by
  let A := wignerMatrix ξ η (n + 1)
  have hA ω := wignerMatrix_isHermitian ξ η ω (n + 1)
  have hm := aemeasurable_wignerMatrix hξ hη
  have ht : Measurable (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ↦
      ((n + 1 : ℕ) : ℂ)⁻¹ * ((B - z • 1)⁻¹).trace) := by
    simp only [Matrix.trace, Matrix.diag]
    fun_prop
  have ht' : AEMeasurable (fun ω ↦
      resolventTransform ((A ω).spectralMeasure (hA ω) : Measure ℝ) z) P := by
    simp_rw [fun ω ↦ resolventTransform_spectralMeasure (A ω) (hA ω)
      ((hA ω).notMem_spectrum_of_im_ne_zero hz.ne'), Fintype.card_fin]
    exact ht.comp_aemeasurable hm
  refine Integrable.of_bound (ht'.sub_const _).aestronglyMeasurable (2 * z.im⁻¹) (.of_forall ?_)
  intro ω
  have h₁ := norm_resolventTransform_le (μ := ((A ω).spectralMeasure (hA ω) : Measure ℝ)) hz.ne'
  have h₂ := norm_resolventTransform_le (μ := semicircleReal 0 1) hz.ne'
  simp only [abs_of_pos hz, probReal_univ, mul_one] at h₁ h₂
  exact (norm_sub_le _ _).trans (by linarith)

private theorem integral_norm_resolventTransform_wignerMatrix_zero_sub_semicircle_le
    (hind : iIndepFun ξ P) (hLp : ∀ ij, MemLp (ξ ij) 2 P)
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
  let R (i : Fin (n + 1)) (ω : Ω) :=
    (((A ω).submatrix (↑) (↑) : Matrix {j // j ≠ i} {j // j ≠ i} ℂ) - z • 1)⁻¹
  let a (i : Fin (n + 1)) (ω : Ω) (j : {j // j ≠ i}) := A ω j i
  let Q (i : Fin (n + 1)) (ω : Ω) :=
    star (a i ω) ⬝ᵥ R i ω *ᵥ a i ω - ((n + 1 : ℕ) : ℂ)⁻¹ * (R i ω).trace
  have hq i := quadraticForm_wigner_minor_bound hind hLp hc hv i hz r
  have hi (i : Fin (n + 1)) : Integrable (fun ω ↦ ‖Q i ω‖) P := (hq i).1.norm
  have hsum : Integrable (fun ω ↦ ∑ i, ‖Q i ω‖) P := integrable_finsetSum _ fun i _ ↦ hi i
  have htest : Integrable (fun ω ↦
      ‖resolventTransform ((A ω).spectralMeasure (wignerMatrix_isHermitian ξ
        (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z - resolventTransform (semicircleReal 0 1) z‖)
      P := (integrable_wignerTransform_error (fun ij _ ↦ (hLp ij).aemeasurable)
        (fun _ _ ↦ aemeasurable_const) hz).norm
  let c := 3 / ((n + 1 : ℝ) * z.im)
  have hmajor : Integrable (fun ω ↦ z.im⁻¹ ^ 2 *
      ((n + 1 : ℝ)⁻¹ * ∑ i, ‖Q i ω‖ + c)) P :=
    ((hsum.const_mul _).add (integrable_const c)).const_mul _
  have hpoint (ω : Ω) := norm_wignerTransform_sub_le_mean_quadraticError
    (A ω) (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) (by simp [A]) hz
  refine (integral_mono htest hmajor
    (fun ω ↦ by simpa only [Q, R, a, c, Nat.cast_succ] using hpoint ω)).trans ?_
  rw [integral_const_mul, integral_add (hsum.const_mul _) (integrable_const c),
    integral_const_mul, integral_const, probReal_univ, one_smul,
    integral_finsetSum _ (fun i _ ↦ hi i)]
  have h := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin (n + 1)))) ↦ (hq i).2
  refine (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left h (by positivity)) le_rfl) (sq_nonneg _)).trans_eq ?_
  have htail := wignerLindebergSum_toReal (P := P) A r (fun i j ↦ by
    have hsq := (memLp_wignerMatrix_apply (fun ij _ ↦ hLp ij) (fun _ _ ↦ memLp_const 0)
      j.val i).integrable_norm_pow (by decide : 2 ≠ 0)
    exact hsq.indicator₀ (nullMeasurableSet_lt aemeasurable_const hsq.aemeasurable))
  rw [← mul_sum, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    htail, Nat.cast_succ]
  simp_rw [← mul_sum]
  dsimp only [A, c, zeroDiagonalWigner]
  field_simp

omit [MeasurableSpace Ω] in
open scoped Matrix.Norms.Frobenius in
private theorem norm_resolventTransform_wignerMatrix_sub_zero_le (ω : Ω)
    {z : ℂ} (hz : 0 < z.im) :
    ‖resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z -
      resolventTransform ((zeroDiagonalWigner ξ (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z‖ ≤
      z.im⁻¹ ^ 2 * Real.sqrt ((n + 1 : ℝ)⁻¹ ^ 2 * ∑ i : Fin (n + 1), η i ω ^ 2) := by
  let B := diagonal (fun i : Fin (n + 1) ↦ ((η i ω / Real.sqrt (n + 1) : ℝ) : ℂ))
  have hB : wignerMatrix ξ η (n + 1) ω - zeroDiagonalWigner ξ (n + 1) ω = B := by
    simp only [B, wignerMatrix_eq_add_diagonal ξ η, add_sub_cancel_left, Nat.cast_succ]
  have hs : ‖B‖ ^ 2 = (n + 1 : ℝ)⁻¹ * ∑ i : Fin (n + 1), η i ω ^ 2 := by
    dsimp only [B]
    rw [frobenius_norm_diagonal, PiLp.norm_sq_eq_of_L2, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    -- The product norm of the embedded diagonal is the Euclidean norm of its entries.
    change ‖((η i ω / Real.sqrt (n + 1 : ℝ) : ℝ) : ℂ)‖ ^ 2 = _
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by positivity),
      div_eq_inv_mul]
  have hnorm : ‖B‖ / Real.sqrt (n + 1 : ℝ) =
      Real.sqrt ((n + 1 : ℝ)⁻¹ ^ 2 * ∑ i : Fin (n + 1), η i ω ^ 2) := by
    rw [← Real.sqrt_sq (div_nonneg (norm_nonneg B) (Real.sqrt_nonneg _)), div_pow, hs,
      Real.sq_sqrt (by positivity)]
    congr 1
    ring
  have hp := norm_resolventTransform_spectralMeasure_sub_le_frobenius
    (wignerMatrix_isHermitian ξ η ω (n + 1))
    (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) hz.ne'
  simpa only [hB, Fintype.card_fin, Nat.cast_succ, abs_of_pos hz, mul_div_assoc, hnorm] using hp

private theorem integral_norm_resolventTransform_wignerMatrix_sub_zero_le [IsProbabilityMeasure P]
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n + 1, MemLp (η i) 2 P) {z : ℂ} (hz : 0 < z.im) :
    (∫ ω, ‖resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z -
      resolventTransform ((zeroDiagonalWigner ξ (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z‖ ∂P) ≤
      z.im⁻¹ ^ 2 * Real.sqrt ((n + 1 : ℝ)⁻¹ ^ 2 *
        ∑ i : Fin (n + 1), ∫ ω, η i ω ^ 2 ∂P) := by
  let S (ω : Ω) := (n + 1 : ℝ)⁻¹ ^ 2 * ∑ i : Fin (n + 1), η i ω ^ 2
  have hS (ω : Ω) : 0 ≤ S ω := by unfold S; positivity
  have hi (i : Fin (n + 1)) : Integrable (fun ω ↦ η i ω ^ 2) P := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (hη i i.isLt).aestronglyMeasurable).mp (hη i i.isLt)
  have hSi : Integrable S P := (integrable_finsetSum _ fun i _ ↦ hi i).const_mul _
  have he : MemLp (fun ω ↦ Real.sqrt (S ω)) 2 P := by
    refine (memLp_two_iff_integrable_sq_norm
      (Real.continuous_sqrt.comp_aestronglyMeasurable hSi.aestronglyMeasurable)).mpr ?_
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hS _)] using hSi
  have ha := integrable_wignerTransform_error hξ (fun i hi ↦ (hη i hi).aemeasurable) hz
  have hb := integrable_wignerTransform_error hξ
    (η := fun _ _ ↦ 0) (fun _ _ ↦ aemeasurable_const) hz
  have hab := ((ha.sub hb).congr (.of_forall fun ω ↦ sub_sub_sub_cancel_right _ _ _)).norm
  refine (integral_mono hab ((he.integrable one_le_two).const_mul _)
    (fun ω ↦ norm_resolventTransform_wignerMatrix_sub_zero_le (ξ := ξ) (η := η) ω hz)).trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ((integral_le_sqrt_integral_sq he).trans_eq ?_) (sq_nonneg _)
  simp_rw [Real.sq_sqrt (hS _)]
  rw [show (∫ ω, S ω ∂P) = _ from integral_const_mul _ _, integral_finsetSum _ (fun i _ ↦ hi i)]

/-- The upper/lower entry tails are unchanged by replacing the real diagonal. -/
theorem wignerLindebergSum_wignerMatrix_eq {N : ℕ} (ξ : StrictUpper → Ω → ℂ)
    (η η' : ℕ → Ω → ℝ) (r : ℝ≥0) :
    wignerLindebergSum (wignerMatrix ξ η N) P r =
      wignerLindebergSum (wignerMatrix ξ η' N) P r := by
  unfold wignerLindebergSum
  congr 1
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp_rw [norm_wignerMatrix_apply_sq_of_ne _ _ _ j.property]

/-- In unnormalized coordinates the Lindeberg sum divides the discarded second moments
by the square of the dimension. Each upper entry is counted once for either orientation. -/
theorem wignerLindebergSum_wignerMatrix_eq_sum {N : ℕ} (ξ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (r : ℝ≥0) :
    let edge (i : Fin N) (j : {j : Fin N // j ≠ i}) : StrictUpper :=
      ⟨(min j.val.val i.val, max j.val.val i.val), min_lt_max.mpr (Fin.val_ne_of_ne j.property)⟩
    wignerLindebergSum (wignerMatrix ξ η N) P r =
      (N : ℝ≥0∞)⁻¹ ^ 2 * ∑ i : Fin N, ∑ j : {j : Fin N // j ≠ i},
        ∫⁻ ω, ENNReal.ofReal ({ω | (r : ℝ) * N < ‖ξ (edge i j) ω‖ ^ 2}.indicator
          (fun ω ↦ ‖ξ (edge i j) ω‖ ^ 2) ω) ∂P := by
  cases N with
  | zero => simp [wignerLindebergSum]
  | succ n =>
    intro edge
    have hN : 0 < (n + 1 : ℝ) := by positivity
    rw [wignerLindebergSum, pow_two, mul_assoc]
    congr 1
    simp only [mul_sum]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    rw [← lintegral_const_mul' _ _ (by simp)]
    apply lintegral_congr
    intro ω
    simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ j.property, Nat.cast_succ,
      Set.indicator_apply, Set.mem_ofPred_eq]
    have hcut : (r : ℝ) < (n + 1 : ℝ)⁻¹ * ‖ξ (edge i j) ω‖ ^ 2 ↔
        (r : ℝ) * (n + 1 : ℝ) < ‖ξ (edge i j) ω‖ ^ 2 := by
      rw [← div_eq_inv_mul, lt_div_iff₀ hN]
    dsimp only [edge] at hcut ⊢
    simp only [hcut]
    split_ifs
    · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hN,
        ← Nat.cast_succ, ENNReal.ofReal_natCast, Nat.cast_succ]
    · simp

private theorem integral_norm_resolventTransform_wignerMatrix_sub_semicircle_le_of_global
    (hind : iIndepFun ξ P) (hLp : ∀ ij, MemLp (ξ ij) 2 P)
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
  have hm (ij : StrictUpper) (_ : ij.val.2 < n + 1) := (hLp ij).aemeasurable
  have ha := integrable_wignerTransform_error hm (fun i hi ↦ (hd i hi).aemeasurable) hz
  have hb := integrable_wignerTransform_error hm
    (η := fun _ _ ↦ 0) (fun _ _ ↦ aemeasurable_const) hz
  have h := integral_norm_resolventTransform_wignerMatrix_zero_sub_semicircle_le
    hind hLp hc hv hz r
  rw [wignerLindebergSum_wignerMatrix_eq ξ _ η] at h
  have hab := integral_norm_resolventTransform_wignerMatrix_sub_zero_le hm hd hz
  have hd' := (ha.sub hb).congr (.of_forall fun _ ↦ sub_sub_sub_cancel_right _ _ _)
  refine (integral_mono ha.norm (hb.norm.add hd'.norm) (fun ω ↦ ?_)).trans ?_
  · simpa [add_comm] using norm_sub_le_norm_sub_add_norm_sub
      (resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z)
      (resolventTransform ((zeroDiagonalWigner ξ (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z)
      (resolventTransform (semicircleReal 0 1) z)
  rw [integral_add' hb.norm hd'.norm]
  exact (add_le_add h hab).trans_eq (by ring)

private theorem memLp_upper_of_integral_norm_sq_eq_one
    (hm : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (ij : StrictUpper) (hij : ij.val.2 < n + 1) : MemLp (ξ ij) 2 P := by
  apply (memLp_two_iff_integrable_sq_norm (hm ij hij).aestronglyMeasurable).mpr
  by_contra h
  exact one_ne_zero ((hv ij hij).symm.trans (integral_undef h))

/-- At each upper-half-plane parameter, the mean absolute error of a Wigner resolvent
transform is controlled by the matrix size, the off-diagonal Lindeberg sum and the
diagonal second moments. Independence and the moment conditions concern the entries
in the corner of size `n + 1` and ensure that the Lindeberg sum is finite. -/
theorem integral_norm_resolventTransform_wignerMatrix_sub_semicircle_le
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
  let ζ (ij : StrictUpper) := if ij.val.2 < n + 1 then ξ ij else 0
  have hcorner : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ζ ij.val) P := by
    refine hind.congr fun ij ↦ .of_forall fun ω ↦ ?_
    simp only [ζ, ite_eq_left ij.property]
  have hζ : iIndepFun ζ P :=
    iIndepFun.of_subtype_of_ae_eq_const (s := {ij : StrictUpper | ij.val.2 < n + 1}) hcorner
      (fun ij hij ↦ ⟨0, .of_forall fun ω ↦ by
        simp only [ζ, ite_eq_right (show ¬ij.val.2 < n + 1 from hij), Pi.zero_apply]⟩)
  have hLp (ij : StrictUpper) : MemLp (ζ ij) 2 P := by
    by_cases h : ij.val.2 < n + 1
    · simpa only [ζ, ite_eq_left h] using memLp_upper_of_integral_norm_sq_eq_one hm hv ij h
    · simpa only [ζ, ite_eq_right h] using (MemLp.zero : MemLp (0 : Ω → ℂ) 2 P)
  have h := integral_norm_resolventTransform_wignerMatrix_sub_semicircle_le_of_global hζ hLp
    (fun ij hij ↦ by simpa only [ζ, ite_eq_left hij] using hc ij hij)
    (fun ij hij ↦ by simpa only [ζ, ite_eq_left hij] using hv ij hij) hd hz r
  have hmat : wignerMatrix ζ η (n + 1) = wignerMatrix ξ η (n + 1) :=
    funext fun ω ↦
      wignerMatrix_congr ω (fun ij hij ↦ by simp only [ζ, ite_eq_left hij]) (fun _ _ ↦ rfl)
  simpa only [hmat] using h

end TauCeti.Probability

namespace TauCeti.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
  {ξ : ∀ n, StrictUpper → Ω n → ℂ} {η : ∀ n, ℕ → Ω n → ℝ}

/-- For triangular Wigner arrays with centered independent upper entries of unit second
absolute moment, the Lindeberg condition and a vanishing diagonal contribution imply
mean absolute convergence of the transforms at each upper-half-plane parameter. The
sample spaces may vary with the dimension. -/
theorem tendsto_integral_norm_resolventTransform_wignerMatrix_sub_semicircle_of_lindeberg
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
  have hδ : 0 < δ := by dsimp [δ]; positivity
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
    rw [← mul_assoc]
    -- Fold the two constants used to choose the cutoff.
    change C * δ = ε / 2
    dsimp only [δ]
    field_simp [hC.ne']
  rw [hlim'] at hlim
  filter_upwards [hlim.eventually_lt_const (u := ε) (by linarith)] with n hn
  exact (integral_norm_resolventTransform_wignerMatrix_sub_semicircle_le
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
    tendsto_integral_norm_resolventTransform_wignerMatrix_sub_semicircle_of_lindeberg
      hind hm hc hv hd hdiag hL hz
  have hupper := ENNReal.tendsto_ofReal (hlim.div_const t)
  simp only [zero_div, ENNReal.ofReal_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ ↦ bot_le) (fun n ↦ ?_)
  have := (hind n).isProbabilityMeasure
  have hi : Integrable (E n) (P n) := integrable_wignerTransform_error
    (hm n) (fun i hi ↦ (hd n i hi).aemeasurable) hz
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (.of_forall fun ω ↦ norm_nonneg (E n ω)) hi.norm t
  have hb := (le_div_iff₀ ht).2 (by simpa only [mul_comm] using hMarkov)
  exact (ofReal_measureReal (measure_ne_top _ _)).symm.le.trans (ENNReal.ofReal_le_ofReal hb)

end TauCeti.Probability
