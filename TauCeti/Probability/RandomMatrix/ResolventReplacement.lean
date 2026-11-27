/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Derivative
public import TauCeti.Probability.Moments.Lindeberg
public import Mathlib.Probability.HasLaw

import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Matrix.Resolvent.Expansion
import TauCeti.Analysis.Matrix.Resolvent.Integrable
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.MeasureTheory.Integral.TruncatedMoment
import TauCeti.Probability.Moments.Complex
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Lindeberg replacement for resolvent traces

Consider a Hermitian matrix `H(x) = A + ∑ i, x i • B i` with independent real coordinates.
Replacing their laws by laws with the same moments through degree `r` changes the expectation of
the normalized resolvent trace by at most

`∑ i, (rank(B i) / card n) ‖B i‖^(r+1) |Im z|^(-r-2) (E |X i|^(r+1) + E |Y i|^(r+1))`.

The norm of `B i` is the Euclidean operator norm. The coordinate laws can differ, the matrices
need not commute, and the coordinates need not be centered. All integrability and smoothness of
the resolvent test are consequences of Hermitian symmetry and the nonreal spectral parameter.
The comparison controls the complex expectation itself, and hence both its real and imaginary
parts, retaining the rank-to-dimension improvement for low-rank coordinate perturbations. Empty
coordinate and matrix index types are allowed.

The proof combines
`Matrix.IsHermitian.norm_iteratedDeriv_succ_normalized_trace_inv_add_smul_sub_smul_one_le` with
the scalar Lindeberg theorem `TauCeti.Probability.abs_integral_pi_sub_integral_pi_le_of_bounded`.

For complex coordinates, each perturbation has the form `x i • B i + conj (x i) • (B i)ᴴ`.
Matching mixed moments through degree two gives a rank-sensitive bound in terms of truncated
second moments, allowing entry laws with just a finite second moment.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American
  Mathematical Society (2012), §§2.2, 2.4.
-/

public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped Matrix.Norms.L2Operator ContDiff

attribute [local instance] Matrix.l2OpNormedAlgebraReal

namespace Matrix.IsHermitian

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
  {A : Matrix n n ℂ} {B : ι → Matrix n n ℂ}

private theorem resolvent_test_continuous (hA : A.IsHermitian)
    (hB : ∀ i, (B i).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun x : ι → ℝ ↦
      (Fintype.card n : ℂ)⁻¹ * (A + ∑ i, x i • B i - z • 1)⁻¹.trace) := by
  have hH (x : ι → ℝ) : (A + ∑ i, x i • B i).IsHermitian :=
    hA.add (isSelfAdjoint_sum univ fun i _ ↦ (hB i).smul (by simp [IsSelfAdjoint]))
  have hc : Continuous (fun x : ι → ℝ ↦ A + ∑ i, x i • B i) := by fun_prop
  exact continuous_const.mul (hc.matrix_inv_sub_smul_one hH hz).matrix_trace

private theorem resolvent_test_coordinate [DecidableEq ι] (hA : A.IsHermitian)
    (hB : ∀ i, (B i).IsHermitian) (l : ℂ →L[ℝ] ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (r : ℕ) (x : ι → ℝ) (i : ι) :
    let f := fun t : ℝ ↦ l ((Fintype.card n : ℂ)⁻¹ *
      (A + ∑ j, Function.update x i t j • B j - z • 1)⁻¹.trace)
    ContDiff ℝ (r + 1) f ∧ ∀ t, |iteratedDeriv (r + 1) f t| ≤
      ‖l‖ * (((B i).rank : ℝ) / Fintype.card n *
        ((Nat.factorial (r + 1) : ℝ) * ‖B i‖ ^ (r + 1) * |z.im|⁻¹ ^ (r + 2))) := by
  classical
  let C := A + ∑ j ∈ univ.erase i, x j • B j
  have hC : C.IsHermitian :=
    hA.add (isSelfAdjoint_sum _ fun j _ ↦ (hB j).smul (by simp [IsSelfAdjoint]))
  have heq (t : ℝ) : A + ∑ j, Function.update x i t j • B j = C + t • B i := by
    rw [funext fun j ↦ Function.apply_update (fun k (a : ℝ) ↦ a • B k) x i t j,
      sum_update_of_mem (mem_univ i), sdiff_singleton_eq_erase]
    dsimp only [C]
    abel
  simp only [heq]
  have hs := hC.contDiff_inv_add_smul_sub_smul_one (hB i) hz (r + 1)
  have ht : ContDiff ℝ (r + 1) (fun t : ℝ ↦ (C + t • B i - z • 1)⁻¹.trace) := by
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', traceLinearMap_apply]
      using (traceLinearMap n ℝ ℂ).toContinuousLinearMap.contDiff.comp hs
  have hn := (contDiff_const (c := (Fintype.card n : ℂ)⁻¹)).mul ht
  refine ⟨l.contDiff.comp hn, fun t ↦ ?_⟩
  rw [← Real.norm_eq_abs, ← Function.comp_def,
    l.iteratedDeriv_comp_left hn.contDiffAt le_rfl]
  exact (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (hC.norm_iteratedDeriv_succ_normalized_trace_inv_add_smul_sub_smul_one_le (hB i) r t hz)
    (norm_nonneg _))

/-- **Resolvent Lindeberg comparison.** For an affine Hermitian matrix in independent real
coordinates indexed by any finite type, replacing their laws by laws whose moments agree through
order `r` changes its expected normalized resolvent trace by at most the sum of the `(r+1)`st
absolute moments weighted by `(rank(B i) / card n) ‖B i‖^(r+1) / |Im z|^(r+2)`.
The norm is the Euclidean operator norm. -/
theorem norm_integral_pi_normalized_trace_inv_add_sum_smul_sub_smul_one_sub_integral_pi_le
    (hA : A.IsHermitian) (hB : ∀ i, (B i).IsHermitian)
    {r : ℕ} (μ ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hμ : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (μ i))
    (hν : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (ν i))
    (hmom : ∀ i, ∀ k ≤ r, ∫ t, t ^ k ∂μ i = ∫ t, t ^ k ∂ν i)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖(∫ x : ι → ℝ, (Fintype.card n : ℂ)⁻¹ *
        (A + ∑ i, x i • B i - z • 1)⁻¹.trace ∂Measure.pi μ) -
      ∫ x : ι → ℝ, (Fintype.card n : ℂ)⁻¹ *
        (A + ∑ i, x i • B i - z • 1)⁻¹.trace ∂Measure.pi ν‖ ≤
      ∑ i, (((B i).rank : ℝ) / Fintype.card n) *
        ‖B i‖ ^ (r + 1) * |z.im|⁻¹ ^ (r + 2) *
        (∫ t, |t| ^ (r + 1) ∂μ i + ∫ t, |t| ^ (r + 1) ∂ν i) := by
  classical
  let f := fun x : ι → ℝ ↦
    (Fintype.card n : ℂ)⁻¹ * (A + ∑ i, x i • B i - z • 1)⁻¹.trace
  have hc : Continuous f := resolvent_test_continuous hA hB hz
  have hb (x : ι → ℝ) : ‖f x‖ ≤ |z.im|⁻¹ := by
    have hH : (A + ∑ i, x i • B i).IsHermitian :=
      hA.add (isSelfAdjoint_sum univ fun i _ ↦ (hB i).smul (by simp [IsSelfAdjoint]))
    exact (norm_normalized_trace_le_l2_opNorm _).trans
      (hH.l2_opNorm_inv_sub_smul_one_le hz)
  have hfi (ρ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ρ i)] :
      Integrable f (Measure.pi ρ) := Integrable.of_bound hc.aestronglyMeasurable _
        (Filter.Eventually.of_forall hb)
  obtain ⟨l, hl, he⟩ := exists_dual_vector'' ℝ
    ((∫ x, f x ∂Measure.pi μ) - ∫ x, f x ∂Measure.pi ν)
  have h := TauCeti.Probability.abs_integral_pi_sub_integral_pi_le_of_bounded μ ν hμ hν hmom
    (l.continuous.comp hc) (C := ‖l‖ * |z.im|⁻¹)
    (fun x ↦ (Real.norm_eq_abs _).symm.trans_le
      ((l.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _))))
    (M := fun i ↦ ‖l‖ * (((B i).rank : ℝ) / Fintype.card n *
      ((Nat.factorial (r + 1) : ℝ) * ‖B i‖ ^ (r + 1) * |z.im|⁻¹ ^ (r + 2))))
    (fun x i ↦ (resolvent_test_coordinate hA hB l hz r x i).1)
    (fun x i t ↦ (resolvent_test_coordinate hA hB l hz r x i).2 t)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at he
  simp only [Function.comp_def] at h
  rw [l.integral_comp_comm (hfi μ), l.integral_comp_comm (hfi ν), ← map_sub, he,
    abs_of_nonneg (norm_nonneg _)] at h
  refine h.trans (sum_le_sum fun i _ ↦ ?_)
  have hfact : (Nat.factorial (r + 1) : ℝ) ≠ 0 := by positivity
  have hcancel : ‖l‖ * (((B i).rank : ℝ) / Fintype.card n *
      ((Nat.factorial (r + 1) : ℝ) * ‖B i‖ ^ (r + 1) * |z.im|⁻¹ ^ (r + 2))) /
        (Nat.factorial (r + 1) : ℝ) =
      ‖l‖ * ((((B i).rank : ℝ) / Fintype.card n) *
        ‖B i‖ ^ (r + 1) * |z.im|⁻¹ ^ (r + 2)) := by
    field_simp
  rw [hcancel]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (by positivity) hl) (by positivity)

end Matrix.IsHermitian

section ComplexCoordinates

open scoped ComplexConjugate ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private def complexPerturbation (B : Matrix n n ℂ) (w : ℂ) : Matrix n n ℂ :=
  w • B + conj w • Bᴴ

omit [Fintype n] [DecidableEq n] in
private theorem isHermitian_complexPerturbation (B : Matrix n n ℂ) (w : ℂ) :
    (complexPerturbation B w).IsHermitian := by
  simpa only [complexPerturbation, conjTranspose_smul, starRingEnd_apply] using
    isHermitian_add_transpose_self (w • B)

omit [Fintype n] [DecidableEq n] in
private theorem continuous_complexPerturbation (B : Matrix n n ℂ) :
    Continuous (complexPerturbation B) := by
  unfold complexPerturbation
  fun_prop

omit [DecidableEq n] in
private theorem integral_trace_quadratic_eq {μ ν : Measure ℂ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (R B : Matrix n n ℂ) :
    let T := fun w ↦
      (R - R * complexPerturbation B w * R +
        R * complexPerturbation B w * R * complexPerturbation B w * R).trace
    Integrable T μ ∧ Integrable T ν ∧ (∫ w, T w ∂μ) = ∫ w, T w ∂ν := by
  let p : Fin 6 → ℕ := ![0, 1, 0, 2, 1, 0]
  let q : Fin 6 → ℕ := ![0, 0, 1, 0, 1, 2]
  let c : Fin 6 → ℂ := ![R.trace, -(R * B * R).trace, -(R * Bᴴ * R).trace,
    (R * B * R * B * R).trace, (R * B * R * Bᴴ * R).trace + (R * Bᴴ * R * B * R).trace,
    (R * Bᴴ * R * Bᴴ * R).trace]
  have hdeg (i : Fin 6) : p i + q i ≤ 2 := by fin_cases i <;> decide
  have heq (w : ℂ) :
      (R - R * complexPerturbation B w * R +
        R * complexPerturbation B w * R * complexPerturbation B w * R).trace =
      ∑ i, (w ^ p i * conj w ^ q i) * c i := by
    simp only [p, q, c, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, complexPerturbation, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, trace_sub, trace_add, trace_smul, smul_eq_mul]
    ring
  simp only [heq]
  have hint (ρ : Measure ℂ) [IsFiniteMeasure ρ]
      (hρ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ρ) (i : Fin 6) :
      Integrable (fun w : ℂ ↦ (w ^ p i * conj w ^ q i) * c i) ρ := by
    exact (TauCeti.Probability.integrable_pow_mul_conj_pow hρ (hdeg i)).mul_const _
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hint μ hμ i),
    integrable_finsetSum _ (fun i _ ↦ hint ν hν i), ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hint μ hμ i),
    integral_finsetSum _ (fun i _ ↦ hint ν hν i)]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [integral_mul_const]
  congr 1
  exact TauCeti.Probability.integral_pow_mul_conj_pow_eq hmean hsq habs (hdeg i)

private def replacementWeight (b c : ℝ) (w : ℂ) : ℝ :=
  ‖w‖ ^ 2 * min (b * c * ‖w‖) 1

private theorem norm_trace_resolvent_quadratic_remainder {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (B : Matrix n n ℂ) {z : ℂ} (hz : z.im ≠ 0) (w : ℂ) :
    let b := |z.im|⁻¹
    let c := 2 * ‖B‖
    let R := (A - z • 1)⁻¹
    let B₀ := complexPerturbation B w
    ‖(A + B₀ - z • 1)⁻¹.trace - (R - R * B₀ * R + R * B₀ * R * B₀ * R).trace‖ ≤
      (2 * B.rank) * b ^ 3 * c ^ 2 * replacementWeight b c w := by
  let b := |z.im|⁻¹
  let c := 2 * ‖B‖
  dsimp only
  have hnorm : ‖complexPerturbation B w‖ ≤ c * ‖w‖ := by
    calc
      _ ≤ ‖w • B‖ + ‖conj w • Bᴴ‖ := norm_add_le _ _
      _ = _ := by simp [c, norm_smul, l2_opNorm_conjTranspose]; ring
  have hrank : (complexPerturbation B w).rank ≤ 2 * B.rank := by
    calc
      _ ≤ (w • B).rank + (conj w • Bᴴ).rank := rank_add_le _ _
      _ ≤ B.rank + Bᴴ.rank := by
        rw [smul_eq_diagonal_mul, smul_eq_diagonal_mul]
        exact add_le_add (rank_mul_le_right _ _) (rank_mul_le_right _ _)
      _ = _ := by rw [rank_conjTranspose, two_mul]
  rw [← trace_sub]
  refine (hA.norm_trace_inv_add_sub_smul_one_sub_quadratic_le
    (isHermitian_complexPerturbation B w) hz).trans ?_
  calc
    _ ≤ (2 * B.rank : ℝ) * b ^ 3 * (c * ‖w‖) ^ 2 *
        min (b * (c * ‖w‖)) 1 := by
      gcongr
      exact_mod_cast hrank
    _ = _ := by
      rw [← mul_assoc b c ‖w‖]
      dsimp only [replacementWeight, b, c]
      ring

namespace IsHermitian

/-- For two complex laws with matching mixed moments through degree two, the difference of
expected resolvent traces along one Hermitian perturbation is bounded by truncated second
moments, weighted by the rank and Euclidean operator norm of its coefficient matrix.
The spectral parameter is nonreal. -/
theorem norm_integral_trace_inv_add_smul_add_conj_smul_sub_smul_one_sub_integral_le
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n n ℂ) {z : ℂ} (hz : z.im ≠ 0)
    {μ ν : Measure ℂ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν) :
    let b := |z.im|⁻¹
    let c := 2 * ‖B‖
    let f := fun w ↦ (A + (w • B + conj w • Bᴴ) - z • 1)⁻¹.trace
    ‖(∫ w, f w ∂μ) - ∫ w, f w ∂ν‖ ≤
      (2 * B.rank) * b ^ 3 * c ^ 2 *
        ((∫ w, ‖w‖ ^ 2 * min (b * c * ‖w‖) 1 ∂μ) +
          ∫ w, ‖w‖ ^ 2 * min (b * c * ‖w‖) 1 ∂ν) := by
  let b := |z.im|⁻¹
  let c := 2 * ‖B‖
  let R := (A - z • 1)⁻¹
  let f := fun w ↦ (A + complexPerturbation B w - z • 1)⁻¹.trace
  let T := fun w ↦
    (R - R * complexPerturbation B w * R +
      R * complexPerturbation B w * R * complexPerturbation B w * R).trace
  let K : ℝ := (2 * B.rank) * b ^ 3 * c ^ 2
  have hh (w : ℂ) := hA.add (isHermitian_complexPerturbation B w)
  have hcont := (continuous_const (y := A)).add (continuous_complexPerturbation B)
  have hf (ρ : Measure ℂ) [IsFiniteMeasure ρ] : Integrable f ρ :=
    hcont.integrable_trace_inv_sub_smul_one hh hz
  obtain ⟨hTμ, hTν, hT⟩ := integral_trace_quadratic_eq hμ hν hmean hsq habs R B
  have hrest (ρ : Measure ℂ) (hρ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ρ) :
      ‖∫ w, f w - T w ∂ρ‖ ≤ K * ∫ w, replacementWeight b c w ∂ρ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((hρ.norm_sq_mul_min_mul_one (by positivity : 0 ≤ b * c)).const_mul K)
      (Filter.Eventually.of_forall fun w ↦ ?_)
    exact norm_trace_resolvent_quadratic_remainder hA B hz w
  have heq : (∫ w, f w ∂μ) - ∫ w, f w ∂ν =
      (∫ w, f w - T w ∂μ) - ∫ w, f w - T w ∂ν := by
    rw [integral_sub (hf μ) hTμ, integral_sub (hf ν) hTν, hT]
    abel
  have hbound : ‖(∫ w, f w ∂μ) - ∫ w, f w ∂ν‖ ≤
      K * ((∫ w, replacementWeight b c w ∂μ) + ∫ w, replacementWeight b c w ∂ν) := by
    rw [heq, mul_add]
    exact (norm_sub_le _ _).trans (add_le_add (hrest μ hμ) (hrest ν hν))
  exact hbound

/-- Replacing each complex coordinate of an affine Hermitian matrix by a law with matching
mixed moments through degree two changes the expected resolvent trace by at most the sum
of the truncated squared-moment errors. Coordinates are independent under each product law.
The spectral parameter is nonreal. The Euclidean operator norms and ranks are those of the
coefficient matrices. -/
theorem norm_integral_pi_trace_inv_add_sum_smul_add_conj_smul_sub_smul_one_sub_integral_pi_le
    {ι : Type*} [Fintype ι] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (B : ι → Matrix n n ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (μ ν : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hμ : ∀ i, Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) (μ i))
    (hν : ∀ i, Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) (ν i))
    (hmean : ∀ i, (∫ w : ℂ, w ∂μ i) = ∫ w : ℂ, w ∂ν i)
    (hsq : ∀ i, (∫ w : ℂ, w ^ 2 ∂μ i) = ∫ w : ℂ, w ^ 2 ∂ν i)
    (habs : ∀ i, (∫ w : ℂ, ‖w‖ ^ 2 ∂μ i) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν i) :
    let b := |z.im|⁻¹
    let c := fun i ↦ 2 * ‖B i‖
    let f := fun x : ι → ℂ ↦ (A + ∑ i, (x i • B i + conj (x i) • (B i)ᴴ) - z • 1)⁻¹.trace
    ‖(∫ x, f x ∂Measure.pi μ) - ∫ x, f x ∂Measure.pi ν‖ ≤
      ∑ i, (2 * (B i).rank) * b ^ 3 * (c i) ^ 2 *
        ((∫ w : ℂ, ‖w‖ ^ 2 * min (b * c i * ‖w‖) 1 ∂μ i) +
          ∫ w : ℂ, ‖w‖ ^ 2 * min (b * c i * ‖w‖) 1 ∂ν i) := by
  classical
  let H (x : ι → ℂ) := A + ∑ i, complexPerturbation (B i) (x i)
  let f (x : ι → ℂ) := (H x - z • 1)⁻¹.trace
  have hH (x) : (H x).IsHermitian :=
    hA.add (isSelfAdjoint_sum univ fun i _ ↦ isHermitian_complexPerturbation (B i) (x i))
  have hcont : Continuous H :=
    continuous_const.add (continuous_finsetSum _ fun i _ ↦
      (continuous_complexPerturbation (B i)).comp (continuous_apply i))
  have hint (s : Finset ι) : Integrable f (Measure.pi fun i ↦ if i ∈ s then ν i else μ i) := by
    have (i : ι) : IsProbabilityMeasure (if i ∈ s then ν i else μ i) := by split <;> infer_instance
    exact hcont.integrable_trace_inv_sub_smul_one hH hz
  refine TauCeti.norm_integral_pi_sub_integral_pi_le_of_ae_slice_le (α := fun _ ↦ ℂ) μ ν hint _
    (fun _ i _ ↦ ae_of_all _ fun x ↦ ?_)
  let C := A + ∑ j ∈ univ.erase i, complexPerturbation (B j)
    (if hj : j ≠ i then x ⟨j, hj⟩ else 0)
  have hC : C.IsHermitian :=
    hA.add (isSelfAdjoint_sum _ fun j _ ↦ isHermitian_complexPerturbation (B j) _)
  have hsplit (t : ℂ) :
      H ((MeasurableEquiv.piSplitAt i (fun _ : ι ↦ ℂ)).symm (t, x)) =
        C + complexPerturbation (B i) t := by
    unfold H C
    rw [← sum_erase_add _ _ (mem_univ i), ← add_assoc, MeasurableEquiv.piSplitAt_symm_apply_self]
    congr 2
    apply sum_congr rfl
    intro j hj
    have hji := ne_of_mem_erase hj
    simp only [dite_eq_left hji, MeasurableEquiv.piSplitAt_symm_apply_ne i _ j hji]
  simpa only [f, hsplit, complexPerturbation] using
    hC.norm_integral_trace_inv_add_smul_add_conj_smul_sub_smul_one_sub_integral_le
      (B i) hz (hμ i) (hν i) (hmean i) (hsq i) (habs i)

end IsHermitian

end Matrix

end ComplexCoordinates

namespace ProbabilityTheory.HasLaw

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] {r : ℕ}
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
  {μ ν : ι → Measure ℝ}
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
  {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
  {A : Matrix n n ℂ} {B : ι → Matrix n n ℂ}

/-- Resolvent Lindeberg comparison on arbitrary sample spaces. The two joint product-law
hypotheses encode independence within each coordinate family, and can be obtained with
`iIndepFun.hasLaw_pi`. No coupling between the two families is required. -/
theorem norm_integral_normalized_trace_inv_add_sum_smul_sub_smul_one_sub_integral_le
    (hX : HasLaw X (Measure.pi μ) P) (hY : HasLaw Y (Measure.pi ν) Q)
    (hA : A.IsHermitian) (hB : ∀ i, (B i).IsHermitian)
    (hμ : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (μ i))
    (hν : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (ν i))
    (hmom : ∀ i, ∀ k ≤ r, ∫ t, t ^ k ∂μ i = ∫ t, t ^ k ∂ν i)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖(∫ s, (Fintype.card n : ℂ)⁻¹ *
        (A + ∑ i, X s i • B i - z • 1)⁻¹.trace ∂P) -
      ∫ s, (Fintype.card n : ℂ)⁻¹ *
        (A + ∑ i, Y s i • B i - z • 1)⁻¹.trace ∂Q‖ ≤
      ∑ i, (((B i).rank : ℝ) / Fintype.card n) *
        ‖B i‖ ^ (r + 1) * |z.im|⁻¹ ^ (r + 2) *
        (∫ t, |t| ^ (r + 1) ∂μ i + ∫ t, |t| ^ (r + 1) ∂ν i) := by
  have hc := Matrix.IsHermitian.resolvent_test_continuous hA hB hz
  have hx := hX.integral_comp hc.aestronglyMeasurable
  have hy := hY.integral_comp hc.aestronglyMeasurable
  simp only [Function.comp_def] at hx hy
  rw [hx, hy]
  exact hA.norm_integral_pi_normalized_trace_inv_add_sum_smul_sub_smul_one_sub_integral_pi_le
    hB μ ν hμ hν hmom hz

end ProbabilityTheory.HasLaw
