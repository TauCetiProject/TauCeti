/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Expansion
public import Mathlib.Probability.HasLaw

import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.Matrix.L2OpNorm.Single
import TauCeti.MeasureTheory.Integral.Pi.Replacement

import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.Data.Matrix.Basis
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite-variance replacement for Hermitian block resolvents

Replacing independent complex entries with entries having the same first and second moments
preserves the asymptotic expected resolvent trace of a shifted Hermitian dilation. Each entry and
its conjugate are replaced together, so its real and imaginary parts may be dependent. The
moment hypotheses match the complex mean, the complex second moment, and the second absolute
moment. A second-order resolvent expansion bounds the error by the square of the entry times
a bounded factor that tends to zero at the matrix scaling.

## References

* T. Tao, *Topics in Random Matrix Theory*, AMS, 2012, §2.2.4 (Lindeberg swapping).
* C. Bordenave and D. Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), 1–89, §5.
-/

public section

noncomputable section

open Filter Finset MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private def complexPerturbation (B : Matrix n n ℂ) (w : ℂ) : Matrix n n ℂ :=
  w • B + conj w • Bᴴ

omit [Fintype n] [DecidableEq n] in
private theorem isHermitian_complexPerturbation (B : Matrix n n ℂ) (w : ℂ) :
    (complexPerturbation B w).IsHermitian := by
  simp [complexPerturbation, IsHermitian, conjTranspose_smul, add_comm]

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
    simp [p, q, c, Fin.sum_univ_succ, complexPerturbation, mul_add, add_mul,
      smul_smul, trace_sub, trace_add, trace_smul, smul_eq_mul]
    ring
  simp only [heq]
  have hint (ρ : Measure ℂ) [IsProbabilityMeasure ρ]
      (hρ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ρ) (i : Fin 6) :
      Integrable (fun w : ℂ ↦ (w ^ p i * conj w ^ q i) * c i) ρ := by
    apply Integrable.mul_const
    apply (integrable_norm_iff (by fun_prop)).mp
    simpa only [id_eq, norm_mul, norm_pow, Complex.norm_conj, ← pow_add] using
      integrable_norm_pow_of_le (f := id) aestronglyMeasurable_id (hdeg i) hρ
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hint μ hμ i),
    integrable_finsetSum _ (fun i _ ↦ hint ν hν i), ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hint μ hμ i),
    integral_finsetSum _ (fun i _ ↦ hint ν hν i)]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [integral_mul_const]
  congr 1
  fin_cases i
  · simp [p, q]
  · simpa [p, q] using hmean
  · have he : (∫ w : ℂ, conj w ∂μ) = ∫ w : ℂ, conj w ∂ν :=
      (integral_conj (f := id)).trans ((congrArg conj hmean).trans (integral_conj (f := id)).symm)
    simpa [p, q] using he
  · simpa [p, q] using hsq
  · simpa [p, q, Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal] using
      congrArg Complex.ofReal habs
  · simpa [p, q, ← map_pow, integral_conj] using congrArg conj hsq

private def replacementWeight (b c : ℝ) (w : ℂ) : ℝ :=
  ‖w‖ ^ 2 * min (b * c * ‖w‖) 1

private theorem integrable_replacementWeight {μ : Measure ℂ}
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ) {b c : ℝ} (hbc : 0 ≤ b * c) :
    Integrable (replacementWeight b c) μ := by
  refine hμ.mono' (by unfold replacementWeight; fun_prop) (Filter.Eventually.of_forall fun w ↦ ?_)
  unfold replacementWeight
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (min_le_right _ _)

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

private theorem norm_integral_trace_resolvent_sub_le
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n n ℂ) {z : ℂ} (hz : z.im ≠ 0)
    {μ ν : Measure ℂ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν) :
    let b := |z.im|⁻¹
    let c := 2 * ‖B‖
    let f := fun w ↦ (A + complexPerturbation B w - z • 1)⁻¹.trace
    ‖(∫ w, f w ∂μ) - ∫ w, f w ∂ν‖ ≤
      (2 * B.rank) * b ^ 3 * c ^ 2 *
        ((∫ w, replacementWeight b c w ∂μ) + ∫ w, replacementWeight b c w ∂ν) := by
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
  have hf (ρ : Measure ℂ) [IsProbabilityMeasure ρ] : Integrable f ρ := by
    refine Integrable.of_bound
      (hcont.matrix_trace_inv_sub_smul_one hh hz).aestronglyMeasurable (Fintype.card n * b)
      (Filter.Eventually.of_forall fun w ↦ ?_)
    exact (norm_trace_le_card_mul_l2_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hh w).l2_opNorm_inv_sub_smul_one_le hz) (by positivity))
  obtain ⟨hTμ, hTν, hT⟩ := integral_trace_quadratic_eq hμ hν hmean hsq habs R B
  have hrest (ρ : Measure ℂ) (hρ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ρ) :
      ‖∫ w, f w - T w ∂ρ‖ ≤ K * ∫ w, replacementWeight b c w ∂ρ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((integrable_replacementWeight hρ (by positivity)).const_mul K)
      (Filter.Eventually.of_forall fun w ↦ ?_)
    exact norm_trace_resolvent_quadratic_remainder hA B hz w
  have heq : (∫ w, f w ∂μ) - ∫ w, f w ∂ν =
      (∫ w, f w - T w ∂μ) - ∫ w, f w - T w ∂ν := by
    rw [integral_sub (hf μ) hTμ, integral_sub (hf ν) hTν, hT]
    abel
  dsimp only
  rw [heq]
  exact (norm_sub_le _ _).trans (by rw [mul_add]; exact add_le_add (hrest μ hμ) (hrest ν hν))

/-- Replacing each complex coordinate of an affine Hermitian matrix by a law with matching
mixed moments through degree two changes the expected resolvent trace by at most the sum
of the truncated squared-moment errors. Coordinates are independent under each product law.
The Euclidean operator norms and ranks are those of the coefficient matrices. -/
theorem IsHermitian.norm_integral_pi_trace_inv_add_sum_smul_add_conj_smul_sub_le
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
  have hf : Continuous f := hcont.matrix_trace_inv_sub_smul_one hH hz
  have hint (s : Finset ι) : Integrable f (Measure.pi fun i ↦ if i ∈ s then ν i else μ i) := by
    have (i : ι) : IsProbabilityMeasure (if i ∈ s then ν i else μ i) := by split <;> infer_instance
    refine Integrable.of_bound hf.aestronglyMeasurable (Fintype.card n * |z.im|⁻¹)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    exact (norm_trace_le_card_mul_l2_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hH x).l2_opNorm_inv_sub_smul_one_le hz) (by positivity))
  refine norm_integral_pi_sub_integral_pi_le_of_splitAt μ ν hint _ fun i x ↦ ?_
  let e := Equiv.piSplitAt i (fun _ : ι ↦ ℂ)
  let C := A + ∑ j ∈ univ.erase i, complexPerturbation (B j) (e.symm (0, x) j)
  have hC : C.IsHermitian :=
    hA.add (isSelfAdjoint_sum _ fun j _ ↦ isHermitian_complexPerturbation (B j) _)
  have hx (t : ℂ) : e.symm (t, x) i = t := congrArg Prod.fst (e.apply_symm_apply (t, x))
  have hx' (t : ℂ) (j : {j // j ≠ i}) : e.symm (t, x) j = x j :=
    congrFun (congrArg Prod.snd (e.apply_symm_apply (t, x))) j
  have hsplit (t : ℂ) :
      H ((Equiv.piSplitAt i (fun _ : ι ↦ ℂ)).symm (t, x)) = C + complexPerturbation (B i) t := by
    unfold H C
    rw [← sum_erase_add _ _ (mem_univ i), ← add_assoc, hx]
    congr 2
    apply sum_congr rfl
    intro j hj
    have hji := ne_of_mem_erase hj
    rw [hx' t ⟨j, hji⟩, hx' 0 ⟨j, hji⟩]
  simpa only [f, hsplit, replacementWeight] using
    norm_integral_trace_resolvent_sub_le hC (B i) hz (hμ i) (hν i) (hmean i) (hsq i) (habs i)

private theorem fromBlocks_add_sum_complexPerturbation_single
    {k : Type*} [Fintype k] [DecidableEq k] (D : Matrix k k ℂ)
    (a : ℝ) (x : k × k → ℂ) :
    fromBlocks 0 D Dᴴ 0 +
        ∑ i : k × k, complexPerturbation (single (Sum.inl i.1) (Sum.inr i.2) (a : ℂ)) (x i) =
      fromBlocks 0 (D + a • Matrix.of (fun i j ↦ x (i, j)))
        (D + a • Matrix.of (fun i j ↦ x (i, j)))ᴴ 0 := by
  have hsum :
      ∑ i : k × k, complexPerturbation (single (Sum.inl i.1) (Sum.inr i.2) (a : ℂ)) (x i) =
        fromBlocks 0 (a • Matrix.of (fun i j ↦ x (i, j)))
          (a • Matrix.of (fun i j ↦ x (i, j)))ᴴ 0 := by
    ext (i | i) (j | j)
    · simp [complexPerturbation, Matrix.sum_apply, conjTranspose_single]
    · simp [complexPerturbation, Matrix.sum_apply, conjTranspose_single, Matrix.single_apply,
        Complex.real_smul, mul_comm, ← Prod.mk.injEq]
    · simp [complexPerturbation, Matrix.sum_apply, conjTranspose_single, Matrix.single_apply,
        Complex.real_smul, mul_comm, ← Prod.mk.injEq, and_comm]
    · simp [complexPerturbation, Matrix.sum_apply, conjTranspose_single]
  simp only [hsum, fromBlocks_add, conjTranspose_add, zero_add]

private theorem tendsto_integral_replacementWeight {μ : Measure ℂ}
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ) {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun k : ℕ ↦ ∫ w, replacementWeight b (2 * (Real.sqrt (k + 1))⁻¹) w ∂μ)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun k : ℕ ↦ (Real.sqrt ((k : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ) (f := fun _ ↦ (0 : ℝ)) (fun w : ℂ ↦ ‖w‖ ^ 2)
    (F := fun k (w : ℂ) ↦ replacementWeight b (2 * (Real.sqrt (k + 1))⁻¹) w)
    (fun _ ↦ by unfold replacementWeight; fun_prop) hμ
    (fun k ↦ Filter.Eventually.of_forall fun w ↦ by
      unfold replacementWeight
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (min_le_right _ _))
    (Filter.Eventually.of_forall fun w ↦ by
      have hh := ((((hc.const_mul (2 : ℝ)).const_mul b).mul_const ‖w‖).min
        (tendsto_const_nhds (x := (1 : ℝ)))).const_mul (‖w‖ ^ 2)
      simpa [replacementWeight] using hh)
  simpa using ht

private theorem normalized_rank_factor (k : ℕ) (b : ℝ) :
    ‖((2 : ℂ) * (k + 1))⁻¹‖ * ((k + 1 : ℝ) ^ 2 * 2) *
      b ^ 3 * (2 * (Real.sqrt (k + 1))⁻¹) ^ 2 = 4 * b ^ 3 := by
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hsize : ‖(k + 1 : ℂ)‖ = (k : ℝ) + 1 := by
    exact_mod_cast Complex.norm_natCast (k + 1)
  have ha : (Real.sqrt (k + 1))⁻¹ ^ 2 = ((k : ℝ) + 1)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 1)]
  rw [norm_inv, norm_mul, htwo, hsize, mul_pow, ha]
  field_simp
  ring

private theorem norm_sub_integral_normalized_trace_inv_fromBlocks_le
    (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (k : ℕ) (D : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Y (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f x := ((2 : ℂ) * (k + 1))⁻¹ * (fromBlocks 0 (Y x) (Y x)ᴴ 0 - z • 1)⁻¹.trace
    let b := |z.im|⁻¹
    let c := 2 * (Real.sqrt (k + 1))⁻¹
    ‖(∫ x, f x ∂Measure.pi (fun _ ↦ μ)) - ∫ x, f x ∂Measure.pi (fun _ ↦ ν)‖ ≤
      4 * b ^ 3 * ((∫ w, replacementWeight b c w ∂μ) + ∫ w, replacementWeight b c w ∂ν) := by
  dsimp only
  let b := |z.im|⁻¹
  let c := 2 * (Real.sqrt (k + 1))⁻¹
  let a : ℝ := (Real.sqrt (k + 1))⁻¹
  let B (i : Fin (k + 1) × Fin (k + 1)) :
      Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) ℂ :=
    single (Sum.inl i.1) (Sum.inr i.2) (a : ℂ)
  let A := fromBlocks 0 D Dᴴ 0
  have hA : A.IsHermitian := by simp [A, IsHermitian, fromBlocks_conjTranspose]
  have h := hA.norm_integral_pi_trace_inv_add_sum_smul_add_conj_smul_sub_le
    B hz (fun _ ↦ μ) (fun _ ↦ ν) (fun _ ↦ hμ) (fun _ ↦ hν)
    (fun _ ↦ hmean) (fun _ ↦ hsq) (fun _ ↦ habs)
  have hnorm (i) : ‖B i‖ = a := by
    have ha : 0 ≤ a := by positivity
    simp only [B, l2_opNorm_single, Complex.norm_real, Real.norm_of_nonneg ha]
  have hrank (i) : (B i).rank ≤ 1 := by
    dsimp only [B]
    rw [single_eq_smul_single_one _ _ (a : ℂ), smul_eq_diagonal_mul,
      single_eq_single_vecMulVec_single]
    exact (rank_mul_le_right _ _).trans (rank_vecMulVec_le _ _)
  have heq (x : Fin (k + 1) × Fin (k + 1) → ℂ) :
      A + ∑ i, (x i • B i + conj (x i) • (B i)ᴴ) =
        fromBlocks 0 (D + a • Matrix.of (fun i j ↦ x (i, j)))
          (D + a • Matrix.of (fun i j ↦ x (i, j)))ᴴ 0 :=
    fromBlocks_add_sum_complexPerturbation_single D a x
  simp only [heq, hnorm] at h
  rw [← sum_mul, ← sum_mul, ← sum_mul] at h
  rw [integral_const_mul, integral_const_mul, ← mul_sub, norm_mul]
  refine (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans ?_
  -- There are (k + 1)² entries and each changes only two rows of the dilation.
  have hsum : (∑ i : Fin (k + 1) × Fin (k + 1), (2 * (B i).rank : ℝ)) ≤
      (k + 1 : ℝ) ^ 2 * 2 := by
    calc
      _ ≤ ∑ _i : Fin (k + 1) × Fin (k + 1), (2 : ℝ) := by
        refine sum_le_sum fun i _ ↦ ?_
        have hi : ((B i).rank : ℝ) ≤ 1 := by exact_mod_cast hrank i
        linarith
      _ = _ := by simp [Fintype.card_prod, sq]
  let E := (∫ w, replacementWeight b c w ∂μ) + ∫ w, replacementWeight b c w ∂ν
  have hE : 0 ≤ E :=
    add_nonneg (integral_nonneg fun _ ↦ by unfold replacementWeight; positivity)
      (integral_nonneg fun _ ↦ by unfold replacementWeight; positivity)
  calc
    _ ≤ ‖((2 : ℂ) * (k + 1))⁻¹‖ * (((k + 1 : ℝ) ^ 2 * 2) * b ^ 3 * (2 * a) ^ 2 * E) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum (by positivity))
          (sq_nonneg _)) hE
    _ = (‖((2 : ℂ) * (k + 1))⁻¹‖ * ((k + 1 : ℝ) ^ 2 * 2) * b ^ 3 * (2 * a) ^ 2) * E := by ring
    _ = _ := by rw [normalized_rank_factor k b]

/-- For two i.i.d. complex entry product laws of finite second moment whose mixed moments
match through degree two, the expected normalized resolvent traces of their Hermitian
dilations have vanishing difference. The matrices are scaled by the reciprocal square root
of their dimension before adding the same arbitrary deterministic matrix. -/
theorem tendsto_sub_integral_normalized_trace_inv_fromBlocks
    (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (D : ∀ k : ℕ, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Y (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f (k : ℕ) x := ((2 : ℂ) * (k + 1))⁻¹ *
      (fromBlocks 0 (Y k x) (Y k x)ᴴ 0 - z • 1)⁻¹.trace
    Tendsto (fun k : ℕ ↦ (∫ x, f k x ∂Measure.pi (fun _ ↦ μ)) -
      ∫ x, f k x ∂Measure.pi (fun _ ↦ ν)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦
    norm_sub_integral_normalized_trace_inv_fromBlocks_le μ ν hμ hν hmean hsq habs k (D k) hz) ?_
  have hb : 0 ≤ |z.im|⁻¹ := by positivity
  have hsum := (tendsto_integral_replacementWeight hμ hb).add
    (tendsto_integral_replacementWeight hν hb)
  have hlim := hsum.const_mul (4 * |z.im|⁻¹ ^ (3 : ℕ))
  simpa only [add_zero, mul_zero] using hlim

end Matrix

namespace ProbabilityTheory.HasLaw

open Matrix

/-- Finite-variance replacement for the expected normalized resolvent traces of shifted
Hermitian dilations on arbitrary sample spaces. The joint product laws encode independence
of the entries within each matrix, with no restriction on coupling across dimensions. -/
theorem tendsto_sub_integral_normalized_trace_inv_fromBlocks
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {μ ν : Measure ℂ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : (k : ℕ) → Ω → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    {Y : (k : ℕ) → Ω' → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hX : ∀ k, HasLaw (X k) (Measure.pi (fun _ ↦ μ)) P)
    (hY : ∀ k, HasLaw (Y k) (Measure.pi (fun _ ↦ ν)) Q)
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (D : ∀ k : ℕ, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Z (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f (k : ℕ) x := ((2 : ℂ) * (k + 1))⁻¹ *
      (fromBlocks 0 (Z k x) (Z k x)ᴴ 0 - z • 1)⁻¹.trace
    Tendsto (fun k ↦ (∫ ω, f k (X k ω) ∂P) - ∫ ω, f k (Y k ω) ∂Q) atTop (𝓝 0) := by
  intro Z f
  have hc (k : ℕ) : Continuous (f k) := by
    have hZ : Continuous (Z k) := by
      unfold Z
      fun_prop
    let H x := fromBlocks 0 (Z k x) (Z k x)ᴴ 0
    have hH : Continuous H :=
      continuous_const.matrix_fromBlocks hZ hZ.matrix_conjTranspose continuous_const
    have hh (x) : (H x).IsHermitian := by simp [H, IsHermitian, fromBlocks_conjTranspose]
    exact continuous_const.mul (hH.matrix_trace_inv_sub_smul_one hh hz)
  have hx (k) := (hX k).integral_comp (hc k).aestronglyMeasurable
  have hy (k) := (hY k).integral_comp (hc k).aestronglyMeasurable
  simp only [Function.comp_def] at hx hy
  simp_rw [hx, hy]
  exact Matrix.tendsto_sub_integral_normalized_trace_inv_fromBlocks μ ν hμ hν hmean hsq habs D hz

end ProbabilityTheory.HasLaw
