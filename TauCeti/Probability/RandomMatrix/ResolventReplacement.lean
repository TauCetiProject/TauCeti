/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Derivative
public import TauCeti.Probability.Moments.Lindeberg
public import Mathlib.Probability.HasLaw

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

The proof combines `Matrix.IsHermitian.iteratedDeriv_inv_add_smul_sub_smul_one` with the scalar
Lindeberg replacement theorem `TauCeti.Probability.abs_integral_pi_sub_integral_pi_le_of_bounded`.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American
  Mathematical Society (2012), §§2.2, 2.4.
-/

public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped Matrix.Norms.L2Operator ContDiff

attribute [local instance] matrixComplexNormedAlgebraReal

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {d : ℕ}
  {A : Matrix n n ℂ} {B : Fin d → Matrix n n ℂ}

private theorem resolvent_test_continuous (hA : A.IsHermitian)
    (hB : ∀ i, (B i).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun x : Fin d → ℝ ↦
      (Fintype.card n : ℂ)⁻¹ * (A + ∑ i, x i • B i - z • 1)⁻¹.trace) := by
  have hH (x : Fin d → ℝ) : (A + ∑ i, x i • B i).IsHermitian :=
    hA.add (isSelfAdjoint_sum univ fun i _ ↦ (hB i).smul (by simp [IsSelfAdjoint]))
  have hc : Continuous (fun x : Fin d → ℝ ↦ A + ∑ i, x i • B i - z • 1) := by fun_prop
  have hi : Continuous (fun x : Fin d → ℝ ↦ (A + ∑ i, x i • B i - z • 1)⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨u, hu⟩ := (hH x).isUnit_sub_smul_one_of_im_ne_zero hz
    have hi : ContinuousAt Ring.inverse (A + ∑ i, x i • B i - z • 1) :=
      hu ▸ NormedRing.inverse_continuousAt u
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using!
      hi.comp (f := fun y : Fin d → ℝ ↦ A + ∑ i, y i • B i - z • 1)
        hc.continuousAt
  exact continuous_const.mul
    (((traceLinearMap n ℂ ℂ).restrictScalars ℝ).toContinuousLinearMap.continuous.comp hi)

private theorem resolvent_test_coordinate (hA : A.IsHermitian)
    (hB : ∀ i, (B i).IsHermitian) (l : ℂ →L[ℝ] ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (r : ℕ) (x : Fin d → ℝ) (i : Fin d) :
    let f := fun t : ℝ ↦ l ((Fintype.card n : ℂ)⁻¹ *
      (A + ∑ j, Function.update x i t j • B j - z • 1)⁻¹.trace)
    ContDiff ℝ (r + 1) f ∧ ∀ t, ‖iteratedDeriv (r + 1) f t‖ ≤
      ‖l‖ * (((B i).rank : ℝ) / Fintype.card n *
        ((Nat.factorial (r + 1) : ℝ) * ‖B i‖ ^ (r + 1) * |z.im|⁻¹ ^ (r + 2))) := by
  let C := A + ∑ j ∈ univ.erase i, x j • B j
  have hC : C.IsHermitian :=
    hA.add (isSelfAdjoint_sum _ fun j _ ↦ (hB j).smul (by simp [IsSelfAdjoint]))
  have heq (t : ℝ) : A + ∑ j, Function.update x i t j • B j = C + t • B i := by
    rw [← sum_erase_add _ _ (mem_univ i)]
    simp only [Function.update_self]
    have hsum : ∑ j ∈ univ.erase i, Function.update x i t j • B j =
        ∑ j ∈ univ.erase i, x j • B j :=
      sum_congr rfl fun j hj ↦ by simp [Function.update_of_ne (ne_of_mem_erase hj)]
    rw [hsum]
    simp only [C, add_assoc]
  simp only [heq]
  have hs := hC.contDiff_inv_add_smul_sub_smul_one (hB i) hz (r + 1)
  have ht : ContDiff ℝ (r + 1) (fun t : ℝ ↦ (C + t • B i - z • 1)⁻¹.trace) :=
    ((traceLinearMap n ℂ ℂ).restrictScalars ℝ).toContinuousLinearMap.contDiff.comp hs
  exact ⟨l.contDiff.comp (contDiff_const.mul ht), fun t ↦
    hC.norm_iteratedDeriv_succ_normalized_trace_inv_add_smul_sub_smul_one_le (hB i) l r t hz⟩

/-- **Resolvent Lindeberg comparison.** For an affine Hermitian matrix in independent real
coordinates, replacing their laws by laws whose moments agree through order `r` changes its
expected normalized resolvent trace by at most the sum of the `(r+1)`st absolute moments weighted
by `(rank(B i) / card n) ‖B i‖^(r+1) / |Im z|^(r+2)`.
The norm is the Euclidean operator norm. -/
theorem norm_integral_pi_normalized_trace_inv_sub_integral_pi_le
    (hA : A.IsHermitian) (hB : ∀ i, (B i).IsHermitian)
    {r : ℕ} (μ ν : Fin d → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hμ : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (μ i))
    (hν : ∀ i, Integrable (fun t : ℝ ↦ |t| ^ (r + 1)) (ν i))
    (hmom : ∀ i, ∀ k ≤ r, ∫ t, t ^ k ∂μ i = ∫ t, t ^ k ∂ν i)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖(∫ x : Fin d → ℝ, (Fintype.card n : ℂ)⁻¹ *
        (A + ∑ i, x i • B i - z • 1)⁻¹.trace ∂Measure.pi μ) -
      ∫ x : Fin d → ℝ, (Fintype.card n : ℂ)⁻¹ *
        (A + ∑ i, x i • B i - z • 1)⁻¹.trace ∂Measure.pi ν‖ ≤
      ∑ i, (((B i).rank : ℝ) / Fintype.card n) *
        ‖B i‖ ^ (r + 1) * |z.im|⁻¹ ^ (r + 2) *
        (∫ t, |t| ^ (r + 1) ∂μ i + ∫ t, |t| ^ (r + 1) ∂ν i) := by
  let f := fun x : Fin d → ℝ ↦
    (Fintype.card n : ℂ)⁻¹ * (A + ∑ i, x i • B i - z • 1)⁻¹.trace
  have hc : Continuous f := resolvent_test_continuous hA hB hz
  have hb (x : Fin d → ℝ) : ‖f x‖ ≤ |z.im|⁻¹ := by
    have hH : (A + ∑ i, x i • B i).IsHermitian :=
      hA.add (isSelfAdjoint_sum univ fun i _ ↦ (hB i).smul (by simp [IsSelfAdjoint]))
    exact (norm_normalized_trace_le_l2_opNorm _).trans
      (hH.l2_opNorm_inv_sub_smul_one_le hz)
  have hfi (ρ : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (ρ i)] :
      Integrable f (Measure.pi ρ) := Integrable.of_bound hc.aestronglyMeasurable _
        (Filter.Eventually.of_forall hb)
  obtain ⟨l, hl, he⟩ := exists_dual_vector'' ℝ
    ((∫ x, f x ∂Measure.pi μ) - ∫ x, f x ∂Measure.pi ν)
  have h := TauCeti.Probability.abs_integral_pi_sub_integral_pi_le_of_bounded μ ν hμ hν hmom
    (l.continuous.comp hc) (C := ‖l‖ * |z.im|⁻¹)
    (fun x ↦ (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)))
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

namespace ProbabilityTheory.HasLaw

variable {n : Type*} [Fintype n] [DecidableEq n] {d r : ℕ}
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
  {μ ν : Fin d → Measure ℝ}
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
  {X : Ω → Fin d → ℝ} {Y : Ω' → Fin d → ℝ}
  {A : Matrix n n ℂ} {B : Fin d → Matrix n n ℂ}

/-- Resolvent Lindeberg comparison on arbitrary sample spaces. The two joint product-law
hypotheses encode independence within each coordinate family, and can be obtained with
`iIndepFun.hasLaw_pi`. No coupling between the two families is required. -/
theorem norm_integral_normalized_trace_inv_sub_integral_le
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
  exact hA.norm_integral_pi_normalized_trace_inv_sub_integral_pi_le hB μ ν hμ hν hmom hz

end ProbabilityTheory.HasLaw
