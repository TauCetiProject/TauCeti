/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nickrobbins95, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.InnerProductSpace.BilinearNet
import TauCeti.Analysis.Normed.Module.CoveringNumber
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Operator norms of matrices with independent sub-Gaussian entries

If the entries of a real rectangular random matrix are independent and have sub-Gaussian
moment-generating functions with variance proxy `K²`, then its Euclidean operator norm exceeds
`8 K (√(card m) + √(card n) + t)` with probability at most `2 exp(-t²)`.

The proof evaluates the matrix on two quarter-nets of unit spheres and applies the scalar
sub-Gaussian tail bound and a finite union bound. The nets, their cardinality estimates, and
the deterministic operator-norm reduction use the existing covering APIs. Empty row or column
index types and the zero variance proxy are allowed.

## Provenance

prove2me-import: the net and union-bound argument is adapted from Nickrobbins95's accepted
Prove2Me solution `d2ecdbeb-62c5-49cf-a7d1-91479ac18e8b` for
`HighDimProb.RandomMatrices.norm_of_subgaussian_matrix_v2`, exported in
`prove2me/formalpedia` at revision `483b17acc03144d875bd376cffb4e6d96aca8971`.
The source uses an Orlicz norm; here the hypotheses use Mathlib's `HasSubgaussianMGF` directly.

* https://prove2.me/submissions/d2ecdbeb-62c5-49cf-a7d1-91479ac18e8b
* R. Vershynin, *High-Dimensional Probability* (2018), Theorem 4.4.5.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator NNReal

namespace ProbabilityTheory

/-- The cardinality cost of two quarter-nets is absorbed by the Gaussian exponent. -/
private lemma net_card_mul_exp_le (m n : ℕ) {t a b : ℝ}
    (ha : a ≤ 9 ^ n) (hb : b ≤ 9 ^ m) (hb0 : 0 ≤ b) (ht : 0 ≤ t) :
    a * b * exp (-(4 * (√m + √n + t) ^ 2)) ≤ exp (-(t ^ 2)) := by
  have h9 : (9 : ℝ) ≤ exp 3 := by
    have he : (2.7 : ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    exact (by norm_num : (9 : ℝ) ≤ 2.7 ^ 3).trans
      (pow_le_pow_left₀ (by norm_num) he 3)
  have hpow (k : ℕ) : (9 : ℝ) ^ k ≤ exp (3 * k) := by
    calc
      (9 : ℝ) ^ k ≤ exp 3 ^ k := pow_le_pow_left₀ (by norm_num) h9 k
      _ = exp (3 * k) := by rw [← Real.exp_nat_mul]; ring_nf
  have hsq : (m : ℝ) + n + t ^ 2 ≤ (√m + √n + t) ^ 2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
      Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
      mul_nonneg (Real.sqrt_nonneg (m : ℝ)) (Real.sqrt_nonneg (n : ℝ)),
      mul_nonneg (Real.sqrt_nonneg (m : ℝ)) ht,
      mul_nonneg (Real.sqrt_nonneg (n : ℝ)) ht]
  calc
    a * b * exp (-(4 * (√m + √n + t) ^ 2))
        ≤ exp (3 * n) * exp (3 * m) * exp (-(4 * (√m + √n + t) ^ 2)) := by
      gcongr
      · exact ha.trans (hpow n)
      · exact hb.trans (hpow m)
    _ = exp (3 * n + 3 * m - 4 * (√m + √n + t) ^ 2) := by
      rw [← exp_add, ← exp_add]
      ring_nf
    _ ≤ exp (-(t ^ 2)) := by
      apply exp_le_exp.2
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The Euclidean operator norm of a real random matrix with independent sub-Gaussian entries
has a Gaussian tail above the dimension-dependent scale. Each entry has variance proxy `K²`
in Mathlib's MGF convention. The matrix norm is the Euclidean operator norm supplied by
`Matrix.Norms.L2Operator`; no positivity assumptions on the dimensions or `K` are needed. -/
theorem iIndepFun.measureReal_matrix_opNorm_gt_le
    {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [DecidableEq n]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Ω → Matrix m n ℝ}
    (hindep : iIndepFun (fun p : m × n ↦ fun ω ↦ A ω p.1 p.2) μ)
    {K : ℝ≥0} (hA : ∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) (K ^ 2) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | 8 * K * (√(Fintype.card m) + √(Fintype.card n) + t) < ‖A ω‖} ≤
      2 * exp (-(t ^ 2)) := by
  classical
  by_cases hK : K = 0
  · subst K
    have hzero : ∀ᵐ ω ∂μ, A ω = 0 := by
      have hentries : ∀ᵐ ω ∂μ, ∀ i j, A ω i j = 0 := by
        exact ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦
          (by
            have hij : HasSubgaussianMGF (fun ω ↦ A ω i j) 0 μ := by simpa using hA i j
            exact hij.ae_eq_zero_of_hasSubgaussianMGF_zero)
      filter_upwards [hentries] with ω hω
      ext i j
      exact hω i j
    have hnull : μ {ω | 0 < ‖A ω‖} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hzero] with ω hω
      simp [hω]
    simp only [NNReal.coe_zero, mul_zero, zero_mul, Measure.real, hnull, ENNReal.toReal_zero]
    positivity
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (pos_iff_ne_zero.mpr hK)
  let s := √(Fintype.card m) + √(Fintype.card n) + t
  let u := 4 * (K : ℝ) * s
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  obtain ⟨N, hNs, hNcover, hNc⟩ :=
    TauCeti.exists_finset_isCover_sphere (E := EuclideanSpace ℝ n)
      (η := (1 / 4 : ℝ≥0)) (by norm_num)
  obtain ⟨M, hMs, hMcover, hMc⟩ :=
    TauCeti.exists_finset_isCover_sphere (E := EuclideanSpace ℝ m)
      (η := (1 / 4 : ℝ≥0)) (by norm_num)
  have hNc' : (N.card : ℝ) ≤ 9 ^ Fintype.card n := by
    norm_num at hNc
    exact hNc
  have hMc' : (M.card : ℝ) ≤ 9 ^ Fintype.card m := by
    norm_num at hMc
    exact hMc
  let Z (x : EuclideanSpace ℝ n) (y : EuclideanSpace ℝ m) (ω : Ω) : ℝ :=
    ∑ p : m × n, (y p.1 * x p.2) * A ω p.1 p.2
  have htail : ∀ x ∈ N, ∀ y ∈ M,
      μ.real {ω | u ≤ |Z x y ω|} ≤ 2 * exp (-(4 * s ^ 2)) := by
    intro x hx y hy
    have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp (hNs hx)
    have hynorm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp (hMs hy)
    have hxs : ∑ j, x j ^ 2 = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, hxnorm]
      norm_num
    have hys : ∑ i, y i ^ 2 = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, hynorm]
      norm_num
    let c : m × n → ℝ≥0 := fun p ↦ ⟨(y p.1 * x p.2) ^ 2, sq_nonneg _⟩ * K ^ 2
    have hind : iIndepFun (fun (p : m × n) ω ↦ (y p.1 * x p.2) * A ω p.1 p.2) μ :=
      hindep.comp (fun p a ↦ (y p.1 * x p.2) * a)
        (fun _ ↦ measurable_const.mul measurable_id)
    have hsub : ∀ p ∈ (Finset.univ : Finset (m × n)),
        HasSubgaussianMGF (fun ω ↦ (y p.1 * x p.2) * A ω p.1 p.2) (c p) μ :=
      fun p _ ↦ (hA p.1 p.2).const_mul _
    have hc : ∑ p, c p = K ^ 2 := by
      apply NNReal.coe_injective
      rw [NNReal.coe_sum]
      change ∑ p : m × n, (y p.1 * x p.2) ^ 2 * (K : ℝ) ^ 2 = (K : ℝ) ^ 2
      rw [← Finset.sum_mul]
      have hprod : ∑ p : m × n, (y p.1 * x p.2) ^ 2 =
          (∑ i, y i ^ 2) * ∑ j, x j ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hprod, hxs, hys]
      ring
    have hsum : HasSubgaussianMGF (Z x y) (K ^ 2) μ := by
      simpa only [hc, Z] using HasSubgaussianMGF.sum_of_iIndepFun hind hsub
    have hright := hsum.measure_ge_le hu
    have hleft := hsum.neg.measure_ge_le hu
    have hexponent : exp (-u ^ 2 / (2 * (K ^ 2 : ℝ≥0))) = exp (-(8 * s ^ 2)) := by
      congr 1
      simp only [u, NNReal.coe_pow]
      field_simp [ne_of_gt hKpos]
      ring
    rw [hexponent] at hright hleft
    have hsubset : {ω | u ≤ |Z x y ω|} ⊆
        {ω | u ≤ Z x y ω} ∪ {ω | u ≤ -Z x y ω} := by
      intro ω hω
      change u ≤ |Z x y ω| at hω
      change u ≤ Z x y ω ∨ u ≤ -Z x y ω
      exact le_abs.mp hω
    calc
      μ.real {ω | u ≤ |Z x y ω|} ≤
          μ.real ({ω | u ≤ Z x y ω} ∪ {ω | u ≤ -Z x y ω}) := measureReal_mono hsubset
      _ ≤ μ.real {ω | u ≤ Z x y ω} + μ.real {ω | u ≤ -Z x y ω} :=
        measureReal_union_le _ _
      _ ≤ exp (-(8 * s ^ 2)) + exp (-(8 * s ^ 2)) := add_le_add hright hleft
      _ ≤ 2 * exp (-(4 * s ^ 2)) := by
        have he : exp (-(8 * s ^ 2)) ≤ exp (-(4 * s ^ 2)) :=
          exp_le_exp.2 (by nlinarith [sq_nonneg s])
        linarith
  have hinner (ω : Ω) (x : EuclideanSpace ℝ n) (y : EuclideanSpace ℝ m) :
      Inner.inner ℝ y
        ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A ω))) x) = Z x y ω := by
    rw [real_inner_comm]
    dsimp only [Z]
    rw [Fintype.sum_prod_type]
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
      PiLp.inner_apply, Matrix.mulVec, dotProduct,
      RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hbad : {ω | 8 * (K : ℝ) * s < ‖A ω‖} ⊆
      ⋃ x ∈ N, ⋃ y ∈ M, {ω | u ≤ |Z x y ω|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hcon
    have hbound :=
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A ω))).opNorm_le_of_isCover_sphere
        (η := (1 / 4 : ℝ≥0)) (by norm_num) hu
        (hMs.trans Metric.sphere_subset_closedBall)
        (fun x hx y hy ↦ by rw [hinner]; exact (hcon x hx y hy).le) hNcover hMcover
    have hnorm : ‖A ω‖ ≤ 2 * u := by
      norm_num at hbound
      simpa only [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] using hbound
    change 8 * (K : ℝ) * s < ‖A ω‖ at hω
    dsimp [u] at hnorm
    linarith
  calc
    μ.real {ω | 8 * K * (√(Fintype.card m) + √(Fintype.card n) + t) < ‖A ω‖}
        ≤ μ.real (⋃ x ∈ N, ⋃ y ∈ M, {ω | u ≤ |Z x y ω|}) :=
      measureReal_mono hbad (measure_ne_top _ _)
    _ ≤ ∑ x ∈ N, μ.real (⋃ y ∈ M, {ω | u ≤ |Z x y ω|}) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ N, ∑ y ∈ M, μ.real {ω | u ≤ |Z x y ω|} :=
      Finset.sum_le_sum fun _ _ ↦ measureReal_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ N, ∑ y ∈ M, 2 * exp (-(4 * s ^ 2)) :=
      Finset.sum_le_sum fun x hx ↦ Finset.sum_le_sum fun y hy ↦ htail x hx y hy
    _ = 2 * ((N.card : ℝ) * M.card * exp (-(4 * s ^ 2))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * exp (-(t ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (net_card_mul_exp_le (Fintype.card m) (Fintype.card n) hNc' hMc'
          (Nat.cast_nonneg _) ht) (by norm_num)

end ProbabilityTheory
