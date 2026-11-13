/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.SubGaussian.SquaredSum
public import TauCeti.Analysis.InnerProductSpace.QuadraticForm.Net
public import TauCeti.Analysis.Matrix.SingularValues
public import TauCeti.Analysis.Normed.Module.CoveringNumber
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Matrices with independent isotropic sub-Gaussian rows

For a real rectangular matrix with independent rows, isotropic second moments, and a uniform
sub-Gaussian bound on all unit linear forms, the Gram matrix concentrates about `card m • 1`.
Consequently all source singular values lie within `C * c * (sqrt (card n) + t)` of
`sqrt (card m)`, except on a set of probability at most `2 * exp (-t²)`. Here `c` is the
variance proxy, so `c = K²` in the usual sub-Gaussian norm convention. Independence of the
coordinates within a row and identical distribution of the rows are not required.

The matrix norms in this file are Euclidean operator norms. Singular values include zero
values when the matrix has fewer rows than columns; a negative lower bound does not imply
injectivity. Empty row and column types are included.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), Theorem 4.6.1.
-/

public section

open MeasureTheory Real Matrix
open scoped NNReal Matrix.Norms.L2Operator RealInnerProductSpace

namespace ProbabilityTheory.iIndepFun

private lemma isotropicRows_proxy_lower_bound {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype n] [Nonempty n] [Nonempty m] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Ω → Matrix m n ℝ} {c : ℝ≥0}
    (hsub : ∀ i (x : EuclideanSpace ℝ n), ‖x‖ = 1 →
      HasSubgaussianMGF (fun ω ↦ A ω i ⬝ᵥ x) c P)
    (hiso : ∀ i (x : EuclideanSpace ℝ n), ‖x‖ = 1 →
      ∫ ω, (A ω i ⬝ᵥ x) ^ 2 ∂P = 1) : 1 / 4 ≤ (c : ℝ) := by
  classical
  let x₀ := EuclideanSpace.single (Classical.arbitrary n) (1 : ℝ)
  have hx₀ : ‖x₀‖ = 1 := by simp [x₀]
  let X : Ω → ℝ := fun ω ↦ A ω (Classical.arbitrary m) ⬝ᵥ x₀
  have hX : HasSubgaussianMGF X c P := hsub (Classical.arbitrary m) x₀ hx₀
  have hiso : ∫ ω, X ω ^ 2 ∂P = 1 := hiso (Classical.arbitrary m) x₀ hx₀
  by_cases hc : c = 0
  · subst c
    have hzero := hX.ae_eq_zero_of_hasSubgaussianMGF_zero
    have : ∫ ω, X ω ^ 2 ∂P = 0 := integral_eq_zero_of_ae (hzero.mono fun _ h ↦ by simp [h])
    linarith
  have : 0 < (c : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hc)
  let s : ℝ := (4 * (c : ℝ))⁻¹
  have hs : 2 * (c : ℝ) * s = 1 / 2 := by dsimp [s]; field_simp; ring
  have hint := hX.integrable_exp_mul_sq (s := s) (by linarith)
  have hbound := hX.integral_exp_mul_sq_le (s := s) (by positivity) (by linarith)
  have hrpow : (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 := by
    rw [Real.rpow_neg (by norm_num),
      ← Real.inv_rpow (by norm_num)]
    norm_num only [inv_div, div_one]
    exact (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)).trans_eq (rpow_one 2)
  have hle : ∫ ω, 1 + s * X ω ^ 2 ∂P ≤ ∫ ω, exp (s * X ω ^ 2) ∂P :=
    integral_mono ((integrable_const 1).add (((hX.memLp 2).integrable_sq).const_mul s))
      hint (fun ω ↦ by linarith [add_one_le_exp (s * X ω ^ 2)])
  rw [integral_add (integrable_const 1) (((hX.memLp 2).integrable_sq).const_mul s),
    integral_const, probReal_univ, one_smul, integral_const_mul, hiso, mul_one] at hle
  have hs_le : s ≤ 1 := by
    rw [hs] at hbound
    norm_num only [sub_half] at hbound
    linarith [hbound.trans hrpow]
  have : 1 ≤ 4 * (c : ℝ) := (inv_le_one₀ (by positivity : 0 < 4 * (c : ℝ))).mp hs_le
  linarith

private lemma row_tail_rate (m : ℕ) {c s : ℝ} (hm : 0 < m) (hc : 0 < c) (hs : 0 ≤ s) :
    4 * s ^ 2 ≤ (1 / 1536 : ℝ) *
      min ((6144 * c * (√m * s + s ^ 2)) ^ 2 / (c ^ 2 * m))
        ((6144 * c * (√m * s + s ^ 2)) / c) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hmpos.le
  have hquad : 6144 * s ^ 2 ≤
      (6144 * c * (√m * s + s ^ 2)) ^ 2 / (c ^ 2 * m) := by
    apply (le_div_iff₀ (by positivity : 0 < c ^ 2 * m)).mpr
    have hbase : c * √m * s ≤ c * (√m * s + s ^ 2) := by nlinarith
    have hsq := pow_le_pow_left₀ (by positivity) hbase 2
    nlinarith [sq_nonneg (c * (√m * s + s ^ 2)), mul_nonneg hc.le hs]
  have hlin : 6144 * s ^ 2 ≤ (6144 * c * (√m * s + s ^ 2)) / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_nonneg (Real.sqrt_nonneg (m : ℝ)) hs]
  nlinarith [le_min hquad hlin]

private lemma one_net_card_exp_le (n : ℕ) {a t : ℝ} (ha : a ≤ 9 ^ n) (ht : 0 ≤ t) :
    a * exp (-(4 * (√n + t) ^ 2)) ≤ exp (-(t ^ 2)) := by
  have h9 : (9 : ℝ) ≤ exp 3 := by
    have he : (2.7 : ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    exact (by norm_num : (9 : ℝ) ≤ 2.7 ^ 3).trans (pow_le_pow_left₀ (by norm_num) he 3)
  calc
    a * exp (-(4 * (√n + t) ^ 2)) ≤ exp 3 ^ n * exp (-(4 * (√n + t) ^ 2)) := by
      gcongr
      exact ha.trans (pow_le_pow_left₀ (by norm_num) h9 n)
    _ = exp (n * 3 - 4 * (√n + t) ^ 2) := by rw [← exp_nat_mul, ← exp_add]; ring_nf
    _ ≤ exp (-(t ^ 2)) := by
      apply exp_le_exp.mpr
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
        mul_nonneg (Real.sqrt_nonneg (n : ℝ)) ht]

variable {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [DecidableEq n]
  {P : Measure Ω} [IsProbabilityMeasure P] {A : Ω → Matrix m n ℝ} {c : ℝ≥0}

omit [MeasurableSpace Ω] in
private lemma gram_bad_subset_net {N : Finset (EuclideanSpace ℝ n)}
    (hNs : (N : Set (EuclideanSpace ℝ n)) ⊆ Metric.sphere 0 1)
    (hNcover : Metric.IsCover (1 / 4) (Metric.sphere (0 : EuclideanSpace ℝ n) 1) N)
    {r : ℝ} (hr : 0 ≤ r) :
    {ω | 2 * r < ‖(A ω)ᵀ * A ω - (Fintype.card m : ℝ) • 1‖} ⊆
      ⋃ x ∈ N, {ω | r < |∑ i, ((A ω i ⬝ᵥ x) ^ 2 - 1)|} := by
  classical
  intro ω hω
  by_contra h
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at h
  have hHerm : ((A ω)ᵀ * A ω).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      isHermitian_conjTranspose_mul_self (A ω)
  have hSymm := isSymmetric_toEuclideanLin_iff.mpr
    (hHerm.sub (isHermitian_one.smul (by simp : IsSelfAdjoint (Fintype.card m : ℝ))))
  have hb := ContinuousLinearMap.norm_le_of_isSymmetric_of_abs_re_inner_map_self_le_of_isCover
    (toEuclideanCLM (n := n) (𝕜 := ℝ) ((A ω)ᵀ * A ω - (Fintype.card m : ℝ) • 1))
    hSymm
    (η := (1 / 4 : ℝ≥0)) (by norm_num) hr
    (hNs.trans Metric.sphere_subset_closedBall) (fun x hx ↦ by
      have hform : ⟪toEuclideanCLM (n := n) (𝕜 := ℝ)
          ((A ω)ᵀ * A ω - (Fintype.card m : ℝ) • 1) x, x⟫ =
          (∑ i, (A ω i ⬝ᵥ x) ^ 2) - Fintype.card m * ‖x‖ ^ 2 := by
        rw [real_inner_comm, inner_toEuclideanCLM, sub_mulVec, dotProduct_sub,
          ← mulVec_mulVec, dotProduct_transpose_mulVec]
        simp only [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
        congr 1
        · simp only [dotProduct, mulVec, pow_two]
        · rw [EuclideanSpace.real_norm_sq_eq]
          simp only [dotProduct, pow_two]
      rw [hform, mem_sphere_zero_iff_norm.mp (hNs hx), one_pow, mul_one]
      simpa only [RCLike.re_to_real, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one] using h x hx) hNcover
  have hfactor : (1 - 2 * ((1 / 4 : ℝ≥0) : ℝ))⁻¹ = 2 := by norm_num
  rw [hfactor, l2_opNorm_toEuclideanCLM] at hb
  have : ‖(A ω)ᵀ * A ω - (Fintype.card m : ℝ) • 1‖ ≤ 2 * r := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hb
  exact (not_lt_of_ge this) hω

omit [IsProbabilityMeasure P] in
/-- Concentration of the unnormalized Gram matrix of independent isotropic sub-Gaussian rows.
The proxy `c` bounds every unit linear form; the two terms in the threshold give the usual
square-root and linear sample-size regimes. -/
theorem measureReal_gram_sub_smul_one_gt_le
    (hindep : iIndepFun (fun i ω ↦ A ω i) P)
    (hsub : ∀ i (x : EuclideanSpace ℝ n), ‖x‖ = 1 →
      HasSubgaussianMGF (fun ω ↦ A ω i ⬝ᵥ x) c P)
    (hiso : ∀ i (x : EuclideanSpace ℝ n), ‖x‖ = 1 →
      ∫ ω, (A ω i ⬝ᵥ x) ^ 2 ∂P = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | 12288 * c *
      (√(Fintype.card m) * (√(Fintype.card n) + t) + (√(Fintype.card n) + t) ^ 2) <
        ‖(A ω)ᵀ * A ω - (Fintype.card m : ℝ) • 1‖} ≤ 2 * exp (-(t ^ 2)) := by
  classical
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  -- Empty samples give a zero matrix; otherwise isotropy forces a positive proxy.
  by_cases hm : IsEmpty m
  · have := hm
    have hzero (ω : Ω) : (A ω)ᵀ * A ω = 0 := by ext i j; simp [Matrix.mul_apply]
    simp only [Fintype.card_eq_zero, Nat.cast_zero, Real.sqrt_zero, zero_mul, zero_add,
      zero_smul, sub_zero, hzero, norm_zero]
    have hnonneg : 0 ≤ 12288 * (c : ℝ) * (√(Fintype.card n) + t) ^ 2 := by positivity
    simp only [not_lt_of_ge hnonneg, Set.ofPred_false, measureReal_empty]
    positivity
  by_cases hn : IsEmpty n
  · have := hn
    have hzero (ω : Ω) : (A ω)ᵀ * A ω - (Fintype.card m : ℝ) • 1 = 0 := Subsingleton.elim _ _
    simp only [hzero, norm_zero, not_lt_of_ge (by positivity : 0 ≤ 12288 * (c : ℝ) *
      (√(Fintype.card m) * (√(Fintype.card n) + t) + (√(Fintype.card n) + t) ^ 2)),
      Set.ofPred_false, measureReal_empty]
    positivity
  have : Nonempty m := not_isEmpty_iff.mp hm
  have : Nonempty n := not_isEmpty_iff.mp hn
  have hc : 0 < (c : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (isotropicRows_proxy_lower_bound hsub hiso)
  let s := √(Fintype.card n) + t
  let r := 6144 * (c : ℝ) * (√(Fintype.card m) * s + s ^ 2)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  -- A quarter-net reduces the Gram event to fixed-direction sums of squares.
  obtain ⟨N, hNs, hNcover, hNc⟩ := TauCeti.exists_finset_isCover_sphere
    (E := EuclideanSpace ℝ n) (η := (1 / 4 : ℝ≥0)) (by norm_num)
  have hNc' : (N.card : ℝ) ≤ 9 ^ Fintype.card n := by norm_num at hNc; exact hNc
  have htail (x : EuclideanSpace ℝ n) (hx : x ∈ N) :
      P.real {ω | r < |∑ i, ((A ω i ⬝ᵥ x) ^ 2 - 1)|} ≤ 2 * exp (-(4 * s ^ 2)) := by
    have hx1 := mem_sphere_zero_iff_norm.mp (hNs hx)
    have hi : iIndepFun (fun i ω ↦ A ω i ⬝ᵥ x) P :=
      hindep.comp (fun _ v ↦ v ⬝ᵥ x) (fun _ ↦ by fun_prop)
    have hb := hi.measureReal_abs_sum_sq_sub_integral_gt_le (fun i ↦ hsub i x hx1) hr
    simp_rw [hiso _ x hx1] at hb
    exact hb.trans (by
      gcongr
      have hrate := row_tail_rate (Fintype.card m) Fintype.card_pos hc hs
      dsimp [r]
      linarith)
  -- Sum the directional tails and absorb the cardinality cost in the exponent.
  have hbad := gram_bad_subset_net (A := A) hNs hNcover hr
  calc
    _ ≤ P.real (⋃ x ∈ N, {ω | r < |∑ i, ((A ω i ⬝ᵥ x) ^ 2 - 1)|}) := by
      have hscale : 2 * r = 12288 * (c : ℝ) *
          (√(Fintype.card m) * (√(Fintype.card n) + t) + (√(Fintype.card n) + t) ^ 2) := by
        dsimp [r, s]; ring
      rw [hscale] at hbad
      exact measureReal_mono hbad (measure_ne_top _ _)
    _ ≤ ∑ x ∈ N, P.real {ω | r < |∑ i, ((A ω i ⬝ᵥ x) ^ 2 - 1)|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ N, 2 * exp (-(4 * s ^ 2)) := Finset.sum_le_sum htail
    _ = 2 * ((N.card : ℝ) * exp (-(4 * s ^ 2))) := by simp; ring
    _ ≤ 2 * exp (-(t ^ 2)) := mul_le_mul_of_nonneg_left (one_net_card_exp_le
      (Fintype.card n) hNc' ht) (by norm_num)

private lemma singularValues_bad_subset_gram [Nonempty m]
    (hsub : ∀ i (x : EuclideanSpace ℝ n), ‖x‖ = 1 →
      HasSubgaussianMGF (fun ω ↦ A ω i ⬝ᵥ x) c P)
    (hiso : ∀ i (x : EuclideanSpace ℝ n), ‖x‖ = 1 →
      ∫ ω, (A ω i ⬝ᵥ x) ^ 2 ∂P = 1) {s : ℝ} (hs : 0 ≤ s) :
    {ω | ∃ i : Fin (Fintype.card n), 32768 * c * s <
        |(toEuclideanLin (A ω)).singularValues i - √(Fintype.card m)|} ⊆
      {ω | 12288 * c * (√(Fintype.card m) * s + s ^ 2) <
        ‖(A ω)ᵀ * A ω - (Fintype.card m : ℝ) • 1‖} := by
  classical
  let b := 16384 * (c : ℝ) * s
  have hb : 0 ≤ b := by dsimp [b]; positivity
  -- A Gram error of at most b * sqrt m + b² forces each singular-value error to be at most 2b.
  rintro ω ⟨i, hi⟩
  have hi' : 2 * b <
      |(toEuclideanLin (A ω)).singularValues i - √(Fintype.card m)| := by
    have hscale : 2 * b = 32768 * (c : ℝ) * s := by dsimp [b]; ring
    rwa [hscale]
  by_contra h
  have hG : ‖(A ω)ᵀ * A ω - (Fintype.card m : ℝ) • 1‖ ≤
      12288 * c * (√(Fintype.card m) * s + s ^ 2) := by
    simpa only [Set.mem_ofPred_eq, not_lt] using h
  have : Nonempty n := Fintype.card_pos_iff.mp (Nat.zero_le i.val |>.trans_lt i.isLt)
  have hc := isotropicRows_proxy_lower_bound hsub hiso
  have hcs : s ≤ 4 * (c : ℝ) * s := by nlinarith
  have hsq : 12288 * (c : ℝ) * s ^ 2 ≤ b ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hcs
      (mul_nonneg c.coe_nonneg hs)
    dsimp [b]
    nlinarith [mul_nonneg c.coe_nonneg (sq_nonneg s)]
  have hlin : 12288 * (c : ℝ) * √(Fintype.card m) * s ≤ b * √(Fintype.card m) := by
    dsimp [b]
    nlinarith [mul_nonneg (mul_nonneg c.coe_nonneg hs)
      (Real.sqrt_nonneg (Fintype.card m : ℝ))]
  have hσ := (Matrix.abs_sq_singularValues_sub_le (A ω) (Fintype.card m) i)
  rw [conjTranspose_eq_transpose_of_trivial] at hσ
  have hσ' := hσ.trans hG
  have ha : √(Fintype.card m : ℝ) ^ 2 = Fintype.card m := Real.sq_sqrt (by positivity)
  have hupper := (abs_le.mp hσ').2
  have hlower := (abs_le.mp hσ').1
  have hσ0 := (toEuclideanLin (A ω)).singularValues_nonneg i
  have ha0 := Real.sqrt_nonneg (Fintype.card m : ℝ)
  rcases lt_abs.mp hi' with hi | hi
  · nlinarith [mul_nonneg hb ha0, sq_nonneg b,
      sq_nonneg ((toEuclideanLin (A ω)).singularValues i - √(Fintype.card m) - b)]
  · have hba : b < √(Fintype.card m) / 2 := by linarith
    nlinarith [pow_lt_pow_left₀ hba hb (by norm_num : (2 : ℕ) ≠ 0),
      sq_nonneg ((toEuclideanLin (A ω)).singularValues i)]

omit [IsProbabilityMeasure P] in
/-- All source singular values of a matrix with independent isotropic sub-Gaussian rows
concentrate simultaneously about the square root of the number of rows. The absolute constant
is explicit and no independence within a row is assumed. In the usual convention `c = K²`.
The event includes zero singular values when there are fewer rows than columns. -/
theorem measureReal_exists_abs_singularValues_sub_sqrt_gt_le
    (hindep : iIndepFun (fun i ω ↦ A ω i) P)
    (hsub : ∀ i (x : EuclideanSpace ℝ n), ‖x‖ = 1 →
      HasSubgaussianMGF (fun ω ↦ A ω i ⬝ᵥ x) c P)
    (hiso : ∀ i (x : EuclideanSpace ℝ n), ‖x‖ = 1 →
      ∫ ω, (A ω i ⬝ᵥ x) ^ 2 ∂P = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | ∃ i : Fin (Fintype.card n),
      32768 * c * (√(Fintype.card n) + t) <
        |(toEuclideanLin (A ω)).singularValues i - √(Fintype.card m)|} ≤
      2 * exp (-(t ^ 2)) := by
  classical
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  by_cases hm : IsEmpty m
  · have := hm
    have hA (ω : Ω) : A ω = 0 := by ext i; exact isEmptyElim i
    have hnonneg : 0 ≤ 32768 * (c : ℝ) * (√(Fintype.card n) + t) := by positivity
    simp only [hA, map_zero, LinearMap.singularValues_zero, Finsupp.zero_apply,
      Fintype.card_eq_zero, Nat.cast_zero, Real.sqrt_zero, sub_zero, abs_zero,
      not_lt_of_ge hnonneg, exists_false, Set.ofPred_false, measureReal_empty]
    positivity
  have : Nonempty m := not_isEmpty_iff.mp hm
  have hbad := singularValues_bad_subset_gram hsub hiso
    (s := √(Fintype.card n) + t) (by positivity)
  exact (measureReal_mono hbad (measure_ne_top _ _)).trans
    (hindep.measureReal_gram_sub_smul_one_gt_le hsub hiso ht)

end ProbabilityTheory.iIndepFun
