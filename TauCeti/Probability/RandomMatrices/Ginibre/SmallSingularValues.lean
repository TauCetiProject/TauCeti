/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import TauCeti.Analysis.Matrix.SpectralMeasure.SingularValues
public import TauCeti.Probability.RandomMatrices.Ginibre.Basic

import TauCeti.Analysis.Matrix.SingularValues.RowDistance
import TauCeti.Analysis.Matrix.SpectralMeasure.LogarithmicTail
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.Distributions.Gaussian.ProperComplex.SmallBall
import TauCeti.Probability.RandomMatrix.ColumnDistance
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Small singular values of shifted complex Ginibre matrices

Row distances for a shifted Ginibre matrix have lower-tail bounds governed by the
codimension of the span of the other rows. These estimates give a summable bound for
exceptionally small least singular values and control the intermediate singular values
after deleting rows. Together they give almost-sure logarithmic tail control at zero
for the empirical singular-value measures of normalized shifted matrices.

## References

* T. Tao, V. Vu, and M. Krishnapur, *Random matrices: universality of ESDs and the circular law*,
  Ann. Probab. 38 (2010), §4 and Appendix A, https://arxiv.org/abs/0807.4898.
-/

public section

noncomputable section

open Filter Finset Matrix MeasureTheory Metric Module Set Submodule WithLp
open scoped ENNReal Topology

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {m n : ℕ} {X : Ω → Matrix (Fin m) (Fin n) ℂ}

/-- Selecting distinct rows and distinct columns of a complex Ginibre matrix gives
a complex Ginibre matrix in the new dimensions. -/
theorem submatrix_ginibreComplex (hX : HasLaw X (ginibreComplex m n) P) {p q : ℕ}
    (e : Fin p ↪ Fin m) (f : Fin q ↪ Fin n) :
    HasLaw (fun ω ↦ (X ω).submatrix e f) (ginibreComplex p q) P := by
  obtain ⟨hind, hentry⟩ := hasLaw_ginibreComplex_iff.mp hX
  exact hasLaw_ginibreComplex_iff.mpr
    ⟨hind.precomp (Function.Injective.prodMap e.injective f.injective),
      fun i j ↦ hentry (e i) (f j)⟩

/-- For a complex Ginibre matrix with a deterministic shift and scalar rescaling, the probability
that a row is close to the span of the other rows is bounded using the minimal codimension.
The free parameter `s` is the parameter of the gamma Chernoff bound. -/
theorem measureReal_infDist_row_span_shifted_ginibreComplex_lt_le
    (hX : HasLaw X (ginibreComplex m n) P) (D : Matrix (Fin m) (Fin n) ℂ)
    (a : ℂ) (i : Fin m) (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    let A (ω : Ω) := D + a • X ω
    P.real {ω | infDist (toLp 2 (A ω i))
      (span ℂ ((fun j ↦ toLp 2 (A ω j)) '' {i}ᶜ) : Set (EuclideanSpace ℂ (Fin n))) <
        ‖a‖ * t} ≤ Real.exp (s * t ^ 2) / (1 + s) ^ (n - (m - 1)) := by
  intro A
  have hshift : Measurable (fun M : Matrix (Fin m) (Fin n) ℂ ↦ D + a • M) := by fun_prop
  have hAm : AEMeasurable A P := hshift.comp_aemeasurable hX.aemeasurable
  obtain ⟨hind, hentry⟩ := hasLaw_ginibreComplex_iff.mp hX
  have hAind : iIndepFun (fun ij : Fin n × Fin m ↦ fun ω ↦ (A ω)ᵀ ij.1 ij.2) P := by
    have h := hind.precomp (Equiv.prodComm (Fin n) (Fin m)).injective
    exact h.comp (fun ij : Fin n × Fin m ↦ fun z : ℂ ↦ D ij.2 ij.1 + a * z)
      (fun _ ↦ by fun_prop)
  have hrange (M : Matrix (Fin m) (Fin n) ℂ) :
      range (fun j : {j // j ≠ i} ↦ toLp 2 (M j.val)) =
        (fun j ↦ toLp 2 (M j)) '' {i}ᶜ := by
    ext x
    simp [mem_image]
  have htranspose : Measurable (fun M : Matrix (Fin m) (Fin n) ℂ ↦ Mᵀ) := by fun_prop
  simp_rw [← hrange]
  refine hAind.measureReal_infDist_col_span_lt_le_of_forall
    (htranspose.comp_aemeasurable hAm) i ?_
  intro v
  let U := span ℂ (range v)
  have hdim := U.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace, Fintype.card_fin] at hdim
  have hspan : finrank ℂ U ≤ m - 1 := by
    have hcard : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by simp
    exact (finrank_range_le_card (R := ℂ) v).trans_eq hcard
  have hd : n - (m - 1) ≤ finrank ℂ Uᗮ := by omega
  have hrow : HasLaw (fun ω ↦ X ω i) (Measure.pi fun _ ↦ properComplexGaussianScalar) P :=
    hasLaw_pi_iff.mpr
      ⟨hind.precomp (g := fun j ↦ (i, j)) (fun _ _ h ↦ congrArg Prod.snd h), hentry i⟩
  have htail := hrow.measureReal_infDist_add_smul_lt_pi_properComplexGaussianScalar
    U (D i) a t hs
  refine htail.trans ?_
  gcongr
  exact le_add_of_nonneg_right hs

/-- For a shifted square complex Ginibre matrix the probability that the least singular value
is below `‖a‖ * t / √(n + 1)` is at most `(n + 1) * exp(1) * t²`. -/
theorem measureReal_singularValues_last_shifted_ginibreComplex_lt_le
    {n : ℕ} {X : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hX : HasLaw X (ginibreComplex (n + 1) (n + 1)) P)
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℂ) (t : ℝ) :
    P.real {ω | (D + a • X ω).toEuclideanLin.singularValues n <
      ‖a‖ * t / Real.sqrt (n + 1)} ≤ (n + 1) * Real.exp 1 * t ^ 2 := by
  let := hX.isProbabilityMeasure
  rcases le_or_gt t 0 with ht | ht
  · have h : {ω | (D + a • X ω).toEuclideanLin.singularValues n <
        ‖a‖ * t / Real.sqrt (n + 1)} = ∅ :=
      eq_empty_of_forall_notMem fun ω ↦ not_lt_of_ge
        ((div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) ht)
          (Real.sqrt_nonneg _)).trans ((D + a • X ω).toEuclideanLin.singularValues_nonneg n))
    rw [h, measureReal_empty]
    positivity
  let E (i : Fin (n + 1)) : Set Ω :=
    {ω | infDist (toLp 2 ((D + a • X ω) i))
      (span ℂ ((fun j ↦ toLp 2 ((D + a • X ω) j)) '' {i}ᶜ) :
        Set (EuclideanSpace ℂ (Fin (n + 1)))) < ‖a‖ * t}
  refine (measureReal_mono (s₂ := ⋃ i, E i) ?_).trans
    ((measureReal_iUnion_fintype_le E).trans ?_)
  · intro ω hω
    by_contra hbad
    have h := (D + a • X ω).le_singularValues_of_le_infDist_row_span
      ⟨n, by simp⟩ (d := ‖a‖ * t) fun j ↦
        le_of_not_gt (fun hlt ↦ hbad (mem_iUnion.2 ⟨j, hlt⟩))
    have hlast : ‖a‖ * t / Real.sqrt (n + 1) ≤
        (D + a • X ω).toEuclideanLin.singularValues n := by
      simpa [Nat.cast_succ, div_eq_mul_inv, Real.sqrt_inv] using h
    exact (not_le_of_gt hω) hlast
  · have htail (i : Fin (n + 1)) : P.real (E i) ≤ Real.exp 1 * t ^ 2 := by
      have ht₂ : 0 < t ^ 2 := by positivity
      have h := hX.measureReal_infDist_row_span_shifted_ginibreComplex_lt_le
        D a i t (s := (t ^ 2)⁻¹) (by positivity)
      simp only [Nat.add_sub_cancel, Nat.add_sub_self_left, pow_one,
        inv_mul_cancel₀ ht₂.ne'] at h
      refine h.trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        ((inv_anti₀ (by positivity : 0 < (t ^ 2)⁻¹) (le_add_of_nonneg_left zero_le_one))
          |>.trans_eq (inv_inv _)) (Real.exp_nonneg _)
    calc
      _ ≤ ∑ _ : Fin (n + 1), Real.exp 1 * t ^ 2 := sum_le_sum fun i _ ↦ htail i
      _ = _ := by simp [mul_assoc]

/-- In a shifted rectangular complex Ginibre matrix, the probability that any row is at
distance below half the natural codimension scale from the span of the others is at most
the number of rows times an exponential in the minimal codimension. -/
theorem measureReal_exists_infDist_row_span_shifted_ginibreComplex_lt_le
    (hX : HasLaw X (ginibreComplex m n) P) (D : Matrix (Fin m) (Fin n) ℂ) (a : ℂ) :
    let d := n - (m - 1)
    let A (ω : Ω) := D + a • X ω
    P.real {ω | ∃ i : Fin m, infDist (toLp 2 (A ω i))
      (span ℂ ((fun j ↦ toLp 2 (A ω j)) '' {i}ᶜ) : Set (EuclideanSpace ℂ (Fin n))) <
        ‖a‖ * (Real.sqrt d / 2)} ≤ m * Real.exp (-(d : ℝ) / 4) := by
  intro d A
  let E (i : Fin m) : Set Ω := {ω | infDist (toLp 2 (A ω i))
    (span ℂ ((fun j ↦ toLp 2 (A ω j)) '' {i}ᶜ) : Set (EuclideanSpace ℂ (Fin n))) <
      ‖a‖ * (Real.sqrt d / 2)}
  have hE : {ω | ∃ i, ω ∈ E i} = ⋃ i, E i := by ext ω; simp
  have htail (i : Fin m) : P.real (E i) ≤ Real.exp (-(d : ℝ) / 4) := by
    have h := hX.measureReal_infDist_row_span_shifted_ginibreComplex_lt_le D a i
      (Real.sqrt d / 2) (s := 1) zero_le_one
    simp only [one_mul, div_pow, Real.sq_sqrt (Nat.cast_nonneg d)] at h
    refine h.trans ?_
    have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
      linarith [Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hfour : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
    rw [one_add_one_eq_two, hfour, ← Real.exp_log (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_natCast_mul, ← Real.exp_sub]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d)])
  calc
    _ = P.real {ω | ∃ i, ω ∈ E i} := rfl
    _ = P.real (⋃ i, E i) := congrArg P.real hE
    _ ≤ ∑ i : Fin m, P.real (E i) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _i : Fin m, Real.exp (-(d : ℝ) / 4) := sum_le_sum fun i _ ↦ htail i
    _ = _ := by simp

end ProbabilityTheory.HasLaw

namespace TauCeti.Probability

open ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : (n : ℕ) → Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}

private theorem ae_eventually_ginibre_least_singularValue
    (hX : ∀ n, HasLaw (X n) (ginibreComplex (n + 1) (n + 1)) P)
    (D : ∀ n, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    let A (n : ℕ) (ω : Ω) := D n + Complex.ofReal ((Real.sqrt (n + 1))⁻¹) • X n ω
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ (-3 : ℝ) ≤
      (A n ω).toEuclideanLin.singularValues n := by
  intro A
  let := (hX 0).isProbabilityMeasure
  let E (n : ℕ) : Set Ω :=
    {ω | (A n ω).toEuclideanLin.singularValues n < ((n : ℝ) + 1) ^ (-3 : ℝ)}
  have htail (n : ℕ) : P.real (E n) ≤ Real.exp 1 * (1 / ((n : ℝ) + 1) ^ 3) := by
    let N : ℝ := (n : ℝ) + 1
    have hN : 0 < N := by positivity
    have hscale : ‖((Real.sqrt N)⁻¹ : ℝ)‖ * (N ^ 2)⁻¹ / Real.sqrt N = N ^ (-3 : ℝ) := by
      rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hN.le]
      norm_num
      rw [div_eq_mul_inv, mul_right_comm, ← pow_two, inv_pow, Real.sq_sqrt hN.le, ← mul_inv]
      congr 1
      ring
    have h := (hX n).measureReal_singularValues_last_shifted_ginibreComplex_lt_le
      (D n) (Complex.ofReal ((Real.sqrt N)⁻¹)) (N ^ 2)⁻¹
    rw [Complex.norm_real, hscale] at h
    have hbound : N * Real.exp 1 * ((N ^ 2)⁻¹) ^ 2 = Real.exp 1 * (1 / N ^ 3) := by
      field_simp
    simpa only [E, A, hbound, N] using h
  have hsum : Summable (fun n ↦ P.real (E n)) := by
    refine (((Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3)).comp_injective
      (add_left_injective 1)).mul_left (Real.exp 1)).of_nonneg_of_le
      (fun _ ↦ measureReal_nonneg) ?_
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using htail
  have hfin : (∑' n, P (E n)) ≠ ∞ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hsum.tsum_ofReal_ne_top
  simpa only [E, mem_ofPred_eq, not_lt] using ae_eventually_notMem hfin

private theorem measureReal_ginibre_row_minor_distances_lt {n : ℕ}
    {Y : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hY : HasLaw Y (ginibreComplex (n + 1) (n + 1)) P)
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : Fin (n + 1))
    (e : Fin (n + 1 - (k : ℕ)) ↪ Fin (n + 1)) :
    let A (ω : Ω) := D + Complex.ofReal ((Real.sqrt (n + 1))⁻¹) • Y ω
    P.real {ω | ∃ j : Fin (n + 1 - (k : ℕ)), infDist (toLp 2 (A ω (e j)))
      (span ℂ ((fun l ↦ toLp 2 (A ω (e l))) '' {j}ᶜ) : Set (EuclideanSpace ℂ (Fin (n + 1)))) <
        1 / 2 * Real.sqrt (((k : ℝ) + 1) / (n + 1))} ≤
      (n + 1 - (k : ℕ) : ℕ) * Real.exp (-((k : ℝ) + 1) / 4) := by
  intro A
  have hk := k.isLt
  have hdim : n + 1 - (n + 1 - (k : ℕ) - 1) = (k : ℕ) + 1 := by omega
  let N : ℝ := (n : ℝ) + 1
  let a : ℂ := Complex.ofReal ((Real.sqrt N)⁻¹)
  let f : Fin (n + 1) ↪ Fin (n + 1) := Function.Embedding.refl _
  let D' := D.submatrix e f
  have hminor := hY.submatrix_ginibreComplex e f
  have htail := hminor.measureReal_exists_infDist_row_span_shifted_ginibreComplex_lt_le D' a
  have hscale : ‖a‖ * (Real.sqrt ((k : ℝ) + 1) / 2) =
      1 / 2 * Real.sqrt (((k : ℝ) + 1) / N) := by
    simp only [a, Complex.norm_real, Real.norm_of_nonneg (by positivity :
      0 ≤ (Real.sqrt N)⁻¹), Real.sqrt_div (by positivity : 0 ≤ (k : ℝ) + 1)]
    ring
  have hrow (ω : Ω) (j : Fin (n + 1 - (k : ℕ))) :
      (D' + a • (Y ω).submatrix e f) j = A ω (e j) := by
    funext l
    rfl
  simpa only [hdim, Nat.cast_succ, hrow, hscale, N] using htail

private theorem ae_eventually_ginibre_row_minor_distances
    (hX : ∀ n, HasLaw (X n) (ginibreComplex (n + 1) (n + 1)) P)
    (D : ∀ n, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    let A (n : ℕ) (ω : Ω) := D n + Complex.ofReal ((Real.sqrt (n + 1))⁻¹) • X n ω
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, ⌈16 * Real.log ((n : ℝ) + 1)⌉₊ ≤ k → k ≤ n / 2 →
        ∃ e : Fin (n + 1 - k) ↪ Fin (n + 1), ∀ j,
          1 / 2 * Real.sqrt (((k : ℝ) + 1) / (n + 1)) ≤ infDist (toLp 2 (A n ω (e j)))
            (span ℂ ((fun l ↦ toLp 2 (A n ω (e l))) '' {j}ᶜ) :
              Set (EuclideanSpace ℂ (Fin (n + 1)))) := by
  intro A
  let := (hX 0).isProbabilityMeasure
  let r (n : ℕ) := ⌈16 * Real.log (n + 1)⌉₊
  let e (n k : ℕ) : Fin (n + 1 - k) ↪ Fin (n + 1) := Fin.castLEEmb (Nat.sub_le _ _)
  let bad (n : ℕ) (k : Fin (n + 1)) : Set Ω :=
    {ω | r n ≤ (k : ℕ) ∧ ∃ j : Fin (n + 1 - (k : ℕ)),
      infDist (toLp 2 (A n ω (e n k j)))
        (span ℂ ((fun l ↦ toLp 2 (A n ω (e n k l))) '' {j}ᶜ) :
          Set (EuclideanSpace ℂ (Fin (n + 1)))) <
        1 / 2 * Real.sqrt (((k : ℝ) + 1) / (n + 1))}
  have hbad (n : ℕ) (k : Fin (n + 1)) : P.real (bad n k) ≤ ((n : ℝ) + 1)⁻¹ ^ 3 := by
    by_cases hk : r n ≤ (k : ℕ)
    · have hfirst := measureReal_ginibre_row_minor_distances_lt (hX n) (D n) k (e n k)
      refine (measureReal_mono (s₁ := bad n k) ?_).trans (hfirst.trans ?_)
      · exact fun _ hω ↦ hω.2
      have hlog : 16 * Real.log ((n : ℝ) + 1) ≤ (k : ℝ) :=
        (Nat.le_ceil _).trans (Nat.cast_le.mpr hk)
      have hexp : Real.exp (-((k : ℝ) + 1) / 4) ≤ ((n : ℝ) + 1)⁻¹ ^ 4 := by
        have hN : 0 < (n : ℝ) + 1 := by positivity
        rw [inv_pow, ← Real.exp_log hN, ← Real.exp_natCast_mul, ← Real.exp_neg]
        exact Real.exp_le_exp.mpr (by linarith)
      calc
        _ ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ ^ 4) := by
          gcongr
          exact_mod_cast Nat.sub_le (n + 1) (k : ℕ)
        _ = _ := by field_simp
    · simpa [bad, hk] using (by positivity : 0 ≤ ((n : ℝ) + 1)⁻¹ ^ 3)
  let E (n : ℕ) := ⋃ k : Fin (n + 1), bad n k
  have hEn (n : ℕ) : P.real (E n) ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ ∑ k : Fin (n + 1), P.real (bad n k) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _k : Fin (n + 1), ((n : ℝ) + 1)⁻¹ ^ 3 := sum_le_sum fun k _ ↦ hbad n k
      _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_succ]
        field_simp
  have hsum : Summable (fun n ↦ P.real (E n)) :=
    ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).comp_injective
      (add_left_injective 1)).of_nonneg_of_le (fun _ ↦ measureReal_nonneg)
      (by simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using hEn)
  have hfin : (∑' n, P (E n)) ≠ ∞ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hsum.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with n hn k hk hkn
  let k' : Fin (n + 1) := ⟨k, by omega⟩
  refine ⟨e n k, fun j ↦ le_of_not_gt fun hj ↦ hn ?_⟩
  exact mem_iUnion.mpr ⟨k', hk, j, hj⟩

private theorem tendsto_ginibre_logarithmic_tail_budget :
    Tendsto (fun n : ℕ ↦ (⌈16 * Real.log ((n : ℝ) + 1)⌉₊ : ℝ) / (n + 1) *
      Real.log (n + 1)) atTop (𝓝 0) := by
  have hN := tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / Real.sqrt (n + 1)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    refine (h.comp hN).congr fun n ↦ ?_
    simp only [Function.comp_apply, Real.sqrt_eq_rpow]
  have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)
  have hlim := (hlog.pow 2 |>.const_mul 16).add (hlog.mul hinv)
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hlim
  have hlog₀ (n : ℕ) : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
  refine squeeze_zero (fun n ↦ mul_nonneg (by positivity) (hlog₀ n)) (fun n ↦ ?_) hlim
  let N := (n : ℝ) + 1
  have hN₀ : 0 < N := by positivity
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (hlog₀ n))).le
  calc
    _ ≤ (16 * Real.log N + 1) / N * Real.log N :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hceil hN₀.le) (hlog₀ n)
    _ = _ := by
      simp only [Function.comp_apply]
      have hsq : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = N⁻¹ := by
        rw [← pow_two, inv_pow, Real.sq_sqrt hN₀.le]
      rw [div_pow, Real.sq_sqrt hN₀.le, div_eq_mul_inv (Real.log N), mul_assoc, hsq]
      ring

/-- The logarithmic tails at zero of the singular values of normalized, deterministically
shifted complex Ginibre matrices vanish almost surely. The matrices can have arbitrary coupling
across sizes and the deterministic shifts need no norm bound. -/
theorem ae_log_tail_zero_singularValueMeasure_shifted_ginibreComplex
    (hX : ∀ n, HasLaw (X n) (ginibreComplex (n + 1) (n + 1)) P)
    (D : ∀ n, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    let A (n : ℕ) (ω : Ω) := D n + Complex.ofReal ((Real.sqrt (n + 1))⁻¹) • X n ω
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ a > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x)
        ∂((A n ω).singularValueMeasure : Measure ℝ) ≤ ENNReal.ofReal ε := by
  intro A
  filter_upwards [ae_eventually_ginibre_least_singularValue hX D,
    ae_eventually_ginibre_row_minor_distances hX D] with ω hmin hrow
  exact log_tail_zero_of_row_distances (fun n ↦ A n ω)
    (by norm_num : 0 < (1 / 2 : ℝ)) tendsto_ginibre_logarithmic_tail_budget hmin hrow

end TauCeti.Probability
