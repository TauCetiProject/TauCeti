/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Compressible
public import TauCeti.Analysis.Normed.Module.FiniteSpan
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Invertibility on incompressible vectors via column distances

If a linear combination with incompressible unit coefficients is small, many columns are close
to the spans of the remaining columns. Averaging the indicators of these distance events gives
a probability bound with no loss of a factor equal to the number of columns. The columns may
be dependent and need not have the same law.

We work with finite families in a normed space, so the result applies to rectangular real or
complex matrices. The threshold is `ε ρ / √n` for the unnormalized matrix. The exact integer
sparsity bound gives denominator `k + 1` in the probability estimate.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 3.5.
-/

public section

open Finset MeasureTheory Metric Set

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]

/-- A small linear combination with incompressible coefficients forces more than `k` column
distances to be small. The threshold `a` may be any nonnegative number with `n a² ≤ ρ²`. -/
theorem IsIncompressibleVector.lt_card_filter_infDist_span_other
    {k : ℕ} {ρ a ε : ℝ} {x : EuclideanSpace 𝕜 ι} (hx : IsIncompressibleVector k ρ x)
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (haρ : (Fintype.card ι : ℝ) * a ^ 2 ≤ ρ ^ 2)
    (v : ι → E) (hv : ‖∑ i, x i • v i‖ < a * ε) :
    k < (univ.filter fun i ↦ infDist (v i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j) : Set E) < ε).card := by
  apply (hx.lt_card_filter_norm hρ haρ).trans_le
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hd := norm_mul_infDist_span_other_le v (fun j ↦ x j) i
  have he : 0 < ε := by nlinarith [norm_nonneg (∑ j, x j • v j)]
  by_contra h
  have hεd : ε ≤ infDist (v i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j) : Set E) := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_left hεd (norm_nonneg (x i))
  nlinarith

/-- Having a small linear combination with incompressible unit coefficients is an open
condition on the column family, so this event is measurable for a random matrix. -/
theorem isOpen_exists_incompressible_norm_sum_lt (k : ℕ) (ρ t : ℝ) :
    IsOpen {v : ι → E | ∃ x : EuclideanSpace 𝕜 ι,
      IsIncompressibleVector k ρ x ∧ ‖∑ i, x i • v i‖ < t} := by
  simp only [Set.ofPred_exists]
  apply isOpen_iUnion
  intro x
  by_cases hx : IsIncompressibleVector k ρ x
  · simp only [hx, true_and]
    exact isOpen_lt (continuous_finsetSum _ fun i _ ↦
      (continuous_apply i).const_smul (x i)).norm continuous_const
  · simp [hx]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **Invertibility via distance.** The probability of a small linear combination with
incompressible unit coefficients is controlled by the average column-distance probabilities.
This holds for finite measures and arbitrary dependent columns; `a` records the normalization. -/
theorem measureReal_exists_incompressible_norm_sum_lt_le
    {k : ℕ} {ρ a ε : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a)
    (haρ : (Fintype.card ι : ℝ) * a ^ 2 ≤ ρ ^ 2)
    {v : Ω → ι → E} (hv : AEMeasurable v P) :
    P.real {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖∑ i, x i • v ω i‖ < a * ε} ≤
      (∑ i, P.real {ω | infDist (v ω i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v ω j) : Set E) < ε}) /
        (k + 1 : ℝ) := by
  classical
  let D (i : ι) (w : ι → E) := infDist (w i)
    (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ w j) : Set E)
  have hD (i : ι) : Measurable (D i) :=
    (upperSemicontinuous_infDist_span_range (𝕜 := 𝕜)
      (v := fun w : ι → E ↦ fun j : {j // j ≠ i} ↦ w j)
      (x := fun w : ι → E ↦ w i)
      (fun j ↦ continuous_apply j.val) (continuous_apply i)).measurable
  let f (ω : Ω) : ℝ := ∑ i, if D i (v ω) < ε then 1 else 0
  have hi (i : ι) : Integrable (fun ω ↦ if D i (v ω) < ε then (1 : ℝ) else 0) P := by
    exact (integrable_const (1 : ℝ)).indicator₀
      (((hD i).comp_aemeasurable hv).nullMeasurable measurableSet_Iio)
  have hf : Integrable f P := integrable_finsetSum _ fun i _ ↦ hi i
  have hfi : ∫ ω, f ω ∂P = ∑ i, P.real {ω | D i (v ω) < ε} := by
    rw [integral_finsetSum _ fun i _ ↦ hi i]
    apply sum_congr rfl
    intro i _
    simpa [Set.indicator, Set.preimage, Function.comp_def] using
      integral_indicator₀ (f := fun _ : Ω ↦ (1 : ℝ))
        (((hD i).comp_aemeasurable hv).nullMeasurable measurableSet_Iio)
  have hsub : {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
      ‖∑ i, x i • v ω i‖ < a * ε} ⊆ {ω | (k + 1 : ℝ) ≤ f ω} := by
    rintro ω ⟨x, hx, hsmall⟩
    have hcard := hx.lt_card_filter_infDist_span_other hρ ha haρ (v ω) hsmall
    have hcount : f ω = ((univ.filter fun i ↦ D i (v ω) < ε).card : ℝ) := by
      simp [f]
    rw [Set.mem_ofPred_eq, hcount]
    exact_mod_cast Nat.succ_le_of_lt hcard
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < k + 1)).mpr
  rw [mul_comm]
  calc
    _ ≤ (k + 1 : ℝ) * P.real {ω | (k + 1 : ℝ) ≤ f ω} := by
      exact mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _))
        (by positivity)
    _ ≤ ∫ ω, f ω ∂P := mul_meas_ge_le_integral_of_nonneg
      (.of_forall fun ω ↦ sum_nonneg fun i _ ↦ by split_ifs <;> norm_num) hf _
    _ = _ := hfi

/-- The usual `ε ρ / √n` normalization of invertibility via distance, valid also for an empty
column type. In that case there are no unit coefficient vectors and both sides vanish. -/
theorem measureReal_exists_incompressible_norm_sum_lt_sqrt_le
    {k : ℕ} {ρ ε : ℝ} (hρ : 0 ≤ ρ) {v : Ω → ι → E} (hv : AEMeasurable v P) :
    P.real {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖∑ i, x i • v ω i‖ < ρ / Real.sqrt (Fintype.card ι) * ε} ≤
      (∑ i, P.real {ω | infDist (v ω i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v ω j) : Set E) < ε}) /
        (k + 1 : ℝ) := by
  apply measureReal_exists_incompressible_norm_sum_lt_le hρ (by positivity) _ hv
  by_cases hn : Fintype.card ι = 0
  · simp [hn, sq_nonneg]
  · have hnp : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_pow, Real.sq_sqrt hnp.le]
    exact (mul_div_cancel₀ (ρ ^ 2) (ne_of_gt hnp)).le

/-- The matrix form of invertibility via distance for rectangular real or complex matrices.
The distances are Euclidean distances between columns and the spans of the other columns;
`A` is the unnormalized matrix, and no independence assumptions are needed. -/
theorem measureReal_exists_incompressible_norm_toEuclideanLin_lt_le
    {κ : Type*} [Fintype κ] [DecidableEq ι]
    {k : ℕ} {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    {A : Ω → Matrix κ ι 𝕜} (hA : AEMeasurable A P) :
    P.real {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖Matrix.toEuclideanLin (A ω) x‖ < ρ / Real.sqrt (Fintype.card ι) * ε} ≤
      (∑ i, P.real {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦
          WithLp.toLp 2 fun r ↦ A ω r j) : Set (EuclideanSpace 𝕜 κ)) < ε}) /
        (k + 1 : ℝ) := by
  have hv : AEMeasurable (fun ω i ↦ (WithLp.toLp 2 fun r ↦ A ω r i : EuclideanSpace 𝕜 κ)) P := by
    fun_prop
  have hsum (ω : Ω) (x : EuclideanSpace 𝕜 ι) :
      (∑ i, x i • (WithLp.toLp 2 fun r ↦ A ω r i : EuclideanSpace 𝕜 κ)) =
        Matrix.toEuclideanLin (A ω) x := by
    ext r
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]
  simpa only [hsum] using measureReal_exists_incompressible_norm_sum_lt_sqrt_le
    (𝕜 := 𝕜) (k := k) (ε := ε) hρ hv

end TauCeti
