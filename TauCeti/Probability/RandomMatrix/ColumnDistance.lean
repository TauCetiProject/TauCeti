/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.Moments.SubspaceDistance
public import TauCeti.Probability.Independence.Matrix
import TauCeti.Analysis.Normed.Module.FiniteSpan
import TauCeti.Probability.Independence.Integration

/-!
# Distances of independent columns from the span of the other columns

Conditioning on the remaining columns transfers a uniform bound for each fixed span to the
distance from their random span. For real sub-Gaussian entries with second moments at least one,
the fixed-subspace distance inequality gives an exponential bound in the minimal codimension
`m - (n - 1)`. The bound applies at every rank of the remaining columns.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), [§4](https://arxiv.org/abs/math/0703503).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Metric Set Module
open scoped ENNReal NNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] {P : Measure Ω}

/-- For a matrix with independent entries, any bound uniform over fixed spans of `n - 1`
vectors also bounds the probability that a column is close to the random span of the other
columns. The distance event is measurable in the independent inputs because distance to a
varying finite span is upper semicontinuous. -/
theorem measureReal_infDist_col_span_lt_le_of_forall {𝕜 : Type*} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Countable n] {A : Ω → Matrix m n 𝕜}
    (hind : iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P)
    (hm : AEMeasurable A P) (i : n) {t b : ℝ}
    (h : ∀ v : {j // j ≠ i} → EuclideanSpace 𝕜 m,
      P.real {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i)
        (Submodule.span 𝕜 (range v) : Set (EuclideanSpace 𝕜 m)) < t} ≤ b) :
    P.real {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦
        WithLp.toLp 2 fun r ↦ A ω r j) : Set (EuclideanSpace 𝕜 m)) < t} ≤ b := by
  classical
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let v (M : Matrix m n 𝕜) (j : {j // j ≠ i}) : EuclideanSpace 𝕜 m :=
    WithLp.toLp 2 fun r ↦ M r j
  let U (M : Matrix m n 𝕜) := Submodule.span 𝕜 (range (v M))
  let X (ω : Ω) := (A ω).updateCol i 0
  let Y (ω : Ω) (r : m) := A ω r i
  have hX : AEMeasurable X P := by
    refine AEMeasurable.of_eval fun r ↦ AEMeasurable.of_eval fun j ↦ ?_
    by_cases hj : j = i
    · simp [X, hj]
    · simpa [X, Matrix.updateCol_apply, hj, Function.comp_def] using
        (Matrix.measurable_apply (i := r) (j := j)).comp_aemeasurable hm
  have hY : AEMeasurable Y P := AEMeasurable.of_eval fun r ↦
    (Matrix.measurable_apply (i := r) (j := i)).comp_aemeasurable hm
  have hU (ω : Ω) : U (X ω) = U (A ω) := by
    dsimp only [U, X, v]
    congr 2
    funext j
    congr 1
    funext r
    simp [j.property]
  let S : Set (Matrix m n 𝕜 × (m → 𝕜)) :=
    {p | infDist (WithLp.toLp 2 p.2 : EuclideanSpace 𝕜 m) (U p.1 : Set _) < t}
  have hS : MeasurableSet S :=
    ((TauCeti.upperSemicontinuous_infDist_span_range (𝕜 := 𝕜)
      (v := fun p : Matrix m n 𝕜 × (m → 𝕜) ↦ fun j : {j // j ≠ i} ↦
        (WithLp.toLp 2 fun r ↦ p.1 r j : EuclideanSpace 𝕜 m))
      (x := fun p ↦ WithLp.toLp 2 p.2)
      (fun _ ↦ by fun_prop) (by fun_prop)).isOpen_preimage t).measurableSet
  have hb : 0 ≤ b := measureReal_nonneg.trans (h fun _ ↦ 0)
  have hs (M : Matrix m n 𝕜) : P (Y ⁻¹' (Prod.mk M ⁻¹' S)) ≤ ENNReal.ofReal b := by
    have hpre : Y ⁻¹' (Prod.mk M ⁻¹' S) =
        {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i) (U M : Set _) < t} := rfl
    rw [hpre, ← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (h (v M))
  have hSprob :=
    (hind.indepFun_updateCol_zero hm i).measure_preimage_prodMk_le_of_forall hX hY hS hs
  have hevent : (fun ω ↦ (X ω, Y ω)) ⁻¹' S =
      {ω | infDist (WithLp.toLp 2 (Y ω) : EuclideanSpace 𝕜 m) (U (A ω) : Set _) < t} := by
    ext ω
    simp only [S, mem_preimage, mem_ofPred_eq, hU]
  rw [hevent, measure_univ, mul_one] at hSprob
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hSprob).trans_eq (ENNReal.toReal_ofReal hb)

/-- In a real matrix with independent sub-Gaussian entries, the distance of one column from
the span of the other columns has an exponential lower tail at the square root of the
minimal codimension. Only entries of the chosen column need a variance lower bound. -/
theorem measureReal_infDist_col_span_lt_one_sub_mul_sqrt_le
    [Fintype n] {A : Ω → Matrix m n ℝ} {K : ℝ≥0}
    (hind : iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P)
    (hm : AEMeasurable A P) (i : n)
    (hA : ∀ r, HasSubgaussianMGF (fun ω ↦ A ω r i) K P)
    (hvar : ∀ r, 1 ≤ ∫ ω, (A ω r i) ^ 2 ∂P)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i)
      (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
        WithLp.toLp 2 fun r ↦ A ω r j) : Set (EuclideanSpace ℝ m)) <
      (1 - ε) * Real.sqrt (Fintype.card m - (Fintype.card n - 1) : ℕ)} ≤
        2 * Real.exp (-(ε ^ 2 * (Fintype.card m - (Fintype.card n - 1) : ℕ)) /
          (3200 * (K : ℝ) ^ 2)) := by
  classical
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let d := Fintype.card m - (Fintype.card n - 1)
  have hcol : iIndepFun (fun r ω ↦ A ω r i) P :=
    hind.precomp (g := fun r : m ↦ (r, i)) (fun _ _ h ↦ congrArg Prod.fst h)
  apply hind.measureReal_infDist_col_span_lt_le_of_forall hm i
  intro v
  let U := Submodule.span ℝ (range v)
  have hdim := U.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace] at hdim
  have hspan : finrank ℝ U ≤ Fintype.card n - 1 := by
    have hcard : Fintype.card {j : n // j ≠ i} = Fintype.card n - 1 := by
      simp
    exact (finrank_range_le_card (R := ℝ) v).trans_eq hcard
  have hd : d ≤ finrank ℝ Uᗮ := by dsimp [d]; omega
  exact hcol.measureReal_infDist_lt_one_sub_mul_sqrt_le_of_indepFun hA hvar (fun _ ↦ U)
    aemeasurable_const (indepFun_const_left _ _) (.of_forall fun _ ↦ hd) hε

end ProbabilityTheory.iIndepFun
