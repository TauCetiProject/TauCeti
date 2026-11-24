/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Compressible

/-!
# Random subspaces are incompressible

Let a real random matrix have independent, uniformly sub-Gaussian entries with second moments
bounded below by one, and at least half as many columns as rows. Outside an event whose
probability is exponentially small in the number of columns, every unit vector orthogonal to all
columns is incompressible. For a square or wide matrix, the same holds for the unit normals to
the span of the columns other than a fixed one.

Small-ball estimates for the inner product of a column with such a normal need its mass spread
over many coordinates, so this is the first step in bounding the distance of a column from the
span of the other columns. The proof applies invertibility on compressible vectors to the
transposed matrix, whose kernel is the orthogonal complement of the column span.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 3.6.
* M. Rudelson and R. Vershynin, *Smallest singular value of a random rectangular matrix*,
  Communications on Pure and Applied Mathematics 62 (2009), Lemma 4.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Set
open scoped NNReal

namespace TauCeti.Probability

/-- For a real random matrix with independent, uniformly sub-Gaussian entries of second moments
at least one and at least half as many columns as rows, the probability that some compressible
unit vector is orthogonal to every column is exponentially small in the number of columns. The
constants depend only on the common variance proxy `K`. -/
theorem exists_measureReal_exists_mem_orthogonal_span_isCompressibleVector_le (K : ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ ∃ a : ℝ, 0 < a ∧
      ∀ {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        {P : Measure Ω} {A : Ω → Matrix m n ℝ},
        iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        Fintype.card m ≤ 2 * Fintype.card n →
        P.real {ω | ∃ x ∈ (Submodule.span ℝ (range fun j : n ↦
            (WithLp.toLp 2 fun r ↦ A ω r j : EuclideanSpace ℝ m)))ᗮ,
          TauCeti.IsCompressibleVector ⌊δ * Fintype.card m⌋₊ ρ x} ≤
          4 * Real.exp (-a * Fintype.card n) := by
  obtain ⟨δ, hδ, hδ₁, ρ, hρ, hρ₄, a, ha, hcomp⟩ :=
    exists_measureReal_exists_isCompressibleVector_norm_toEuclideanLin_lt_le K
  refine ⟨δ, hδ, hδ₁, ρ, hρ, hρ₄, a, ha, ?_⟩
  intro Ω m n _ _ _ P A hind hA hmom hdim
  classical
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  -- With no columns the bound is at least one.
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · rw [hn, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans (by norm_num)
  -- The rows of the transposed matrix are the columns, so its kernel is the orthogonal
  -- complement of the column span.
  have hindT : iIndepFun (fun ij : n × m ↦ fun ω ↦ (A ω)ᵀ ij.1 ij.2) P := by
    simpa only [transpose_apply, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using
      hind.precomp Prod.swap_injective
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (hcomp hindT (fun i j ↦ hA j i) (fun i j ↦ hmom j i) hdim)
  rintro ω ⟨x, hx, hcx⟩
  refine ⟨x, hcx, ?_⟩
  have hzero : (A ω)ᵀ *ᵥ WithLp.ofLp x = 0 := by
    funext j
    have h := (Submodule.mem_orthogonal _ x).mp hx _ (Submodule.subset_span ⟨j, rfl⟩)
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, WithLp.ofLp_toLp] at h
    rw [mulVec_transpose, vecMul_apply, col_apply', Pi.zero_apply, ← h]
  rw [Matrix.toLpLin_apply, hzero, WithLp.toLp_zero, norm_zero]
  positivity

/-- For a square or wide real random matrix with independent, uniformly sub-Gaussian entries of
second moments at least one, the probability that some compressible unit vector is orthogonal to
every column other than a fixed one is exponentially small in the number of columns. The constants
depend only on the common variance proxy `K`. -/
theorem exists_measureReal_exists_mem_orthogonal_span_ne_isCompressibleVector_le (K : ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ ∃ a : ℝ, 0 < a ∧
      ∀ {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        {P : Measure Ω} {A : Ω → Matrix m n ℝ},
        iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        Fintype.card m ≤ Fintype.card n → ∀ i : n,
        P.real {ω | ∃ x ∈ (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
            (WithLp.toLp 2 fun r ↦ A ω r j : EuclideanSpace ℝ m)))ᗮ,
          TauCeti.IsCompressibleVector ⌊δ * Fintype.card m⌋₊ ρ x} ≤
          4 * Real.exp (-a * Fintype.card n) := by
  obtain ⟨δ, hδ, hδ₁, ρ, hρ, hρ₄, a, ha, hspan⟩ :=
    exists_measureReal_exists_mem_orthogonal_span_isCompressibleVector_le K
  refine ⟨δ, hδ, hδ₁, ρ, hρ, hρ₄, min (a / 2) (1 / 2), lt_min (half_pos ha) one_half_pos, ?_⟩
  intro Ω m n _ _ _ P A hind hA hmom hdim i
  classical
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card n - 1 := by simp
  have hn : 1 ≤ Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  rcases hn.eq_or_lt with hn₁ | hn₂
  · -- With one column the rate is at most `1 / 2`, so the bound is at least one.
    rw [← hn₁, Nat.cast_one, mul_one]
    have hexp : 1 - 1 / 2 ≤ Real.exp (-min (a / 2) (1 / 2)) := by
      have := Real.add_one_le_exp (-min (a / 2) (1 / 2))
      linarith [min_le_right (a / 2) (1 / 2)]
    exact measureReal_le_one.trans (by linarith)
  -- Remove the fixed column and use that at least half of the columns remain.
  let B : Ω → Matrix m {j // j ≠ i} ℝ := fun ω ↦ (A ω).submatrix id Subtype.val
  have hindB : iIndepFun (fun ij : m × {j // j ≠ i} ↦ fun ω ↦ B ω ij.1 ij.2) P := by
    simpa only [B, submatrix_apply, id_eq, Function.comp_def] using
      hind.precomp (g := fun ij : m × {j // j ≠ i} ↦ (ij.1, ij.2.val))
        fun _ _ h ↦ Prod.ext (Prod.mk.inj h).1 (Subtype.ext (Prod.mk.inj h).2)
  have hdimB : Fintype.card m ≤ 2 * Fintype.card {j // j ≠ i} := by omega
  have hrate : -a * (Fintype.card {j // j ≠ i} : ℝ) ≤
      -min (a / 2) (1 / 2) * Fintype.card n := by
    have hn' : (2 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn₂
    rw [hcard, Nat.cast_sub hn, Nat.cast_one]
    nlinarith [min_le_left (a / 2) (1 / 2)]
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
    ((hspan hindB (fun r j ↦ by simpa only [B, submatrix_apply, id_eq] using hA r j)
      (fun r j ↦ by simpa only [B, submatrix_apply, id_eq] using hmom r j) hdimB).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (by norm_num)))
  intro ω hω
  simpa only [B, submatrix_apply, id_eq] using hω

end TauCeti.Probability
