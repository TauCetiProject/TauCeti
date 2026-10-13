/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import TauCeti.Analysis.Matrix.Eigenvalues
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.Probability.Moments.Chebyshev
public import TauCeti.Probability.Moments.SampleMean

/-!
# Elementary concentration of random matrices

Let `S` be a random `m × n` matrix with entries in a normed group and `A` a fixed matrix whose
entrywise mean-square deviations satisfy `∫ ‖S k l - A k l‖² ≤ v`. Chebyshev's inequality for
each entry and a union bound over the `card m * card n` entries show that, outside an event of
probability at most `card m * card n * v / η²`, every entry of `S - A` has norm at most `η`.
Combined with the deterministic entrywise-to-spectral comparisons for matrices over `ℝ` or `ℂ`
this gives, with the same probability,

* the Euclidean operator bound `‖(S - A) x‖ ≤ n η ‖x‖` for an `n × n` matrix;
* for Hermitian `S` and `A`, the bound `|λₖ(S) - λₖ(A)| ≤ n η` for every sorted eigenvalue,
  and in particular the one-sided floor `λₖ(A) - n η ≤ λₖ(S)`.

None of these statements needs the entries of `S` to be measurable: the union bound and the
complement bound `MeasureTheory.Measure.one_sub_measure_compl_le` hold for arbitrary sets. When
the entries are measurable, the entrywise deviation event is itself measurable.

Applied to the empirical second-moment matrix `TauCeti.sampleSecondMoment` of `r` samples, whose
entries have mean-square error at most `v / r` by
`TauCeti.integral_sampleSecondMoment_apply_sub_sq_le`, this shows that, except with probability
at most `4 d⁴ v / (r c²)`, whenever the `k`-th largest eigenvalue of the `d × d` population
second-moment matrix is at least `c > 0`, so is twice the `k`-th largest empirical eigenvalue.

## Main statements

* `TauCeti.measure_exists_lt_norm_sub_le`: the entrywise deviation event has probability at
  most `card m * card n * v / η²`.
* `TauCeti.measurableSet_exists_lt_norm_sub`: measurability of the entrywise deviation event.
* `TauCeti.one_sub_le_measure_forall_norm_sub_le`: entrywise concentration.
* `TauCeti.one_sub_le_measure_forall_norm_toEuclideanLin_sub_le`: operator-norm concentration.
* `TauCeti.one_sub_le_measure_forall_abs_eigenvalues₀_sub_le` and
  `TauCeti.one_sub_le_measure_forall_eigenvalues₀_sub_le`: eigenvalue concentration and the
  one-sided eigenvalue floor.
* `TauCeti.one_sub_le_measure_forall_le_eigenvalues₀_sampleSecondMoment`: the eigenvalue floor
  for the empirical second-moment matrix.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §4.7: covariance estimation from samples.
-/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace TauCeti

variable {Ω E 𝕜 m n ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section Entrywise

variable [NormedAddCommGroup E]

/-- If the entries of a random matrix are measurable, then so is the event that some entry
deviates from the corresponding entry of a fixed matrix by more than `η`. -/
theorem measurableSet_exists_lt_norm_sub [MeasurableSpace E] [BorelSpace E] [Countable m]
    [Countable n] {S : Ω → Matrix m n E} (hS : Measurable S) (A : Matrix m n E) (η : ℝ) :
    MeasurableSet {ω | ∃ k l, η < ‖S ω k l - A k l‖} := by
  simp only [Set.ofPred_exists]
  exact .iUnion fun k ↦ .iUnion fun l ↦
    measurableSet_lt measurable_const ((hS.eval_matrix.sub_const _).norm)

variable [Fintype m] [Fintype n]

/-- **Entrywise deviation bound.** If every entry of a random matrix `S` has mean-square deviation
at most `v` from the corresponding entry of `A`, then the probability that some entry deviates by
more than `η > 0` is at most `card m * card n * v / η²`. The measure need not be finite and the
entries of `S` need not be measurable. -/
theorem measure_exists_lt_norm_sub_le {S : Ω → Matrix m n E} {A : Matrix m n E}
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ) {v η : ℝ} (hη : 0 < η)
    (hv : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) :
    μ {ω | ∃ k l, η < ‖S ω k l - A k l‖} ≤
      ENNReal.ofReal (Fintype.card m * Fintype.card n * v / η ^ 2) := by
  calc μ {ω | ∃ k l, η < ‖S ω k l - A k l‖}
      ≤ μ (⋃ k, ⋃ l, {ω | η ≤ ‖S ω k l - A k l‖}) :=
        measure_mono fun ω ⟨k, l, h⟩ ↦ Set.mem_iUnion₂.2 ⟨k, l, h.le⟩
    _ ≤ ∑ k, ∑ l, μ {ω | η ≤ ‖S ω k l - A k l‖} :=
        (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun k _ ↦
          measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _k : m, ∑ _l : n, ENNReal.ofReal (v / η ^ 2) := by
        gcongr with k _ l _
        exact (meas_ge_le_integral_norm_sq_div_sq (hint k l) hη).trans
          (ENNReal.ofReal_le_ofReal (by gcongr; exact hv k l))
    _ = ENNReal.ofReal (Fintype.card m * Fintype.card n * v / η ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
        rw [mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

variable [IsProbabilityMeasure μ]

/-- **Entrywise concentration.** If every entry of a random matrix `S` has mean-square deviation
at most `v` from the corresponding entry of `A`, then with probability at least
`1 - card m * card n * v / η²` every entry of `S - A` has norm at most `η`. -/
theorem one_sub_le_measure_forall_norm_sub_le {S : Ω → Matrix m n E} {A : Matrix m n E}
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ) {v η : ℝ} (hη : 0 < η)
    (hv : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) :
    1 - ENNReal.ofReal (Fintype.card m * Fintype.card n * v / η ^ 2) ≤
      μ {ω | ∀ k l, ‖S ω k l - A k l‖ ≤ η} := by
  have hcompl : {ω | ∀ k l, ‖S ω k l - A k l‖ ≤ η}ᶜ = {ω | ∃ k l, η < ‖S ω k l - A k l‖} := by
    ext ω
    simp
  refine le_trans ?_ (Measure.one_sub_measure_compl_le μ _)
  rw [hcompl]
  exact tsub_le_tsub_left (measure_exists_lt_norm_sub_le hint hη hv) 1

end Entrywise

section Spectral

variable [RCLike 𝕜] [IsProbabilityMeasure μ]

section Rectangular

variable [Fintype m] [Fintype n]

/-- **Operator-norm concentration.** Under the hypotheses of
`TauCeti.one_sub_le_measure_forall_norm_sub_le`, with probability at least
`1 - card m * card n * v / η²` the Euclidean action of `S - A` is bounded by
`√(card m) * η * √(card n)`. -/
theorem one_sub_le_measure_forall_norm_toEuclideanLin_sub_le [DecidableEq n]
    {S : Ω → Matrix m n 𝕜} {A : Matrix m n 𝕜}
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ) {v η : ℝ} (hη : 0 < η)
    (hv : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) :
    1 - ENNReal.ofReal (Fintype.card m * Fintype.card n * v / η ^ 2) ≤
      μ {ω | ∀ x : EuclideanSpace 𝕜 n, ‖toEuclideanLin (S ω - A) x‖ ≤
        √(Fintype.card m) * η * √(Fintype.card n) * ‖x‖} :=
  (one_sub_le_measure_forall_norm_sub_le hint hη hv).trans <| measure_mono fun _ hω x ↦
    norm_toEuclideanLin_le_of_entry_le (fun k l ↦ hω k l) x

end Rectangular

variable [Fintype ι] [DecidableEq ι]

/-- **Operator-norm concentration for square matrices.** Under the hypotheses of
`TauCeti.one_sub_le_measure_forall_norm_sub_le`, with probability at least
`1 - n² v / η²` the Euclidean action of the `n × n` matrix `S - A` is bounded by `n η`. -/
theorem one_sub_le_measure_forall_norm_toEuclideanLin_sub_le_square
    {S : Ω → Matrix ι ι 𝕜} {A : Matrix ι ι 𝕜}
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ) {v η : ℝ} (hη : 0 < η)
    (hv : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) :
    1 - ENNReal.ofReal (Fintype.card ι ^ 2 * v / η ^ 2) ≤
      μ {ω | ∀ x : EuclideanSpace 𝕜 ι,
        ‖toEuclideanLin (S ω - A) x‖ ≤ Fintype.card ι * η * ‖x‖} := by
  rw [sq]
  exact (one_sub_le_measure_forall_norm_sub_le hint hη hv).trans <| measure_mono fun _ hω x ↦
    norm_toEuclideanLin_le_of_entry_le_square (fun k l ↦ hω k l) x

/-- **Eigenvalue concentration.** If `S` is a random Hermitian `n × n` matrix and `A` a Hermitian
matrix such that every entry of `S` has mean-square deviation at most `v` from the corresponding
entry of `A`, then with probability at least `1 - n² v / η²` every sorted eigenvalue of `S` is
within `n η` of the corresponding sorted eigenvalue of `A`. -/
theorem one_sub_le_measure_forall_abs_eigenvalues₀_sub_le
    {S : Ω → Matrix ι ι 𝕜} {A : Matrix ι ι 𝕜} (hS : ∀ ω, (S ω).IsHermitian) (hA : A.IsHermitian)
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ) {v η : ℝ} (hη : 0 < η)
    (hv : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) :
    1 - ENNReal.ofReal (Fintype.card ι ^ 2 * v / η ^ 2) ≤
      μ {ω | ∀ k, |(hS ω).eigenvalues₀ k - hA.eigenvalues₀ k| ≤ Fintype.card ι * η} := by
  rw [sq]
  exact (one_sub_le_measure_forall_norm_sub_le hint hη hv).trans <| measure_mono fun ω hω k ↦
    (hS ω).abs_eigenvalues₀_sub_le_of_entry_le hA hω k

/-- **One-sided eigenvalue floor.** Under the hypotheses of
`TauCeti.one_sub_le_measure_forall_abs_eigenvalues₀_sub_le`, with probability at least
`1 - n² v / η²` every sorted eigenvalue of `S` is at least the corresponding sorted eigenvalue
of `A` minus `n η`. -/
theorem one_sub_le_measure_forall_eigenvalues₀_sub_le
    {S : Ω → Matrix ι ι 𝕜} {A : Matrix ι ι 𝕜} (hS : ∀ ω, (S ω).IsHermitian) (hA : A.IsHermitian)
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ) {v η : ℝ} (hη : 0 < η)
    (hv : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) :
    1 - ENNReal.ofReal (Fintype.card ι ^ 2 * v / η ^ 2) ≤
      μ {ω | ∀ k, hA.eigenvalues₀ k - Fintype.card ι * η ≤ (hS ω).eigenvalues₀ k} :=
  (one_sub_le_measure_forall_abs_eigenvalues₀_sub_le hS hA hint hη hv).trans <|
    measure_mono fun _ hω k ↦ by linarith [(abs_le.mp (hω k)).1]

end Spectral

section SampleSecondMoment

variable {κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]
  [IsProbabilityMeasure μ]

/-- **Eigenvalue floor for the empirical second moment.** Let `V₁, …, V_r` be random vectors in
`ℝᵈ` and `M` a symmetric matrix. Suppose that for every pair of coordinates `k, l` the products
`Vᵢₖ Vᵢₗ` are square-integrable, pairwise independent, have common mean `M k l` and centered
second moments at most `v`. Then for every `c > 0`, with probability at least
`1 - 4 d⁴ v / (r c²)`, every sorted eigenvalue of the empirical second-moment matrix whose
population counterpart is at least `c` is itself at least `c / 2`. -/
theorem one_sub_le_measure_forall_le_eigenvalues₀_sampleSecondMoment
    {V : ι → Ω → κ → ℝ} {M : Matrix κ κ ℝ} (hM : M.IsHermitian)
    (hV : ∀ k l i, MemLp (fun ω ↦ V i ω k * V i ω l) 2 μ)
    (hmean : ∀ k l i, ∫ ω, V i ω k * V i ω l ∂μ = M k l)
    (hindep : ∀ k l, Pairwise fun i j ↦
      (fun ω ↦ V i ω k * V i ω l) ⟂ᵢ[μ] fun ω ↦ V j ω k * V j ω l)
    {v : ℝ} (hv : ∀ k l i, ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂μ ≤ v) {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal (4 * Fintype.card κ ^ 4 * v / (Fintype.card ι * c ^ 2)) ≤
      μ {ω | ∀ k, c ≤ hM.eigenvalues₀ k →
        c / 2 ≤ (isHermitian_sampleSecondMoment (V · ω)).eigenvalues₀ k} := by
  -- With no coordinates there are no eigenvalues, and the event is everything.
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · refine tsub_le_self.trans (le_of_eq ?_)
    rw [← measure_univ (μ := μ)]
    congr 1
    exact (Set.eq_univ_of_forall fun ω k ↦ absurd k.isLt (by simp)).symm
  -- Otherwise apply the one-sided floor with `η = c / (2d)` to entries of mean-square error
  -- at most `v / r`.
  have hd : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hr : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hη : 0 < c / (2 * Fintype.card κ) := by positivity
  have hint : ∀ k l, Integrable
      (fun ω ↦ ‖sampleSecondMoment (V · ω) k l - M k l‖ ^ 2) μ := fun k l ↦ by
    have h := (memLp_sampleSecondMoment_apply (hV k l)).sub (memLp_const (M k l))
    exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h
  have hmom : ∀ k l, ∫ ω, ‖sampleSecondMoment (V · ω) k l - M k l‖ ^ 2 ∂μ ≤
      v / Fintype.card ι := fun k l ↦ by
    simpa only [Real.norm_eq_abs, sq_abs] using
      integral_sampleSecondMoment_apply_sub_sq_le (hV k l) (hmean k l) (hindep k l) (hv k l)
  have h := one_sub_le_measure_forall_eigenvalues₀_sub_le
    (fun ω ↦ isHermitian_sampleSecondMoment (V · ω)) hM hint hη hmom
  have hbound : (Fintype.card κ : ℝ) ^ 2 * (v / Fintype.card ι) / (c / (2 * Fintype.card κ)) ^ 2 =
      4 * Fintype.card κ ^ 4 * v / (Fintype.card ι * c ^ 2) := by
    field_simp
    ring
  rw [hbound] at h
  refine h.trans (measure_mono fun ω hω k hk ↦ ?_)
  have hk' := hω k
  have hcancel : (Fintype.card κ : ℝ) * (c / (2 * Fintype.card κ)) = c / 2 := by
    field_simp
  linarith

end SampleSecondMoment

end TauCeti
