/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues
public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.Probability.Moments.Chebyshev
public import TauCeti.Probability.Moments.SampleMean

/-!
# Elementary concentration of random matrices from entrywise second moments

Let `S : Ω → Matrix m n E` be a random matrix and `A` a fixed matrix, and suppose every entrywise
deviation has second moment `∫ ‖S k l - A k l‖² ≤ v`. Chebyshev's inequality for each of the
`card m * card n` entries, followed by a union bound, gives

`μ {ω | ∃ k l, η < ‖S ω k l - A k l‖} ≤ card m * card n * v / η²`.

On a probability space, every deterministic consequence of entrywise `η`-closeness therefore holds
with probability at least `1 - card m * card n * v / η²`. For square matrices over `ℝ` or `ℂ` the
entrywise-to-spectral comparisons of `TauCeti.Analysis.Matrix.Eigenvalues` and
`TauCeti.Analysis.Matrix.EntrywiseOpNorm` turn this into simultaneous high-probability control of
every sorted eigenvalue and of the Euclidean action of `S - A`, each up to the dimension factor
`card n`.

None of these bounds needs the entries to be measurable: Chebyshev's inequality only uses the
integrability of the squared deviation, and `1 - μ sᶜ ≤ μ s` holds for every set. Measurability of
the deviation event is recorded separately.

Finally, for real samples `V i`, every entry of the empirical second-moment matrix
`TauCeti.sampleSecondMoment` is the sample mean of the products `V i k * V i l`. When those products
are pairwise independent with common mean `M k l` and second moments about it at most `v`, the
entry has mean-square error at most `v / r` for `r` samples. Feeding this into the eigenvalue bound
with `η = c / (2 d)`, where `d` is the dimension, shows that, with probability at least
`1 - 4 d⁴ v / (r c²)`, every eigenvalue of the population matrix `M` that is at least `c` stays at
least `c / 2` for the empirical matrix.

## Main statements

* `TauCeti.measure_exists_lt_norm_sub_le`: the entrywise Chebyshev union bound.
* `TauCeti.measurableSet_exists_lt_norm_sub`: the entrywise deviation event is measurable when the
  entries are.
* `TauCeti.one_sub_le_measure_of_entry_le`: with probability at least
  `1 - card m * card n * v / η²`, every consequence of entrywise `η`-closeness holds.
* `TauCeti.one_sub_le_measure_forall_abs_eigenvalues₀_sub_le`: eigenvalue concentration.
* `TauCeti.one_sub_le_measure_forall_eigenvalues₀_sub_le`: the one-sided eigenvalue floor.
* `TauCeti.one_sub_le_measure_forall_norm_toEuclideanLin_sub_le`: rectangular operator
  concentration.
* `TauCeti.integral_sampleSecondMoment_apply_sub_sq_le`: the mean-square error of an entry of the
  empirical second-moment matrix.
* `TauCeti.one_sub_le_measure_forall_half_le_eigenvalues₀_sampleSecondMoment`: the empirical
  second-moment matrix keeps every population eigenvalue above `c` above `c / 2`.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §1.2 (Chebyshev's inequality) and §4.7
  (covariance estimation).
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed. (2013), Theorem 4.3.1 (Weyl's inequality).
-/

public section

open MeasureTheory ProbabilityTheory Matrix

namespace TauCeti

variable {Ω m n : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Fintype m] [Fintype n]

section Entrywise

variable {E : Type*} [NormedAddCommGroup E] {S : Ω → Matrix m n E} {A : Matrix m n E} {v η : ℝ}

/-- **Entrywise Chebyshev union bound.** If every entrywise deviation of a random matrix `S` from
a fixed matrix `A` has second moment at most `v`, then the probability that some entry deviates by
more than `η > 0` is at most `card m * card n * v / η²`. -/
theorem measure_exists_lt_norm_sub_le
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ)
    (hmoment : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) (hη : 0 < η) :
    μ {ω | ∃ k l, η < ‖S ω k l - A k l‖} ≤
      ENNReal.ofReal (Fintype.card m * Fintype.card n * v / η ^ 2) := by
  have hentry (k : m) (l : n) : μ {ω | η < ‖S ω k l - A k l‖} ≤ ENNReal.ofReal (v / η ^ 2) :=
    meas_gt_le_div_sq_of_integral_sq_le (hint k l) (hmoment k l) hη
  calc μ {ω | ∃ k l, η < ‖S ω k l - A k l‖}
      = μ (⋃ k, ⋃ l, {ω | η < ‖S ω k l - A k l‖}) := by simp only [Set.ofPred_exists]
    _ ≤ ∑ k, ∑ l, μ {ω | η < ‖S ω k l - A k l‖} :=
        (measure_iUnion_fintype_le μ _).trans
          (Finset.sum_le_sum fun k _ ↦ measure_iUnion_fintype_le μ _)
    _ ≤ ∑ _k : m, ∑ _l : n, ENNReal.ofReal (v / η ^ 2) := by gcongr with k _ l _; exact hentry k l
    _ = ENNReal.ofReal (Fintype.card m * Fintype.card n * v / η ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
        rw [mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

omit [Fintype m] [Fintype n] in
/-- The event that some entry of a random matrix deviates from a fixed matrix by more than `η` is
measurable when every entry is measurable. -/
theorem measurableSet_exists_lt_norm_sub [Finite m] [Finite n] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSub E] (hS : ∀ k l, Measurable fun ω ↦ S ω k l) (η : ℝ) :
    MeasurableSet {ω | ∃ k l, η < ‖S ω k l - A k l‖} := by
  simp only [Set.ofPred_exists]
  exact .iUnion fun k ↦ .iUnion fun l ↦
    measurableSet_lt measurable_const ((hS k l).sub_const (A k l)).norm

/-- **High-probability entrywise closeness.** On a probability space, if every entrywise deviation
of a random matrix `S` from a fixed matrix `A` has second moment at most `v`, then any set `s`
containing every outcome at which all entries of `S` are within `η > 0` of those of `A` has
probability at least `1 - card m * card n * v / η²`. -/
theorem one_sub_le_measure_of_entry_le [IsProbabilityMeasure μ] {s : Set Ω}
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ)
    (hmoment : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) (hη : 0 < η)
    (hs : ∀ ω, (∀ k l, ‖S ω k l - A k l‖ ≤ η) → ω ∈ s) :
    1 - ENNReal.ofReal (Fintype.card m * Fintype.card n * v / η ^ 2) ≤ μ s := by
  have hcompl : sᶜ ⊆ {ω | ∃ k l, η < ‖S ω k l - A k l‖} := fun ω hω ↦
    by_contra fun h ↦ hω (hs ω fun k l ↦ not_lt.1 fun hlt ↦ h ⟨k, l, hlt⟩)
  calc 1 - ENNReal.ofReal (Fintype.card m * Fintype.card n * v / η ^ 2)
      ≤ 1 - μ sᶜ :=
        tsub_le_tsub_left ((measure_mono hcompl).trans
          (measure_exists_lt_norm_sub_le hint hmoment hη)) 1
    _ ≤ μ s := Measure.one_sub_measure_compl_le μ s

end Entrywise

section Spectral

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq n] [IsProbabilityMeasure μ]
  {S : Ω → Matrix n n 𝕜} {A : Matrix n n 𝕜} {v η : ℝ}

/-- **Eigenvalue concentration.** If every entrywise deviation of a random Hermitian matrix `S`
from a fixed Hermitian matrix `A` has second moment at most `v`, then with probability at least
`1 - (card n)² v / η²` every sorted eigenvalue of `S` is within `card n * η` of the corresponding
eigenvalue of `A`. -/
theorem one_sub_le_measure_forall_abs_eigenvalues₀_sub_le (hS : ∀ ω, (S ω).IsHermitian)
    (hA : A.IsHermitian) (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ)
    (hmoment : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) (hη : 0 < η) :
    1 - ENNReal.ofReal (Fintype.card n ^ 2 * v / η ^ 2) ≤
      μ {ω | ∀ k, |(hS ω).eigenvalues₀ k - hA.eigenvalues₀ k| ≤ Fintype.card n * η} := by
  rw [sq (Fintype.card n : ℝ)]
  exact one_sub_le_measure_of_entry_le hint hmoment hη fun ω h k ↦
    (hS ω).abs_eigenvalues₀_sub_le_of_entry_le hA h k

/-- **One-sided eigenvalue floor.** Under the hypotheses of
`TauCeti.one_sub_le_measure_forall_abs_eigenvalues₀_sub_le`, with probability at least
`1 - (card n)² v / η²` every sorted eigenvalue of `S` is at least the corresponding eigenvalue of
`A` minus `card n * η`. -/
theorem one_sub_le_measure_forall_eigenvalues₀_sub_le (hS : ∀ ω, (S ω).IsHermitian)
    (hA : A.IsHermitian) (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ)
    (hmoment : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) (hη : 0 < η) :
    1 - ENNReal.ofReal (Fintype.card n ^ 2 * v / η ^ 2) ≤
      μ {ω | ∀ k, hA.eigenvalues₀ k - Fintype.card n * η ≤ (hS ω).eigenvalues₀ k} :=
  (one_sub_le_measure_forall_abs_eigenvalues₀_sub_le hS hA hint hmoment hη).trans <|
    measure_mono fun _ h k ↦ by linarith [(abs_le.1 (h k)).1]

/-- **Operator concentration for rectangular matrices.** If every entrywise deviation of a
random `m × n` matrix `S` from a fixed matrix `A` has second moment at most `v`, then with
probability at least `1 - card m * card n * v / η²` its Euclidean action is bounded by
`sqrt (card m) * η * sqrt (card n)`. -/
theorem one_sub_le_measure_forall_norm_toEuclideanLin_sub_le
    {S : Ω → Matrix m n 𝕜} {A : Matrix m n 𝕜}
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ)
    (hmoment : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) (hη : 0 < η) :
    1 - ENNReal.ofReal (Fintype.card m * Fintype.card n * v / η ^ 2) ≤
      μ {ω | ∀ x : EuclideanSpace 𝕜 n,
        ‖toEuclideanLin (S ω - A) x‖ ≤
          √(Fintype.card m) * η * √(Fintype.card n) * ‖x‖} :=
  one_sub_le_measure_of_entry_le hint hmoment hη fun ω h x ↦
    norm_toEuclideanLin_le_of_entry_le (A := S ω - A) (fun k l ↦ by
      simpa only [Matrix.sub_apply] using h k l) x

end Spectral

section SampleSecondMoment

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq n] [IsProbabilityMeasure μ]
  {V : ι → Ω → n → ℝ}
  {M : Matrix n n ℝ} {v : ℝ}

omit [Fintype n] [DecidableEq n] in
/-- **Mean-square error of an empirical second moment.** For real random vectors `V i`, if the
products `V i k * V i l` of two fixed coordinates are square-integrable, pairwise independent and
have a common mean `M k l`, and each has second moment about `M k l` at most `v`, then the
`(k, l)` entry of the empirical second-moment matrix has mean-square error at most `v / r`, where
`r` is the number of samples. -/
theorem integral_sampleSecondMoment_apply_sub_sq_le {k l : n}
    (hV : ∀ i, MemLp (fun ω ↦ V i ω k * V i ω l) 2 μ)
    (hmean : ∀ i, μ[fun ω ↦ V i ω k * V i ω l] = M k l)
    (hindep : Pairwise fun i j ↦ (fun ω ↦ V i ω k * V i ω l) ⟂ᵢ[μ] fun ω ↦ V j ω k * V j ω l)
    (hv : ∀ i, ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂μ ≤ v) :
    ∫ ω, (sampleSecondMoment (V · ω) k l - M k l) ^ 2 ∂μ ≤ v / Fintype.card ι := by
  simp only [sampleSecondMoment_apply, star_trivial]
  simpa only [Real.norm_eq_abs, sq_abs] using
    integral_norm_finiteMean_sub_sq_le_of_forall_le hV hmean hindep
      (by simpa only [Real.norm_eq_abs, sq_abs] using hv)

/-- **Eigenvalue floor for the empirical second-moment matrix.** Let `V i` be `r` real random
vectors of dimension `d`. Suppose that for every pair of coordinates `k, l` the products
`V i k * V i l` are square-integrable, pairwise independent and have a common mean `M k l`, with
second moments about it at most `v`, and that `M` is symmetric. Then for every `c > 0`, with
probability at least `1 - 4 d⁴ v / (r c²)`, every sorted eigenvalue of `M` that is at least `c`
has the corresponding eigenvalue of the empirical second-moment matrix at least `c / 2`. -/
theorem one_sub_le_measure_forall_half_le_eigenvalues₀_sampleSecondMoment (hM : M.IsHermitian)
    (hV : ∀ k l i, MemLp (fun ω ↦ V i ω k * V i ω l) 2 μ)
    (hmean : ∀ k l i, μ[fun ω ↦ V i ω k * V i ω l] = M k l)
    (hindep : ∀ k l,
      Pairwise fun i j ↦ (fun ω ↦ V i ω k * V i ω l) ⟂ᵢ[μ] fun ω ↦ V j ω k * V j ω l)
    (hv : ∀ k l i, ∫ ω, (V i ω k * V i ω l - M k l) ^ 2 ∂μ ≤ v) {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal (4 * Fintype.card n ^ 4 * v / (Fintype.card ι * c ^ 2)) ≤
      μ {ω | ∀ k, c ≤ hM.eigenvalues₀ k →
        c / 2 ≤ (isHermitian_sampleSecondMoment (V · ω)).eigenvalues₀ k} := by
  set d := Fintype.card n
  -- In dimension `0` there are no eigenvalues, so the event is certain.
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have huniv : {ω | ∀ k : Fin d, c ≤ hM.eigenvalues₀ k →
        c / 2 ≤ (isHermitian_sampleSecondMoment (V · ω)).eigenvalues₀ k} = Set.univ :=
      Set.eq_univ_of_forall fun _ k ↦ (Fin.cast hd k).elim0
    rw [huniv, measure_univ]
    exact tsub_le_self
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hr : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  -- Each entry of the empirical matrix is a square-integrable sample mean with mean-square
  -- error at most `v / r`.
  have hmemLp (k l : n) : MemLp (fun ω ↦ sampleSecondMoment (V · ω) k l - M k l) 2 μ := by
    simp only [sampleSecondMoment_apply, star_trivial, finiteMean_eq_inv_smul_sum, smul_eq_mul]
    exact ((memLp_finsetSum _ fun i _ ↦ hV k l i).const_mul _).sub (memLp_const _)
  have hfloor := one_sub_le_measure_forall_eigenvalues₀_sub_le
    (S := fun ω ↦ sampleSecondMoment (V · ω)) (v := v / Fintype.card ι) (η := c / (2 * d))
    (fun ω ↦ isHermitian_sampleSecondMoment (V · ω)) hM
    (fun k l ↦ by simpa only [Real.norm_eq_abs, sq_abs] using (hmemLp k l).integrable_sq)
    (fun k l ↦ by
      simpa only [Real.norm_eq_abs, sq_abs] using
        integral_sampleSecondMoment_apply_sub_sq_le (hV k l) (hmean k l) (hindep k l) (hv k l))
    (by positivity)
  have hbound : (d : ℝ) ^ 2 * (v / Fintype.card ι) / (c / (2 * d)) ^ 2 =
      4 * d ^ 4 * v / (Fintype.card ι * c ^ 2) := by
    field_simp
    ring
  have hshift : (d : ℝ) * (c / (2 * d)) = c / 2 := by
    field_simp
  rw [hbound, hshift] at hfloor
  exact hfloor.trans <| measure_mono fun _ h k hk ↦ by linarith [h k]

end SampleSecondMoment

end TauCeti
