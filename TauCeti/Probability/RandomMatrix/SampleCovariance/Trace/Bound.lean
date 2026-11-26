/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SampleCovariance.Trace.Word
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Combinatorics.TraceWord.Bipartite.Coding
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Füredi–Komlós bound on growing sample covariance traces

Let `X` be a random `p × n` matrix with independent, almost everywhere strongly measurable,
centred entries, bounded by `K` almost surely and with second absolute moments at most `v ≥ 0`,
and let `S = X Xᴴ / n`. If `K ^ 2 ≤ v * γ ^ 4 * √(p * n)` with `0 ≤ γ ≤ 1`, then for every `k`,
writing `y = p / n`,

`‖E trace S ^ k‖ ≤ p * (v * (1 + √y + 2 * k * γ * √y) * (1 + √y + 2 * k * γ)) ^ k`.

The bound is uniform in `k`. For entries truncated at a power `n ^ a` with `a < 1/2`, a fixed
variance bound `v > 0` and `p / n` bounded away from `0` and `∞`, the parameter `γ` can be chosen
to decay like a negative power of `n`, so that `k * γ` tends to zero along orders `k` of
logarithmic size. Then the expected trace grows at most like `p * (v * (1 + √y) ^ 2) ^ k`, the
`k`-th power of the upper edge of the Marchenko–Pastur law of ratio `y` and scale `v`. This is
the input of the moment method for the largest eigenvalue of a sample covariance matrix.

The proof expands the trace into closed bipartite words reading each position at least twice
(`TauCeti.Probability.integral_trace_sampleCovariance_pow`). A position read `d` times contributes
at most `K ^ (d - 2) * min v (K ^ 2)`
(`TauCeti.Probability.norm_integral_prod_mul_star_le_of_no_singleton_edge`). The word weights are
put in the form of the weighted bipartite Füredi–Komlós enumeration
`TauCeti.sum_pow_div_sqrt_mul_pow_le_of_no_singleton_edge` by
`TauCeti.pow_card_bipartiteEdge_mul_pow_le_of_no_singleton_edge` and counted by it.

## Main results

* `ProbabilityTheory.iIndepFun.norm_integral_trace_pow_sampleCovariance_le`: the trace bound.

## References

* Y. Q. Yin, Z. D. Bai, P. R. Krishnaiah, *On the limit of the largest eigenvalue of the large
  dimensional sample covariance matrix*, Probab. Theory Related Fields 78 (1988), 509–521.
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), Theorem 2.15.
* Z. Füredi and J. Komlós, *The eigenvalues of random symmetric matrices*, Combinatorica 1
  (1981), 233–241.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset

namespace ProbabilityTheory.iIndepFun

open TauCeti TauCeti.Probability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {P : Measure Ω}
  {X : Ω → Matrix p n 𝕜} [Fintype p] [Fintype n] [DecidableEq p]

/-- With rows and columns, the expected trace of the `k`-th power of the sample covariance,
`k ≠ 0`, is bounded by `n⁻ᵏ * (v * m) ^ k * m` times the weighted count of bipartite words of the
bipartite Füredi–Komlós enumeration, where `m = √(p * n)`. -/
private theorem norm_integral_trace_pow_sampleCovariance_le_mul_sum [DecidableEq n]
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hXm : ∀ i j, AEStronglyMeasurable (fun ω ↦ X ω i j) P)
    (hX₀ : ∀ i j, ∫ ω, X ω i j ∂P = 0) {K v γ : ℝ} (hXK : ∀ i j, ∀ᵐ ω ∂P, ‖X ω i j‖ ≤ K)
    (hXv : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P ≤ v)
    (hK : K ^ 2 ≤ v * γ ^ 4 * √(Fintype.card p * Fintype.card n)) {k : ℕ} (hk : k ≠ 0) :
    ‖∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P‖ ≤ (Fintype.card n : ℝ)⁻¹ ^ k *
      ((v * √(Fintype.card p * Fintype.card n)) ^ k * √(Fintype.card p * Fintype.card n)) *
        ∑ u : Fin k → p, ∑ w : Fin k → n with
          ∀ a, ∃ b ≠ a, bipartiteEdge u w b = bipartiteEdge u w a,
            γ ^ (2 * (2 * k + 2 - 2 * (#(univ.image u) + #(univ.image w)))) /
              √(Fintype.card p * Fintype.card n) ^ (#(univ.image u) + #(univ.image w)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hXk (i : p) (j : n) : MemLp (fun ω ↦ X ω i j) (2 * k : ℕ) P :=
    .of_bound (hXm i j) K (hXK i j)
  rw [integral_trace_sampleCovariance_pow hindep hX₀ hk (by exact_mod_cast hXk), norm_mul,
    norm_pow, norm_inv, RCLike.norm_natCast, mul_assoc, mul_sum]
  gcongr
  refine (norm_sum_le _ _).trans (sum_le_sum fun u _ ↦ (norm_sum_le _ _).trans ?_)
  rw [mul_sum]
  refine sum_le_sum fun w hw ↦ ?_
  have huw := (mem_filter.mp hw).2
  -- A position read `d ≥ 2` times contributes at most `K ^ (d - 2) * min v (K ^ 2)`.
  refine (norm_integral_prod_mul_star_le_of_no_singleton_edge (b := K) (c := min v (K ^ 2))
    hindep (fun a ↦ (hXm _ _).aemeasurable) huw fun a ↦ ?_).trans ?_
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le'
      (two_le_card_filter_eq_of_no_singleton_fiber huw _ (mem_image_of_mem _ (mem_univ a)))
    rw [hd, Nat.add_sub_cancel]
    exact integral_norm_pow_add_two_le (hXK _ _) (hXv _ _) d
  · let i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
    have hv : 0 ≤ v := (integral_nonneg fun _ ↦ by positivity).trans (hXv (u i) (w i))
    exact pow_card_bipartiteEdge_mul_pow_le_of_no_singleton_edge hk huw hv
      (by rwa [mul_right_comm])

/-- **Füredi–Komlós bound on sample covariance traces.** Let the entries of a random `p × n`
matrix `X` be independent, almost everywhere strongly measurable and centred, bounded by `K` in
norm almost surely, and with second absolute moments at most `v ≥ 0`. If `0 ≤ γ ≤ 1` and
`K ^ 2 ≤ v * γ ^ 4 * √(p * n)`, then for every `k` the expected trace of the `k`-th power of the
sample covariance `X Xᴴ / n` has norm at most
`p * (v * (1 + √y + 2 * k * γ * √y) * (1 + √y + 2 * k * γ)) ^ k`, where `y = p / n`. -/
theorem norm_integral_trace_pow_sampleCovariance_le
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hXm : ∀ i j, AEStronglyMeasurable (fun ω ↦ X ω i j) P)
    (hX₀ : ∀ i j, ∫ ω, X ω i j ∂P = 0) {K v γ : ℝ} (hXK : ∀ i j, ∀ᵐ ω ∂P, ‖X ω i j‖ ≤ K)
    (hXv : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P ≤ v) (hv : 0 ≤ v) (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    (hK : K ^ 2 ≤ v * γ ^ 4 * √(Fintype.card p * Fintype.card n)) (k : ℕ) :
    ‖∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P‖ ≤
      Fintype.card p * (v * (1 + √(Fintype.card p / Fintype.card n) +
        2 * k * γ * √(Fintype.card p / Fintype.card n)) *
          (1 + √(Fintype.card p / Fintype.card n) + 2 * k * γ)) ^ k := by
  classical
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  -- Without rows or without columns the traces vanish.
  rcases isEmpty_or_nonempty p with hp | hp
  · simp [Matrix.trace]
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 (ω : Ω) : (X ω).sampleCovariance = 0 := by simp [sampleCovariance_def]
    simp only [h0, zero_pow hk.ne', trace_zero, integral_zero, norm_zero]
    positivity
  refine ((norm_integral_trace_pow_sampleCovariance_le_mul_sum hindep hXm hX₀ hXK hXv hK
    hk.ne').trans (mul_le_mul_of_nonneg_left
      (sum_pow_div_sqrt_mul_pow_le_of_no_singleton_edge hk.ne' hγ₀ hγ₁)
        (by positivity))).trans_eq ?_
  -- Rescale the bound of the bipartite enumeration by the word weights: with `s = √(p / n)`,
  -- `√(p * n) = n * s`, `√(n / p) = s⁻¹` and `p = n * s ^ 2`.
  have hp₀ : (0 : ℝ) < Fintype.card p := Nat.cast_pos.mpr Fintype.card_pos
  have hn₀ : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have h₁ : √(Fintype.card p * Fintype.card n : ℝ) =
      Fintype.card n * √(Fintype.card p / Fintype.card n : ℝ) :=
    Real.sqrt_mul_eq_mul_sqrt_div _ hn₀.le
  have h₂ : √(Fintype.card n / Fintype.card p : ℝ) =
      (√(Fintype.card p / Fintype.card n : ℝ))⁻¹ := by
    rw [← Real.sqrt_inv, inv_div]
  have h₃ : (Fintype.card p : ℝ) =
      Fintype.card n * √(Fintype.card p / Fintype.card n : ℝ) ^ 2 := by
    rw [Real.sq_sqrt (div_pos hp₀ hn₀).le, mul_div_cancel₀ _ hn₀.ne']
  have hs : √(Fintype.card p / Fintype.card n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (div_pos hp₀ hn₀)).ne'
  rw [h₁, h₂]
  generalize √(Fintype.card p / Fintype.card n : ℝ) = s at h₃ hs ⊢
  rw [h₃]
  -- The base of the right side is the product of the bases `n⁻¹`, `v * (n * s)` and
  -- `(s⁻¹ + 1 + 2 * k * γ) * (s + 1 + 2 * k * γ)` of the left side.
  have hbase : v * (1 + s + 2 * k * γ * s) * (1 + s + 2 * k * γ) = (Fintype.card n : ℝ)⁻¹ *
      (v * (Fintype.card n * s)) * ((s⁻¹ + 1 + 2 * k * γ) * (s + 1 + 2 * k * γ)) := by
    field_simp
    ring
  rw [hbase]
  simp only [mul_pow]
  ring

end ProbabilityTheory.iIndepFun
