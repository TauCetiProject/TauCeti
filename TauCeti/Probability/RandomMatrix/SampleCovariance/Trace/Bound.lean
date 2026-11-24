/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SampleCovariance.Trace.Word
import TauCeti.Algebra.Order.GroupWithZero.Pow
import TauCeti.Combinatorics.TraceWord.Bipartite.Coding
import TauCeti.Probability.Moments.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Füredi–Komlós bound on growing sample covariance traces

Let `X` be a random `p × n` matrix with independent centred entries, bounded by `K` almost surely
and with second absolute moments at most `v ≥ 0`, and let `S = X Xᴴ / n`. If
`K ^ 2 ≤ v * γ ^ 4 * √(p * n)` with `0 ≤ γ ≤ 1`, then for every `k`, writing `y = p / n`,

`‖E trace S ^ k‖ ≤ p * (v * (1 + √y + 2 * k * γ * √y) * (1 + √y + 2 * k * γ)) ^ k`.

The bound is uniform in `k`. For entries truncated at a power `n ^ a` with `a < 1/2` and
`p / n` bounded away from `0` and `∞`, the parameter `γ` can be chosen to decay like a negative
power of `n`, so that `k * γ` tends to zero along orders `k` of logarithmic size. Then the expected
trace grows at most like `p * (v * (1 + √y) ^ 2) ^ k`, the `k`-th power of the upper edge of the
Marchenko–Pastur law of ratio `y` and scale `v`. This is the input of the moment method for the
largest eigenvalue of a sample covariance matrix.

The proof expands the trace into closed bipartite words reading each position at least twice
(`TauCeti.Probability.integral_trace_sampleCovariance_pow`). A position read `d` times contributes
at most `K ^ (d - 2) * min v (K ^ 2)`
(`TauCeti.Probability.norm_integral_prod_mul_star_le_of_no_singleton_edge`), and the words are
counted by the weighted bipartite Füredi–Komlós enumeration
`TauCeti.sum_pow_div_sqrt_mul_pow_le_of_no_singleton_edge`.

## Main results

* `ProbabilityTheory.iIndepFun.norm_integral_trace_sampleCovariance_pow_le`: the trace bound.

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

namespace TauCeti

/-- The bound for a single bipartite word in the form counted by the bipartite Füredi–Komlós
enumeration: a word reading `e ≤ k` distinct positions and visiting `1 ≤ t ≤ e + 1` row and
column indices contributes at most `(v * m) ^ k * m * γ ^ (2 * (2 * k + 2 - 2 * t)) / m ^ t`. -/
private theorem pow_mul_pow_sub_le_mul_pow_div_pow {b c v γ m : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcb : c ≤ b ^ 2) (hcv : c ≤ v) (hbm : b ^ 2 ≤ v * γ ^ 4 * m) (hm : 0 < m)
    {e t k : ℕ} (ht : 1 ≤ t) (hte : t ≤ e + 1) (hek : e ≤ k) :
    c ^ e * b ^ (2 * k - 2 * e) ≤ (v * m) ^ k * m * (γ ^ (2 * (2 * k + 2 - 2 * t)) / m ^ t) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = t + j := ⟨k - t, by omega⟩
  have hv : 0 ≤ v := hc.trans hcv
  calc _ ≤ c ^ t * b ^ (2 * (t + j) - 2 * t) := pow_mul_pow_sub_two_mul_le hb hc hcb (by omega)
        (by omega)
    _ ≤ v ^ t * (v * γ ^ 4 * m) ^ j := by
        rw [show 2 * (t + j) - 2 * t = 2 * j by omega, pow_mul]
        exact mul_le_mul (pow_le_pow_left₀ hc hcv _) (pow_le_pow_left₀ (sq_nonneg b) hbm _)
          (by positivity) (by positivity)
    _ = _ := by
        rw [show 2 * (2 * (t + j) + 2 - 2 * (t + 1)) = 4 * j by omega]
        field_simp
        ring

/-- The rescaled bound of the bipartite Füredi–Komlós enumeration, for `s = √(p / n)`. -/
private theorem inv_pow_mul_pow_mul_mul_eq {n s v δ : ℝ} (hn : n ≠ 0) (hs : s ≠ 0) (k : ℕ) :
    n⁻¹ ^ k * ((v * (n * s)) ^ k * (n * s)) * (s * ((s⁻¹ + 1 + δ) * (s + 1 + δ)) ^ k) =
      n * s ^ 2 * (v * (1 + s + δ * s) * (1 + s + δ)) ^ k := by
  rw [show v * (1 + s + δ * s) * (1 + s + δ) =
      n⁻¹ * (v * (n * s)) * ((s⁻¹ + 1 + δ) * (s + 1 + δ)) by field_simp; ring]
  simp only [mul_pow]
  ring

/-- The bound of the bipartite Füredi–Komlós enumeration, rescaled by the word weights, in terms
of the aspect ratio `y = p / n`. -/
private theorem inv_pow_mul_pow_mul_sqrt_mul_eq {p n v δ : ℝ} (hp : 0 < p) (hn : 0 < n) (k : ℕ) :
    n⁻¹ ^ k * ((v * √(p * n)) ^ k * √(p * n)) *
        (√(p / n) * ((√(n / p) + 1 + δ) * (√(p / n) + 1 + δ)) ^ k) =
      p * (v * (1 + √(p / n) + δ * √(p / n)) * (1 + √(p / n) + δ)) ^ k := by
  have h₁ : √(p * n) = n * √(p / n) := by
    rw [← Real.sqrt_sq hn.le, ← Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]
    congr 1
    field_simp
  have h₂ : √(n / p) = (√(p / n))⁻¹ := by rw [← Real.sqrt_inv, inv_div]
  rw [h₁, h₂, inv_pow_mul_pow_mul_mul_eq hn.ne' (Real.sqrt_pos.mpr (div_pos hp hn)).ne',
    Real.sq_sqrt (div_pos hp hn).le, mul_div_cancel₀ _ hn.ne']

end TauCeti

namespace ProbabilityTheory.iIndepFun

open TauCeti TauCeti.Probability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {P : Measure Ω}
  {X : Ω → Matrix p n 𝕜} [Fintype p] [Fintype n] [DecidableEq p]

/-- With rows and columns, the expected trace of the `k`-th power of the sample covariance,
`k ≠ 0`, is bounded by `n⁻ᵏ * (v * m) ^ k * m` times the weighted count of bipartite words of the
bipartite Füredi–Komlós enumeration, where `m = √(p * n)`. -/
private theorem norm_integral_trace_sampleCovariance_pow_le_mul_sum [Nonempty p] [Nonempty n]
    [DecidableEq n] (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hXm : ∀ i j, AEStronglyMeasurable (fun ω ↦ X ω i j) P)
    (hX₀ : ∀ i j, ∫ ω, X ω i j ∂P = 0) {K v γ : ℝ} (hXK : ∀ i j, ∀ᵐ ω ∂P, ‖X ω i j‖ ≤ K)
    (hXv : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P ≤ v) (hv : 0 ≤ v)
    (hK : K ^ 2 ≤ v * γ ^ 4 * √(Fintype.card p * Fintype.card n)) {k : ℕ} (hk : k ≠ 0) :
    ‖∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P‖ ≤ (Fintype.card n : ℝ)⁻¹ ^ k *
      ((v * √(Fintype.card p * Fintype.card n)) ^ k * √(Fintype.card p * Fintype.card n)) *
        ∑ u : Fin k → p, ∑ w : Fin k → n with
          ∀ a, ∃ b ≠ a, bipartiteEdge u w b = bipartiteEdge u w a,
            γ ^ (2 * (2 * k + 2 - 2 * (#(univ.image u) + #(univ.image w)))) /
              √(Fintype.card p * Fintype.card n) ^ (#(univ.image u) + #(univ.image w)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  have hm : 0 < √(Fintype.card p * Fintype.card n) := Real.sqrt_pos.mpr
    (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos))
  have hK₀ : 0 ≤ K := (hXK (Classical.arbitrary p) (Classical.arbitrary n)).exists.elim
    fun _ h ↦ (norm_nonneg _).trans h
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
    (fun i j ↦ (hXm i j).aemeasurable) hindep huw fun a ↦ ?_).trans ?_
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le'
      (two_le_card_filter_eq_of_no_singleton_fiber huw _ (mem_image_of_mem _ (mem_univ a)))
    rw [hd, Nat.add_sub_cancel]
    exact integral_norm_pow_add_two_le (hXK _ _) (hXv _ _) d
  · exact pow_mul_pow_sub_le_mul_pow_div_pow hK₀ (le_min hv (sq_nonneg K)) (min_le_right _ _)
      (min_le_left _ _) hK hm (card_pos.mpr (univ_nonempty.image _) |>.trans_le le_self_add)
      (card_image_add_card_image_le_card_image_bipartiteEdge_add_one u w)
      (card_image_bipartiteEdge_le_of_no_singleton_edge huw)

/-- **Füredi–Komlós bound on sample covariance traces.** Let the entries of a random `p × n`
matrix `X` be independent and centred, bounded by `K` in norm almost surely, and with second
absolute moments at most `v ≥ 0`. If `0 ≤ γ ≤ 1` and `K ^ 2 ≤ v * γ ^ 4 * √(p * n)`, then for
every `k` the expected trace of the `k`-th power of the sample covariance `X Xᴴ / n` has norm at
most `p * (v * (1 + √y + 2 * k * γ * √y) * (1 + √y + 2 * k * γ)) ^ k`, where `y = p / n`. -/
theorem norm_integral_trace_sampleCovariance_pow_le
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
  refine ((norm_integral_trace_sampleCovariance_pow_le_mul_sum hindep hXm hX₀ hXK hXv hv hK
    hk.ne').trans ?_).trans_eq (inv_pow_mul_pow_mul_sqrt_mul_eq
      (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos) k)
  gcongr
  exact sum_pow_div_sqrt_mul_pow_le_of_no_singleton_edge hk.ne' hγ₀ hγ₁

end ProbabilityTheory.iIndepFun
