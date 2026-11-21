/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Uniform Leibniz bounds for bilinear expressions

Mathlib's Leibniz bound `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear` controls
the `k`-th derivative of `y ↦ B (f y) (g y)` by a binomial sum over the derivatives of `f` and
`g`. It holds at any point near which `f` and `g` are smooth enough, with no global regularity
(`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt`), and so gives
asymptotic bounds along any filter on which `f` and `g` are eventually smooth
(`ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear_of_contDiffAt`). When all derivatives
of `f` of order at most `k` are bounded by `M₁` and those of `g` by `M₂`, the sum collapses to
`‖B‖ * 2 ^ k * M₁ * M₂`
(`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_forall_le`). The constant
`‖B‖ * 2 ^ k` depends only on `B` and `k`, which gives one constant serving every function and
every order at most `k` (`TauCeti.exists_norm_iteratedFDeriv_bilinear_le`).
-/

public section

open scoped ContDiff

variable {𝕜 E X Y Z : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- **The Leibniz bound at a point.** If `f` and `g` are `C^N` at `x`, the `n`-th derivative of
`y ↦ B (f y) (g y)` at `x`, for `n ≤ N`, is bounded by the binomial sum of the derivatives of `f`
and `g` at `x`. This is the local form of `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear`,
which asks for global smoothness. -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt
    (B : X →L[𝕜] Y →L[𝕜] Z) {f : E → X} {g : E → Y} {x : E} {N : ℕ∞ω}
    (hf : ContDiffAt 𝕜 N f x) (hg : ContDiffAt 𝕜 N g x) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => B (f y) (g y)) x‖ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := n) hn (by simp)
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn (m := n) hn (by simp)
  obtain ⟨t, htuv, ht, hxt⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hv)
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfu.mono (htuv.trans Set.inter_subset_left)) (hgv.mono (htuv.trans Set.inter_subset_right))
    ht.uniqueDiffOn hxt le_rfl
  simpa only [iteratedFDerivWithin_of_isOpen _ ht hxt] using h

open Asymptotics in
/-- **Asymptotic Leibniz bound.** Along a filter `l` on which `f` and `g` are eventually `C^N`, if
for `i ≤ n` the `i`-th derivatives of `f` and `g` are `O(ρ₁ i)` and `O(ρ₂ i)`, and every product
`ρ₁ i * ρ₂ (n - i)` is `O(ρ)`, then the `n`-th derivative of `y ↦ B (f y) (g y)` is `O(ρ)`. -/
theorem ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear_of_contDiffAt
    (B : X →L[𝕜] Y →L[𝕜] Z) {f : E → X} {g : E → Y} {N : ℕ∞ω} {l : Filter E}
    (hf : ∀ᶠ y in l, ContDiffAt 𝕜 N f y) (hg : ∀ᶠ y in l, ContDiffAt 𝕜 N g y) {n : ℕ}
    (hn : n ≤ N) {ρ₁ ρ₂ : ℕ → E → ℝ} {ρ : E → ℝ}
    (hfn : ∀ i ≤ n, iteratedFDeriv 𝕜 i f =O[l] ρ₁ i)
    (hgn : ∀ i ≤ n, iteratedFDeriv 𝕜 i g =O[l] ρ₂ i)
    (hρ : ∀ i ≤ n, (fun y ↦ ρ₁ i y * ρ₂ (n - i) y) =O[l] ρ) :
    iteratedFDeriv 𝕜 n (fun y ↦ B (f y) (g y)) =O[l] ρ := by
  have hsum : (fun y ↦ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv 𝕜 i f y‖ * ‖iteratedFDeriv 𝕜 (n - i) g y‖) =O[l] ρ := by
    refine IsBigO.const_mul_left (IsBigO.fun_sum fun i hi ↦ ?_) _
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact (((hfn i hi').norm_left.const_mul_left _).mul
      (hgn (n - i) (Nat.sub_le n i)).norm_left).trans (hρ i hi')
  refine IsBigO.trans (IsBigO.of_bound 1 ?_) hsum
  filter_upwards [hf, hg] with y hfy hgy
  rw [one_mul, Real.norm_eq_abs]
  exact (B.norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt hfy hgy hn).trans (le_abs_self _)

/-- The Leibniz rule at a point of an open set, with all derivatives of order at most `k` of `f`
and `g` bounded by constants. -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_forall_le
    (B : X →L[𝕜] Y →L[𝕜] Z) {f : E → X} {g : E → Y} {U : Set E} (hU : IsOpen U) {x : E}
    (hx : x ∈ U) {k : ℕ} (hf : ContDiffOn 𝕜 k f U) (hg : ContDiffOn 𝕜 k g U) {M₁ M₂ : ℝ}
    (h₁ : ∀ i ≤ k, ‖iteratedFDeriv 𝕜 i f x‖ ≤ M₁) (h₂ : ∀ i ≤ k, ‖iteratedFDeriv 𝕜 i g x‖ ≤ M₂) :
    ‖iteratedFDeriv 𝕜 k (fun y => B (f y) (g y)) x‖ ≤ ‖B‖ * 2 ^ k * M₁ * M₂ := by
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hU.uniqueDiffOn hx (n := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hU hx] at h
  refine h.trans ?_
  calc ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f U x‖ *
        ‖iteratedFDerivWithin 𝕜 (k - i) g U x‖
      ≤ ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M₁ * M₂ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (norm_nonneg B)
        rw [iteratedFDerivWithin_of_isOpen i hU hx, iteratedFDerivWithin_of_isOpen (k - i) hU hx]
        have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (h₁ 0 (Nat.zero_le _))
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (h₁ i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) (Nat.cast_nonneg _))
          (h₂ (k - i) (Nat.sub_le k i)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hM₁)
    _ = ‖B‖ * 2 ^ k * M₁ * M₂ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring

namespace TauCeti

variable (E) in
/-- The Leibniz rule at a point, as a bound with a constant depending only on `B` and `k`, valid
for all derivatives of order at most `k`. -/
theorem exists_norm_iteratedFDeriv_bilinear_le (B : X →L[𝕜] Y →L[𝕜] Z) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (f : E → X) (g : E → Y) (U : Set E) (x : E), IsOpen U → x ∈ U →
      ContDiffOn 𝕜 k f U → ContDiffOn 𝕜 k g U → ∀ M₁ M₂ : ℝ,
      (∀ i ≤ k, ‖iteratedFDeriv 𝕜 i f x‖ ≤ M₁) → (∀ i ≤ k, ‖iteratedFDeriv 𝕜 i g x‖ ≤ M₂) →
      ∀ j ≤ k, ‖iteratedFDeriv 𝕜 j (fun y => B (f y) (g y)) x‖ ≤ C * (M₁ * M₂) := by
  refine ⟨‖B‖ * 2 ^ k, by positivity, fun f g U x hU hx hf hg M₁ M₂ h₁ h₂ j hj => ?_⟩
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (h₁ 0 (Nat.zero_le _))
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ 0 (Nat.zero_le _))
  have hjk : ((j : ℕ∞ω)) ≤ k := by exact_mod_cast hj
  refine (B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le hU hx (hf.of_le hjk) (hg.of_le hjk)
    (fun i hi => h₁ i (hi.trans hj)) (fun i hi => h₂ i (hi.trans hj))).trans ?_
  have : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hj
  calc ‖B‖ * 2 ^ j * M₁ * M₂ = ‖B‖ * 2 ^ j * (M₁ * M₂) := by ring
    _ ≤ ‖B‖ * 2 ^ k * (M₁ * M₂) := by gcongr

end TauCeti
