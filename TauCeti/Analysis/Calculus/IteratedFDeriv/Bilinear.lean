/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Uniform Leibniz bounds for bilinear expressions

Mathlib's Leibniz bound `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear` controls
the `k`-th derivative of `y ↦ B (f y) (g y)` by a binomial sum over the derivatives of `f` and
`g`. It holds at any point near which `f` and `g` are smooth enough, with no global regularity
(`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt`), and so gives
asymptotic bounds along any filter on which `f` and `g` are eventually smooth
(`ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear_of_contDiffAt`), for instance power
bounds `‖y‖ ^ (ℓ - i)` and `‖y‖ ^ (m - i)`, whose orders add
(`ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear_rpow`). When all derivatives
of `f` of order at most `k` are bounded by `M₁` and those of `g` by `M₂`, the sum collapses to
`‖B‖ * 2 ^ k * M₁ * M₂`
(`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_forall_le`). The constant
`‖B‖ * 2 ^ k` depends only on `B` and `k`, which gives one constant serving every function and
every order at most `k` (`TauCeti.exists_norm_iteratedFDeriv_bilinear_le`).

Applied to differences, the same bound shows that the `k`-th derivative of `B (f y) (g y)` at a
point depends continuously on the derivatives of order at most `k` of `f` and `g` there
(`ContinuousLinearMap.norm_iteratedFDeriv_sub_le_of_bilinear`). For maps `f τ`, `g τ` depending on
a parameter `τ`, it follows that if the derivatives of order at most `k` at `x` are differentiable
in `τ`, then so is the `k`-th derivative of `B (f τ y) (g τ y)` at `x`, with the derivative given by
the product rule (`ContinuousLinearMap.hasDerivWithinAt_iteratedFDeriv_of_bilinear`). This is how
a time derivative passes through the spatial derivatives of a product of space-time functions.
Its proof takes derivatives of first-order Taylor remainders `f τ - f t - (τ - t) • f'` termwise
(`TauCeti.iteratedFDeriv_sub_sub_const_smul_apply`).
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

open Asymptotics in
/-- The exponents in the Leibniz rule for power bounds add up, along any filter: the product of
the bounds `‖y‖ ^ (ℓ - i)` and `‖y‖ ^ (m - (n - i))` is at most `‖y‖ ^ (ℓ + m - n)`. -/
private theorem isBigO_rpow_mul_rpow (l : Filter E) (ℓ m : ℝ) {n i : ℕ} (hi : i ≤ n) :
    (fun y : E ↦ ‖y‖ ^ (ℓ - i) * ‖y‖ ^ (m - (n - i : ℕ))) =O[l] fun y ↦ ‖y‖ ^ (ℓ + m - n) := by
  have he : ℓ - i + (m - (n - i : ℕ)) = ℓ + m - n := by
    push_cast [Nat.cast_sub hi]
    ring
  refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun y ↦ ?_)
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), ← he]
  exact Real.le_rpow_add (norm_nonneg y) _ _

open Asymptotics in
/-- **The Leibniz rule for power bounds.** Along a filter `l` on which `f` and `g` are eventually
`C^N`, if for `i ≤ n ≤ N` the `i`-th derivatives of `f` and `g` are `O(‖y‖ ^ (ℓ - i))` and
`O(‖y‖ ^ (m - i))`, then the `n`-th derivative of `y ↦ B (f y) (g y)` is
`O(‖y‖ ^ (ℓ + m - n))`. -/
theorem ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear_rpow
    (B : X →L[𝕜] Y →L[𝕜] Z) {l : Filter E} {f : E → X} {g : E → Y} {N : ℕ∞ω}
    (hf : ∀ᶠ y in l, ContDiffAt 𝕜 N f y) (hg : ∀ᶠ y in l, ContDiffAt 𝕜 N g y) {ℓ m : ℝ} {n : ℕ}
    (hn : n ≤ N) (hfn : ∀ i ≤ n, iteratedFDeriv 𝕜 i f =O[l] fun y ↦ ‖y‖ ^ (ℓ - i))
    (hgn : ∀ i ≤ n, iteratedFDeriv 𝕜 i g =O[l] fun y ↦ ‖y‖ ^ (m - i)) :
    iteratedFDeriv 𝕜 n (fun y ↦ B (f y) (g y)) =O[l] fun y ↦ ‖y‖ ^ (ℓ + m - n) :=
  B.isBigO_iteratedFDeriv_of_bilinear_of_contDiffAt (ρ₁ := fun i y ↦ ‖y‖ ^ (ℓ - i))
    (ρ₂ := fun i y ↦ ‖y‖ ^ (m - i)) hf hg hn hfn hgn fun _ hi ↦ isBigO_rpow_mul_rpow l ℓ m hi

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

/-- **The Leibniz rule for differences.** At a point `x`, the `n`-th derivatives of
`y ↦ B (f₁ y) (g₁ y)` and `y ↦ B (f₂ y) (g₂ y)` differ by at most `‖B‖ 2ⁿ (δ₁ N + M δ₂)` when the
derivatives at `x` of order at most `n` of `f₁ - f₂` are bounded by `δ₁`, those of `g₁ - g₂` by
`δ₂`, those of `g₁` by `N` and those of `f₂` by `M`. -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_sub_le_of_bilinear (B : X →L[𝕜] Y →L[𝕜] Z)
    {f₁ f₂ : E → X} {g₁ g₂ : E → Y} {n : ℕ} (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂)
    (hg₁ : ContDiff 𝕜 n g₁) (hg₂ : ContDiff 𝕜 n g₂) {x : E} {M N δ₁ δ₂ : ℝ}
    (hδ₁ : ∀ i ≤ n, ‖iteratedFDeriv 𝕜 i f₁ x - iteratedFDeriv 𝕜 i f₂ x‖ ≤ δ₁)
    (hN : ∀ i ≤ n, ‖iteratedFDeriv 𝕜 i g₁ x‖ ≤ N) (hM : ∀ i ≤ n, ‖iteratedFDeriv 𝕜 i f₂ x‖ ≤ M)
    (hδ₂ : ∀ i ≤ n, ‖iteratedFDeriv 𝕜 i g₁ x - iteratedFDeriv 𝕜 i g₂ x‖ ≤ δ₂) :
    ‖iteratedFDeriv 𝕜 n (fun y ↦ B (f₁ y) (g₁ y)) x -
        iteratedFDeriv 𝕜 n (fun y ↦ B (f₂ y) (g₂ y)) x‖ ≤ ‖B‖ * 2 ^ n * (δ₁ * N + M * δ₂) := by
  -- `B f₁ g₁ - B f₂ g₂ = B (f₁ - f₂) g₁ + B f₂ (g₁ - g₂)`, and each term obeys the Leibniz bound.
  have hsplit : ((fun y ↦ B (f₁ y) (g₁ y)) - fun y ↦ B (f₂ y) (g₂ y)) =
      (fun y ↦ B ((f₁ - f₂) y) (g₁ y)) + fun y ↦ B (f₂ y) ((g₁ - g₂) y) := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, sub_apply]
    abel
  have hf : ContDiff 𝕜 n (f₁ - f₂) := hf₁.sub hf₂
  have hg : ContDiff 𝕜 n (g₁ - g₂) := hg₁.sub hg₂
  rw [← iteratedFDeriv_sub_apply ((hf₁.continuousLinearMap_comp B).clm_apply hg₁).contDiffAt
      ((hf₂.continuousLinearMap_comp B).clm_apply hg₂).contDiffAt, hsplit,
    iteratedFDeriv_add_apply ((hf.continuousLinearMap_comp B).clm_apply hg₁).contDiffAt
      ((hf₂.continuousLinearMap_comp B).clm_apply hg).contDiffAt]
  have h₁ := B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le isOpen_univ (Set.mem_univ x)
    hf.contDiffOn hg₁.contDiffOn (fun i hi ↦ by
      rw [iteratedFDeriv_sub_apply (hf₁.of_le (by exact_mod_cast hi)).contDiffAt
        (hf₂.of_le (by exact_mod_cast hi)).contDiffAt]
      exact hδ₁ i hi) hN
  have h₂ := B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le isOpen_univ (Set.mem_univ x)
    hf₂.contDiffOn hg.contDiffOn hM (fun i hi ↦ by
      rw [iteratedFDeriv_sub_apply (hg₁.of_le (by exact_mod_cast hi)).contDiffAt
        (hg₂.of_le (by exact_mod_cast hi)).contDiffAt]
      exact hδ₂ i hi)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ‖B‖ * 2 ^ n * δ₁ * N + ‖B‖ * 2 ^ n * M * δ₂ := add_le_add h₁ h₂
    _ = _ := by ring

/-- A first-order Taylor remainder `h τ - h t - (τ - t) h'` of `Cⁿ` maps is `Cⁿ`. -/
private theorem contDiff_taylor_remainder {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {h : 𝕜 → E → V} {h' : E → V} {n : ℕ∞ω} (hh : ∀ τ, ContDiff 𝕜 n (h τ)) (hh' : ContDiff 𝕜 n h')
    (t τ : 𝕜) : ContDiff 𝕜 n (h τ - h t - (τ - t) • h') :=
  ((hh τ).sub (hh t)).sub (hh'.const_smul _)

/-- The algebra behind `ContinuousLinearMap.hasDerivWithinAt_iteratedFDeriv_of_bilinear`: the
first-order Taylor remainder in `τ` of the `n`-th derivative at `x` of `B (f τ y) (g τ y)` is the
`n`-th derivative of `B φ (g τ) + B (f t) ψ + (τ - t) B f' (g τ - g t)`, where `φ` and `ψ` are the
first-order Taylor remainders of `f` and `g`. -/
private theorem ContinuousLinearMap.iteratedFDeriv_bilinear_taylor_eq
    (B : X →L[𝕜] Y →L[𝕜] Z) {f : 𝕜 → E → X} {g : 𝕜 → E → Y} {f' : E → X} {g' : E → Y} {t τ : 𝕜}
    {x : E} {n : ℕ} (hf : ∀ τ, ContDiff 𝕜 n (f τ)) (hg : ∀ τ, ContDiff 𝕜 n (g τ))
    (hf' : ContDiff 𝕜 n f') (hg' : ContDiff 𝕜 n g') :
    iteratedFDeriv 𝕜 n (fun y ↦ B (f τ y) (g τ y)) x -
        iteratedFDeriv 𝕜 n (fun y ↦ B (f t y) (g t y)) x -
        (τ - t) • (iteratedFDeriv 𝕜 n (fun y ↦ B (f' y) (g t y)) x +
          iteratedFDeriv 𝕜 n (fun y ↦ B (f t y) (g' y)) x) =
      iteratedFDeriv 𝕜 n (fun y ↦ B ((f τ - f t - (τ - t) • f') y) (g τ y)) x +
        iteratedFDeriv 𝕜 n (fun y ↦ B (f t y) ((g τ - g t - (τ - t) • g') y)) x +
        (τ - t) • iteratedFDeriv 𝕜 n (fun y ↦ B (f' y) ((g τ - g t) y)) x := by
  have hB {φ : E → X} {ψ : E → Y} (hφ : ContDiff 𝕜 n φ) (hψ : ContDiff 𝕜 n ψ) :
      ContDiff 𝕜 n fun y ↦ B (φ y) (ψ y) :=
    (hφ.continuousLinearMap_comp B).clm_apply hψ
  have hφ := contDiff_taylor_remainder hf hf' t τ
  have hψ := contDiff_taylor_remainder hg hg' t τ
  have hgs : ContDiff 𝕜 n (g τ - g t) := (hg τ).sub (hg t)
  have hsplit : (fun y ↦ B (f τ y) (g τ y)) - (fun y ↦ B (f t y) (g t y)) -
      (τ - t) • ((fun y ↦ B (f' y) (g t y)) + fun y ↦ B (f t y) (g' y)) =
      (fun y ↦ B ((f τ - f t - (τ - t) • f') y) (g τ y)) +
        (fun y ↦ B (f t y) ((g τ - g t - (τ - t) • g') y)) +
        (τ - t) • fun y ↦ B (f' y) ((g τ - g t) y) := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, map_sub, map_smul, sub_apply,
      smul_apply]
    module
  have hP : ContDiff 𝕜 n ((fun y ↦ B (f τ y) (g τ y)) - fun y ↦ B (f t y) (g t y)) :=
    (hB (hf τ) (hg τ)).sub (hB (hf t) (hg t))
  have hQ : ContDiff 𝕜 n ((fun y ↦ B (f' y) (g t y)) + fun y ↦ B (f t y) (g' y)) :=
    (hB hf' (hg t)).add (hB (hf t) hg')
  have hQs : ContDiff 𝕜 n ((τ - t) • ((fun y ↦ B (f' y) (g t y)) + fun y ↦ B (f t y) (g' y))) :=
    hQ.const_smul _
  have hR : ContDiff 𝕜 n ((fun y ↦ B ((f τ - f t - (τ - t) • f') y) (g τ y)) +
      fun y ↦ B (f t y) ((g τ - g t - (τ - t) • g') y)) :=
    (hB hφ (hg τ)).add (hB (hf t) hψ)
  have hRs : ContDiff 𝕜 n ((τ - t) • fun y ↦ B (f' y) ((g τ - g t) y)) :=
    (hB hf' hgs).const_smul _
  rw [← iteratedFDeriv_add_apply (hB hf' (hg t)).contDiffAt (hB (hf t) hg').contDiffAt,
    ← iteratedFDeriv_const_smul_apply hQ.contDiffAt,
    ← iteratedFDeriv_sub_apply (hB (hf τ) (hg τ)).contDiffAt (hB (hf t) (hg t)).contDiffAt,
    ← iteratedFDeriv_sub_apply hP.contDiffAt hQs.contDiffAt, hsplit,
    iteratedFDeriv_add_apply hR.contDiffAt hRs.contDiffAt,
    iteratedFDeriv_add_apply (hB hφ (hg τ)).contDiffAt (hB (hf t) hψ).contDiffAt,
    iteratedFDeriv_const_smul_apply (hB hf' hgs).contDiffAt]

/-- The `i`-th derivative of `f - g - c • h` is `D^i f - D^i g - c • D^i h`; for instance, the
derivatives of a first-order Taylor remainder are the first-order Taylor remainders of the
derivatives. -/
theorem TauCeti.iteratedFDeriv_sub_sub_const_smul_apply {V : Type*} [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] {f g h : E → V} {c : 𝕜} {x : E} {i : ℕ} (hf : ContDiffAt 𝕜 i f x)
    (hg : ContDiffAt 𝕜 i g x) (hh : ContDiffAt 𝕜 i h x) :
    iteratedFDeriv 𝕜 i (f - g - c • h) x =
      iteratedFDeriv 𝕜 i f x - iteratedFDeriv 𝕜 i g x - c • iteratedFDeriv 𝕜 i h x := by
  rw [iteratedFDeriv_sub_apply (f := f - g) (g := c • h) (hf.sub hg) (hh.const_smul c),
    iteratedFDeriv_sub_apply hf hg,
    iteratedFDeriv_const_smul_apply hh]

/-- The bound behind `ContinuousLinearMap.hasDerivWithinAt_iteratedFDeriv_of_bilinear`: the
first-order Taylor remainder in `τ` of the `n`-th derivative at `x` of `B (f τ y) (g τ y)` is
controlled by the remainders and sizes of the derivatives of order at most `n` of the factors. -/
private theorem ContinuousLinearMap.norm_iteratedFDeriv_bilinear_taylor_le
    (B : X →L[𝕜] Y →L[𝕜] Z) {f : 𝕜 → E → X} {g : 𝕜 → E → Y} {f' : E → X} {g' : E → Y} {t τ : 𝕜}
    {x : E} {n : ℕ} (hf : ∀ τ, ContDiff 𝕜 n (f τ)) (hg : ∀ τ, ContDiff 𝕜 n (g τ))
    (hf' : ContDiff 𝕜 n f') (hg' : ContDiff 𝕜 n g') :
    ‖iteratedFDeriv 𝕜 n (fun y ↦ B (f τ y) (g τ y)) x -
        iteratedFDeriv 𝕜 n (fun y ↦ B (f t y) (g t y)) x -
        (τ - t) • (iteratedFDeriv 𝕜 n (fun y ↦ B (f' y) (g t y)) x +
          iteratedFDeriv 𝕜 n (fun y ↦ B (f t y) (g' y)) x)‖ ≤
      ‖B‖ * 2 ^ n *
        ((∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv 𝕜 i (f τ) x -
            iteratedFDeriv 𝕜 i (f t) x - (τ - t) • iteratedFDeriv 𝕜 i f' x‖) *
          (∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv 𝕜 i (g τ) x‖) +
        (∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv 𝕜 i (f t) x‖) *
          (∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv 𝕜 i (g τ) x -
            iteratedFDeriv 𝕜 i (g t) x - (τ - t) • iteratedFDeriv 𝕜 i g' x‖) +
        ‖τ - t‖ * ((∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv 𝕜 i f' x‖) *
          (∑ i ∈ Finset.range (n + 1),
            ‖iteratedFDeriv 𝕜 i (g τ) x - iteratedFDeriv 𝕜 i (g t) x‖))) := by
  have hle {i : ℕ} (hi : i ≤ n) : (i : ℕ∞ω) ≤ n := by exact_mod_cast hi
  -- A single term is bounded by the sum over all orders `i ≤ n`.
  have hterm (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) {i : ℕ} (hi : i ≤ n) :
      w i ≤ ∑ j ∈ Finset.range (n + 1), w j :=
    Finset.single_le_sum (fun j _ ↦ hw j) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hDf {i : ℕ} (hi : i ≤ n) := TauCeti.iteratedFDeriv_sub_sub_const_smul_apply (c := τ - t)
    (x := x) ((hf τ).of_le (hle hi)).contDiffAt ((hf t).of_le (hle hi)).contDiffAt
    (hf'.of_le (hle hi)).contDiffAt
  have hDg {i : ℕ} (hi : i ≤ n) := TauCeti.iteratedFDeriv_sub_sub_const_smul_apply (c := τ - t)
    (x := x) ((hg τ).of_le (hle hi)).contDiffAt ((hg t).of_le (hle hi)).contDiffAt
    (hg'.of_le (hle hi)).contDiffAt
  rw [B.iteratedFDeriv_bilinear_taylor_eq hf hg hf' hg']
  have h₁ := B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le isOpen_univ (Set.mem_univ x)
    (contDiff_taylor_remainder hf hf' t τ).contDiffOn (hg τ).contDiffOn
    (fun i hi ↦ by
      rw [hDf hi]
      exact hterm (fun j ↦ ‖iteratedFDeriv 𝕜 j (f τ) x - iteratedFDeriv 𝕜 j (f t) x -
        (τ - t) • iteratedFDeriv 𝕜 j f' x‖) (fun j ↦ norm_nonneg _) hi)
    (fun i hi ↦ hterm (fun j ↦ ‖iteratedFDeriv 𝕜 j (g τ) x‖) (fun j ↦ norm_nonneg _) hi)
  have h₂ := B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le isOpen_univ (Set.mem_univ x)
    (hf t).contDiffOn (contDiff_taylor_remainder hg hg' t τ).contDiffOn
    (fun i hi ↦ hterm (fun j ↦ ‖iteratedFDeriv 𝕜 j (f t) x‖) (fun j ↦ norm_nonneg _) hi)
    (fun i hi ↦ by
      rw [hDg hi]
      exact hterm (fun j ↦ ‖iteratedFDeriv 𝕜 j (g τ) x - iteratedFDeriv 𝕜 j (g t) x -
        (τ - t) • iteratedFDeriv 𝕜 j g' x‖) (fun j ↦ norm_nonneg _) hi)
  have h₃ := B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le isOpen_univ (Set.mem_univ x)
    (g := g τ - g t) hf'.contDiffOn ((hg τ).sub (hg t)).contDiffOn
    (fun i hi ↦ hterm (fun j ↦ ‖iteratedFDeriv 𝕜 j f' x‖) (fun j ↦ norm_nonneg _) hi)
    (fun i hi ↦ by
      rw [iteratedFDeriv_sub_apply ((hg τ).of_le (hle hi)).contDiffAt
        ((hg t).of_le (hle hi)).contDiffAt]
      exact hterm (fun j ↦ ‖iteratedFDeriv 𝕜 j (g τ) x - iteratedFDeriv 𝕜 j (g t) x‖)
        (fun j ↦ norm_nonneg _) hi)
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [norm_smul]
  calc _ ≤ _ := add_le_add (add_le_add h₁ h₂) (mul_le_mul_of_nonneg_left h₃ (norm_nonneg _))
    _ = _ := by ring

open Asymptotics Filter Topology in
/-- **Differentiating the Leibniz rule in a parameter.** Let `f τ` and `g τ` be `Cⁿ` maps
depending on a parameter `τ`, and suppose that at `t`, within `s`, the derivatives at `x` of order
at most `n` of `f τ` and `g τ` have derivatives in `τ` the corresponding derivatives of `f'` and
`g'`. Then the `n`-th derivative at `x` of `y ↦ B (f τ y) (g τ y)` has derivative in `τ` given by
the product rule: the sum of the `n`-th derivatives at `x` of `y ↦ B (f' y) (g t y)` and of
`y ↦ B (f t y) (g' y)`. -/
theorem ContinuousLinearMap.hasDerivWithinAt_iteratedFDeriv_of_bilinear (B : X →L[𝕜] Y →L[𝕜] Z)
    {f : 𝕜 → E → X} {g : 𝕜 → E → Y} {f' : E → X} {g' : E → Y} {s : Set 𝕜} {t : 𝕜} {x : E}
    {n : ℕ} (hf : ∀ τ, ContDiff 𝕜 n (f τ)) (hg : ∀ τ, ContDiff 𝕜 n (g τ))
    (hf' : ContDiff 𝕜 n f') (hg' : ContDiff 𝕜 n g')
    (hfd : ∀ i ≤ n, HasDerivWithinAt (fun τ ↦ iteratedFDeriv 𝕜 i (f τ) x)
      (iteratedFDeriv 𝕜 i f' x) s t)
    (hgd : ∀ i ≤ n, HasDerivWithinAt (fun τ ↦ iteratedFDeriv 𝕜 i (g τ) x)
      (iteratedFDeriv 𝕜 i g' x) s t) :
    HasDerivWithinAt (fun τ ↦ iteratedFDeriv 𝕜 n (fun y ↦ B (f τ y) (g τ y)) x)
      (iteratedFDeriv 𝕜 n (fun y ↦ B (f' y) (g t y)) x +
        iteratedFDeriv 𝕜 n (fun y ↦ B (f t y) (g' y)) x) s t := by
  have hi {i : ℕ} (h : i ∈ Finset.range (n + 1)) : i ≤ n :=
    Nat.lt_succ_iff.1 (Finset.mem_range.1 h)
  -- The remainders of the derivatives of the factors are `o(τ - t)` ...
  have ha := IsLittleO.fun_sum fun i h ↦ (hasDerivWithinAt_iff_isLittleO.1 (hfd i (hi h))).norm_left
  have hc := IsLittleO.fun_sum fun i h ↦ (hasDerivWithinAt_iff_isLittleO.1 (hgd i (hi h))).norm_left
  -- ... the derivatives of `g τ` stay bounded, and converge to those of `g t`.
  have hb : (fun τ ↦ ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv 𝕜 i (g τ) x‖) =O[𝓝[s] t]
      fun _ ↦ (1 : 𝕜) :=
    (tendsto_finsetSum _ fun i h ↦ (hgd i (hi h)).continuousWithinAt.norm).isBigO_one 𝕜
  have he : (fun τ ↦ ∑ i ∈ Finset.range (n + 1),
      ‖iteratedFDeriv 𝕜 i (g τ) x - iteratedFDeriv 𝕜 i (g t) x‖) =o[𝓝[s] t] fun _ ↦ (1 : 𝕜) :=
    (isLittleO_one_iff 𝕜).2 (by
      simpa using tendsto_finsetSum (Finset.range (n + 1)) fun i h ↦
        ((hgd i (hi h)).continuousWithinAt.sub
          (continuousWithinAt_const (b := iteratedFDeriv 𝕜 i (g t) x))).norm)
  have h₁ := ha.mul_isBigO hb
  have h₃ := (isBigO_norm_left.2 (isBigO_refl (fun τ ↦ τ - t) (𝓝[s] t))).mul_isLittleO
    (he.const_mul_left (∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv 𝕜 i f' x‖))
  simp only [mul_one] at h₁ h₃
  have hsum := ((h₁.add (hc.const_mul_left
    (∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv 𝕜 i (f t) x‖))).add h₃).const_mul_left
      (‖B‖ * 2 ^ n)
  rw [hasDerivWithinAt_iff_isLittleO]
  refine (isBigO_of_le _ fun τ ↦ ?_).trans_isLittleO hsum
  exact (B.norm_iteratedFDeriv_bilinear_taylor_le hf hg hf' hg').trans (Real.le_norm_self _)

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
