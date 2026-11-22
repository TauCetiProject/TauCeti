/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import TauCeti.Analysis.Calculus.Gradient

/-!
# A point is removable for bounded weakly divergence-free fields

Let `Ω` be an open subset of a real inner product space `E` of dimension `n ≥ 2`, let `p` be a
point and let `V` be a measurable vector field on `Ω` with `|V| ≤ C`. If
`∫_Ω ⟨V, ∇ψ⟩ = 0` for every test function `ψ` whose support avoids `p`, then the same holds for
every test function on `Ω`.

The proof cuts off near `p`. For a smooth `η_ε` equal to `1` on `B_ε(p)`, supported in
`B_{2ε}(p)`, with `|∇η_ε| ≤ K/ε`, the test function `φ (1 - η_ε)` avoids `p`, so
`∫_Ω ⟨V, ∇φ⟩ = ∫_Ω ⟨V, ∇(η_ε φ)⟩`, whose absolute value is at most
`C (sup |∇φ| + sup |φ| · K/ε) |B_{2ε}| = O(ε^(n-1))`, which tends to `0` as `ε → 0`.

## Main results

* `TauCeti.setIntegral_inner_gradient_eq_zero_of_forall_notMem_tsupport`: the removability.

## References

* O. Chodosh, *Introduction to minimal surfaces*, proof of Theorem 32.5.
-/

public section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace Filter Topology
open scoped ContDiff Distributions Gradient InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {V : E → E} {C : ℝ}

private theorem integrableOn_inner_gradient (hV : AEStronglyMeasurable V (μ.restrict Ω))
    (hC : ∀ x ∈ Ω, ‖V x‖ ≤ C) {g : E → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun x ↦ ⟪V x, ∇ g x⟫_ℝ) Ω μ := by
  refine (innerSL ℝ).integrable_of_bilin_of_bdd_left C hV ?_
    ((hg.continuous_gradient one_ne_zero).integrable_of_hasCompactSupport hgc.gradient).integrableOn
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Eventually.of_forall hC)

/-- **A point is removable for bounded weakly divergence-free fields** in dimension at least
`2`: if `V` is bounded on `Ω` and `∫_Ω ⟨V, ∇ψ⟩ = 0` for every test function `ψ` whose support
avoids `p`, then `∫_Ω ⟨V, ∇φ⟩ = 0` for every test function `φ` on `Ω`. -/
theorem setIntegral_inner_gradient_eq_zero_of_forall_notMem_tsupport
    (hE : 2 ≤ Module.finrank ℝ E) (p : E) (hV : AEStronglyMeasurable V (μ.restrict Ω))
    (hC : ∀ x ∈ Ω, ‖V x‖ ≤ C)
    (h : ∀ ψ : 𝓓(Ω, ℝ), p ∉ tsupport (ψ : E → ℝ) →
      ∫ x in Ω, ⟪V x, ∇ (ψ : E → ℝ) x⟫_ℝ ∂μ = 0)
    (φ : 𝓓(Ω, ℝ)) : ∫ x in Ω, ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ = 0 := by
  set C' := max C 0
  have hC' (x : E) (hx : x ∈ Ω) : ‖V x‖ ≤ C' := (hC x hx).trans (le_max_left _ _)
  obtain ⟨K, hK, hcut⟩ := exists_cutoff_fderiv_bound (E := E)
  have hφ1 : ContDiff ℝ 1 (φ : E → ℝ) := φ.contDiff.of_le (by simp)
  obtain ⟨A, hA⟩ := (hφ1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (φ.hasCompactSupport.fderiv (𝕜 := ℝ))
  obtain ⟨B, hB⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  set I := ∫ x in Ω, ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ
  have hbound (ε : ℝ) (hε : 0 < ε) :
      ‖I‖ ≤ μ.real (closedBall p (2 * ε)) * (C' * A + B * (K / ε) * C') := by
    obtain ⟨η, η', hηs', hη01, hη1', hη0, hηderiv, hηbound⟩ := hcut p ε hε
    have hηs : ContDiff ℝ ∞ η := hηs' ⊤
    have hη1 (x : E) (hx : x ∈ ball p ε) : η x = 1 :=
      hη1' x (ball_subset_closedBall hx)
    have htsupp : tsupport η ⊆ closedBall p (2 * ε) := by
      refine closure_minimal (fun x hx ↦ ?_) isClosed_closedBall
      by_contra hxb
      exact hx (hη0 x (not_le.mp hxb))
    have hηd (x : E) : ‖fderiv ℝ η x‖ ≤ K / ε := by
      simpa only [(hηderiv x).fderiv, div_eq_mul_inv] using hηbound x
    let ψ : 𝓓(Ω, ℝ) :=
      TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ)
        ((contDiff_const (c := (1 : ℝ))).sub hηs) φ
    have hψp : p ∉ tsupport (ψ : E → ℝ) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [ball_mem_nhds p hε] with x hx
      simp [ψ, hη1 x hx]
    have hψ1 : ContDiff ℝ 1 (ψ : E → ℝ) := ψ.contDiff.of_le (by simp)
    have hdiff (x : E) : ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ - ⟪V x, ∇ (ψ : E → ℝ) x⟫_ℝ =
        η x * fderiv ℝ φ x (V x) + φ x * fderiv ℝ η x (V x) := by
      have hφd := (hφ1.differentiable one_ne_zero x).hasFDerivAt
      have hηd' := ((hηs.differentiable (by simp)) x).hasFDerivAt
      have hd : HasFDerivAt (ψ : E → ℝ)
          ((φ x) • (-fderiv ℝ η x) + (1 - η x) • fderiv ℝ φ x) x :=
        hφd.mul (hηd'.const_sub 1)
      simp only [inner_gradient_right, RCLike.conj_to_real, hd.fderiv]
      simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
      ring
    have hpt (x : E) (hx : x ∈ Ω) : ‖η x * fderiv ℝ φ x (V x) + φ x * fderiv ℝ η x (V x)‖ ≤
        C' * A + B * (K / ε) * C' := by
      obtain ⟨hηnonneg, hηle⟩ := hη01 x
      have h1 : ‖fderiv ℝ φ x (V x)‖ ≤ C' * A := by
        rw [mul_comm]
        exact ((fderiv ℝ φ x).le_opNorm _).trans
          (mul_le_mul (hA x) (hC' x hx) (norm_nonneg _) ((norm_nonneg _).trans (hA x)))
      have h2 : ‖fderiv ℝ η x (V x)‖ ≤ K / ε * C' :=
        ((fderiv ℝ η x).le_opNorm _).trans
          (mul_le_mul (hηd x) (hC' x hx) (norm_nonneg _) ((norm_nonneg _).trans (hηd x)))
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Real.norm_of_nonneg hηnonneg]
        exact (mul_le_of_le_one_left (norm_nonneg _) hηle).trans h1
      · rw [norm_mul, mul_assoc]
        exact mul_le_mul (hB x) h2 (norm_nonneg _) ((norm_nonneg _).trans (hB x))
    have hφi := integrableOn_inner_gradient (μ := μ) hV hC hφ1 φ.hasCompactSupport
    have hψi := integrableOn_inner_gradient (μ := μ) hV hC hψ1 ψ.hasCompactSupport
    have hI : I = ∫ x in Ω, (η x * fderiv ℝ φ x (V x) + φ x * fderiv ℝ η x (V x)) ∂μ := by
      rw [← sub_zero I, ← h ψ hψp, ← integral_sub hφi hψi]
      simp only [hdiff]
    rw [hI, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet
      (s := (Ω : Set E) ∩ closedBall p (2 * ε)) inter_subset_left]
    · have hM : 0 ≤ C' * A + B * (K / ε) * C' := by
        have := (norm_nonneg _).trans (hA 0)
        have := (norm_nonneg _).trans (hB 0)
        positivity
      refine (norm_setIntegral_le_of_norm_le_const
        (measure_lt_top_of_subset inter_subset_right measure_closedBall_lt_top.ne)
        (fun x hx ↦ hpt x hx.1)).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (measureReal_mono inter_subset_right measure_closedBall_lt_top.ne) hM
    · intro x hx
      have hxs : x ∉ tsupport η := fun hs ↦ hx.2 ⟨hx.1, htsupp hs⟩
      rw [image_eq_zero_of_notMem_tsupport hxs, fderiv_of_notMem_tsupport ℝ hxs]
      simp
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank ℝ E = m + 2 := ⟨_, (Nat.sub_add_cancel hE).symm⟩
  set c := μ.real (ball (0 : E) 1)
  set g : ℝ → ℝ := fun ε ↦ c * 2 ^ (m + 2) * ε ^ (m + 1) * (C' * A * ε + B * K * C')
  have hg : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have : Continuous g := by fun_prop
    simpa [g] using this.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖I‖ ≤ g ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine (hbound ε hε).trans (le_of_eq ?_)
    have hε' : 0 < ε := hε
    rw [Measure.addHaar_real_closedBall μ p (by positivity), hm]
    have hε0 : ε ≠ 0 := hε'.ne'
    simp only [g, c]
    field_simp
    ring
  exact norm_le_zero_iff.1 (ge_of_tendsto hg hle)

end TauCeti
