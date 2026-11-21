/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

omit [MeasurableSpace E] [BorelSpace E] in
private theorem inner_gradient_eq_fderiv (g : E → ℝ) (x v : E) :
    ⟪v, ∇ g x⟫_ℝ = fderiv ℝ g x v := by
  rw [real_inner_comm, inner_gradient_left]

private theorem integrableOn_inner_gradient (hV : AEStronglyMeasurable V (μ.restrict Ω))
    (hC : ∀ x ∈ Ω, ‖V x‖ ≤ C) {g : E → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun x ↦ ⟪V x, ∇ g x⟫_ℝ) Ω μ := by
  have hcont : Continuous fun x ↦ ∇ g x :=
    (toDual ℝ E).symm.continuous.comp (hg.continuous_fderiv one_ne_zero)
  have hsupp : HasCompactSupport fun x ↦ ∇ g x :=
    (hgc.fderiv (𝕜 := ℝ)).comp_left (g := (toDual ℝ E).symm) (map_zero _)
  have hint : Integrable (fun x ↦ C * ‖∇ g x‖) μ :=
    (hcont.norm.integrable_of_hasCompactSupport hsupp.norm).const_mul C
  refine hint.integrableOn.mono' (hV.inner hcont.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _))

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
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb1 : ContDiff ℝ 1 b := b.contDiff
  obtain ⟨K, hK⟩ := (hb1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hφ1 : ContDiff ℝ 1 (φ : E → ℝ) := φ.contDiff.of_le (by simp)
  obtain ⟨A, hA⟩ := (hφ1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (φ.hasCompactSupport.fderiv (𝕜 := ℝ))
  obtain ⟨B, hB⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  set I := ∫ x in Ω, ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ
  have hbound (ε : ℝ) (hε : 0 < ε) :
      ‖I‖ ≤ μ.real (closedBall p (2 * ε)) * (C' * A + B * (K / ε) * C') := by
    set η : E → ℝ := fun x ↦ b (ε⁻¹ • (x - p))
    have hηs : ContDiff ℝ ∞ η :=
      b.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)
    have hη1 (x : E) (hx : x ∈ ball p ε) : η x = 1 := by
      refine b.one_of_mem_closedBall ?_
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hε.le,
        ← dist_eq_norm]
      exact (inv_mul_le_one₀ hε).2 (mem_ball.1 hx).le
    have htsupp : tsupport η ⊆ closedBall p (2 * ε) := by
      refine closure_minimal (fun x hx ↦ ?_) isClosed_closedBall
      by_contra hxb
      refine hx (b.zero_of_le_dist ?_)
      rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hε.le, ← dist_eq_norm]
      rw [mem_closedBall, not_le] at hxb
      exact (le_inv_mul_iff₀ hε).2 (by simpa [b, mul_comm] using hxb.le)
    have hηd (x : E) : ‖fderiv ℝ η x‖ ≤ K / ε := by
      have hd : HasFDerivAt η ((fderiv ℝ b (ε⁻¹ • (x - p))).comp
          (ε⁻¹ • ContinuousLinearMap.id ℝ E)) x := by
        refine (hb1.differentiable one_ne_zero _).hasFDerivAt.comp x ?_
        exact ((hasFDerivAt_id x).sub_const p).const_smul ε⁻¹
      rw [hd.fderiv, div_eq_mul_inv]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hK _) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hK 0)))
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hε.le]
      exact mul_le_of_le_one_right (inv_nonneg.2 hε.le) ContinuousLinearMap.norm_id_le
    set ψ : 𝓓(Ω, ℝ) := ⟨fun x ↦ φ x * (1 - η x),
      φ.contDiff.mul (contDiff_const.sub hηs), φ.hasCompactSupport.mul_right,
      (tsupport_mul_subset_left).trans φ.tsupport_subset⟩
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
      rw [inner_gradient_eq_fderiv, inner_gradient_eq_fderiv, hd.fderiv]
      simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
      ring
    have hpt (x : E) (hx : x ∈ Ω) : ‖η x * fderiv ℝ φ x (V x) + φ x * fderiv ℝ η x (V x)‖ ≤
        (closedBall p (2 * ε)).indicator (fun _ ↦ C' * A + B * (K / ε) * C') x := by
      by_cases hxb : x ∈ closedBall p (2 * ε)
      · rw [indicator_of_mem hxb]
        have hη0 : 0 ≤ η x := b.nonneg
        have hηle : η x ≤ 1 := b.le_one
        have h1 : ‖fderiv ℝ φ x (V x)‖ ≤ C' * A := by
          rw [mul_comm]
          exact ((fderiv ℝ φ x).le_opNorm _).trans
            (mul_le_mul (hA x) (hC' x hx) (norm_nonneg _) ((norm_nonneg _).trans (hA x)))
        have h2 : ‖fderiv ℝ η x (V x)‖ ≤ K / ε * C' :=
          ((fderiv ℝ η x).le_opNorm _).trans
            (mul_le_mul (hηd x) (hC' x hx) (norm_nonneg _) ((norm_nonneg _).trans (hηd x)))
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Real.norm_of_nonneg hη0]
          exact (mul_le_of_le_one_left (norm_nonneg _) hηle).trans h1
        · rw [norm_mul, mul_assoc]
          exact mul_le_mul (hB x) h2 (norm_nonneg _) ((norm_nonneg _).trans (hB x))
      · have hxs : x ∉ tsupport η := fun h ↦ hxb (htsupp h)
        rw [indicator_of_notMem hxb, image_eq_zero_of_notMem_tsupport hxs,
          fderiv_of_notMem_tsupport ℝ hxs]
        simp
    have hφi := integrableOn_inner_gradient (μ := μ) hV hC hφ1 φ.hasCompactSupport
    have hψi := integrableOn_inner_gradient (μ := μ) hV hC hψ1 ψ.hasCompactSupport
    have hI : I = ∫ x in Ω, (η x * fderiv ℝ φ x (V x) + φ x * fderiv ℝ η x (V x)) ∂μ := by
      rw [← sub_zero I, ← h ψ hψp, ← integral_sub hφi hψi]
      simp only [hdiff]
    have hgi : Integrable ((closedBall p (2 * ε)).indicator
        (fun _ ↦ C' * A + B * (K / ε) * C')) μ :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (measure_closedBall_lt_top (x := p)).ne)
    have hM : 0 ≤ C' * A + B * (K / ε) * C' := by
      have := (norm_nonneg _).trans (hA 0)
      have := (norm_nonneg _).trans (hB 0)
      have := (norm_nonneg _).trans (hK 0)
      positivity
    rw [hI]
    refine (norm_integral_le_of_norm_le hgi.integrableOn
      ((ae_restrict_iff' Ω.isOpen.measurableSet).2 (Eventually.of_forall hpt))).trans ?_
    refine (integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun x ↦ indicator_nonneg (fun _ _ ↦ hM) x) hgi).trans ?_
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
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
