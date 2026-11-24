/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# A point is removable for bounded weakly divergence-free fields

Let `Ω` be an open subset of a real inner product space `E` of dimension `n ≥ 2`, let `p` be a
point and let `V` be an a.e. strongly measurable vector field on `Ω` with `|V| ≤ C` almost
everywhere. If `∫_Ω ⟨V, ∇ψ⟩ = 0` for every test function `ψ` whose support avoids `p`, then the
same holds for every test function on `Ω`.

The proof cuts off near `p`. For a smooth `η_ε` equal to `1` on `B_ε(p)`, supported in
`B_{2ε}(p)`, with `|∇η_ε| ≤ K/ε`, the test function `φ (1 - η_ε)` avoids `p`, so
`∫_Ω ⟨V, ∇φ⟩ = ∫_Ω ⟨V, ∇(η_ε φ)⟩`, whose absolute value is at most
`C (sup |∇φ| + sup |φ| · K/ε) |B_{2ε}| = O(ε^(n-1))`, which tends to `0` as `ε → 0`.

## Main results

* `TauCeti.setIntegral_inner_gradient_eq_zero_of_forall_notMem_tsupport`: the removability.

## References

Adapted from Giada Franz's formalization in the `ForTauCeti` module.

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
    (hC : ∀ᵐ x ∂μ.restrict Ω, ‖V x‖ ≤ C) {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    IntegrableOn (fun x ↦ ⟪V x, ∇ g x⟫_ℝ) Ω μ := by
  exact (innerSL ℝ).integrable_of_bilin_of_bdd_left C hV hC
    ((hg.continuous_gradient one_ne_zero).integrable_of_hasCompactSupport hgc.gradient).integrableOn

private theorem setIntegral_inner_gradient_eq_cutoff
    (p : E) (hV : AEStronglyMeasurable V (μ.restrict Ω)) (hC : ∀ᵐ x ∂μ.restrict Ω, ‖V x‖ ≤ C)
    (h : ∀ ψ : 𝓓(Ω, ℝ), p ∉ tsupport (ψ : E → ℝ) →
      ∫ x in Ω, ⟪V x, ∇ (ψ : E → ℝ) x⟫_ℝ ∂μ = 0)
    (φ : 𝓓(Ω, ℝ)) {ε : ℝ} (hε : 0 < ε) (η : E → ℝ) (hηs : ContDiff ℝ ∞ η)
    (hη1 : ∀ x ∈ closedBall p ε, η x = 1) :
    (∫ x in Ω, ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ) =
      ∫ x in Ω, (η x * fderiv ℝ φ x (V x) + φ x * fderiv ℝ η x (V x)) ∂μ := by
  have hφ1 : ContDiff ℝ 1 (φ : E → ℝ) := φ.contDiff.of_le (by simp)
  let ψ : 𝓓(Ω, ℝ) :=
    TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ)
      ((contDiff_const (c := (1 : ℝ))).sub hηs) φ
  have hψ : (ψ : E → ℝ) = fun x ↦ φ x * (1 - η x) := by
    simp only [ψ, TestFunction.bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']
  have hψp : p ∉ tsupport (ψ : E → ℝ) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [ball_mem_nhds p hε] with x hx
    simp only [hψ, hη1 x (ball_subset_closedBall hx), sub_self, mul_zero, Pi.zero_apply]
  have hdiff (x : E) : ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ - ⟪V x, ∇ (ψ : E → ℝ) x⟫_ℝ =
      η x * fderiv ℝ φ x (V x) + φ x * fderiv ℝ η x (V x) := by
    simp only [inner_gradient_right, RCLike.conj_to_real, hψ,
      fderiv_fun_mul (hφ1.differentiable one_ne_zero x)
        ((contDiff_const.sub hηs).differentiable (by simp) x), fderiv_const_sub,
      add_apply, smul_apply, neg_apply, smul_eq_mul]
    ring
  have hφi := integrableOn_inner_gradient (μ := μ) hV hC hφ1 φ.hasCompactSupport
  have hψi := integrableOn_inner_gradient (μ := μ) hV hC
    (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport
  rw [← sub_zero (∫ x in Ω, ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ),
    ← h ψ hψp, ← integral_sub hφi hψi]
  simp only [hdiff]

private theorem norm_setIntegral_inner_gradient_le_of_cutoff
    (p : E) (hV : AEStronglyMeasurable V (μ.restrict Ω)) (hC : ∀ᵐ x ∂μ.restrict Ω, ‖V x‖ ≤ C)
    (hC0 : 0 ≤ C)
    (h : ∀ ψ : 𝓓(Ω, ℝ), p ∉ tsupport (ψ : E → ℝ) →
      ∫ x in Ω, ⟪V x, ∇ (ψ : E → ℝ) x⟫_ℝ ∂μ = 0)
    (φ : 𝓓(Ω, ℝ)) {A B K ε : ℝ}
    (hA : ∀ x, ‖fderiv ℝ φ x‖ ≤ A) (hB : ∀ x, ‖φ x‖ ≤ B) (hK : 0 ≤ K) (hε : 0 < ε)
    (η : E → ℝ) (hηs : ContDiff ℝ ∞ η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hη1 : ∀ x ∈ closedBall p ε, η x = 1) (hη0 : ∀ x, 2 * ε < dist x p → η x = 0)
    (hηbound : ∀ x, ‖fderiv ℝ η x‖ ≤ K / ε)
    (hηderiv0 : ∀ x, 2 * ε < dist x p → fderiv ℝ η x = 0) :
    ‖∫ x in Ω, ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ‖ ≤
      μ.real (closedBall p (2 * ε)) * (C * A + B * (K / ε) * C) := by
  have hpt (x : E) (hx : ‖V x‖ ≤ C) : ‖η x * fderiv ℝ φ x (V x) + φ x * fderiv ℝ η x (V x)‖ ≤
      C * A + B * (K / ε) * C := by
    obtain ⟨hηnonneg, hηle⟩ := hη01 x
    simpa only [smul_eq_mul, one_mul, mul_comm A C] using
      (fderiv ℝ φ x).norm_smul_apply_add_smul_apply_le (fderiv ℝ η x)
        (a := η x) (b := φ x) (v := V x) (w := V x) (A := 1)
        (by simpa only [Real.norm_of_nonneg hηnonneg] using hηle)
        (hB x) (hA x) (hηbound x) hx hx
  -- The error vanishes outside the cutoff support, so only the ball of radius 2ε contributes.
  rw [setIntegral_inner_gradient_eq_cutoff p hV hC h φ hε η hηs hη1,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet
    (s := (Ω : Set E) ∩ closedBall p (2 * ε)) inter_subset_left]
  · have hM : 0 ≤ C * A + B * (K / ε) * C := by
      have := (norm_nonneg _).trans (hA 0)
      have := (norm_nonneg _).trans (hB 0)
      positivity
    refine (norm_setIntegral_le_of_norm_le_const_ae
      (measure_lt_top_of_subset inter_subset_right measure_closedBall_lt_top.ne)
      ((ae_restrict_of_ae_restrict_of_subset inter_subset_left hC).mono hpt)).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right
      (measureReal_mono inter_subset_right measure_closedBall_lt_top.ne) hM
  · intro x hx
    have hxball : x ∉ closedBall p (2 * ε) := fun hxball ↦ hx.2 ⟨hx.1, hxball⟩
    have hxdist : 2 * ε < dist x p := lt_of_not_ge (mt Metric.mem_closedBall.2 hxball)
    rw [hη0 x hxdist, hηderiv0 x hxdist]
    simp

/-- **A point is removable for bounded weakly divergence-free fields** in dimension at least
`2`: if `V` is bounded almost everywhere on `Ω` and `∫_Ω ⟨V, ∇ψ⟩ = 0` for every test function `ψ`
whose support avoids `p`, then `∫_Ω ⟨V, ∇φ⟩ = 0` for every test function `φ` on `Ω`. -/
theorem setIntegral_inner_gradient_eq_zero_of_forall_notMem_tsupport
    (hE : 2 ≤ Module.finrank ℝ E) (p : E) (hV : AEStronglyMeasurable V (μ.restrict Ω))
    (hC : ∀ᵐ x ∂μ.restrict Ω, ‖V x‖ ≤ C)
    (h : ∀ ψ : 𝓓(Ω, ℝ), p ∉ tsupport (ψ : E → ℝ) →
      ∫ x in Ω, ⟪V x, ∇ (ψ : E → ℝ) x⟫_ℝ ∂μ = 0)
    (φ : 𝓓(Ω, ℝ)) : ∫ x in Ω, ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ = 0 := by
  set C' := max C 0
  have hC' : ∀ᵐ x ∂μ.restrict Ω, ‖V x‖ ≤ C' :=
    hC.mono fun _ hx ↦ hx.trans (le_max_left _ _)
  obtain ⟨K, hK, hcut⟩ := exists_cutoff_fderiv_bound (E := E)
  have hφ1 : ContDiff ℝ 1 (φ : E → ℝ) := φ.contDiff.of_le (by simp)
  obtain ⟨A, hA⟩ := (hφ1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (φ.hasCompactSupport.fderiv (𝕜 := ℝ))
  obtain ⟨B, hB⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  set I := ∫ x in Ω, ⟪V x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ
  -- Cut off φ near p and bound the error using the uniform bounds on V, φ and its derivative.
  have hbound (ε : ℝ) (hε : 0 < ε) :
      ‖I‖ ≤ μ.real (closedBall p (2 * ε)) * (C' * A + B * (K / ε) * C') := by
    obtain ⟨η, η', hηs, hη01, hη1, hη0, hηderiv, hηbound, -, hηderiv0⟩ := hcut p ε hε
    exact norm_setIntegral_inner_gradient_le_of_cutoff p hV hC' (le_max_right _ _) h φ
      hA hB hK hε η (hηs ⊤) hη01 hη1 hη0
      (fun x ↦ by simpa only [(hηderiv x).fderiv, div_eq_mul_inv] using hηbound x)
      (fun x hx ↦ by rw [(hηderiv x).fderiv, hηderiv0 x hx])
  -- Ball volume scales as ε^(m + 2); the cutoff derivative costs 1/ε, so the error tends to zero.
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
