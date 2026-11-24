/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.InitialTrace
import TauCeti.Topology.MetricSpace.Equicontinuity

/-!
# The rate of attainment of the initial trace

Let `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` on the slab `ℝⁿ × [t₀, t₁]`, with degenerate elliptic
Hölder coefficients bounded by `|aⁱʲ| ≤ Λ`, `|bⁱ| ≤ β` and `|c| ≤ γ`. This file shows that an
element `u` of `C_b^{2+α,1+α/2}` attains its initial trace `g = u(·, t₀)` at a rate governed only
by the modulus of continuity of `g`, by `‖P u‖_∞` and by `‖g‖_∞`: if `|P u| ≤ K`, `|g| ≤ M` and
`g` moves by at most `η` over distances at most `√s`, where `s = t - t₀`, then

`|u(x, t) - g(x)| ≤ C (η + s (M + K))`

(`TauCeti.ParabolicC2HolderSpace.exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le`), where
`C` depends only on the dimension, `t₁ - t₀`, `Λ`, `β` and `γ`. No Hölder norm of `g` or of the
coefficients enters, so for a uniformly bounded family of solutions with uniformly bounded `P u`
whose initial traces are uniformly equicontinuous, `u(·, t) → u(·, t₀)` uniformly in the family as
`t → t₀` (`TauCeti.ParabolicC2HolderSpace.exists_forall_abs_sub_lt_of_uniformEquicontinuous`).

## The argument

Shifted to start at time `0`, `u` is a bounded classical solution of the coordinate form of `P`
(`hasDerivAt_slabMk_projIcc_add` and
`deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq_euclideanParabolicOperatorL`, in
`TauCeti.Analysis.PDE.Parabolic.Holder.Operator`), so the modulus estimate for classical
solutions of `TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.InitialTrace`
(`exists_abs_sub_le_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le`)
applies to it with the nondecreasing modulus `ω(r) = η` for `r ≤ √s` and `ω(r) = η + 2 |M|`
beyond.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le`: the
  rate of attainment of the initial trace.
* `TauCeti.ParabolicC2HolderSpace.exists_forall_abs_sub_lt_of_uniformEquicontinuous`: uniform
  attainment for families with uniformly equicontinuous initial traces.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004), Chapter 4.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Hölder Spaces*, Section 8.1
  (the Cauchy problem with continuous initial data).
-/

public section

noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Real Set ParabolicSpaceTime
open scoped NNReal

/-- A bounded function that moves by at most `η` over distances at most `r₀` has the
nondecreasing modulus of continuity `ω(r) = η` for `r ≤ r₀` and `ω(r) = η + 2 |M|` beyond. -/
private theorem exists_monotoneOn_abs_sub_le_of_dist_le {X : Type*} [PseudoMetricSpace X]
    {g : X → ℝ} {M η r₀ : ℝ} (hη0 : 0 ≤ η) (hM : ∀ x, |g x| ≤ M)
    (hη : ∀ x y, dist x y ≤ r₀ → |g x - g y| ≤ η) :
    ∃ ω : ℝ → ℝ, MonotoneOn ω (Ici 0) ∧ (∀ x y, |g x - g y| ≤ ω (dist x y)) ∧ ω r₀ = η := by
  refine ⟨fun r ↦ η + if r₀ < r then 2 * |M| else 0, fun r _ r' _ hrr' ↦ ?_, fun x y ↦ ?_,
    by simp⟩
  · dsimp only
    split_ifs with h h' <;>
      first | exact absurd (h.trans_le hrr') h' | linarith [abs_nonneg M]
  · dsimp only
    split_ifs with h
    · linarith [abs_sub (g x) (g y), hM x, hM y, le_abs_self M]
    · linarith [hη x y (not_lt.1 h)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- **The rate of attainment of the initial trace.** There is a constant `C`, depending only on
the dimension, `t₁ - t₀`, `Λ`, `β` and `γ`, with the following property. Let
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` have degenerate elliptic Hölder coefficients on the slab
`ℝⁿ × [t₀, t₁]` with `|aⁱʲ| ≤ Λ`, `|bⁱ| ≤ β` and `|c| ≤ γ`, and let `u ∈ C_b^{2+α,1+α/2}` satisfy
`|P u| ≤ K` and `|u(·, t₀)| ≤ M`. If, at a point `(x, t)` of the slab with `s = t - t₀`, the
initial trace `u(·, t₀)` moves by at most `η` over distances at most `√s`, then

`|u(x, t) - u(x, t₀)| ≤ C (η + s (M + K))`.

No Hölder norm of the trace or of the coefficients enters the bound. -/
theorem exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le (Λ β γ : ℝ) :
    ∃ C ≥ 0, ∀ {α : ℝ≥0} (hα : α ≤ 1)
      {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
      {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
      {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ} {K M η : ℝ}
      (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht),
      (∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ p i j, |a i j p| ≤ Λ) → (∀ p i, |b i p| ≤ β) → (∀ p, |c p| ≤ γ) →
      (∀ p, |euclideanParabolicOperatorL hα a b c u p| ≤ K) →
      (∀ x, |u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤ M) →
      ∀ p : slab (E := EuclideanSpace ℝ ι) t₀ t₁, (∀ x y, dist x y ≤ √(slabTime p - t₀) →
        |u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩) - u (slabMk y ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤
          η) →
        |u p - u (slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤
          C * (η + (slabTime p - t₀) * (M + K)) := by
  obtain ⟨C, hC0, hC⟩ :=
    PDE.exists_abs_sub_le_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
      (ι := ι) (t₁ - t₀) Λ (Fintype.card ι * β) γ
  refine ⟨C, hC0, fun hα a b c K M η u ha hΛ hβ hγ hP hM p hη ↦ ?_⟩
  have hη0 : 0 ≤ η := by simpa using hη 0 0 (by simp)
  have hs0 : 0 ≤ (slabTime p : ℝ) - t₀ := sub_nonneg.2 (slabTime p).property.1
  rcases hs0.eq_or_lt with hs | hs
  · -- At the initial time the left side vanishes and the right side is nonnegative.
    have hp : slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩ = p := by
      conv_rhs => rw [← slabMk_space_slabTime p]
      congr 1
      exact Subtype.ext (by linarith)
    rw [hp, sub_self, abs_zero, ← hs, zero_mul, add_zero]
    positivity
  obtain ⟨ω, hωm, hω, hωs⟩ := exists_monotoneOn_abs_sub_le_of_dist_le hη0 hM hη
  have hsT : (slabTime p : ℝ) - t₀ ∈ Ioc 0 (t₁ - t₀) := ⟨hs, by linarith [(slabTime p).property.2]⟩
  have hτ : projIcc t₀ t₁ ht.le (slabTime p - t₀ + t₀) = slabTime p := by
    rw [sub_add_cancel, projIcc_val]
  have key := hC (u := fun t x ↦ u (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))))
    (a := fun t x ↦ Matrix.of fun i j ↦ a i j (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))))
    (b := fun t x ↦
      ∑ i, b i (slabMk x (projIcc t₀ t₁ ht.le (t + t₀))) • EuclideanSpace.single i 1)
    (c := fun t x ↦ c (slabMk x (projIcc t₀ t₁ ht.le (t + t₀)))) (ω := ω) (M := M) (F := K)
    (fun t _ x ξ ↦ ha _ ξ) (fun t _ x i j ↦ hΛ _ i j)
    (fun t _ x ↦ (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ by
      simpa [norm_smul] using hβ _ i).trans (by simp)))
    (fun t _ x ↦ hγ _)
    ((valueL u).continuous.comp (continuous_slabMk.comp (continuous_snd.prodMk
      ((continuous_projIcc (h := ht.le)).comp (continuous_fst.add continuous_const))))).continuousOn
    ((Metric.isBounded_iff_subset_closedBall 0).2 ⟨‖valueL u‖, by
      rintro _ ⟨z, -, rfl⟩
      simpa [Function.uncurry_def] using (valueL u).norm_coe_le_norm _⟩)
    (fun t _ x ↦ (u.contDiff_spatialSlice _).contDiffAt)
    (fun t h x ↦ (hasDerivAt_slabMk_projIcc_add u x h).differentiableAt)
    (fun t h x ↦ by
      rw [deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq_euclideanParabolicOperatorL hα u
        h x]
      exact hP _)
    (fun x ↦ by simpa [projIcc_left] using hM x) hωm
    (fun x y ↦ by simpa [projIcc_left] using hω x y)
    hsT (p : ParabolicSpaceTime _).space
  simpa only [hτ, slabMk_space_slabTime, zero_add, projIcc_left, hωs] using key

/-- **Uniform attainment for equicontinuous families.** Let `P` have degenerate elliptic Hölder
coefficients on the slab `ℝⁿ × [t₀, t₁]`, and let `(u_k)` be a family in `C_b^{2+α,1+α/2}` with
`|P u_k| ≤ K` and `|u_k(·, t₀)| ≤ M`, whose initial traces `u_k(·, t₀)` are uniformly
equicontinuous. Then `u_k(x, t) → u_k(x, t₀)` as `t → t₀`, uniformly in `k` and `x`. -/
theorem exists_forall_abs_sub_lt_of_uniformEquicontinuous {α : ℝ≥0} (hα : α ≤ 1)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {κ : Type*} {K M : ℝ} (u : κ → ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hP : ∀ k p, |euclideanParabolicOperatorL hα a b c (u k) p| ≤ K)
    (hM : ∀ k x, |u k (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤ M)
    (hu : UniformEquicontinuous fun k x ↦ u k (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ k (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁), (slabTime p : ℝ) - t₀ < δ →
      |u k p - u k (slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩)| < ε := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le (ι := ι)
    (ht := ht) (∑ i, ∑ j, ‖a i j‖) (∑ i, ‖b i‖) ‖c‖
  exact hu.exists_forall_lt_of_le_mul_add_mul (fun p ↦ sub_nonneg.2 (slabTime p).property.1)
    hC0 (fun η k p ↦ hC hα (u k) ha (HolderSpace.abs_apply_le_sum_sum_norm a)
      (HolderSpace.abs_apply_le_sum_norm b) (HolderSpace.abs_apply_le_norm c) (hP k) (hM k) p) hε

end TauCeti.ParabolicC2HolderSpace
