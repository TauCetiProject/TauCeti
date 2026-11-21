/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# `C¹`-small perturbations of compositions and iterates

Let `f₁ : E → F` and `f₂ : F → G` be differentiable maps of normed spaces, and let `K` be a
compact set. If `g₁` is `C¹`-close to `f₁` on `K`, meaning that its values and its derivatives
are uniformly close to those of `f₁` there, and `g₂` is `C¹`-close to `f₂` on a neighbourhood of
`f₁ '' K`, then `g₂ ∘ g₁` is `C¹`-close to `f₂ ∘ f₁` on `K`
(`IsCompact.exists_pos_forall_differentiableAt_comp_and_norm_sub_le`). Only the derivative of
`f₁` has to be continuous on `K`, and only the value and the derivative of `f₂` have to be
continuous at the points of `f₁ '' K`: by compactness they are then uniformly continuous at these
sets, which controls the error made by evaluating `f₂` and its derivative at `g₁ x` instead of
`f₁ x`.

Iterating, if `f : E → E` is `C¹` near the first `k` points of the orbits of the points of `K`,
then every map `g` which is `C¹`-close enough to `f` on a given neighbourhood `U` of these orbit
points has its `k`-th iterate `C¹`-close to `f^[k]` on `K`
(`IsCompact.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le`). This is the step that
makes conditions on the iterates of a map, such as nondegeneracy of all its periodic points of
period at most `k` in a compact set, open in the `C¹` topology, and so it is what a Baire argument
making all periodic points of a map nondegenerate up to a period cutoff needs.

The iterate of a map which is `Cⁿ` along an orbit is `Cⁿ` at its starting point
(`TauCeti.contDiffAt_iterate`), as in the differentiable case `TauCeti.differentiableAt_iterate`.

## Main results

* `TauCeti.contDiffAt_iterate`: iterates are `Cⁿ` along `Cⁿ` orbits.
* `IsCompact.exists_pos_forall_differentiableAt_comp_and_norm_sub_le`: composition of `C¹`-close
  maps.
* `IsCompact.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le`: iterates of `C¹`-close
  maps.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 2, for the continuity of composition in the `C¹` topologies.
* R. C. Robinson, *Generic properties of conservative systems*, Amer. J. Math. 92 (1970),
  562–603, for the use of `C¹`-openness of conditions on iterates in the genericity of
  nondegenerate periodic points.
-/

public section

open ContinuousLinearMap Filter Metric Set Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace TauCeti

/-- **Iterates are `Cⁿ` along `Cⁿ` orbits.** If `f` is `Cⁿ` at the first `k` points `f^[j] x`,
`j < k`, of the orbit of `x`, then `f^[k]` is `Cⁿ` at `x`. The point `x` need not be fixed. -/
theorem contDiffAt_iterate {n : WithTop ℕ∞} {f : E → E} {x : E} :
    ∀ {k : ℕ}, (∀ j < k, ContDiffAt 𝕜 n f (f^[j] x)) → ContDiffAt 𝕜 n f^[k] x
  | 0, _ => contDiffAt_id
  | k + 1, h => by
    rw [Function.iterate_succ']
    exact (h k (by omega)).comp x (contDiffAt_iterate fun j hj ↦ h j (by omega))

end TauCeti

/-- Points within a common distance `η` of a compact set `L` lie in a given neighbourhood `U` of
`L`, and two maps continuous at the points of `L` move from there by less than `ε₁` and `ε₂`. -/
private theorem exists_pos_forall_dist_lt {X Y₁ Y₂ : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y₁] [PseudoMetricSpace Y₂] {L U : Set X} (hL : IsCompact L)
    (hU : U ∈ 𝓝ˢ L) {h₁ : X → Y₁} {h₂ : X → Y₂} (hh₁ : ∀ y ∈ L, ContinuousAt h₁ y)
    (hh₂ : ∀ y ∈ L, ContinuousAt h₂ y) {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    ∃ η > 0, ∀ y ∈ L, ∀ z, dist y z < η →
      z ∈ U ∧ dist (h₁ y) (h₁ z) < ε₁ ∧ dist (h₂ y) (h₂ z) < ε₂ := by
  obtain ⟨r, hr, hrU⟩ := (hasBasis_nhdsSet_thickening hL).mem_iff.1 hU
  obtain ⟨η₁, hη₁, H₁⟩ := mem_uniformity_dist.1 <|
    hL.uniformContinuousAt_of_continuousAt h₁ hh₁ (dist_mem_uniformity hε₁)
  obtain ⟨η₂, hη₂, H₂⟩ := mem_uniformity_dist.1 <|
    hL.uniformContinuousAt_of_continuousAt h₂ hh₂ (dist_mem_uniformity hε₂)
  refine ⟨min r (min η₁ η₂), lt_min hr (lt_min hη₁ hη₂), fun y hy z hyz ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [dist_comm] at hyz
    exact hrU (mem_thickening_iff.2 ⟨y, hy, hyz.trans_le (min_le_left _ _)⟩)
  · exact H₁ (hyz.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hy
  · exact H₂ (hyz.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hy

/-- **Compositions of `C¹`-close maps are `C¹`-close.** Let `K` be compact, let `f₁` be
differentiable on `K` with derivative continuous on `K`, and let `f₂` be differentiable at the
points of `f₁ '' K` with derivative continuous there. For every `ε > 0` and every neighbourhood `U`
of `f₁ '' K` there is `δ > 0` with the following property. If `g₁` is differentiable at the points
of `K` and `δ`-close to `f₁` there in value and derivative, and `g₂` is differentiable at the
points of `U` and `δ`-close to `f₂` there in value and derivative, then at every point of `K` the
composition `g₂ ∘ g₁` is differentiable and `ε`-close to `f₂ ∘ f₁` in value and derivative. -/
theorem IsCompact.exists_pos_forall_differentiableAt_comp_and_norm_sub_le {K : Set E}
    (hK : IsCompact K) {f₁ : E → F} {f₂ : F → G}
    (hf₁ : ∀ x ∈ K, DifferentiableAt 𝕜 f₁ x) (hf₁' : ContinuousOn (fderiv 𝕜 f₁) K)
    (hf₂ : ∀ y ∈ f₁ '' K, DifferentiableAt 𝕜 f₂ y)
    (hf₂' : ∀ y ∈ f₁ '' K, ContinuousAt (fderiv 𝕜 f₂) y)
    {ε : ℝ} (hε : 0 < ε) {U : Set F} (hU : U ∈ 𝓝ˢ (f₁ '' K)) :
    ∃ δ > 0, ∀ g₁ : E → F, ∀ g₂ : F → G,
      (∀ x ∈ K, DifferentiableAt 𝕜 g₁ x) → (∀ x ∈ K, ‖g₁ x - f₁ x‖ ≤ δ) →
      (∀ x ∈ K, ‖fderiv 𝕜 g₁ x - fderiv 𝕜 f₁ x‖ ≤ δ) →
      (∀ y ∈ U, DifferentiableAt 𝕜 g₂ y) → (∀ y ∈ U, ‖g₂ y - f₂ y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv 𝕜 g₂ y - fderiv 𝕜 f₂ y‖ ≤ δ) →
      ∀ x ∈ K, DifferentiableAt 𝕜 (g₂ ∘ g₁) x ∧ ‖(g₂ ∘ g₁) x - (f₂ ∘ f₁) x‖ ≤ ε ∧
        ‖fderiv 𝕜 (g₂ ∘ g₁) x - fderiv 𝕜 (f₂ ∘ f₁) x‖ ≤ ε := by
  have hL : IsCompact (f₁ '' K) :=
    hK.image_of_continuousOn fun x hx ↦ (hf₁ x hx).continuousAt.continuousWithinAt
  -- Bounds for the derivatives of `f₁` on `K` and of `f₂` on `f₁ '' K`, made nonnegative.
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn hf₁'
  obtain ⟨M₂, hM₂⟩ :=
    hL.exists_bound_of_continuousOn (continuousOn_of_forall_continuousAt hf₂')
  set B : ℝ := |M₁| + 1
  have hB : 0 < B := by positivity
  set τ : ℝ := ε / (2 * B)
  have hτ : 0 < τ := by positivity
  have hτB : τ * B = ε / 2 := by simp only [τ]; field_simp
  -- A distance `η` within which points near `f₁ '' K` stay in `U`, and `f₂` and its derivative
  -- move by less than `ε / 2` and `τ`.
  obtain ⟨η, hη, hηL⟩ := exists_pos_forall_dist_lt hL hU (fun y hy ↦ (hf₂ y hy).continuousAt) hf₂'
    (half_pos hε) hτ
  set A : ℝ := B + |M₂|
  set δ : ℝ := min (min 1 (ε / 2)) (min (η / 2) (ε / (2 * A)))
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδη : δ < η := (min_le_right _ _).trans_lt <| (min_le_left _ _).trans_lt (half_lt_self hη)
  have hδA : δ * A ≤ ε / 2 := by
    have : δ ≤ ε / (2 * A) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  refine ⟨δ, hδ, fun g₁ g₂ hg₁ hg₁₀ hg₁₁ hg₂ hg₂₀ hg₂₁ x hx ↦ ?_⟩
  have hy : f₁ x ∈ f₁ '' K := mem_image_of_mem f₁ hx
  obtain ⟨hz, hf₂z, hDf₂z⟩ := hηL (f₁ x) hy (g₁ x) (by
    rw [dist_comm, dist_eq_norm]; exact (hg₁₀ x hx).trans_lt hδη)
  rw [dist_comm, dist_eq_norm] at hf₂z hDf₂z
  refine ⟨(hg₂ _ hz).comp x (hg₁ x hx), ?_, ?_⟩
  · -- The value: compare `g₂ (g₁ x)` with `f₂ (g₁ x)`, and that with `f₂ (f₁ x)`.
    calc ‖(g₂ ∘ g₁) x - (f₂ ∘ f₁) x‖
        ≤ ‖g₂ (g₁ x) - f₂ (g₁ x)‖ + ‖f₂ (g₁ x) - f₂ (f₁ x)‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ δ + ε / 2 := add_le_add (hg₂₀ _ hz) hf₂z.le
      _ ≤ ε := by linarith
  · -- The derivative, by the chain rule and the three-term estimate for compositions.
    rw [fderiv_comp x (hg₂ _ hz) (hg₁ x hx), fderiv_comp x (hf₂ _ hy) (hf₁ x hx)]
    have hP : ‖fderiv 𝕜 g₂ (g₁ x) - fderiv 𝕜 f₂ (f₁ x)‖ ≤ δ + τ :=
      (norm_sub_le_norm_sub_add_norm_sub _ (fderiv 𝕜 f₂ (g₁ x)) _).trans
        (add_le_add (hg₂₁ _ hz) hDf₂z.le)
    have hQ : ‖fderiv 𝕜 g₁ x - fderiv 𝕜 f₁ x‖ ≤ δ := hg₁₁ x hx
    have hQ1 : ‖fderiv 𝕜 g₁ x - fderiv 𝕜 f₁ x‖ ≤ 1 := hQ.trans hδ1
    have hDf₁ : ‖fderiv 𝕜 f₁ x‖ ≤ |M₁| := (hM₁ x hx).trans (le_abs_self _)
    have hDf₂ : ‖fderiv 𝕜 f₂ (f₁ x)‖ ≤ |M₂| := (hM₂ _ hy).trans (le_abs_self _)
    calc _ ≤ _ := norm_comp_sub_comp_le _ _ _ _
      _ ≤ (δ + τ) * 1 + (δ + τ) * |M₁| + |M₂| * δ := by gcongr
      _ = δ * A + τ * B := by simp only [A, B]; ring
      _ ≤ ε := by linarith

/-- **Iterates of `C¹`-close maps are `C¹`-close.** Let `K` be compact and let `f` be `C¹` at the
first `k` points `f^[j] x`, `j < k`, of the orbit of every `x ∈ K`. For every `ε > 0` and every
neighbourhood `U` of these orbit points there is `δ > 0` with the following property. If `g` is
differentiable at the points of `U` and `δ`-close to `f` there in value and derivative, then at
every point of `K` the iterate `g^[k]` is differentiable and `ε`-close to `f^[k]` in value and
derivative. -/
theorem IsCompact.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le {K : Set E}
    (hK : IsCompact K) {f : E → E} {k : ℕ} (hf : ∀ j < k, ∀ x ∈ K, ContDiffAt 𝕜 1 f (f^[j] x))
    {ε : ℝ} (hε : 0 < ε) {U : Set E} (hU : U ∈ 𝓝ˢ (⋃ j < k, f^[j] '' K)) :
    ∃ δ > 0, ∀ g : E → E, (∀ y ∈ U, DifferentiableAt 𝕜 g y) → (∀ y ∈ U, ‖g y - f y‖ ≤ δ) →
      (∀ y ∈ U, ‖fderiv 𝕜 g y - fderiv 𝕜 f y‖ ≤ δ) →
      ∀ x ∈ K, DifferentiableAt 𝕜 g^[k] x ∧ ‖g^[k] x - f^[k] x‖ ≤ ε ∧
        ‖fderiv 𝕜 g^[k] x - fderiv 𝕜 f^[k] x‖ ≤ ε := by
  induction k generalizing ε with
  | zero =>
    exact ⟨1, one_pos, fun g _ _ _ x _ ↦ ⟨differentiableAt_id, by simp [hε.le], by simp [hε.le]⟩⟩
  | succ k ih =>
    -- Write `g^[k + 1] = g ∘ g^[k]` and compose the inductive hypothesis with the closeness of
    -- `g` to `f` near `f^[k] '' K`.
    have hfk (x : E) (hx : x ∈ K) : ContDiffAt 𝕜 1 f^[k] x :=
      TauCeti.contDiffAt_iterate fun j hj ↦ hf j (by omega) x hx
    have hUk : U ∈ 𝓝ˢ (f^[k] '' K) :=
      nhdsSet_mono (subset_iUnion₂ (s := fun j (_ : j < k + 1) ↦ f^[j] '' K) k (by omega)) hU
    have hU' : U ∈ 𝓝ˢ (⋃ j < k, f^[j] '' K) := nhdsSet_mono
      (iUnion₂_subset fun j hj ↦ subset_iUnion₂ (s := fun j (_ : j < k + 1) ↦ f^[j] '' K) j
        (by omega)) hU
    obtain ⟨δ₁, hδ₁, h₁⟩ := hK.exists_pos_forall_differentiableAt_comp_and_norm_sub_le
      (fun x hx ↦ (hfk x hx).differentiableAt one_ne_zero)
      (continuousOn_of_forall_continuousAt fun x hx ↦ (hfk x hx).continuousAt_fderiv one_ne_zero)
      (by rintro _ ⟨x, hx, rfl⟩; exact (hf k (by omega) x hx).differentiableAt one_ne_zero)
      (by rintro _ ⟨x, hx, rfl⟩; exact (hf k (by omega) x hx).continuousAt_fderiv one_ne_zero)
      hε hUk
    obtain ⟨δ₂, hδ₂, h₂⟩ := ih (fun j hj ↦ hf j (by omega)) hδ₁ hU'
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun g hg hg₀ hg₁ x hx ↦ ?_⟩
    have hk := h₂ g hg (fun y hy ↦ (hg₀ y hy).trans (min_le_right _ _))
      (fun y hy ↦ (hg₁ y hy).trans (min_le_right _ _))
    rw [Function.iterate_succ', Function.iterate_succ']
    exact h₁ g^[k] g (fun x hx ↦ (hk x hx).1) (fun x hx ↦ (hk x hx).2.1)
      (fun x hx ↦ (hk x hx).2.2) hg (fun y hy ↦ (hg₀ y hy).trans (min_le_left _ _))
      (fun y hy ↦ (hg₁ y hy).trans (min_le_left _ _)) x hx
