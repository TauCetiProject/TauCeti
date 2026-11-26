/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Differentiability across a hyperplane

Let `ℓ` be a nonzero continuous linear functional on a real normed space `E`, so that `ker ℓ` is
a closed hyperplane separating the open half-spaces `{ℓ > 0}` and `{ℓ < 0}`. A function that is
continuous on the part of an open set `B` in the closed half-space `{ℓ ≥ 0}`, differentiable at
the points of `B` with `ℓ > 0`, and whose derivative there extends continuously to `B ∩ {ℓ ≥ 0}`,
has the extended derivative within `{ℓ ≥ 0}` at every point of `B ∩ {ℓ ≥ 0}`
(`TauCeti.hasFDerivWithinAt_setOf_nonneg_of_hasFDerivAt`). Gluing the two sides, a function that is
continuous on `B`, differentiable at the points of `B` off the hyperplane, and whose derivative
there extends continuously to all of `B`, is differentiable on `B`, with the extended derivative
(`TauCeti.hasFDerivAt_of_forall_ne_zero_hasFDerivAt`). Iterating, if the first and second
derivatives off the hyperplane extend continuously, the function is `C²` on `B`
(`TauCeti.contDiffOn_two_of_forall_ne_zero_hasFDerivAt`).

This is how functions defined piecewise on the two sides of a flat boundary, such as odd or even
reflections, are shown to be smooth across it: only the matching of the one-sided limits of the
derivatives on the hyperplane has to be checked.

The one-sided statement applies Mathlib's `hasFDerivWithinAt_closure_of_tendsto_fderiv` on the open
half-ball `B(x, r) ∩ {ℓ > 0}`, which is convex, and whose closure contains `B(x, r) ∩ {ℓ ≥ 0}`.
-/

public section

noncomputable section

open Filter Metric Set Topology

namespace TauCeti

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {ℓ : E →L[ℝ] ℝ}

/-- A point of the hyperplane `ker ℓ` in a ball lies in the closure of each of the two open
half-balls. -/
private theorem mem_closure_ball_inter_of_apply_eq_zero {x y e : E} {r : ℝ} (hy : y ∈ ball x r)
    (he : 0 < ℓ e) (hy0 : ℓ y = 0) :
    y ∈ closure (ball x r ∩ {z | 0 < ℓ z}) := by
  have hc : Tendsto (fun t : ℝ ↦ y + t • e) (𝓝[>] 0) (𝓝 y) := by
    have : Continuous fun t : ℝ ↦ y + t • e := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hc ?_
  have hball : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • e ∈ ball x r :=
    hc.eventually (isOpen_ball.mem_nhds hy)
  filter_upwards [hball, self_mem_nhdsWithin] with t ht ht0
  refine ⟨ht, ?_⟩
  simp only [mem_ofPred_eq, map_add, map_smul, hy0, smul_eq_mul, zero_add]
  exact mul_pos ht0 he

/-- **Differentiability up to a hyperplane.** Let `ℓ ≠ 0` and let `B` be open. If `f` and `f'` are
continuous on the part `B ∩ {ℓ ≥ 0}` of `B` in the closed half-space, and `f` has derivative
`f' x` at every point `x` of `B` with `ℓ x > 0`, then `f` has derivative `f' x` within the closed
half-space `{ℓ ≥ 0}` at every point `x` of `B` in it. -/
theorem hasFDerivWithinAt_setOf_nonneg_of_hasFDerivAt (hℓ : ℓ ≠ 0) {B : Set E} (hB : IsOpen B)
    {f : E → G} {f' : E → E →L[ℝ] G} (hf : ContinuousOn f (B ∩ {x | 0 ≤ ℓ x}))
    (hf' : ContinuousOn f' (B ∩ {x | 0 ≤ ℓ x})) (hd : ∀ x ∈ B, 0 < ℓ x → HasFDerivAt f (f' x) x)
    {x : E} (hx : x ∈ B) (hx0 : 0 ≤ ℓ x) : HasFDerivWithinAt f (f' x) {x | 0 ≤ ℓ x} x := by
  obtain ⟨r, hr, hrB⟩ := nhds_basis_closedBall.mem_iff.1 (hB.mem_nhds hx)
  obtain ⟨e, he⟩ : ∃ e, 0 < ℓ e := by
    obtain ⟨e, he⟩ : ∃ e, ℓ e ≠ 0 := by
      by_contra! h
      exact hℓ (ContinuousLinearMap.ext h)
    rcases he.lt_or_gt with he | he
    · exact ⟨-e, by simpa using he⟩
    · exact ⟨e, he⟩
  -- The derivative within the closure of the open half-ball `s`.
  set s := ball x r ∩ {z | 0 < ℓ z}
  have hsB : closure s ⊆ B ∩ {z | 0 ≤ ℓ z} :=
    (closure_inter_subset_inter_closure _ _).trans <| inter_subset_inter
      (closure_ball_subset_closedBall.trans hrB)
      (closure_lt_subset_le continuous_const ℓ.continuous)
  have hsd : ∀ z ∈ s, HasFDerivAt f (f' z) z := fun z hz ↦
    hd z (hsB (subset_closure hz)).1 hz.2
  have hcl : HasFDerivWithinAt f (f' x) (closure s) x := by
    refine hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun z hz ↦ (hsd z hz).differentiableAt.differentiableWithinAt)
      ((convex_ball x r).inter (convex_halfSpace_gt ℓ.isLinear 0))
      (isOpen_ball.inter (isOpen_lt continuous_const ℓ.continuous))
      (fun z hz ↦ (hf z (hsB hz)).mono (subset_closure.trans hsB)) ?_
    refine ((hf' x ⟨hx, hx0⟩).mono (subset_closure.trans hsB)).tendsto.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hsd z hz).fderiv.symm
  -- Near `x`, the closed half-space lies in the closure of `s`.
  refine (hasFDerivWithinAt_inter (ball_mem_nhds x hr)).1 (hcl.mono fun y hy ↦ ?_)
  rcases (mem_ofPred.1 hy.1).eq_or_lt with hy0 | hy0
  · exact mem_closure_ball_inter_of_apply_eq_zero hy.2 he hy0.symm
  · exact subset_closure ⟨hy.2, hy0⟩

/-- **Differentiability across a hyperplane.** Let `ℓ ≠ 0`. If `f` is continuous on an open set
`B`, has derivative `f' x` at every point `x` of `B` off the hyperplane `ℓ x = 0`, and `f'` is
continuous on `B`, then `f` has derivative `f' x` at every point of `B`. -/
theorem hasFDerivAt_of_forall_ne_zero_hasFDerivAt (hℓ : ℓ ≠ 0) {B : Set E} (hB : IsOpen B)
    {f : E → G} {f' : E → E →L[ℝ] G} (hf : ContinuousOn f B) (hf' : ContinuousOn f' B)
    (hd : ∀ x ∈ B, ℓ x ≠ 0 → HasFDerivAt f (f' x) x) {x : E} (hx : x ∈ B) :
    HasFDerivAt f (f' x) x := by
  -- The derivatives within the two closed half-spaces `{σ ℓ ≥ 0}`, `σ = ±1`, glue.
  have hside (σ : ℝ) (hσ : σ ≠ 0) (hxσ : 0 ≤ (σ • ℓ) x) :
      HasFDerivWithinAt f (f' x) {z | 0 ≤ (σ • ℓ) z} x :=
    hasFDerivWithinAt_setOf_nonneg_of_hasFDerivAt (smul_ne_zero hσ hℓ) hB
      (hf.mono inter_subset_left) (hf'.mono inter_subset_left)
      (fun z hz hz0 ↦ hd z hz (by simpa [hσ] using hz0.ne')) hx hxσ
  by_cases hx0 : ℓ x ≠ 0
  · exact hd x hx hx0
  push Not at hx0
  have hpos := hside 1 one_ne_zero (by simp [hx0])
  have hneg := hside (-1) (by norm_num) (by simp [hx0])
  refine (hpos.union hneg).hasFDerivAt (Filter.univ_mem' fun y ↦ ?_)
  rcases le_total 0 (ℓ y) with hy | hy
  · exact Or.inl (by simpa using hy)
  · exact Or.inr (by simpa using hy)

/-- **`C²` across a hyperplane.** Let `ℓ ≠ 0`. If `f` is continuous on an open set `B`, and off
the hyperplane `ℓ x = 0` it has derivative `f₁ x` and `f₁` has derivative `f₂ x`, where `f₁` and
`f₂` are continuous on all of `B`, then `f` is `C²` on `B`, with first derivative `f₁` and second
derivative `f₂` at every point of `B`. -/
theorem contDiffOn_two_of_forall_ne_zero_hasFDerivAt (hℓ : ℓ ≠ 0) {B : Set E} (hB : IsOpen B)
    {f : E → G} {f₁ : E → E →L[ℝ] G} {f₂ : E → E →L[ℝ] E →L[ℝ] G} (hf : ContinuousOn f B)
    (hf₁ : ContinuousOn f₁ B) (hf₂ : ContinuousOn f₂ B)
    (h₁ : ∀ x ∈ B, ℓ x ≠ 0 → HasFDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ B, ℓ x ≠ 0 → HasFDerivAt f₁ (f₂ x) x) :
    ContDiffOn ℝ 2 f B ∧ ∀ x ∈ B, fderiv ℝ f x = f₁ x ∧ fderiv ℝ (fderiv ℝ f) x = f₂ x := by
  have hd₁ : ∀ x ∈ B, HasFDerivAt f (f₁ x) x := fun x hx ↦
    hasFDerivAt_of_forall_ne_zero_hasFDerivAt hℓ hB hf hf₁ h₁ hx
  have hd₂ : ∀ x ∈ B, HasFDerivAt f₁ (f₂ x) x := fun x hx ↦
    hasFDerivAt_of_forall_ne_zero_hasFDerivAt hℓ hB hf₁ hf₂ h₂ hx
  have heq : EqOn (fderiv ℝ f) f₁ B := fun x hx ↦ (hd₁ x hx).fderiv
  have heq₂ : ∀ x ∈ B, fderiv ℝ (fderiv ℝ f) x = f₂ x := fun x hx ↦ by
    rw [(Filter.eventuallyEq_of_mem (hB.mem_nhds hx) heq).fderiv_eq]
    exact (hd₂ x hx).fderiv
  refine ⟨?_, fun x hx ↦ ⟨heq hx, heq₂ x hx⟩⟩
  rw [← one_add_one_eq_two, contDiffOn_succ_iff_fderiv_of_isOpen hB]
  refine ⟨fun x hx ↦ (hd₁ x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  refine ContDiffOn.congr ?_ heq
  rw [← zero_add (1 : WithTop ℕ∞), contDiffOn_succ_iff_fderiv_of_isOpen hB]
  refine ⟨fun x hx ↦ (hd₂ x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hf₂.congr fun x hx ↦ (hd₂ x hx).fderiv

end TauCeti
