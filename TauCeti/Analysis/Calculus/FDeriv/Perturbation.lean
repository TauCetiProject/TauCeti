/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Topology.MetricSpace.Lebesgue
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# `C¹`-small perturbations of compositions and iterates

Let `f₁ : E → F` and `f₂ : F → G` be differentiable maps of normed spaces, and let `K` be a
compact set. If `g₁` is `C¹`-close to `f₁` on `K`, meaning that its values and its derivatives
are uniformly close to those of `f₁` there, and `g₂` is `C¹`-close to `f₂` on a neighbourhood of
`f₁ '' K`, then `g₂ ∘ g₁` is `C¹`-close to `f₂ ∘ f₁` on `K`
(`IsCompact.exists_pos_forall_differentiableAt_comp_and_norm_sub_le`). Only the derivative of
`f₁` has to be continuous on `K`, and only the value and the derivative of `f₂` have to be
continuous at the points of `f₁ '' K`: by compactness they are then uniformly continuous at these
sets (`IsCompact.exists_pos_forall_mem_and_dist_lt`), which controls the error made by evaluating
`f₂` and its derivative at `g₁ x` instead of `f₁ x`.

Iterating, if `f : E → E` is `C¹` near the first `k` points of the orbits of the points of `K`,
then every map `g` which is `C¹`-close enough to `f` on a given neighbourhood `U` of these orbit
points has its `k`-th iterate `C¹`-close to `f^[k]` on `K`
(`IsCompact.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le`). This is one ingredient
in showing that conditions on the iterates of a map, such as nondegeneracy of all its periodic
points of period at most `k` in a compact set, are open in the `C¹` topology, as a Baire argument
making all periodic points of a map nondegenerate up to a period cutoff needs. The other
ingredients, persistence of nondegenerate fixed points under `C¹`-small perturbations (applied to
`f^[k]` and `g^[k]`) and control of the periodic points of `g` in the compact set, are not proved
in this file.

The induction uses that `f^[k]` is `C¹` along the orbit (`TauCeti.contDiffAt_iterate`).

Local perturbations are compositions `f ∘ ψ` with a map `ψ` that is the identity outside a compact
set `S`. If `f` is `C¹` at the points of `S` and `ψ` is `C¹`-close enough to the identity on `S`,
then `f ∘ ψ` is `C¹`-close to `f` at every point, not only on `S`
(`IsCompact.exists_pos_forall_norm_comp_sub_le`).

Perturbations are often built as compositions `g ∘ ψ` with maps `ψ` close to the identity in `C¹`
(`TauCeti.IsNearId`). Such maps compose with an explicit bound (`TauCeti.IsNearId.comp`), and a
`C¹`-open condition on `g` holds for `g ∘ ψ` once `ψ` is close enough to the identity
(`TauCeti.eventually_forall_isNearId_comp`). The `C¹` distances of successive perturbations
`g ∘ ψ₁` and `g ∘ ψ₁ ∘ ψ₂` of `g` add up (`TauCeti.norm_comp_comp_sub_le`).

## Main results

* `IsCompact.exists_pos_forall_differentiableAt_comp_and_norm_sub_le`: composition of `C¹`-close
  maps.
* `IsCompact.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le`: iterates of `C¹`-close
  maps.
* `TauCeti.IsNearId`: closeness to the identity in `C¹`, with its composition law
  `TauCeti.IsNearId.comp`.
* `TauCeti.eventually_forall_isNearId_comp`: `C¹`-open conditions on `g` hold for `g ∘ ψ` with `ψ`
  close enough to the identity.
* `IsCompact.eventually_forall_norm_iterate_sub_le`: iterates of maps `C¹`-close everywhere.
* `IsCompact.exists_pos_forall_norm_comp_sub_le`: composition with a compactly supported
  `C¹`-small perturbation of the identity.
* `TauCeti.norm_comp_comp_sub_le`: the `C¹` distances of two successive perturbations
  `g ∘ ψ₁` and `g ∘ ψ₁ ∘ ψ₂` of `g` add up.

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
  obtain ⟨M₂, hM₂⟩ := hL.exists_bound_of_continuousOn (continuousOn_of_forall_continuousAt hf₂')
  set B : ℝ := |M₁| + 1
  have hB : 0 < B := by positivity
  set τ : ℝ := ε / (2 * B)
  have hτ : 0 < τ := by positivity
  have hτB : τ * B = ε / 2 := by simp only [τ]; field_simp
  -- Radii near `f₁ '' K` for staying in `U` and for the continuity of `f₂` and its derivative.
  obtain ⟨η₁, hη₁, H₁⟩ := hL.exists_pos_forall_mem_and_dist_lt hU
    (fun y hy ↦ (hf₂ y hy).continuousAt) (half_pos hε)
  obtain ⟨η₂, hη₂, H₂⟩ := hL.exists_pos_forall_mem_and_dist_lt hU hf₂' hτ
  set A : ℝ := B + |M₂|
  set δ : ℝ := min (min 1 (ε / 2)) (min (min η₁ η₂ / 2) (ε / (2 * A)))
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδη : δ < min η₁ η₂ :=
    (min_le_right _ _).trans_lt <| (min_le_left _ _).trans_lt (half_lt_self (lt_min hη₁ hη₂))
  have hδA : δ * A ≤ ε / 2 := by
    have : δ ≤ ε / (2 * A) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  refine ⟨δ, hδ, fun g₁ g₂ hg₁ hg₁₀ hg₁₁ hg₂ hg₂₀ hg₂₁ x hx ↦ ?_⟩
  have hy : f₁ x ∈ f₁ '' K := mem_image_of_mem f₁ hx
  have hd : dist (g₁ x) (f₁ x) < min η₁ η₂ := by rw [dist_eq_norm]; exact (hg₁₀ x hx).trans_lt hδη
  obtain ⟨hz, hf₂z⟩ := H₁ (f₁ x) hy (g₁ x) (hd.trans_le (min_le_left _ _))
  obtain ⟨-, hDf₂z⟩ := H₂ (f₁ x) hy (g₁ x) (hd.trans_le (min_le_right _ _))
  rw [dist_eq_norm] at hf₂z hDf₂z
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

/-- **Iterates of maps `C¹`-close everywhere.** Let `K` be compact and let `f` be `C¹`. For every
`ε > 0` and all small enough `δ > 0`, every differentiable map `g` that is `δ`-close to `f` in
value and derivative at every point has its iterate `g^[k]` `ε`-close to `f^[k]` on `K`. This is
the global form of `IsCompact.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le`, stated
as an eventual property so that several such conditions on `δ` can be combined. -/
theorem IsCompact.eventually_forall_norm_iterate_sub_le {K : Set E} (hK : IsCompact K) {f : E → E}
    (hf : ContDiff 𝕜 1 f) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ g : E → E, Differentiable 𝕜 g → (∀ y, ‖g y - f y‖ ≤ δ) →
      (∀ y, ‖fderiv 𝕜 g y - fderiv 𝕜 f y‖ ≤ δ) → ∀ x ∈ K, ‖g^[k] x - f^[k] x‖ ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le
    (k := k) (fun _ _ _ _ ↦ hf.contDiffAt) hε univ_mem
  filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ' g hg h₀ h₁ x hx
  exact (h g (fun y _ ↦ hg y) (fun y _ ↦ (h₀ y).trans hδ'.2.le)
    (fun y _ ↦ (h₁ y).trans hδ'.2.le) x hx).2.1

/-- **Compactly supported `C¹`-small perturbations of the identity.** Let `S` be compact and let
`f` be `C¹` at the points of `S`. For every `ε > 0` there is `δ > 0` with the following property.
If `ψ` is the identity outside `S`, differentiable at the points of `S` and `δ`-close to the
identity there in value and derivative, then `f ∘ ψ` is `ε`-close to `f` in value and derivative
at every point. -/
theorem IsCompact.exists_pos_forall_norm_comp_sub_le {S : Set E} (hS : IsCompact S) {f : E → F}
    (hf : ∀ x ∈ S, ContDiffAt 𝕜 1 f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ψ : E → E, (∀ x ∉ S, ψ x = x) → (∀ x ∈ S, DifferentiableAt 𝕜 ψ x) →
      (∀ x ∈ S, ‖ψ x - x‖ ≤ δ) → (∀ x ∈ S, ‖fderiv 𝕜 ψ x - ContinuousLinearMap.id 𝕜 E‖ ≤ δ) →
      ∀ x, ‖f (ψ x) - f x‖ ≤ ε ∧ ‖fderiv 𝕜 (f ∘ ψ) x - fderiv 𝕜 f x‖ ≤ ε := by
  -- `f` is `C¹` near `S`, so on this neighbourhood it is its own `0`-close perturbation.
  have hU : {y | ContDiffAt 𝕜 1 f y} ∈ 𝓝ˢ (id '' S) := by
    rw [image_id, mem_nhdsSet_iff_forall]
    exact fun x hx ↦ (hf x hx).eventually (by simp)
  obtain ⟨δ, hδ, h⟩ := hS.exists_pos_forall_differentiableAt_comp_and_norm_sub_le
    (fun x _ ↦ differentiableAt_id) (continuousOn_const.congr fun _ _ ↦ fderiv_id)
    (fun y hy ↦ (hf y (by simpa using hy)).differentiableAt one_ne_zero)
    (fun y hy ↦ (hf y (by simpa using hy)).continuousAt_fderiv one_ne_zero) hε hU
  refine ⟨δ, hδ, fun ψ hψS hψ hψ₀ hψ₁ x ↦ ?_⟩
  by_cases hx : x ∈ S
  · obtain ⟨-, h₀, h₁⟩ := h ψ f hψ (by simpa using hψ₀) (by simpa [fderiv_id] using hψ₁)
      (fun y hy ↦ hy.differentiableAt one_ne_zero) (by simp [hδ.le]) (by simp [hδ.le]) x hx
    exact ⟨by simpa using h₀, by simpa using h₁⟩
  · -- Outside `S`, `ψ` is the identity near `x`.
    have hev : f ∘ ψ =ᶠ[𝓝 x] f := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp [hψS y hy]
    rw [hψS x hx, hev.fderiv_eq]
    simp [hε.le]

namespace TauCeti

/-- **Closeness of successive perturbations adds up.** If `g ∘ ψ₁` is within `a` of `g` and
`g ∘ ψ₁ ∘ ψ₂` within `b` of `g ∘ ψ₁`, in value and derivative at every point, then `g ∘ ψ₁ ∘ ψ₂` is
within any `c ≥ a + b` of `g`. -/
theorem norm_comp_comp_sub_le {g : E → F} {ψ₁ ψ₂ : E → E} {a b c : ℝ}
    (h₁₀ : ∀ y, ‖g (ψ₁ y) - g y‖ ≤ a) (h₁₁ : ∀ y, ‖fderiv 𝕜 (g ∘ ψ₁) y - fderiv 𝕜 g y‖ ≤ a)
    (h₂₀ : ∀ y, ‖g (ψ₁ (ψ₂ y)) - g (ψ₁ y)‖ ≤ b)
    (h₂₁ : ∀ y, ‖fderiv 𝕜 (g ∘ ψ₁ ∘ ψ₂) y - fderiv 𝕜 (g ∘ ψ₁) y‖ ≤ b) (habc : a + b ≤ c) :
    (∀ y, ‖g (ψ₁ (ψ₂ y)) - g y‖ ≤ c) ∧
      ∀ y, ‖fderiv 𝕜 (g ∘ ψ₁ ∘ ψ₂) y - fderiv 𝕜 g y‖ ≤ c :=
  ⟨fun y ↦ (norm_sub_le_norm_sub_add_norm_sub _ (g (ψ₁ y)) _).trans
      ((add_comm a b ▸ add_le_add (h₂₀ y) (h₁₀ y)).trans habc),
    fun y ↦ (norm_sub_le_norm_sub_add_norm_sub _ (fderiv 𝕜 (g ∘ ψ₁) y) _).trans
      ((add_comm a b ▸ add_le_add (h₂₁ y) (h₁₁ y)).trans habc)⟩

/-! ### Maps close to the identity in `C¹` -/

/-- A self-map `ψ` is `η`-close to the identity in `C¹`: it is differentiable, moves no point by
more than `η`, and its derivative is within `η` of the identity everywhere. -/
structure IsNearId (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (η : ℝ) (ψ : E → E) : Prop where
  /-- A map close to the identity in `C¹` is differentiable. -/
  differentiable : Differentiable 𝕜 ψ
  /-- A map `η`-close to the identity in `C¹` moves no point by more than `η`. -/
  norm_sub_le (w : E) : ‖ψ w - w‖ ≤ η
  /-- The derivative of a map `η`-close to the identity in `C¹` is within `η` of the identity. -/
  norm_fderiv_sub_id_le (w : E) : ‖fderiv 𝕜 ψ w - ContinuousLinearMap.id 𝕜 E‖ ≤ η

/-- The identity is `η`-close to itself in `C¹` for every `η ≥ 0`. -/
theorem isNearId_id {η : ℝ} (hη : 0 ≤ η) : IsNearId 𝕜 η (id : E → E) :=
  ⟨differentiable_id, by simpa using hη, by simpa [fderiv_id] using hη⟩

/-- The bound of a map close to the identity in `C¹` is nonnegative. -/
theorem IsNearId.nonneg {η : ℝ} {ψ : E → E} (h : IsNearId 𝕜 η ψ) : 0 ≤ η :=
  (norm_nonneg _).trans (h.norm_sub_le 0)

/-- Closeness to the identity in `C¹` is monotone in the bound. -/
theorem IsNearId.mono {η η' : ℝ} {ψ : E → E} (h : IsNearId 𝕜 η ψ) (hη : η ≤ η') :
    IsNearId 𝕜 η' ψ :=
  ⟨h.differentiable, fun w ↦ (h.norm_sub_le w).trans hη,
    fun w ↦ (h.norm_fderiv_sub_id_le w).trans hη⟩

/-- The composition of a map `a`-close to the identity in `C¹` with one `b`-close to it is
`(a + b + a * b)`-close to it. -/
theorem IsNearId.comp {a b : ℝ} {Ψ ψ : E → E} (hΨ : IsNearId 𝕜 a Ψ) (hψ : IsNearId 𝕜 b ψ) :
    IsNearId 𝕜 (a + b + a * b) (Ψ ∘ ψ) := by
  have ha : 0 ≤ a := hΨ.nonneg
  have hb : 0 ≤ b := hψ.nonneg
  obtain ⟨hΨd, hΨ₀, hΨ₁⟩ := hΨ
  obtain ⟨hψd, hψ₀, hψ₁⟩ := hψ
  refine ⟨hΨd.comp hψd, fun w ↦ ?_, fun w ↦ ?_⟩
  · calc ‖Ψ (ψ w) - w‖ ≤ ‖Ψ (ψ w) - ψ w‖ + ‖ψ w - w‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ a + b := add_le_add (hΨ₀ _) (hψ₀ w)
      _ ≤ a + b + a * b := le_add_of_nonneg_right (mul_nonneg ha hb)
  · -- `DΨ ∘ Dψ - 1 = (DΨ - 1) ∘ Dψ + (Dψ - 1)`, and `‖Dψ‖ ≤ 1 + b`.
    set A := fderiv 𝕜 Ψ (ψ w)
    set B := fderiv 𝕜 ψ w
    have hB : ‖B‖ ≤ 1 + b := by
      calc ‖B‖ = ‖(B - ContinuousLinearMap.id 𝕜 E) + ContinuousLinearMap.id 𝕜 E‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖B - ContinuousLinearMap.id 𝕜 E‖ + ‖ContinuousLinearMap.id 𝕜 E‖ := norm_add_le _ _
        _ ≤ b + 1 := add_le_add (hψ₁ w) ContinuousLinearMap.norm_id_le
        _ = 1 + b := add_comm _ _
    rw [fderiv_comp w (hΨd _) (hψd w)]
    calc ‖A.comp B - ContinuousLinearMap.id 𝕜 E‖
        = ‖(A - ContinuousLinearMap.id 𝕜 E).comp B + (B - ContinuousLinearMap.id 𝕜 E)‖ := by
          congr 1
          ext v
          simp
      _ ≤ ‖A - ContinuousLinearMap.id 𝕜 E‖ * ‖B‖ + ‖B - ContinuousLinearMap.id 𝕜 E‖ :=
          (norm_add_le _ _).trans (add_le_add_left (ContinuousLinearMap.opNorm_comp_le _ _) _)
      _ ≤ a * (1 + b) + b := by gcongr; exacts [hΨ₁ _, hψ₁ w]
      _ = a + b + a * b := by ring

/-- A conclusion about the maps `C¹`-close to a `C¹` map `g` on a compact set `U` holds for the
compositions `g ∘ ψ` with every `ψ` close enough to the identity in `C¹`. -/
theorem eventually_forall_isNearId_comp {g : E → E} (hg : ContDiff 𝕜 1 g) {U : Set E}
    (hU : IsCompact U) {Q : (E → E) → Prop}
    (h : ∃ δ > 0, ∀ g' : E → E, (∀ y ∈ U, DifferentiableAt 𝕜 g' y) →
      (∀ y ∈ U, ‖g' y - g y‖ ≤ δ) → (∀ y ∈ U, ‖fderiv 𝕜 g' y - fderiv 𝕜 g y‖ ≤ δ) → Q g') :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ ψ, IsNearId 𝕜 η ψ → Q (g ∘ ψ) := by
  obtain ⟨δ, hδ, hQ⟩ := h
  obtain ⟨η₀, hη₀, hcomp⟩ := hU.exists_pos_forall_differentiableAt_comp_and_norm_sub_le
    (f₁ := id) (f₂ := g) (fun x _ ↦ differentiableAt_id)
    ((continuousOn_const (c := ContinuousLinearMap.id 𝕜 E)).congr fun _ _ ↦ fderiv_id)
    (fun y _ ↦ hg.differentiable one_ne_zero y)
    (fun y _ ↦ (hg.continuous_fderiv one_ne_zero).continuousAt) hδ univ_mem
  filter_upwards [Ioo_mem_nhdsGT hη₀] with η hη ψ ⟨hψd, hψ₀, hψ₁⟩
  have H := hcomp ψ g (fun x _ ↦ hψd x) (fun x _ ↦ (hψ₀ x).trans hη.2.le)
    (fun x _ ↦ by rw [fderiv_id]; exact (hψ₁ x).trans hη.2.le)
    (fun y _ ↦ hg.differentiable one_ne_zero y) (fun y _ ↦ by simp [hη₀.le])
    (fun y _ ↦ by simp [hη₀.le])
  exact hQ _ (fun y hy ↦ (H y hy).1) (fun y hy ↦ (H y hy).2.1) fun y hy ↦ (H y hy).2.2

end TauCeti
