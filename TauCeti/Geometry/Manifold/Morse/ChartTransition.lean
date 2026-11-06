/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.Calculus.Morse.NegativeDisk

/-!
# Transitions between split Morse charts

Two partial diffeomorphisms centred at the same point and expressing the same function as
`f(x) - ‖u‖² + ‖v‖²` have a transition whose derivative at zero preserves that quadratic form.
Its negative-to-negative block is therefore invertible in finite dimension. This supplies the
linear map to which one applies polar decomposition when comparing the negative disks of
different Morse charts. No assertion about overlap of the whole negative disks is needed:
the coordinate equations are used only on an open neighbourhood of their common centre.

Through the polar factor `h` of that block, a small negative disk `u ↦ ψ₁⁻¹ (u, 0)` of the second
chart deforms to the negative disk `u ↦ ψ₀⁻¹ (h u, 0)` of the first, without raising `f` above
`f(x) - ‖u‖²` (`PartialDiffeomorph.exists_small_disk_homotopy_polarFactor`). This is the
small-disk part of the comparison of the characteristic maps of the cells that the two charts
attach across the critical level `f(x)`.

The product target can be obtained from normalized Euclidean Morse coordinates by splitting
negative and positive coordinates with `EuclideanSpace.sumComplEquivProd`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§2–3.
-/

public section

open Filter Metric Set Topology
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable {V H M E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  {I : ModelWithCorners ℝ V H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {n : ℕ∞ω} (ψ₀ ψ₁ : PartialDiffeomorph I 𝓘(ℝ, E × F) M (E × F) n) (hn : 1 ≤ n)
  {f : M → ℝ} {x : M}
  (hx₀ : x ∈ ψ₀.source) (hx₁ : x ∈ ψ₁.source) (hψ₀ : ψ₀ x = 0) (hψ₁ : ψ₁ x = 0)
  (hf₀ : ∀ y ∈ ψ₀.source, f y = f x - ‖(ψ₀ y).1‖ ^ 2 + ‖(ψ₀ y).2‖ ^ 2)
  (hf₁ : ∀ y ∈ ψ₁.source, f y = f x - ‖(ψ₁ y).1‖ ^ 2 + ‖(ψ₁ y).2‖ ^ 2)

include hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁

private theorem split_transition_data :
    DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∧ ψ₀ (ψ₁.symm 0) = 0 ∧
      ∀ᶠ z in 𝓝 0,
        ‖(ψ₀ (ψ₁.symm z)).1‖ ^ 2 - ‖(ψ₀ (ψ₁.symm z)).2‖ ^ 2 =
          ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 := by
  have htarget : (0 : E × F) ∈ ψ₁.target := hψ₁ ▸ ψ₁.map_source hx₁
  have hinv : ψ₁.symm 0 = x := by
    rw [← hψ₁]
    exact ψ₁.left_inv hx₁
  have hreg₀ := (ψ₀.contMDiffOn.contMDiffAt (ψ₀.open_source.mem_nhds hx₀)).of_le hn
  have hreg₁ := (ψ₁.symm.contMDiffOn.contMDiffAt (ψ₁.open_target.mem_nhds htarget)).of_le hn
  have hreg : ContMDiffAt 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) 1
      (fun z ↦ ψ₀ (ψ₁.symm z)) 0 :=
    hreg₀.comp_of_eq hreg₁ hinv
  refine ⟨(contMDiffAt_iff_contDiffAt.mp hreg).differentiableAt one_ne_zero, hinv ▸ hψ₀, ?_⟩
  have hsource : ∀ᶠ z in 𝓝 0, ψ₁.symm z ∈ ψ₀.source :=
    hreg₁.continuousAt.preimage_mem_nhds (hinv ▸ ψ₀.open_source.mem_nhds hx₀)
  filter_upwards [hsource, ψ₁.open_target.mem_nhds htarget] with z hz₀ hz₁
  have h₀ := hf₀ _ hz₀
  have h₁ := hf₁ _ (ψ₁.map_target hz₁)
  rw [ψ₁.right_inv hz₁] at h₁
  simp only [PartialDiffeomorph.symm_toPartialEquiv] at h₀ ⊢
  linarith

/-- The derivative of a transition between two split Morse charts preserves the signed
sum of squared norms. Only a neighbourhood of the common centre is used. -/
theorem norm_sq_sub_fderiv_transition (z : E × F) :
    ‖(fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0 z).1‖ ^ 2 -
        ‖(fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0 z).2‖ ^ 2 =
      ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 := by
  obtain ⟨hreg, hzero, hQ⟩ := ψ₀.split_transition_data ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁
  exact hreg.norm_sq_sub_fderiv hzero hQ z

/-- The negative-to-negative block of the derivative of a transition between split Morse
charts is invertible. No finite-dimensionality assumption on the positive factor is needed. -/
theorem isInvertible_fst_fderiv_transition_inl [FiniteDimensional ℝ E] :
    ((ContinuousLinearMap.fst ℝ E F).comp
      ((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp
        (ContinuousLinearMap.inl ℝ E F))).IsInvertible := by
  obtain ⟨hreg, hzero, hQ⟩ := ψ₀.split_transition_data ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁
  exact hreg.isInvertible_fst_fderiv_inl hzero hQ

/-- **The small-disk comparison of two Morse charts.** Let `ψ₀` and `ψ₁` be split Morse charts
centred at `x`, in which `f = f(x) - ‖u‖² + ‖v‖²`, and let `h` be the polar factor of the
negative-to-negative block of the derivative at the origin of the transition `ψ₀ ∘ ψ₁⁻¹`. Then,
for some small `δ > 0`, the negative disk `u ↦ ψ₁⁻¹ (u, 0)`, `‖u‖ ≤ δ`, of `ψ₁` deforms to the
negative disk `u ↦ ψ₀⁻¹ (h u, 0)` of `ψ₀`, inside the source of `ψ₀`, with `f ≤ f(x) - ‖u‖²` at
every time. In particular the boundary sphere `‖u‖ = δ` stays in the sublevel
`{f ≤ f(x) - δ²}` throughout. -/
theorem exists_small_disk_homotopy_polarFactor [CompleteSpace E] :
    ∃ δ > 0, closedBall (0 : E × F) δ ⊆ ψ₁.target ∧
      ∃ G : C(unitInterval × closedBall (0 : E) δ, M),
      (∀ u, G (0, u) = ψ₁.symm (u, 0) ∧
        G (1, u) = ψ₀.symm (((ContinuousLinearMap.fst ℝ E F).comp
          ((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp
            (ContinuousLinearMap.inl ℝ E F))).polarFactor u, 0)) ∧
      ∀ t u, G (t, u) ∈ ψ₀.source ∧ f (G (t, u)) ≤ f x - ‖(u : E)‖ ^ 2 := by
  obtain ⟨hreg, hzero, -⟩ := ψ₀.split_transition_data ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁
  -- The transition is defined on the open set of chart points of `ψ₁` landing in `ψ₀.source`.
  set U := ψ₁.target ∩ ψ₁.symm ⁻¹' ψ₀.source
  have hU : IsOpen U :=
    ψ₁.symm.contMDiffOn.continuousOn.isOpen_inter_preimage ψ₁.open_target ψ₀.open_source
  have htarget : (0 : E × F) ∈ ψ₁.target := hψ₁ ▸ ψ₁.map_source hx₁
  have hinv : ψ₁.symm 0 = x := by
    rw [← hψ₁]
    exact ψ₁.left_inv hx₁
  have h0U : (0 : E × F) ∈ U := ⟨htarget, by rw [mem_preimage, hinv]; exact hx₀⟩
  have hc : ContinuousOn (fun w ↦ ψ₀ (ψ₁.symm w)) U :=
    ψ₀.contMDiffOn.continuousOn.comp (ψ₁.symm.contMDiffOn.continuousOn.mono inter_subset_left)
      fun _ hw ↦ hw.2
  -- In the coordinates of `ψ₀`, `f` is `f(x) - ‖u‖² + ‖v‖²`.
  have hf₀' {z : E × F} (hz : z ∈ ψ₀.target) :
      f (ψ₀.symm z) = f x - ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
    have h := hf₀ _ (ψ₀.map_target hz)
    rwa [ψ₀.right_inv hz] at h
  have hQ : ∀ w ∈ U, -‖(ψ₀ (ψ₁.symm w)).1‖ ^ 2 + ‖(ψ₀ (ψ₁.symm w)).2‖ ^ 2 =
      -‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 := by
    intro w hw
    have h₀ := hf₀ _ hw.2
    have h₁ := hf₁ _ (ψ₁.map_target hw.1)
    rw [ψ₁.right_inv hw.1] at h₁
    simp only [PartialDiffeomorph.symm_toPartialEquiv] at h₀ ⊢
    linarith
  have hV : ψ₀.target ∈ 𝓝 (0 : E × F) :=
    ψ₀.open_target.mem_nhds (hψ₀ ▸ ψ₀.map_source hx₀)
  obtain ⟨δ, hδ, hδU, G, hends, hP⟩ :=
    hreg.hasFDerivAt.exists_small_disk_homotopy_polarFactor hzero hU h0U hc hQ hV
  refine ⟨δ, hδ, hδU.trans inter_subset_left, ⟨fun p ↦ ψ₀.symm (G p),
    ψ₀.symm.contMDiffOn.continuousOn.comp_continuous G.continuous fun p ↦ (hP p.1 p.2).1⟩,
    fun u ↦ ?_, fun t u ↦ ?_⟩
  · have hu₀ : ((u : E), (0 : F)) ∈ U :=
      hδU (mem_closedBall_zero_iff.mpr (by simpa using mem_closedBall_zero_iff.mp u.property))
    simp only [ContinuousMap.coe_mk, (hends u).1, (hends u).2, and_true]
    exact ψ₀.left_inv hu₀.2
  · obtain ⟨hGV, hGQ⟩ := hP t u
    refine ⟨ψ₀.map_target hGV, ?_⟩
    simp only [ContinuousMap.coe_mk, hf₀' hGV]
    linarith

end PartialDiffeomorph
