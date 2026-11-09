/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import TauCeti.Analysis.Calculus.Morse.NegativeDisc

/-!
# Comparing the small negative discs of two Morse charts

Let `ψ₀` and `ψ₁` be two charts of a space `M` with values in `E × F`, centred at the same point
`p`, in which a function `f` has the split normal form `f = c - ‖u‖² + ‖v‖²`. The negative disc of
radius `δ` of `ψ₁` is `w ↦ ψ₁⁻¹ (w, 0)` for `‖w‖ ≤ δ`; along it `f = c - ‖w‖²`, so its boundary
sphere lies on the level `c - δ²`. Comparing the cells attached by two Morse charts requires
deforming this disc to the negative disc of `ψ₀`, without raising its boundary above the level
`c - δ²`.

When the transition `T = ψ₀ ∘ ψ₁⁻¹` is differentiable at the origin, with derivative `A`, the
negative block `N u = (A (u, 0)).1` of `A` is invertible and has a polar decomposition `N = h P`
with `h` a linear isometry equivalence (`ContinuousLinearMap.polarFactor`). For every sufficiently
small `δ > 0` there is a homotopy `G` from `w ↦ ψ₁⁻¹ (w, 0)` to `w ↦ ψ₀⁻¹ (h w, 0)` on the disc
`‖w‖ ≤ δ` with `f (G (t, w)) ≤ c - ‖w‖²` throughout
(`OpenPartialHomeomorph.exists_negativeDisc_homotopy`). In particular the boundary sphere stays
in the sublevel `{f ≤ c - δ²}`. The homotopy is the coordinate deformation
`HasFDerivAt.exists_negativeDisc_homotopy` read through `ψ₀⁻¹`; only a neighbourhood of the
common centre is used, so the whole negative discs of the two charts need not overlap.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

open Set Metric Topology unitInterval

namespace OpenPartialHomeomorph

variable {M E F : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The small negative discs of two Morse charts are homotopic below the critical level.** Let
`ψ₀` and `ψ₁` be charts with a common centre, in which `f = c - ‖u‖² + ‖v‖²`, and whose transition
`ψ₀ ∘ ψ₁⁻¹` is differentiable at the origin. Let the linear isometry `h` be the polar factor of the
negative block of the derivative of the transition. Then for every small `δ > 0`, the negative disc
`w ↦ ψ₁⁻¹ (w, 0)` of radius `δ` is homotopic to `w ↦ ψ₀⁻¹ (h w, 0)` through maps `g` with
`f (g w) ≤ c - ‖w‖²`. -/
theorem exists_negativeDisc_homotopy (ψ₀ ψ₁ : OpenPartialHomeomorph M (E × F)) {f : M → ℝ}
    {c : ℝ} (hf₀ : ∀ y ∈ ψ₀.source, f y = c - ‖(ψ₀ y).1‖ ^ 2 + ‖(ψ₀ y).2‖ ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c - ‖(ψ₁ y).1‖ ^ 2 + ‖(ψ₁ y).2‖ ^ 2)
    (h₀ : (0 : E × F) ∈ ψ₀.target) (h₁ : (0 : E × F) ∈ ψ₁.target)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0) :
    ∃ h : E ≃ₗᵢ[ℝ] E, ⇑h = ((ContinuousLinearMap.fst ℝ E F).comp
        ((fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, ∃ G : C(I × closedBall (0 : E) δ, M),
        (∀ w, G (0, w) = ψ₁.symm ((w : E), 0)) ∧ (∀ w, G (1, w) = ψ₀.symm (h w, 0)) ∧
        ∀ t w, f (G (t, w)) ≤ c - ‖(w : E)‖ ^ 2 := by
  -- The transition is a change of coordinates preserving `Q` on the open set `U`.
  set U := ψ₁.target ∩ ψ₁.symm ⁻¹' ψ₀.source
  have hU : IsOpen U := ψ₁.isOpen_inter_preimage_symm ψ₀.open_source
  have h0U : (0 : E × F) ∈ U := ⟨h₁, by simpa [← hp] using ψ₀.map_target h₀⟩
  have hT0 : ψ₀ (ψ₁.symm 0) = 0 := by rw [← hp, ψ₀.right_inv h₀]
  have hc : ContinuousOn (fun z ↦ ψ₀ (ψ₁.symm z)) U :=
    ψ₀.continuousOn.comp (ψ₁.continuousOn_symm.mono inter_subset_left) fun _ hy ↦ hy.2
  have hQ (y : E × F) (hy : y ∈ U) :
      -‖(ψ₀ (ψ₁.symm y)).1‖ ^ 2 + ‖(ψ₀ (ψ₁.symm y)).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
    have h₀' := hf₀ _ hy.2
    have h₁' := hf₁ _ (ψ₁.map_target hy.1)
    rw [ψ₁.right_inv hy.1] at h₁'
    linarith
  obtain ⟨h, hh, δ₀, hδ₀, hH⟩ := hT.hasFDerivAt.exists_negativeDisc_homotopy hT0 hU h0U hc hQ
    (ψ₀.open_target.mem_nhds h₀)
  refine ⟨h, hh, δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  obtain ⟨hdisc, H, hH0, hH1, hHb⟩ := hH δ hδ
  -- Read the coordinate homotopy through the inverse of `ψ₀`.
  refine ⟨⟨fun p ↦ ψ₀.symm (H p),
    ψ₀.continuousOn_symm.comp_continuous H.continuous fun p ↦ (hHb p.1 p.2).1⟩,
    fun w ↦ ?_, fun w ↦ ?_, fun t w ↦ ?_⟩
  · simp only [ContinuousMap.coe_mk, hH0]
    exact ψ₀.left_inv (hdisc w w.2).2
  · simp only [ContinuousMap.coe_mk, hH1]
  · obtain ⟨hz, hq⟩ := hHb t w
    simp only [ContinuousMap.coe_mk]
    rw [hf₀ _ (ψ₀.map_target hz), ψ₀.right_inv hz]
    linarith

end OpenPartialHomeomorph
