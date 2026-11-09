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

The comparison can be made continuously over a compact space `P` of pairs of charts
(`OpenPartialHomeomorph.exists_negativeDisc_homotopy_family`). If on one common ball about the
origin the inverses of `ψ₀ p` are jointly continuous in `p` and the transitions are jointly
continuous with jointly continuous derivatives, then the polar factors `h p` depend continuously
on `p`, and one radius `δ` and one homotopy, continuous in `p`, serve the whole family. This is the
coordinate deformation `TauCeti.exists_negativeDisc_homotopy_family` read through `(ψ₀ p)⁻¹`.

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

/-- **The small negative discs of two compact families of Morse charts are homotopic below the
critical level, continuously in the parameter.** Let `ψ₀ p` and `ψ₁ p` be charts with a common
centre, in which `f = c - ‖u‖² + ‖v‖²`, for `p` in a compact space `P`. Suppose that on one ball
of radius `r` about the origin the inverses of `ψ₀ p` are jointly continuous in `p` and the point,
and the transitions `ψ₀ p ∘ (ψ₁ p)⁻¹` are defined, jointly continuous, and differentiable with
derivatives `D p y` jointly continuous in `p` and `y`. Then the polar factor `h p` of the negative
block of `D p 0` depends continuously on `p`, and for every small `δ > 0` a single homotopy `G`,
continuous in `p`, deforms the negative discs `w ↦ (ψ₁ p)⁻¹ (w, 0)` of radius `δ` to
`w ↦ (ψ₀ p)⁻¹ (h p w, 0)` through maps `g` with `f (g w) ≤ c - ‖w‖²`. -/
theorem exists_negativeDisc_homotopy_family {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (ψ₀ ψ₁ : P → OpenPartialHomeomorph M (E × F)) {f : M → ℝ} {c : ℝ}
    (hf₀ : ∀ p, ∀ y ∈ (ψ₀ p).source, f y = c - ‖(ψ₀ p y).1‖ ^ 2 + ‖(ψ₀ p y).2‖ ^ 2)
    (hf₁ : ∀ p, ∀ y ∈ (ψ₁ p).source, f y = c - ‖(ψ₁ p y).1‖ ^ 2 + ‖(ψ₁ p y).2‖ ^ 2)
    (hp : ∀ p, (ψ₀ p).symm 0 = (ψ₁ p).symm 0) {r : ℝ} (hr : 0 < r)
    (h₀ : ∀ p, ball (0 : E × F) r ⊆ (ψ₀ p).target)
    (h₁ : ∀ p, ball (0 : E × F) r ⊆ (ψ₁ p).target ∩ (ψ₁ p).symm ⁻¹' (ψ₀ p).source)
    (hs₀ : ContinuousOn (fun q : P × (E × F) ↦ (ψ₀ q.1).symm q.2) (univ ×ˢ ball 0 r))
    {D : P → E × F → (E × F) →L[ℝ] E × F}
    (hT : ∀ p, ∀ y ∈ ball (0 : E × F) r, HasFDerivAt (fun z ↦ ψ₀ p ((ψ₁ p).symm z)) (D p y) y)
    (hTc : ContinuousOn (fun q : P × (E × F) ↦ ψ₀ q.1 ((ψ₁ q.1).symm q.2)) (univ ×ˢ ball 0 r))
    (hD : ContinuousOn (Function.uncurry D) (univ ×ˢ ball 0 r)) :
    Continuous (fun p ↦ ((ContinuousLinearMap.fst ℝ E F).comp
        ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor) ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, ∃ G : C(P × I × closedBall (0 : E) δ, M),
        (∀ p w, G (p, 0, w) = (ψ₁ p).symm ((w : E), 0)) ∧
        (∀ p w, G (p, 1, w) = (ψ₀ p).symm (((ContinuousLinearMap.fst ℝ E F).comp
          ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor w, 0)) ∧
        ∀ p t w, f (G (p, t, w)) ≤ c - ‖(w : E)‖ ^ 2 := by
  have h0r : (0 : E × F) ∈ ball 0 r := mem_ball_self hr
  -- Each transition is a change of coordinates fixing the origin and preserving `Q` on the ball.
  have hT0 (p : P) : ψ₀ p ((ψ₁ p).symm 0) = 0 := by rw [← hp, (ψ₀ p).right_inv (h₀ p h0r)]
  have hQ (p : P) (y : E × F) (hy : y ∈ ball (0 : E × F) r) :
      -‖(ψ₀ p ((ψ₁ p).symm y)).1‖ ^ 2 + ‖(ψ₀ p ((ψ₁ p).symm y)).2‖ ^ 2 =
        -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
    have h₀' := hf₀ p _ (h₁ p hy).2
    have h₁' := hf₁ p _ ((ψ₁ p).map_target (h₁ p hy).1)
    rw [(ψ₁ p).right_inv (h₁ p hy).1] at h₁'
    linarith
  obtain ⟨hh, δ₀, hδ₀, hH⟩ := TauCeti.exists_negativeDisc_homotopy_family
    (T := fun p z ↦ ψ₀ p ((ψ₁ p).symm z)) hr hT hTc hD hT0 hQ (ball_mem_nhds 0 hr)
  refine ⟨hh, δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  obtain ⟨hdisc, H, hH0, hH1, hHb⟩ := hH δ hδ
  -- Read the coordinate homotopy through the inverses of the charts `ψ₀ p`.
  refine ⟨⟨fun q ↦ (ψ₀ q.1).symm (H q),
    hs₀.comp_continuous (f := fun q : P × I × closedBall (0 : E) δ ↦ (q.1, H q))
      (continuous_fst.prodMk H.continuous) fun q ↦ ⟨mem_univ _, (hHb q.1 q.2.1 q.2.2).1⟩⟩,
    fun p w ↦ ?_, fun p w ↦ ?_, fun p t w ↦ ?_⟩
  · simp only [ContinuousMap.coe_mk, hH0]
    exact (ψ₀ p).left_inv (h₁ p (hdisc w w.2)).2
  · simp only [ContinuousMap.coe_mk, hH1]
  · obtain ⟨hz, hq⟩ := hHb p t w
    simp only [ContinuousMap.coe_mk]
    rw [hf₀ p _ ((ψ₀ p).map_target (h₀ p hz)), (ψ₀ p).right_inv (h₀ p hz)]
    linarith

end OpenPartialHomeomorph
