/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ChartRescaling
public import TauCeti.Analysis.InnerProductSpace.Indefinite
public import TauCeti.Analysis.InnerProductSpace.Polar.Deformation
public import Mathlib.Topology.Homotopy.Basic

/-!
# Deforming a small negative disk of a Morse coordinate change to an orthogonal disk

Let `T : E × F → E × F` be a local change of coordinates fixing the origin and preserving the
split quadratic expression `Q(u, v) = -‖u‖² + ‖v‖²`, with derivative `A` at the origin. Write
`N u = (A (u, 0)).1` for the negative-to-negative block of `A`. It expands norms, so its
canonical polar factor `h = N.polarFactor` preserves norms; in finite dimension `h` is an
orthogonal transformation of `E`. This file deforms the image `u ↦ T (u, 0)` of a small
negative disk to the orthogonal disk `u ↦ (h u, 0)`, in three stages:

* the rescaling `T (s • (u, 0)) / s`, `s` running from `1` to `0`, ends at the linear disk
  `u ↦ A (u, 0)` (`HasFDerivAt.exists_small_disk_derivativeRescale`), and keeps `Q` equal to
  `-‖u‖²`;
* the positive component of `A (u, 0)` is contracted to zero, which can only decrease `Q`;
* the negative component `N u` follows the polar deformation `N.polarDeformation t u` to `h u`,
  which keeps `‖u‖` at most the norm of the image.

The two linear stages are `ContinuousLinearMap.nonempty_homotopyWith_inl_comp_polarFactor`.

Throughout, `Q` stays at most `-‖u‖²` and the image stays in a prescribed neighbourhood of the
origin (`HasFDerivAt.exists_small_disk_homotopy_polarFactor`). For a transition between two Morse
charts in which `f = f(p) + Q`, this is the small-disk part of the comparison of their
characteristic maps: the boundary sphere of the disk of radius `δ` stays in the sublevel
`{f ≤ f(p) - δ²}` during the whole deformation.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3.
-/

public section

open Filter Set Topology Metric unitInterval

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {T : E × F → E × F} {A : (E × F) →L[ℝ] E × F} {U V : Set (E × F)}

/-- **The small-disk deformation of a split-quadratic coordinate change.** Let `T` fix the
origin, be differentiable there with derivative `A`, and preserve `-‖u‖² + ‖v‖²` on an open
neighbourhood `U` of the origin. Then, for some small `δ > 0`, the negative disk
`u ↦ T (u, 0)`, `‖u‖ ≤ δ`, deforms to `u ↦ (h u, 0)`, where `h` is the polar factor of the
negative-to-negative block of `A`. At every time the deformed point lies in the prescribed
neighbourhood `V` of the origin and has `-‖·.1‖² + ‖·.2‖² ≤ -‖u‖²`. -/
theorem _root_.HasFDerivAt.exists_small_disk_homotopy_polarFactor
    (hT : HasFDerivAt T A 0) (hT0 : T 0 = 0)
    (hU : IsOpen U) (h0U : (0 : E × F) ∈ U) (hc : ContinuousOn T U)
    (hQ : ∀ y ∈ U, -‖(T y).1‖ ^ 2 + ‖(T y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    (hV : V ∈ 𝓝 0) :
    ∃ δ > 0, closedBall (0 : E × F) δ ⊆ U ∧ ∃ G : C(I × closedBall (0 : E) δ, E × F),
      (∀ u, G (0, u) = T (u, 0) ∧
        G (1, u) = (((ContinuousLinearMap.fst ℝ E F).comp
          (A.comp (ContinuousLinearMap.inl ℝ E F))).polarFactor u, 0)) ∧
      ∀ t u, G (t, u) ∈ V ∧ -‖(G (t, u)).1‖ ^ 2 + ‖(G (t, u)).2‖ ^ 2 ≤ -‖(u : E)‖ ^ 2 := by
  -- The derivative preserves the quadratic form, so its negative column straightens.
  have hL (u : E) : ‖(A (u, 0)).1‖ ^ 2 - ‖(A (u, 0)).2‖ ^ 2 = ‖u‖ ^ 2 := by
    have hQ' : ∀ᶠ z in 𝓝 (0 : E × F),
        ‖(T z).1‖ ^ 2 - ‖(T z).2‖ ^ 2 = ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 :=
      Filter.mem_of_superset (hU.mem_nhds h0U) fun z hz ↦ by
        have := hQ z hz
        simp only [mem_ofPred_eq]
        linarith
    simpa [hT.fderiv] using hT.differentiableAt.norm_sq_sub_fderiv hT0 hQ' (u, 0)
  obtain ⟨H₂⟩ := (A.comp (ContinuousLinearMap.inl ℝ E F)).nonempty_homotopyWith_inl_comp_polarFactor
    (by simpa using hL)
  -- One small disk carries the rescaling stage, with the linear bound `‖A‖ ≤ K`.
  obtain ⟨K, hK, hAK, δ, hδ, hδU, hKδV, hcont, hres⟩ :=
    hT.exists_small_disk_derivativeRescale hT0 hU h0U hc hQ hV
  refine ⟨δ, hδ, hδU, ?_⟩
  let X := closedBall (0 : E) δ
  have hδu (u : X) : ‖(u : E)‖ ≤ δ := mem_closedBall_zero_iff.mp u.property
  have hmem (u : X) : ((u : E), (0 : F)) ∈ closedBall (0 : E × F) δ :=
    mem_closedBall_zero_iff.mpr (by simpa using hδu u)
  have hKδ (u : X) : ‖A ((u : E), 0)‖ ≤ K * δ :=
    (A.le_opNorm _).trans (mul_le_mul hAK (by simpa using hδu u) (norm_nonneg _) hK.le)
  let P : C(X, E × F) → Prop := fun g ↦ ∀ u : X, g u ∈ V ∧
    -‖(g u).1‖ ^ 2 + ‖(g u).2‖ ^ 2 ≤ -‖(u : E)‖ ^ 2
  let ι : C(X, E) := ⟨Subtype.val, continuous_subtype_val⟩
  -- The rescaling stage, from `T (u, 0)` to `A (u, 0)`.
  let H₁ : ContinuousMap.HomotopyWith
      ⟨fun u : X ↦ T (u, 0), hc.comp_continuous (by fun_prop) fun u ↦ hδU (hmem u)⟩
      (((A.comp (ContinuousLinearMap.inl ℝ E F) : C(E, E × F))).comp ι) P :=
    { toFun := fun p ↦ derivativeRescale T A (σ p.1 : ℝ) ((p.2 : E), 0)
      continuous_toFun := hcont.comp_continuous
        (f := fun p : I × X ↦ (((σ p.1 : I) : ℝ), ((p.2 : E), (0 : F)))) (by fun_prop)
        fun p ↦ ⟨(σ p.1).property, hmem p.2⟩
      map_zero_left := fun u ↦ by simp [hT0]
      map_one_left := fun u ↦ by simp [ι]
      prop' := fun t u ↦ by
        obtain ⟨-, hV', hlevel⟩ := hres _ (σ t).property _ (hmem u)
        exact ⟨hV', hlevel.trans_le (by simp)⟩ }
  -- The linear stages, restricted to the disk; they stay in the ball of radius `K * δ`.
  let H₃ : ContinuousMap.HomotopyWith _ _ P :=
    { H₂.toHomotopy.compContinuousMap ι with
      prop' := fun t u ↦ by
        obtain ⟨hnorm, hlevel⟩ := H₂.prop t u
        exact ⟨hKδV (mem_closedBall_zero_iff.mpr (hnorm.trans (hKδ u))), hlevel⟩ }
  let H := H₁.trans H₃
  refine ⟨⟨H, H.continuous⟩, fun u ↦ ⟨H.apply_zero u, H.apply_one u⟩, fun t u ↦ ?_⟩
  simpa only [ContinuousMap.coe_mk, ContinuousMap.Homotopy.curry_apply,
    ContinuousMap.HomotopyWith.coe_toHomotopy]
    using H.prop t u

end TauCeti
