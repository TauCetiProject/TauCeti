/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.Calculus.Morse.ChartRescaling

/-!
# Transitions between split Morse charts

Two partial diffeomorphisms centred at the same point and expressing the same function as
`f(x) - ‖u‖² + ‖v‖²` have a transition whose derivative at zero preserves that quadratic form.
Its negative-to-negative block is therefore invertible in finite dimension. This supplies the
linear map to which one applies polar decomposition when comparing the negative disks of
different Morse charts. No assertion about overlap of the whole negative disks is needed:
the coordinate equations are used only on an open neighbourhood of their common centre.

With `h` the polar factor of that block, the small negative disk `u ↦ ψ₁⁻¹(u, 0)` of the second
chart is homotopic to the disk `u ↦ ψ₀⁻¹(h u, 0)` of the first chart, by a homotopy along which
`f` stays at or below `f(x) - ‖u‖²` over each point `u`
(`PartialDiffeomorph.exists_negative_disk_homotopy_polarFactor`). In particular the boundary
sphere of radius `δ` stays in the sublevel `{f ≤ f(x) - δ²}` throughout. This is the comparison
of characteristic maps of Morse cells near the critical point, before the outer annuli of the
cells are taken into account.

The product target can be obtained from normalized Euclidean Morse coordinates by splitting
negative and positive coordinates with `EuclideanSpace.sumComplEquivProd`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§2–3.
-/

public section

open Filter Set Topology
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

/-- **The small negative disks of two split Morse charts are homotopic** (Milnor, *Morse
Theory*, §3). Let `h` be the polar factor of the negative-to-negative block of the derivative at
`0` of the transition `ψ₀ ∘ ψ₁⁻¹`. For every neighbourhood `W` of the common centre `x` there are
`δ > 0` and a homotopy `G` from the negative disk `u ↦ ψ₁⁻¹(u, 0)`, `‖u‖ ≤ δ`, of `ψ₁` to the
disk `u ↦ ψ₀⁻¹(h u, 0)` of `ψ₀`, staying in `W`, with `f (G (t, u)) ≤ f x - ‖u‖²` throughout.
In particular the boundary sphere `‖u‖ = δ` stays in the sublevel `{f ≤ f x - δ²}`. -/
theorem exists_negative_disk_homotopy_polarFactor [CompleteSpace E] {W : Set M} (hW : W ∈ 𝓝 x) :
    ∃ δ > 0, ∃ G : C(unitInterval × Metric.closedBall (0 : E) δ, M),
      (∀ u, G (0, u) = ψ₁.symm ((u : E), 0)) ∧
      (∀ u, G (1, u) = ψ₀.symm (((ContinuousLinearMap.fst ℝ E F).comp
        ((fderiv ℝ (fun w ↦ ψ₀ (ψ₁.symm w)) 0).comp
          (ContinuousLinearMap.inl ℝ E F))).polarFactor u, 0)) ∧
      ∀ p, G p ∈ W ∧ f (G p) ≤ f x - ‖(p.2 : E)‖ ^ 2 := by
  obtain ⟨hreg, hzero, hQ⟩ := ψ₀.split_transition_data ψ₁ hn hx₀ hx₁ hψ₀ hψ₁ hf₀ hf₁
  have htarget₀ : (0 : E × F) ∈ ψ₀.target := hψ₀ ▸ ψ₀.map_source hx₀
  have htarget₁ : (0 : E × F) ∈ ψ₁.target := hψ₁ ▸ ψ₁.map_source hx₁
  have hinv₀ : ψ₀.toPartialEquiv.symm 0 = x := hψ₀ ▸ ψ₀.left_inv hx₀
  have hinv₁ : ψ₁.toPartialEquiv.symm 0 = x := hψ₁ ▸ ψ₁.left_inv hx₁
  have hcont₀ := ψ₀.contMDiffOn.continuousOn
  have hcont₀' := ψ₀.symm.contMDiffOn.continuousOn
  have hcont₁' := ψ₁.symm.contMDiffOn.continuousOn
  -- Near `0` the transition is defined and continuous.
  set U := ψ₁.target ∩ ψ₁.symm ⁻¹' ψ₀.source
  have hU : U ∈ 𝓝 0 := (hcont₁'.isOpen_inter_preimage ψ₁.open_target ψ₀.open_source).mem_nhds
    ⟨htarget₁, by simpa [hinv₁] using hx₀⟩
  have hc : ∀ᶠ z in 𝓝 0, ContinuousAt (fun w ↦ ψ₀ (ψ₁.symm w)) z := by
    filter_upwards [ψ₁.open_target.mem_nhds htarget₁, hU] with z hz hzU
    exact (hcont₀.continuousAt (ψ₀.open_source.mem_nhds hzU.2)).comp
      (hcont₁'.continuousAt (ψ₁.open_target.mem_nhds hz))
  -- Chart coordinates of points of `W` near `0`.
  set V := ψ₀.target ∩ ψ₀.symm ⁻¹' W
  have hV : V ∈ 𝓝 0 := inter_mem (ψ₀.open_target.mem_nhds htarget₀)
    ((hcont₀'.continuousAt (ψ₀.open_target.mem_nhds htarget₀)).preimage_mem_nhds
      (by rwa [PartialDiffeomorph.symm_toPartialEquiv, hinv₀]))
  obtain ⟨δ, hδ, hδU, H, hH₀, hH₁, hH⟩ :=
    hreg.hasFDerivAt.exists_negative_disk_homotopy_polarFactor hzero hc hQ hU hV
  refine ⟨δ, hδ, ⟨fun p ↦ ψ₀.symm (H p), hcont₀'.comp_continuous H.continuous
    fun p ↦ (hH p).1.1⟩, fun u ↦ ?_, fun u ↦ ?_, fun p ↦ ⟨(hH p).1.2, ?_⟩⟩
  · have hu : ((u : E), (0 : F)) ∈ U := hδU (by
      have h := mem_closedBall_zero_iff.1 u.2
      rw [mem_closedBall_zero_iff]
      simpa using h)
    simp only [ContinuousMap.coe_mk, hH₀]
    exact ψ₀.left_inv hu.2
  · simp only [ContinuousMap.coe_mk, hH₁]
  · have h := hf₀ _ (ψ₀.map_target (hH p).1.1)
    rw [ψ₀.right_inv (hH p).1.1] at h
    simp only [ContinuousMap.coe_mk, PartialDiffeomorph.symm_toPartialEquiv] at h ⊢
    linarith [(hH p).2]

end PartialDiffeomorph
