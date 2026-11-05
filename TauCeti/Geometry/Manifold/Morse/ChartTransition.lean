/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.InnerProductSpace.Indefinite

/-!
# The derivative of a transition between split Morse charts

Two partial diffeomorphisms centred at the same point and expressing the same function as
`f(x) - ‖u‖² + ‖v‖²` have a transition whose derivative at zero preserves that quadratic form.
Its negative-to-negative block is therefore invertible in finite dimension. This supplies the
linear map to which one applies polar decomposition when comparing the negative disks of
different Morse charts. No assertion about overlap of the whole negative disks is needed:
the coordinate equations are used only on an open neighbourhood of their common centre.

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

end PartialDiffeomorph
