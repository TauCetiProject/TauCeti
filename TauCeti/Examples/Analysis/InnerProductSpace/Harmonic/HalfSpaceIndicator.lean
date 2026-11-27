/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl

/-!
# The indicator of a half-space is not weakly harmonic

Weyl's lemma (`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq`) says that a locally
integrable function whose distributional Laplacian vanishes agrees almost everywhere with a
harmonic function. This file checks that the hypothesis has content: local integrability alone
does not make a function weakly harmonic, even one that is locally constant off a hyperplane.

Let `v ≠ 0` and let `u = 1_{⟪v, x⟫ > 0}` be the indicator of an open half-space. It is locally
integrable, and it is constant, hence harmonic, on each side of the hyperplane `⟪v, x⟫ = 0`. On
every open set `Ω` meeting that hyperplane it is not weakly harmonic
(`TauCeti.Examples.HalfSpaceIndicator.not_weaklyHarmonicOn_indicator`). Concretely, for
`v = e₁` the distributional Laplacian of `u` is `φ ↦ ∫ u Δφ = -∫_{x₁ = 0} ∂₁φ`, a derivative of
the surface measure on the hyperplane, which is nonzero for suitable test functions `φ`.

The proof goes through Weyl's lemma instead of this formula. If `u` were weakly harmonic on `Ω`,
it would agree almost everywhere on `Ω` with a harmonic function `h`. A continuous function
agreeing almost everywhere with a constant on an open set is equal to it there, so `h = 1` on the
part of `Ω` with `⟪v, x⟫ > 0` and `h = 0` on the part with `⟪v, x⟫ < 0`. Approaching a point
`x₀ ∈ Ω` of the hyperplane along the line `x₀ + t v` from both sides, the continuity of `h` at
`x₀` gives `h x₀ = 1` and `h x₀ = 0`.

The case of the whole Euclidean space `ℝⁿ⁺¹` with `v = e₁` is
`locallyIntegrable_and_not_weaklyHarmonicOn_indicator_euclideanSpace`, in the namespace
`TauCeti.Examples.HalfSpaceIndicator`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.2.3 (harmonic functions and the
  mean-value property).
* H. Weyl, *The method of orthogonal projection in potential theory*, Duke Math. J. **7** (1940),
  411–444.
-/

public section

namespace TauCeti.Examples.HalfSpaceIndicator

open Filter InnerProductSpace MeasureTheory Set Topology TopologicalSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The indicator of a half-space is not weakly harmonic.** Let `v ≠ 0`, and let the open set `Ω`
contain a point `x₀` of the hyperplane `⟪v, x⟫ = 0`. Then the indicator of the half-space
`⟪v, x⟫ > 0`, which is locally integrable and locally constant off the hyperplane, is not weakly
harmonic on `Ω`. -/
theorem not_weaklyHarmonicOn_indicator {v : E} (hv : v ≠ 0) {Ω : Opens E} {x₀ : E}
    (hx₀ : x₀ ∈ Ω) (hvx₀ : ⟪v, x₀⟫ = 0) :
    ¬WeaklyHarmonicOn μ Ω ({x | 0 < ⟪v, x⟫}.indicator (1 : E → ℝ)) := by
  intro hw
  obtain ⟨h, hh, hae⟩ := hw.exists_harmonicOnNhd_ae_eq
  have hcont : ContinuousOn h Ω := fun x hx ↦ (hh x hx).1.continuousAt.continuousWithinAt
  -- On an open part `Ω ∩ S` of `Ω` where the indicator is the constant `c`, so is `h`.
  have hconst (S : Set E) (c : ℝ) (hS : IsOpen S)
      (hc : ∀ x ∈ S, {x | 0 < ⟪v, x⟫}.indicator (1 : E → ℝ) x = c) :
      EqOn (fun _ ↦ c) h (Ω ∩ S) := by
    refine Measure.eqOn_open_of_ae_eq (μ := μ) ?_ (Ω.isOpen.inter hS) continuousOn_const
      (hcont.mono inter_subset_left)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hae,
      ae_restrict_mem (Ω.isOpen.inter hS).measurableSet] with x hx hxS
    rw [← hx, hc x hxS.2]
  have hinner : Continuous fun x : E ↦ ⟪v, x⟫ := continuous_const.inner continuous_id
  have hpos := hconst {x | 0 < ⟪v, x⟫} 1 (isOpen_lt continuous_const hinner)
    fun x hx ↦ by simp [indicator_of_mem hx]
  have hneg := hconst {x | ⟪v, x⟫ < 0} 0 (isOpen_lt hinner continuous_const)
    fun x hx ↦ by simp [(mem_ofPred.1 hx).le]
  -- Approach `x₀` along the line `x₀ + t v`, which crosses the hyperplane at `t = 0`.
  set γ : ℝ → E := fun t ↦ x₀ + t • v
  have hγ : Tendsto γ (𝓝 0) (𝓝 x₀) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 x₀ (by simp)
  have hγv (t : ℝ) : ⟪v, γ t⟫ = t * ‖v‖ ^ 2 := by
    simp [γ, inner_add_right, inner_smul_right, hvx₀]
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  have hΩ : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ Ω := hγ (Ω.isOpen.mem_nhds hx₀)
  have hlim (l : Filter ℝ) (hl : l ≤ 𝓝 0) : Tendsto (h ∘ γ) l (𝓝 (h x₀)) :=
    ((hcont.continuousAt (Ω.isOpen.mem_nhds hx₀)).tendsto.comp hγ).mono_left hl
  have h1 : h x₀ = 1 := by
    refine tendsto_nhds_unique (hlim (𝓝[>] 0) nhdsWithin_le_nhds) (tendsto_const_nhds.congr' ?_)
    filter_upwards [nhdsWithin_le_nhds hΩ, self_mem_nhdsWithin] with t ht ht0
    exact hpos ⟨ht, mem_ofPred.2 (by rw [hγv]; exact mul_pos ht0 hv2)⟩
  have h0 : h x₀ = 0 := by
    refine tendsto_nhds_unique (hlim (𝓝[<] 0) nhdsWithin_le_nhds) (tendsto_const_nhds.congr' ?_)
    filter_upwards [nhdsWithin_le_nhds hΩ, self_mem_nhdsWithin] with t ht ht0
    exact hneg ⟨ht, mem_ofPred.2 (by rw [hγv]; exact mul_neg_of_neg_of_pos ht0 hv2)⟩
  exact one_ne_zero (h1.symm.trans h0)

/-- **Weyl's lemma non-example.** On `ℝⁿ⁺¹`, the indicator `u = 1_{x₁ > 0}` of a half-space is
locally integrable and is not weakly harmonic. -/
theorem locallyIntegrable_and_not_weaklyHarmonicOn_indicator_euclideanSpace (n : ℕ) :
    LocallyIntegrable
        ({x : EuclideanSpace ℝ (Fin (n + 1)) | 0 < x 0}.indicator
          (1 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)) ∧
      ¬WeaklyHarmonicOn volume ⊤
        ({x : EuclideanSpace ℝ (Fin (n + 1)) | 0 < x 0}.indicator
          (1 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)) := by
  have hset : {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 < x 0} =
      {x | 0 < ⟪EuclideanSpace.single 0 1, x⟫} := by
    ext x
    simp [EuclideanSpace.inner_single_left]
  rw [hset]
  exact ⟨(locallyIntegrable_const 1).indicator
      (measurableSet_lt measurable_const (continuous_const.inner continuous_id).measurable),
    not_weaklyHarmonicOn_indicator volume (fun h ↦ by simpa using congrArg (· 0) h)
      (Opens.mem_top 0) (inner_zero_right _)⟩

end TauCeti.Examples.HalfSpaceIndicator
