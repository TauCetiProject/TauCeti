/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic.Interior

/-!
# The elliptic estimate on a compact manifold

Let `P` be a classical pseudodifferential operator of order `m` on a manifold `M` modelled on
`ℝⁿ` (`TauCeti.classicalPseudodifferentialOperators`) which is elliptic
(`TauCeti.IsClassicalElliptic`). Let `ψᵢ` be finitely many cutoffs in charts `e'ᵢ` whose readings
`Ψᵢ = ψᵢ ∘ e'ᵢ` on `M` add up to `1`; this forces `M` to be compact
(`TauCeti.compactSpace_of_forall_sum_cutoffPullback_eq_one`). The norm
`∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^s}` of a smooth function `u` defines the Sobolev space `H^s(M)` up to
equivalence of norms. This file proves the **elliptic estimate**: for all real `s` and `r` there
is a constant `C` such that every smooth `u` on `M` satisfies

`‖u‖_{H^{s + m}} ≤ C (‖P u‖_{H^s} + ‖u‖_{H^r})`

(`TauCeti.IsClassicalElliptic.exists_sum_norm_le_add`, where the left side may be read through
any finite family of charts and cutoffs). It is meaningful for `r < s + m`. The lower-order term
cannot be dropped: on the circle, the Laplacian kills the constant function `1`, whose `H^2` norm
is positive.

The estimate is the sum over the cutoffs `φⱼ` of the interior elliptic estimate
(`TauCeti.IsClassicalElliptic.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_add`),
which comes from a parametrix of `P`. On a compact manifold every operator is properly supported
(`TauCeti.isProperlySupported_of_compactSpace`), and cutoffs `ψᵢ` adding up to `1` everywhere add
up to `1` on whichever compact set the interior estimate asks for.

The estimate is the a priori half of the regularity theory of an elliptic operator on a compact
manifold. Finiteness of its smooth kernel is proved separately, from Rellich's theorem
(`TauCeti.IsClassicalElliptic.finiteDimensional_ker`).

## Main results

* `TauCeti.IsClassicalElliptic.exists_sum_norm_le_add`: the elliptic estimate
  `‖u‖_{H^{s + m}} ≤ C (‖P u‖_{H^s} + ‖u‖_{H^r})` for smooth `u`, in chart-partition norms.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4,
  (4.6)–(4.11) (elliptic estimates from a parametrix).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.2.
-/

public section

open Filter Set OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap Topology BesselPotentialSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **The elliptic estimate on a compact manifold.** Let `P` be an elliptic classical
pseudodifferential operator of order `m`, and `ψᵢ` finitely many cutoffs in charts `e'ᵢ` whose
readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`. For finitely many cutoffs `φⱼ` in
charts `eⱼ` and all real `s` and `r` there is a constant `C` such that every smooth `u` on `M`
satisfies

`∑ⱼ ‖φⱼ · (u ∘ eⱼ⁻¹)‖_{H^{s + m}} ≤
  C (∑ᵢ ‖ψᵢ · ((P u) ∘ e'ᵢ⁻¹)‖_{H^s} + ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^r})`. -/
theorem IsClassicalElliptic.exists_sum_norm_le_add
    (hPe : IsClassicalElliptic m P)
    {κ : Type*} [Fintype κ] {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) (s r : ℝ) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ j, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
          ((e j).cutoffPushforwardSchwartz (he j) (φ j) u)‖ ≤
        C * (∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
            ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) (P u))‖ +
          ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r 2
            ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖) := by
  have := compactSpace_of_forall_sum_cutoffPullback_eq_one he' ψ hψ
  -- On a compact manifold `P` is properly supported and the cutoffs `ψᵢ` cover every compact set,
  -- so the interior estimate holds near each `φⱼ`; the global estimate is their sum.
  choose K _ hK using fun j ↦ hPe.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_add
    (isProperlySupported_of_compactSpace P) (he j) (φ j)
  choose C hC using fun j ↦ hK j he' ψ (fun x _ ↦ hψ x) 2 ENNReal.one_lt_two
    ENNReal.ofNat_ne_top s r
  refine ⟨∑ j, |C j|, fun u ↦ ?_⟩
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ ↦ (hC j u).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
    (add_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)))

end TauCeti
