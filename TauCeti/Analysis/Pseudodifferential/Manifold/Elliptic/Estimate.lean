/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev

/-!
# The elliptic estimate on a compact manifold

Let `M` be a compact manifold modelled on `ℝⁿ` and `P` an elliptic classical pseudodifferential
operator of order `m` on `M` (`TauCeti.classicalPseudodifferentialOperators`,
`TauCeti.IsClassicalElliptic`). Read the complex-valued smooth functions `u` on `M` through
finitely many charts `eᵢ` and cutoffs `ψᵢ` whose readings `ψᵢ ∘ eᵢ` on `M` add up to `1`, and
write `‖u‖_s = ∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^s}` for the resulting Sobolev norm, as in
`TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev`.

**The elliptic estimate.** For all real `s` and `r` there is a constant `C` such that

`‖u‖_{s + m} ≤ C (‖P u‖_s + ‖u‖_r)`

for every smooth `u` on `M`
(`IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_le`).
So `P` gains back the `m` orders it loses, up to an arbitrarily weak norm of `u`. Choose `N ∈ ℕ`
with `s + m - N ≤ r` and a parametrix `Q` of order `-m` with `L = Q P - 1` of order `-N`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`).
Then `u = Q (P u) - L u`, and the Sobolev estimate on `M`
(`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`)
bounds `‖Q (P u)‖_{s + m}` by `‖P u‖_s` and `‖L u‖_{s + m}` by `‖u‖_{s + m - N} ≤ ‖u‖_r`.

The lower-order term cannot be dropped: on the circle, `P = -∂²` kills the constant `1`, whose
norm is positive.

The finite-dimensionality of the kernel of `P` on a compact manifold
(`TauCeti.IsClassicalElliptic.finiteDimensional_ker`) is proved in
`TauCeti.Analysis.Pseudodifferential.Manifold.Rellich`.

## Main results

* `IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_le`:
  the elliptic estimate `‖u‖_{s + m} ≤ C (‖P u‖_s + ‖u‖_r)`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (4.6)–(4.11), and Lecture II, (3.1)–(3.8) (elliptic estimates from a parametrix).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.2.
-/

public section

noncomputable section

open Filter Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology BesselPotentialSpace

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}

/-- **The elliptic estimate on a compact manifold.** Let `P` be an elliptic classical
pseudodifferential operator of order `m` on `M`, and `ψᵢ` finitely many cutoffs in charts `eᵢ`
whose readings `ψᵢ ∘ eᵢ` on `M`, extended by `0`, add up to `1` (so `M` is compact). For all real
`s` and `r` there is a constant `C` such that every smooth `u` on `M` satisfies

`∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^{s + m}}`
`  ≤ C (∑ᵢ ‖ψᵢ · ((P u) ∘ eᵢ⁻¹)‖_{H^s} + ∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^r})`.
-/
theorem IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_le
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) {ι : Type*} [Fintype ι]
    {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (s r : ℝ) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
          ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖ ≤
        C * (∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
            ((e i).cutoffPushforwardSchwartz (he i) (ψ i) (P u))‖ +
          ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r 2
            ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖) := by
  have := compactSpace_of_sum_cutoffPullback_eq_one he ψ hψ
  -- A parametrix `Q` of order `-m` with `L = Q P - 1` of order `-N`, where `s + m - N ≤ r`.
  set N := ⌈s + m - r⌉₊
  obtain ⟨Q, hQ, -, hL⟩ :=
    hPe.exists_comp_sub_id_mem_classicalPseudodifferentialOperators hP N
  set L := Q ∘ₗ P - LinearMap.id
  have hN : s + m - N ≤ r := by linarith [Nat.le_ceil (s + m - r)]
  -- `Q` gains `m` orders and `L` gains `N` orders.
  obtain ⟨C₁, hC₁⟩ :=
    exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum hQ he ψ he ψ
      hψ s
  obtain ⟨C₂, hC₂⟩ :=
    exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum hL he ψ he ψ
      hψ (s + m - N)
  rw [sub_neg_eq_add] at hC₁
  rw [show s + m - N - -(N : ℝ) = s + m by ring] at hC₂
  refine ⟨max (max C₁ C₂) 0, fun u ↦ ?_⟩
  set K := max (max C₁ C₂) 0
  set A := ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
    ((e i).cutoffPushforwardSchwartz (he i) (ψ i) (P u))‖
  set B := ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r 2
    ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖
  -- The `H^{s + m - N}` norms of the readings are at most their `H^r` norms.
  have hB : ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m - N) 2
      ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖ ≤ B :=
    Finset.sum_le_sum fun i _ ↦ by
      rw [← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hN]
      exact BesselPotentialSpace.norm_inclusion_apply_le hN _
  -- `u = Q (P u) - L u`.
  have hu : u = Q (P u) - L u := by simp [L]
  calc ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
          ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖
      ≤ ∑ i, (‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
            ((e i).cutoffPushforwardSchwartz (he i) (ψ i) (Q (P u)))‖ +
          ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
            ((e i).cutoffPushforwardSchwartz (he i) (ψ i) (L u))‖) :=
        Finset.sum_le_sum fun i _ ↦ by
          conv_lhs => rw [hu, map_sub, map_sub]
          exact norm_sub_le _ _
    _ ≤ C₁ * A + C₂ * ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m - N) 2
          ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖ := by
        rw [Finset.sum_add_distrib]
        exact add_le_add (hC₁ (P u)) (hC₂ u)
    _ ≤ K * A + K * B := by
        gcongr
        exacts [le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _)]
    _ = K * (A + B) := (mul_add _ _ _).symm

end TauCeti
