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

**Finite-dimensional kernel.** The smooth solutions of `P u = 0` form a finite-dimensional
space (`TauCeti.IsClassicalElliptic.finiteDimensional_ker`), because on the kernel the estimate
reads `‖u‖_1 ≤ C ‖u‖_0`. A space `V` of smooth functions with `‖u‖_{s'} ≤ C ‖u‖_s` for some
`s < s'` is finite-dimensional
(`TauCeti.finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le`): the readings of the
elements of `V` with `‖u‖_s ≤ 1` are bounded in `H^{s'}` and supported in the fixed compact sets
`tsupport ψᵢ`, so by Rellich's theorem
(`BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq`) they lie in a compact
subset of `H^s`. Embedded into `(H^s)ⁱ` by its readings, `V` thus has a totally bounded unit
ball, and Riesz's theorem (`FiniteDimensional.of_totallyBounded_nhds_zero`) makes it
finite-dimensional. Compactness of `M` is needed: on a disjoint union of countably many
circles the operator `-∂²` is elliptic, and its kernel, the locally constant functions, is
infinite-dimensional.

## Main results

* `IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_le`:
  the elliptic estimate `‖u‖_{s + m} ≤ C (‖P u‖_s + ‖u‖_r)`.
* `TauCeti.IsClassicalElliptic.finiteDimensional_ker`: an elliptic classical pseudodifferential
  operator on a compact manifold has a finite-dimensional space of smooth solutions of `P u = 0`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (4.6)–(4.11), and Lecture II, (3.1)–(3.8) (elliptic estimates from a parametrix).
* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §6 (finite-dimensional kernels of elliptic operators on compact manifolds).
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

/-- **The kernel of an elliptic operator is finite-dimensional.** On a compact manifold `M`, the
smooth solutions `u` of `P u = 0` of an elliptic classical pseudodifferential operator `P` of
order `m` form a finite-dimensional complex vector space. -/
theorem IsClassicalElliptic.finiteDimensional_ker [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    [CompactSpace M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) : FiniteDimensional ℂ (LinearMap.ker P) := by
  -- Chart cutoffs `ψᵢ` whose readings add up to `1`, and the elliptic estimate with `s + m = 1`
  -- and `r = 0`, which reads `‖u‖_1 ≤ C ‖u‖_0` on the kernel.
  obtain ⟨N, c, ψ, hψ⟩ := isCompact_univ.exists_sum_cutoffPullback_eq_one (M := M)
    (E := CoordinateSpace n)
  have he (i : Fin N) := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    (c i)
  have hψ' (x : M) := hψ x (mem_univ x)
  obtain ⟨C, hC⟩ :=
    hPe.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_le hP he ψ hψ' (1 - m) 0
  rw [sub_add_cancel] at hC
  refine finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le he ψ hψ' zero_lt_one
    (C := C) fun u hu ↦ ?_
  simpa [LinearMap.mem_ker.1 hu] using hC u

end TauCeti
