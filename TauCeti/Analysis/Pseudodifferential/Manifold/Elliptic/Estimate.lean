/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Geometry.Manifold.Sobolev.ChartReading

/-!
# The elliptic estimate on a compact manifold and finiteness of the kernel

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

The estimate follows from a parametrix. For every `N : ℕ` there is an operator `Q` of order `-m`
such that `R = Q ∘ P - 1` has order `-N`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`), so
`u = Q (P u) - R u`. The Sobolev estimate on `M`
(`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`)
bounds `Q (P u)` in `H^{s + m}` by `P u` in `H^s`, and `R u` in `H^{r + N}` by `u` in `H^r`. For
`N ≥ s + m - r` the space `H^{r + N}` embeds continuously into `H^{s + m}`.

As a consequence, **the kernel of an elliptic operator on a compact manifold is
finite-dimensional** (`TauCeti.IsClassicalElliptic.finiteDimensional_ker`). On the kernel, the
estimate with `s = 0` and `r = m - 1` bounds the `H^m` partition norm by the `H^{m - 1}` partition
norm, and by the Rellich theorem a space of smooth functions with such a reverse estimate is
finite-dimensional (`TauCeti.finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le`).

## Main results

* `TauCeti.IsClassicalElliptic.exists_sum_norm_le_add`: the elliptic estimate
  `‖u‖_{H^{s + m}} ≤ C (‖P u‖_{H^s} + ‖u‖_{H^r})` for smooth `u`, in chart-partition norms.
* `TauCeti.IsClassicalElliptic.finiteDimensional_ker`: on a compact manifold, the smooth functions
  killed by an elliptic classical pseudodifferential operator form a finite-dimensional space.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4,
  (4.6)–(4.11) (elliptic estimates from a parametrix).
* M. F. Atiyah and I. M. Singer, *The index of elliptic operators I*, Ann. of Math. 87 (1968),
  §6 (finiteness of the kernel of an elliptic operator on a compact manifold).
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
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
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
  -- A parametrix `Q` of order `-m` with `R = Q P - 1` of order `-N`, where `s + m ≤ r + N`.
  set N := ⌈s + m - r⌉₊
  have hN : s + m ≤ r - -(N : ℝ) := by
    linarith [Nat.le_ceil (s + m - r)]
  obtain ⟨Q, hQ, -, hR⟩ := hPe.exists_comp_sub_id_mem_classicalPseudodifferentialOperators hP N
  set R : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ := Q ∘ₗ P - LinearMap.id with hRdef
  obtain ⟨A, hA⟩ := exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum
    hQ he φ he' ψ hψ s
  rw [sub_neg_eq_add] at hA
  obtain ⟨B, hB⟩ := exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum
    hR he φ he' ψ hψ r
  set c := ‖(BesselPotentialSpace.inclusion (E := CoordinateSpace n) (G := ℂ) (p := 2) hN)‖
  refine ⟨|A| + c * |B|, fun u ↦ ?_⟩
  set X := ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
    ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) (P u))‖
  set Y := ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r 2
    ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hY : 0 ≤ Y := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  -- Each reading of `u = Q (P u) - R u` is split accordingly.
  have hu (j : κ) : ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
      ((e j).cutoffPushforwardSchwartz (he j) (φ j) u)‖ ≤
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
        ((e j).cutoffPushforwardSchwartz (he j) (φ j) (Q (P u)))‖ +
      c * ‖SchwartzMap.toBesselPotentialSpaceCLM (r - -(N : ℝ)) 2
        ((e j).cutoffPushforwardSchwartz (he j) (φ j) (R u))‖ := by
    have hsplit : u = Q (P u) - R u := by simp [hRdef]
    conv_lhs => rw [hsplit, map_sub, map_sub]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hN]
    exact ContinuousLinearMap.le_opNorm _ _
  calc ∑ j, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
          ((e j).cutoffPushforwardSchwartz (he j) (φ j) u)‖
      ≤ A * X + c * (B * Y) := by
        refine (Finset.sum_le_sum fun j _ ↦ hu j).trans ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        exact add_le_add (hA (P u)) (mul_le_mul_of_nonneg_left (hB u) (norm_nonneg _))
    _ ≤ |A| * X + c * (|B| * Y) := by
        gcongr
        · exact le_abs_self A
        · exact le_abs_self B
    _ ≤ (|A| + c * |B|) * (X + Y) := by
        have := mul_nonneg (abs_nonneg A) hY
        have := mul_nonneg (mul_nonneg (norm_nonneg _ : 0 ≤ c) (abs_nonneg B)) hX
        nlinarith

/-- **The kernel of an elliptic operator is finite-dimensional.** On a compact manifold `M`, the
smooth functions `u` with `P u = 0`, for an elliptic classical pseudodifferential operator `P`, form
a finite-dimensional complex vector space. -/
theorem IsClassicalElliptic.finiteDimensional_ker [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P) :
    FiniteDimensional ℂ (LinearMap.ker P) := by
  -- On the kernel, the elliptic estimate for a chart partition `ρᵢ` of `M` with `s = 0` and
  -- `r = m - 1` bounds the `H^m` readings by the `H^{m - 1}` readings.
  obtain ⟨N, c, ρ, hρ⟩ :=
    (isCompact_univ (X := M)).exists_sum_cutoffPullback_eq_one (E := CoordinateSpace n)
  have he (i : Fin N) :
      chartAt (CoordinateSpace n) (c i) ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (c i)
  have hρ' (x : M) : ∑ i, (chartAt (CoordinateSpace n) (c i)).cutoffPullback (he i) (ρ i) 1 x = 1 :=
    hρ x (mem_univ x)
  obtain ⟨C, hC⟩ := hPe.exists_sum_norm_le_add hP he ρ he ρ hρ' 0 (m - 1)
  rw [zero_add] at hC
  exact finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le he ρ hρ'
    (show m - 1 < m by linarith) fun u hu ↦ by simpa [LinearMap.mem_ker.1 hu] using hC u

end TauCeti
