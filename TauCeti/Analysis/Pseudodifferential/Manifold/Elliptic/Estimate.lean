/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion

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

The estimate follows from a parametrix. For every `N : ℕ` there is an operator `Q` of order `-m`
such that `R = Q ∘ P - 1` has order `-N`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`), so
`u = Q (P u) - R u`. The Sobolev estimate on `M`
(`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`)
bounds `Q (P u)` in `H^{s + m}` by `P u` in `H^s`, and `R u` in `H^{r + N}` by `u` in `H^r`. For
`N ≥ s + m - r` the space `H^{r + N}` embeds continuously into `H^{s + m}`.

The estimate is the a priori half of the regularity theory of an elliptic operator on a compact
manifold. Finiteness of its smooth kernel is proved separately, from Rellich's theorem
(`TauCeti.IsClassicalElliptic.finiteDimensional_ker`).

## Main results

* `TauCeti.IsClassicalElliptic.exists_sum_norm_le_add`: the elliptic estimate
  `‖u‖_{H^{s + m}} ≤ C (‖P u‖_{H^s} + ‖u‖_{H^r})` for smooth `u`, in chart-partition norms.
* `TauCeti.IsClassicalElliptic.exists_norm_le_mul_norm_chartSobolevExtension_add`: the same
  estimate on all of the Sobolev space `H^{s + m}(M)` of a chart partition
  (`TauCeti.chartSobolevSpace`), for the extension of `P` to `H^{s + m}(M) → H^s(M)`; both sides
  are continuous, so it follows from the estimate on the dense smooth functions.

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
  -- A parametrix `Q` of order `-m` with `R = Q P - 1` of order `-N`, where `s + m ≤ r + N`.
  set N := ⌈s + m - r⌉₊
  have hN : s + m ≤ r - -(N : ℝ) := by
    linarith [Nat.le_ceil (s + m - r)]
  obtain ⟨Q, hQ, -, hR⟩ := hPe.exists_comp_sub_id_mem_classicalPseudodifferentialOperators N
  set R : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ := Q ∘ₗ P - LinearMap.id with hRdef
  obtain ⟨A, hA⟩ := exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum
    hQ he φ he' ψ hψ ENNReal.one_lt_two ENNReal.ofNat_ne_top s
  rw [sub_neg_eq_add] at hA
  obtain ⟨B, hB⟩ := exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum
    hR he φ he' ψ hψ ENNReal.one_lt_two ENNReal.ofNat_ne_top r
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

/-! ### The elliptic estimate on the Sobolev spaces -/

/-- **The elliptic estimate on `H^{s + m}(M)`.** If `P` is an elliptic classical
pseudodifferential operator of order `m` and `r ≤ s + m`, there is a constant `C` such that every
`x` in the Sobolev space `H^{s + m}(M)` of a chart partition satisfies

`‖x‖_{H^{s + m}} ≤ C (‖P x‖_{H^s} + ‖x‖_{H^r})`,

for the extension `P : H^{s + m}(M) → H^s(M)` and the inclusion `H^{s + m}(M) ⊆ H^r(M)`. The order
`s + m` is given as `t`, with `s + m = t`. -/
theorem IsClassicalElliptic.exists_norm_le_mul_norm_chartSobolevExtension_add
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    {ι : Type*} [Fintype ι] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    {s t r : ℝ} (hst : s + m = t) (hr : r ≤ t) :
    ∃ C, ∀ x : chartSobolevSpace hc ψ t, ‖x‖ ≤
      C * (‖chartSobolevExtension hc ψ hc ψ P t s x‖ + ‖chartSobolevInclusion hc ψ hr x‖) := by
  subst hst
  obtain ⟨C, hC⟩ := hPe.exists_sum_norm_le_add hc ψ hc ψ hψ s r
  have hPx := chartSobolevExtension_toChartSobolevSpace_of_mem (hc' := hc) (φ := ψ) hP hψ
    (s := s + m) (t := s) (by linarith)
  refine ⟨|C| * Real.sqrt (Fintype.card ι), fun x ↦ ?_⟩
  -- Both sides are continuous in `x`, so the estimate extends from smooth functions.
  refine (denseRange_toChartSobolevSpace hc ψ (s + m)).induction_on x
    (isClosed_le (by fun_prop) (by fun_prop)) fun u ↦ ?_
  rw [hPx, chartSobolevInclusion_toChartSobolevSpace]
  simp only [norm_toChartSobolevSpace]
  -- On smooth functions this is the estimate in the sums of the norms of the chart readings.
  calc ‖chartReading hc ψ (s + m) u‖
      ≤ ∑ i, ‖chartReading hc ψ (s + m) u i‖ := PiLp.norm_le_sum_norm _
    _ ≤ |C| * (∑ i, ‖chartReading hc ψ s (P u) i‖ + ∑ i, ‖chartReading hc ψ r u i‖) := by
        simp only [chartReading_apply]
        exact (hC u).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
          (add_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
            (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)))
    _ ≤ |C| * (Real.sqrt (Fintype.card ι) * ‖chartReading hc ψ s (P u)‖ +
          Real.sqrt (Fintype.card ι) * ‖chartReading hc ψ r u‖) := by
        gcongr <;> exact PiLp.sum_norm_le_sqrt_card_mul_norm _
    _ = |C| * Real.sqrt (Fintype.card ι) *
          (‖chartReading hc ψ s (P u)‖ + ‖chartReading hc ψ r u‖) := by ring

end TauCeti
