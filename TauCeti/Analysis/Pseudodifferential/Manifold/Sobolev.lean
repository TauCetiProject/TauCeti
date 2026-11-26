/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartPatching
public import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables

/-!
# Sobolev estimates for classical pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ` and `P` a classical pseudodifferential operator of order `m`
on `M` (`TauCeti.classicalPseudodifferentialOperators`). A complex-valued smooth function `u` on
`M` is read in a chart `e` of the maximal atlas through a cutoff `φ` with compact support in the
chart target as the Schwartz function `φ · (u ∘ e⁻¹)` on `ℝⁿ`
(`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). Following Taylor, a Sobolev norm of `u` on
a compact manifold is `∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^s}` for finitely many charts `e'ᵢ` and cutoffs
`ψᵢ` whose readings `ψᵢ ∘ e'ᵢ` on `M` add up to `1`; it is equivalent to Taylor's Hilbert norm
`(∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖²_{H^s})^{1/2}`. This file proves that `P` loses `m` orders in these
norms: for every real `s` there is a constant `C` such that

`∑ⱼ ‖φⱼ · ((P u) ∘ eⱼ⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^s}`

for every smooth `u`, where `(eⱼ, φⱼ)` is any finite family of charts and cutoffs
(`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`).
This is the a priori estimate through which `P` extends to a bounded operator
`H^s(M) → H^{s - m}(M)`, the starting point of the Fredholm theory of elliptic operators on compact
manifolds.

## The argument

These are the chart-patching estimates of
`TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le`,
`TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_le_sum` and
`TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum` for the source norm `H^s` and
the target norm `H^{s - m}`. Their hypotheses hold because the inclusion of Schwartz functions in
`H^s` is injective (`SchwartzMap.toBesselPotentialSpaceCLM_injective`), localized changes of
variables are bounded on `H^s`
(`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`), and `Op(a)` is
bounded `H^s → H^{s - m}` for every symbol `a` of order `m` with compact spatial support
(`TauCeti.Symbol.quantizeSobolev`).

## Main results

* `TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le`: the
  estimate between two charts.
* `TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`: the
  reading of `P u` in one chart is bounded in `H^{s - m}` by the `H^s` norm of `u` for a partition.
* `TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`: the
  Sobolev estimate `‖P u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}` in these norms.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31)
  and §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1, Theorem 18.1.13 and Definition 18.1.20.
-/

public section

noncomputable section

open TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}

/-- A quantization `Op(a)` with `a` of order `m` and compact spatial support is bounded
`H^s → H^{s - m}` on Schwartz functions (`TauCeti.Symbol.quantizeSobolev`). -/
private theorem exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    (s : ℝ) (a : Symbol n ℂ ℂ m) (ha : a.HasCompactSpatialSupport) :
    ∃ A, ∀ w : 𝓢(CoordinateSpace n, ℂ),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤
        A * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 w‖ := by
  refine ⟨‖a.quantizeSobolev ha s‖, fun w ↦ ?_⟩
  have h := ha.quantizeSobolev_toBesselPotentialSpaceCLM s w
  -- Both Schwartz functions have underlying function `quantizeSchwartzValue a.coefficient w`.
  rw [show (ha.hasCompactSupport_quantizeSchwartzValue w).toSchwartzMap
      (a.contDiff_quantizeSchwartzValue w) = Symbol.quantizeUniformCLM a ha.isUniform w from
    SchwartzMap.ext fun y ↦ (Symbol.quantizeUniformCLM_apply a ha.isUniform w y).symm] at h
  rw [← h]
  exact (a.quantizeSobolev ha s).le_opNorm _

/-- **The Sobolev estimate between two charts.** Let `P` be a classical pseudodifferential
operator of order `m`, `φ` a cutoff in a chart `e` and `ψ` a cutoff in a chart `e'`, with `Ψ` the
smooth function `ψ ∘ e'` on `M`, extended by `0`. For every real `s` there is a constant `C`
such that for every smooth `g` on `M`, the reading `φ · (P (Ψ g) ∘ e⁻¹)` of `P (Ψ g)` in `e`
satisfies

`‖φ · (P (Ψ g) ∘ e⁻¹)‖_{H^{s - m}} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) (s : ℝ) :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (e.cutoffPushforwardSchwartz he φ
          (P (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g)))‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e'.cutoffPushforwardSchwartz he' ψ g)‖ :=
  exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le hP
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s 2)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs s)
    _ (exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s)
    he he' φ ψ

/-- **The Sobolev estimate in one chart.** Let `P` be a classical pseudodifferential operator of
order `m` and `ψᵢ` finitely many cutoffs in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`,
extended by `0`, add up to `1`; such cutoffs exist on every compact manifold
(`IsCompact.exists_sum_cutoffPullback_eq_one`). For a cutoff `φ` in a chart `e` and every real `s`
there is a constant `C` such that every smooth `u` on `M` satisfies

`‖φ · ((P u) ∘ e⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) (s : ℝ) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (e.cutoffPushforwardSchwartz he φ (P u))‖ ≤
        C * ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ :=
  exists_norm_cutoffPushforwardSchwartz_apply_le_sum hP
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s 2)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs s)
    _ (exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s)
    he φ he' ψ hψ

/-- **Sobolev estimate for classical pseudodifferential operators on a manifold.** Let `P` be a
classical pseudodifferential operator of order `m` and `ψᵢ` finitely many cutoffs in charts `e'ᵢ`
whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`, which forces `M` to be
compact. In the norm `∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^s}`, which defines `H^s(M)` up to equivalence of
norms, `P` loses `m` orders: for finitely many cutoffs `φⱼ` in charts `eⱼ` and every real `s`
there is a constant `C` such that every smooth `u` on `M` satisfies

`∑ⱼ ‖φⱼ · ((P u) ∘ eⱼ⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^s}`. -/
theorem exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    {κ : Type*} [Fintype κ]
    {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) (s : ℝ) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ j, ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          ((e j).cutoffPushforwardSchwartz (he j) (φ j) (P u))‖ ≤
        C * ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ :=
  exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum hP
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s 2)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs s)
    _ (exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s)
    he φ he' ψ hψ

end TauCeti
