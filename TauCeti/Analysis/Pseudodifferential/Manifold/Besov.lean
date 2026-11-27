/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Besov
public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartPatching
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LocalizedChangeOfVariables

/-!
# Hölder–Zygmund and Besov estimates for classical pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ` and `P` a classical pseudodifferential operator of order `m`
on `M` (`TauCeti.classicalPseudodifferentialOperators`). A complex-valued smooth function `u` on
`M` is read in a chart `e` of the maximal atlas through a cutoff `φ` with compact support in the
chart target as the Schwartz function `φ · (u ∘ e⁻¹)` on `ℝⁿ`
(`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). Following Triebel, Besov norms on a compact
manifold are defined through charts as `∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{B^s_{p,q}}` for finitely many
charts `e'ᵢ` and cutoffs `ψᵢ` whose readings `ψᵢ ∘ e'ᵢ` on `M` add up to `1`, the Euclidean norms
being those of the Littlewood–Paley partition of a fixed bump function `b`
(`TauCeti.BesovSpace`); for `p = q = ∞` these are the Hölder–Zygmund norms `𝒞^s = B^s_{∞,∞}`.
This file proves that `P` loses `m` orders on the scale `B^s_{p,∞}`: for every real `s` and
`1 ≤ p ≤ ∞` there is a constant `C` such that

`∑ⱼ ‖φⱼ · ((P u) ∘ eⱼ⁻¹)‖_{B^{s - m}_{p,∞}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}}`

for every smooth `u`, where `(eⱼ, φⱼ)` is any finite family of charts and cutoffs
(`TauCeti.exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`). For `p = ∞` this
is the Zygmund estimate `‖P u‖_{𝒞^{s - m}} ≤ C ‖u‖_{𝒞^s}` on a compact manifold, for every real `s`
and `m`, where operators of order `0` need not be bounded on `L^∞`.

## The argument

This is the argument of the Sobolev estimate
`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`: both
are the chart-patching estimates of
`TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le`,
`TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_le_sum` and
`TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum`, here for the source norm
`B^s_{p,∞}` and the target norm `B^{s - m}_{p,∞}`. Their hypotheses hold because the inclusion of
Schwartz functions in `B^s_{p,∞}` is injective (`SchwartzMap.toBesovSpaceCLM_injective`),
localized changes of variables are bounded on `B^s_{p,∞}`
(`TauCeti.BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp`), and `Op(a)` is bounded
`B^s_{p,∞} → B^{s - m}_{p,∞}` for every symbol `a` of order `m` with compact spatial support
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le`).

## Main results

* `TauCeti.exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le`: the estimate
  between two charts.
* `TauCeti.exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`: the reading of
  `P u` in one chart is bounded in `B^{s - m}_{p,∞}` by the `B^s_{p,∞}` norm of `u` for a
  partition.
* `TauCeti.exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`: the Besov
  estimate `‖P u‖_{B^{s - m}_{p,∞}} ≤ C ‖u‖_{B^s_{p,∞}}` in these norms, in particular the
  Hölder–Zygmund estimate for `p = ∞`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (3.32)–(3.34) (pseudodifferential operators on the Zygmund spaces) and §8.
* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, §7.2 (Besov spaces on manifolds,
  defined through charts and a partition of unity).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1, Definition 18.1.20.
-/

public section

noncomputable section

open TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap ENNReal

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}

/-- **The Besov estimate between two charts.** Let `P` be a classical pseudodifferential operator
of order `m`, `φ` a cutoff in a chart `e` and `ψ` a cutoff in a chart `e'`, with `Ψ` the smooth
function `ψ ∘ e'` on `M`, extended by `0`. For every real `s` and `1 ≤ p ≤ ∞` there is a constant
`C` such that for every smooth `g` on `M`, the reading `φ · (P (Ψ g) ∘ e⁻¹)` of `P (Ψ g)` in `e`
satisfies

`‖φ · (P (Ψ g) ∘ e⁻¹)‖_{B^{s - m}_{p,∞}} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{B^s_{p,∞}}`. -/
theorem exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (b : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesovSpaceCLM ℂ b (s - m) p ∞ (e.cutoffPushforwardSchwartz he φ
          (P (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g)))‖ ≤
        C * ‖SchwartzMap.toBesovSpaceCLM ℂ b s p ∞ (e'.cutoffPushforwardSchwartz he' ψ g)‖ :=
  exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le hP
    (SchwartzMap.toBesovSpaceCLM_injective ℂ b s p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs b s p ∞)
    _ (fun _ ha ↦ (ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le b s).imp
      fun _ hA w ↦ hA.2 w)
    he he' φ ψ

/-- **The Besov estimate in one chart.** Let `P` be a classical pseudodifferential operator of
order `m` and `ψᵢ` finitely many cutoffs in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`,
extended by `0`, add up to `1`; such cutoffs exist on every compact manifold
(`IsCompact.exists_sum_cutoffPullback_eq_one`). For a cutoff `φ` in a chart `e`, every real `s` and
`1 ≤ p ≤ ∞` there is a constant `C` such that every smooth `u` on `M` satisfies

`‖φ · ((P u) ∘ e⁻¹)‖_{B^{s - m}_{p,∞}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}}`. -/
theorem exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (b : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesovSpaceCLM ℂ b (s - m) p ∞ (e.cutoffPushforwardSchwartz he φ (P u))‖ ≤
        C * ∑ i, ‖SchwartzMap.toBesovSpaceCLM ℂ b s p ∞
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ :=
  exists_norm_cutoffPushforwardSchwartz_apply_le_sum hP
    (SchwartzMap.toBesovSpaceCLM_injective ℂ b s p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs b s p ∞)
    _ (fun _ ha ↦ (ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le b s).imp
      fun _ hA w ↦ hA.2 w)
    he φ (K := Set.univ)
    (fun f g hfg ↦ DFunLike.coe_injective ((Set.eqOn_univ f g).1 hfg) ▸ Set.eqOn_refl _ _) he' ψ
    fun x _ ↦ hψ x

/-- **Besov and Hölder–Zygmund estimates for classical pseudodifferential operators on a
manifold.** Let `P` be a classical pseudodifferential operator of order `m` and `ψᵢ` finitely many
cutoffs in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`,
which forces `M` to be compact. In the norm `∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}}`, `P` loses `m`
orders: for finitely many cutoffs `φⱼ` in charts `eⱼ`, every real `s` and `1 ≤ p ≤ ∞` there is a
constant `C` such that every smooth `u` on `M` satisfies

`∑ⱼ ‖φⱼ · ((P u) ∘ eⱼ⁻¹)‖_{B^{s - m}_{p,∞}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}}`.

For `p = ∞` these are the Hölder–Zygmund norms `𝒞^s = B^s_{∞,∞}`. -/
theorem exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    {κ : Type*} [Fintype κ]
    {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (b : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ j, ‖SchwartzMap.toBesovSpaceCLM ℂ b (s - m) p ∞
          ((e j).cutoffPushforwardSchwartz (he j) (φ j) (P u))‖ ≤
        C * ∑ i, ‖SchwartzMap.toBesovSpaceCLM ℂ b s p ∞
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ :=
  exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum hP
    (SchwartzMap.toBesovSpaceCLM_injective ℂ b s p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs b s p ∞)
    _ (fun _ ha ↦ (ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le b s).imp
      fun _ hA w ↦ hA.2 w)
    he φ he' ψ hψ

end TauCeti
