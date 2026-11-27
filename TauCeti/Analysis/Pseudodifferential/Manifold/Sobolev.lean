/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartPatching
public import TauCeti.Analysis.Pseudodifferential.UniformSobolev
public import TauCeti.Geometry.Manifold.Sobolev.Completion
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Pseudodifferential.Lp.BesselPotentialSpace
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables

/-!
# Sobolev estimates for classical pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ` and `P` a classical pseudodifferential operator of order `m`
on `M` (`TauCeti.classicalPseudodifferentialOperators`). A complex-valued smooth function `u` on
`M` is read in a chart `e` of the maximal atlas through a cutoff `φ` with compact support in the
chart target as the Schwartz function `φ · (u ∘ e⁻¹)` on `ℝⁿ`
(`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). Following Taylor, for `1 < p < ∞` an
`Lᵖ` Sobolev norm of `u` on a compact manifold is `∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^{s,p}}` for finitely
many charts `e'ᵢ` and cutoffs `ψᵢ` whose readings `ψᵢ ∘ e'ᵢ` on `M` add up to `1`, with the
Bessel-potential spaces `H^{s,p}(ℝⁿ)`. For `p = 2` it is equivalent to Taylor's Hilbert norm
`(∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖²_{H^s})^{1/2}`. This file proves that `P` loses `m` orders in these
norms: for every real `s` and `1 < p < ∞` there is a constant `C` such that

`∑ⱼ ‖φⱼ · ((P u) ∘ eⱼ⁻¹)‖_{H^{s - m,p}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^{s,p}}`

for every smooth `u`, where `(eⱼ, φⱼ)` is any finite family of charts and cutoffs
(`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`).
This is the a priori estimate through which `P` extends to a bounded operator
`H^{s,p}(M) → H^{s - m,p}(M)`, the starting point of the Fredholm theory of elliptic operators on
compact manifolds and of their `Lᵖ` elliptic estimates. Taking for `P` the identity, an operator
of order `0`, it also compares the norms of two such partitions.

**Extension to Sobolev spaces.** With `H^s(M)` the closure of the chart readings of smooth functions
in the Hilbert sum `⨁ᵢ H^s(ℝⁿ)` (`TauCeti.chartSobolevSpace`), the estimate in its Hilbert norm
(`TauCeti.exists_norm_chartReading_apply_le`) makes the continuous extension
`TauCeti.chartSobolevExtension` of `P` to `H^s(M) → H^t(M)`, `t ≤ s - m`, agree with `P` on smooth
functions (`TauCeti.chartSobolevExtension_toChartSobolevSpace_of_mem`). These extensions compose
(`TauCeti.chartSobolevExtension_comp_of_mem`), and by Rellich's theorem they are compact when
`t < s - m` (`TauCeti.isCompactOperator_chartSobolevExtension_of_mem`), in particular for operators
of negative order.

## The argument

These are the chart-patching estimates of
`TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le`,
`TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_le_sum` and
`TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum` for the source norm `H^{s,p}` and
the target norm `H^{s - m,p}`. Their hypotheses hold because the inclusion of Schwartz functions in
`H^{s,p}` is injective (`SchwartzMap.toBesselPotentialSpaceCLM_injective`), localized changes of
variables are bounded on `H^{s,p}`
(`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`), and `Op(a)` is
bounded `H^{s,p} → H^{s - m,p}` for every uniform symbol `a` of order `m`, in particular for every
symbol with compact spatial support
(`TauCeti.Symbol.IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le`).

## Main results

* `TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le`: the
  estimate between two charts, in `H^{s - m,p}` and `H^{s,p}` for `1 < p < ∞`.
* `TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`: the
  Sobolev estimate `‖P u‖_{H^{s - m,p}} ≤ C ‖u‖_{H^{s,p}}` in these norms, for `1 < p < ∞`.
* `TauCeti.IsProperlySupported.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_sum`: on
  any manifold, the reading of `P u` in one chart is bounded by the readings of `u` through
  cutoffs adding up to `1` on a compact set depending only on `P` and the chart cutoff.
* `TauCeti.chartSobolevExtension_toChartSobolevSpace_of_mem`: `P` extends to a bounded operator
  `H^s(M) → H^t(M)` for `t ≤ s - m`.
* `TauCeti.isCompactOperator_chartSobolevExtension_of_mem`: the extension is compact for
  `t < s - m`.

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
open scoped ContDiff Manifold Distributions SchwartzMap ENNReal

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  {e e' : OpenPartialHomeomorph M (CoordinateSpace n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Sobolev estimate between two charts.** Let `P` be a classical pseudodifferential
operator of order `m`, `φ` a cutoff in a chart `e` and `ψ` a cutoff in a chart `e'`, with `Ψ` the
smooth function `ψ ∘ e'` on `M`, extended by `0`. For every real `s` and `1 < p < ∞` there is a
constant `C` such that for every smooth `g` on `M`, the reading `φ · (P (Ψ g) ∘ e⁻¹)` of `P (Ψ g)`
in `e` satisfies

`‖φ · (P (Ψ g) ∘ e⁻¹)‖_{H^{s - m,p}} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{H^{s,p}}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (hp : 1 < p) (hp_top : p ≠ ⊤) (s : ℝ) :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) p (e.cutoffPushforwardSchwartz he φ
          (P (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g)))‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s p (e'.cutoffPushforwardSchwartz he' ψ g)‖ :=
  exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le hP
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s p)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs hp hp_top s)
    _ (fun _ ha ↦ let ⟨C, hC⟩ :=
      ha.isUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s hp hp_top
      ⟨C, hC⟩)
    he he' φ ψ

/-- **Sobolev estimate for classical pseudodifferential operators on a manifold.** Let `P` be a
classical pseudodifferential operator of order `m` and `ψᵢ` finitely many cutoffs in charts `e'ᵢ`
whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`, which forces `M` to be
compact. For `1 < p < ∞`, in the norm `∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^{s,p}}`, which defines
`H^{s,p}(M)` up to equivalence of norms, `P` loses `m` orders: for finitely many cutoffs `φⱼ` in
charts `eⱼ` and every real `s` there is a constant `C` such that every smooth `u` on `M` satisfies

`∑ⱼ ‖φⱼ · ((P u) ∘ eⱼ⁻¹)‖_{H^{s - m,p}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^{s,p}}`. -/
theorem exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    {κ : Type*} [Fintype κ]
    {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) (hp : 1 < p) (hp_top : p ≠ ⊤)
    (s : ℝ) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ j, ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) p
          ((e j).cutoffPushforwardSchwartz (he j) (φ j) (P u))‖ ≤
        C * ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s p
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ :=
  exists_sum_norm_cutoffPushforwardSchwartz_apply_le_sum hP
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s p)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs hp hp_top s)
    _ (fun _ ha ↦ let ⟨C, hC⟩ :=
      ha.isUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s hp hp_top
      ⟨C, hC⟩)
    he φ he' ψ hψ

/-- **The Sobolev estimate in one chart, on any manifold.** Let `P` be a properly supported
operator and `φ` a cutoff in a chart `e`. There is a compact set `K ⊆ M` with the following
property. Let `ψᵢ` be finitely many cutoffs in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`,
extended by `0`, add up to `1` on `K`. If `P` is a classical pseudodifferential operator of order
`m`, then for every real `s` and `1 < p < ∞` there is a constant `C` such that every smooth `u` on
`M` satisfies

`‖φ · ((P u) ∘ e⁻¹)‖_{H^{s - m,p}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^{s,p}}`.

The cutoffs `ψᵢ` need only add up to `1` on the compact set `K`, so `M` need not be compact. On a
compact manifold every operator is properly supported
(`TauCeti.isProperlySupported_of_compactSpace`) and cutoffs adding up to `1` everywhere qualify.
The set `K` depends only on `P` and `φ`, not on the order `m`, on `s` or on `p`. -/
theorem IsProperlySupported.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_sum
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : IsProperlySupported P)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ K : Set M, IsCompact K ∧ ∀ {ι : Type*} [Fintype ι]
      {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
      (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ)),
      (∀ x ∈ K, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) →
      ∀ m : ℝ, P ∈ classicalPseudodifferentialOperators m →
      ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ → ∀ s : ℝ, ∃ C,
        ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
          ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) p
              (e.cutoffPushforwardSchwartz he φ (P u))‖ ≤
            C * ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s p
              ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ := by
  -- On `e⁻¹(supp φ)`, `P u` only depends on `u` on a compact set `K`.
  obtain ⟨K, hK, hPK⟩ := hP.exists_isCompact_forall_eqOn (e.isCompact_symm_image_tsupport φ)
  exact ⟨K, hK, fun he' ψ hψ m hPm p _ hp hp_top s ↦
    exists_norm_cutoffPushforwardSchwartz_apply_le_sum hPm
      (SchwartzMap.toBesselPotentialSpaceCLM_injective s p)
      (fun hκ hκ' _ hθ hθc hθs ↦
        BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
          hθc hθs hp hp_top s)
      _ (fun _ ha ↦ let ⟨C, hC⟩ :=
        ha.isUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s hp hp_top
        ⟨C, hC⟩)
      he φ hPK he' ψ hψ⟩

/-! ### Extension to the Sobolev spaces of a compact manifold -/

section Extension

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {ι κ ν : Type*} [Fintype ι] [Fintype κ]
  [Fintype ν] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)}
  {c' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc' : ∀ j, c' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ : ∀ j, 𝓓(⟨(c' j).target, (c' j).open_target⟩, ℝ)} {s t : ℝ}

/-- **The Sobolev estimate in the Hilbert norms of chart readings.** Let `P` be a classical
pseudodifferential operator of order `m` and `ψᵢ` cutoffs in charts `cᵢ` whose readings on `M` add
up to `1`. For any finitely many cutoffs `φⱼ` in charts `c'ⱼ` and real orders `t ≤ s - m` there is a
constant `C` such that every smooth `u` on `M` satisfies

`‖(φⱼ · ((P u) ∘ c'ⱼ⁻¹))ⱼ‖_{⨁ H^t} ≤ C ‖(ψᵢ · (u ∘ cᵢ⁻¹))ᵢ‖_{⨁ H^s}`. -/
theorem exists_norm_chartReading_apply_le (hP : P ∈ classicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) (ht : t ≤ s - m) :
    ∃ C, ∀ u, ‖chartReading hc' φ t (P u)‖ ≤ C * ‖chartReading hc ψ s u‖ := by
  obtain ⟨C, hC⟩ :=
    exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum hP hc' φ hc ψ
      hψ ENNReal.one_lt_two ENNReal.ofNat_ne_top s
  refine ⟨|C| * Real.sqrt (Fintype.card ι), fun u ↦ ?_⟩
  calc ‖chartReading hc' φ t (P u)‖
      ≤ ∑ j, ‖chartReading hc' φ t (P u) j‖ := PiLp.norm_le_sum_norm _
    _ ≤ ∑ j, ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          ((c' j).cutoffPushforwardSchwartz (hc' j) (φ j) (P u))‖ :=
      Finset.sum_le_sum fun j _ ↦ by
        rw [chartReading_apply, ← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM ht]
        exact BesselPotentialSpace.norm_inclusion_apply_le ht _
    _ ≤ |C| * ∑ i, ‖chartReading hc ψ s u i‖ := by
      simp only [chartReading_apply]
      exact (hC u).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
    _ ≤ |C| * (Real.sqrt (Fintype.card ι) * ‖chartReading hc ψ s u‖) :=
      mul_le_mul_of_nonneg_left (PiLp.sum_norm_le_sqrt_card_mul_norm _) (abs_nonneg C)
    _ = |C| * Real.sqrt (Fintype.card ι) * ‖chartReading hc ψ s u‖ := (mul_assoc ..).symm

/-- **Classical pseudodifferential operators act on Sobolev spaces.** On a compact manifold, with
the Sobolev spaces `H^s(M)` of a chart partition `ψᵢ` (`TauCeti.chartSobolevSpace`), a classical
pseudodifferential operator `P` of order `m` extends to a continuous linear map
`H^s(M) → H^t(M)` for every `t ≤ s - m`, `TauCeti.chartSobolevExtension`: the extension agrees with
`P` on smooth functions. -/
theorem chartSobolevExtension_toChartSobolevSpace_of_mem
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) (ht : t ≤ s - m)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevExtension hc ψ hc' φ P s t (toChartSobolevSpace hc ψ s u) =
      toChartSobolevSpace hc' φ t (P u) :=
  chartSobolevExtension_toChartSobolevSpace (exists_norm_chartReading_apply_le hP hψ ht) u

/-- **Operators gaining more than their order are compact.** On a compact manifold, the extension
of a classical pseudodifferential operator `P` of order `m` to `H^s(M) → H^t(M)` is a compact
operator when `t < s - m`: it factors through the compact inclusion `H^{s - m}(M) ⊆ H^t(M)`. In
particular operators of negative order are compact on every `H^s(M)`. -/
theorem isCompactOperator_chartSobolevExtension_of_mem
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) (ht : t < s - m) :
    IsCompactOperator (chartSobolevExtension hc ψ hc' φ P s t) := by
  rw [← chartSobolevInclusion_comp_chartSobolevExtension ht.le
    (exists_norm_chartReading_apply_le hP hψ le_rfl)]
  exact (isCompactOperator_chartSobolevInclusion hc' φ ht).comp_clm _

/-- **Extensions of classical pseudodifferential operators compose.** If `Q` and `P` are classical
pseudodifferential operators of orders `m'` and `m`, with `t ≤ s - m'` and `r ≤ t - m`, then the
extension of `P ∘ Q` to `H^s(M) → H^r(M)` is the extension of `Q` to `H^s(M) → H^t(M)` followed by
that of `P` to `H^t(M) → H^r(M)`. -/
theorem chartSobolevExtension_comp_of_mem {c'' : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
    {hc'' : ∀ k, c'' k ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
    {χ : ∀ k, 𝓓(⟨(c'' k).target, (c'' k).open_target⟩, ℝ)}
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m' r : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators m')
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (ht : t ≤ s - m')
    (hr : r ≤ t - m) :
    chartSobolevExtension hc' φ hc'' χ P t r ∘L chartSobolevExtension hc ψ hc' φ Q s t =
      chartSobolevExtension hc ψ hc'' χ (P ∘ₗ Q) s r :=
  chartSobolevExtension_comp (exists_norm_chartReading_apply_le hP hφ hr)
    (exists_norm_chartReading_apply_le hQ hψ ht)

end Extension

end TauCeti
