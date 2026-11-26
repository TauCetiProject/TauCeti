/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Sobolev.BesselPotential.Subsingleton
import TauCeti.Geometry.Manifold.IsManifold.MaximalAtlas
import TauCeti.Geometry.Manifold.Sobolev.ChartReading

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

The core is an estimate between two charts
(`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le`): the
reading through `φ` in a chart `e` of `P (Ψ g)`, where `Ψ` is a cutoff `ψ` in a second chart `e'`
read on `M`, is bounded in `H^{s - m}` by the reading `ψ · (g ∘ e'⁻¹)` of `g` in `H^s`.

* A partition of unity `ρₖ` on `e'⁻¹(supp ψ)` splits `Ψ g` into pieces `ρₖ Ψ g`, where each `ρₖ`
  is supported in the source of a chart `Eₖ` agreeing with `e` over the support of `φ`
  (`IsCompact.exists_smoothPartition_mem_maximalAtlas_eqOn_symm`). Such charts exist because the
  maximal atlas contains every chart, including charts whose domain is a disjoint union of two
  coordinate balls.
* In the chart `Eₖ`, the reading of `P (ρₖ Ψ g)` through `φ` is a chart compression of `P`
  applied to the reading `Wₖ` of `ρₖ Ψ g` in `Eₖ`. So it is `Op(aₖ) Wₖ` for a classical symbol
  `aₖ` of order `m` with compact spatial support, and
  `‖Op(aₖ) Wₖ‖_{H^{s - m}} ≤ C ‖Wₖ‖_{H^s}` (`TauCeti.Symbol.quantizeSobolev`).
* The reading `Wₖ` in `Eₖ` is `θₖ · (w ∘ κₖ)` for the reading `w = ψ · (g ∘ e'⁻¹)` in `e'`, the
  transition map `κₖ = e' ∘ Eₖ⁻¹` and a cutoff `θₖ` with compact support in the source of `κₖ`
  (`OpenPartialHomeomorph.overlapCutoff`). Such changes of chart are bounded on `H^s`
  (`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`).

The estimate for a partition `ψᵢ` then follows by writing `u = ∑ᵢ Ψᵢ u`.

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

open Filter Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology BesselPotentialSpace

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}

/-- **One chart.** In a chart `E` that agrees with `e` over the support of `φ`, reading `P` from
`E` through a cutoff `χ` to `e` through `φ` is a chart compression of `P`, hence a quantization
`Op(a)` with `a` of compact spatial support, bounded `H^s → H^{s - m}`. -/
private theorem exists_norm_cutoffPushforwardSchwartz_apply_complexCutoffPullback_le
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (hP : P ∈ classicalPseudodifferentialOperators m)
    {E : OpenPartialHomeomorph M (CoordinateSpace n)}
    (hE : E ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hφE : tsupport φ ⊆ E.target)
    (hEe : EqOn E.symm e.symm (tsupport φ)) (χ : 𝓓(⟨E.target, E.open_target⟩, ℝ)) (s : ℝ) :
    ∃ A, 0 ≤ A ∧ ∀ w : 𝓢(CoordinateSpace n, ℂ),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (e.cutoffPushforwardSchwartz he φ
          (P (E.complexCutoffPullback hE χ (ContMDiffMap.ofContDiff w (w.smooth ⊤)))))‖ ≤
        A * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 w‖ := by
  let φ' : 𝓓(⟨E.target, E.open_target⟩, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφE⟩
  have hφ' : (φ' : CoordinateSpace n → ℝ) = φ := (rfl)
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 E hE φ' χ
  -- `Op(a) w` is the reading of `P (χ w ∘ E)` through `φ` in `e`, since `E⁻¹ = e⁻¹` on the
  -- support of `φ`.
  have hread (w : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n) :
      quantizeSchwartzValue a.toSymbol.coefficient w y = e.cutoffPushforwardSchwartz he φ
        (P (E.complexCutoffPullback hE χ (ContMDiffMap.ofContDiff w (w.smooth ⊤)))) y := by
    rw [ha, complexChartCompression_def, LinearMap.comp_apply, LinearMap.comp_apply,
      complexCutoffPushforward_congr hE he hφ' hEe, complexCutoffPushforward_apply,
      cutoffPushforwardSchwartz_apply]
  have ha' := hasCompactSpatialSupport_of_eq_complexChartCompression hE ha
  refine ⟨‖a.toSymbol.quantizeSobolev ha' s‖, norm_nonneg _, fun w ↦ ?_⟩
  have h := ha'.quantizeSobolev_toBesselPotentialSpaceCLM s w
  rw [show (ha'.hasCompactSupport_quantizeSchwartzValue w).toSchwartzMap
      (a.toSymbol.contDiff_quantizeSchwartzValue w) = e.cutoffPushforwardSchwartz he φ _ from
    SchwartzMap.ext (hread w)] at h
  rw [← h]
  exact (a.toSymbol.quantizeSobolev ha' s).le_opNorm _

/-- **The estimate between two charts in dimension zero.** There `Ψ g` is the pullback of its
reading `w = ψ · (g ∘ e'⁻¹)`, through a cutoff equal to `1` on the support of `ψ`, so the reading
of `P (Ψ g)` in `e` is homogeneous in `w`. -/
private theorem exists_norm_cutoffPushforwardSchwartz_le_of_dim_eq_zero (hn : n = 0)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) (s r : ℝ) :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM r 2 (e.cutoffPushforwardSchwartz he φ
          (P (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g)))‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e'.cutoffPushforwardSchwartz he' ψ g)‖ := by
  obtain ⟨ψ₁, hψ₁, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨e'.target, e'.open_target⟩) (n := ⊤) ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  have hcw (c : ℂ) (w : 𝓢(CoordinateSpace n, ℂ)) : ContMDiffMap.ofContDiff (c • w)
      ((c • w).smooth ⊤) = c • ContMDiffMap.ofContDiff w (w.smooth ⊤) := by
    ext
    simp
  have : Subsingleton (CoordinateSpace n) := by
    subst hn
    exact ⟨fun x y ↦ PiLp.ext fun i ↦ i.elim0⟩
  obtain ⟨C, hC⟩ := SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_le_of_subsingleton
    (p := 2) (q := 2) (T := fun w ↦ e.cutoffPushforwardSchwartz he φ
      (P (e'.complexCutoffPullback he' ψ₁ (ContMDiffMap.ofContDiff w (w.smooth ⊤)))))
    (fun c w ↦ by simp only [hcw, map_smul]) s r
  refine ⟨C, fun g ↦ ?_⟩
  rw [mulLeft_ofReal_cutoffPullback_one_eq_complexCutoffPullback he'
    fun y hy ↦ hψ₁.self_of_nhdsSet y hy]
  exact hC _

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
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e'.cutoffPushforwardSchwartz he' ψ g)‖ := by
  classical
  rcases eq_or_ne n 0 with hn | hn
  · exact exists_norm_cutoffPushforwardSchwartz_le_of_dim_eq_zero hn he he' φ ψ s (s - m)
  have : NeZero n := ⟨hn⟩
  -- A partition of unity `ρ k` on `e'⁻¹(supp ψ)`, with `ρ k` supported in the source of a chart
  -- `E k` agreeing with `e` over the support of `φ`; `ρ k` is the cutoff `τ k` read on `M`, and
  -- `χ k = 1` on the support of `τ k`.
  obtain ⟨ι, _, ρ, E, hρ1, hE⟩ :=
    (e'.isCompact_symm_image_tsupport ψ).exists_smoothPartition_mem_maximalAtlas_eqOn_symm
      he φ.hasCompactSupport.isCompact φ.tsupport_subset
  choose hEa hρc hρE hφE hEe using hE
  choose τ hτ using fun k ↦ (E k).exists_cutoffPullback_one_eq (hEa k) (hρc k) (hρE k)
  choose χ hχ using fun k ↦ TestFunction.exists_eventually_eq_one
    (Ω := ⟨(E k).target, (E k).open_target⟩) (n := ⊤) (τ k).hasCompactSupport.isCompact
    (τ k).tsupport_subset
  choose A hA0 hA using fun k ↦ exists_norm_cutoffPushforwardSchwartz_apply_complexCutoffPullback_le
    he hP (hEa k) φ (hφE k) (hEe k) (χ k) s
  choose B hB using fun k ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le (hEa k) he' (τ k) ψ s
  refine ⟨∑ k, A k * B k, fun g ↦ ?_⟩
  set G := LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g with hGdef
  -- `G` is supported in `e'⁻¹(supp ψ)`, where the `ρ k` add up to `1`.
  have hG : G = ∑ k,
      LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ((E k).cutoffPullback (hEa k) (τ k) 1)) G := by
    simp only [hτ]
    refine ContMDiffMap.eq_sum_mulLeft_ofReal _ ρ (fun p hp ↦ ?_) hρ1
    refine tsupport_cutoffPullback_subset he' ψ 1 (subset_tsupport _ fun h ↦ hp ?_)
    simp [hGdef, h]
  rw [hG, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [mulLeft_ofReal_cutoffPullback_one_eq_complexCutoffPullback (hEa k)
    fun y hy ↦ (hχ k).1.self_of_nhdsSet y hy, mul_assoc]
  exact (hA k _).trans (mul_le_mul_of_nonneg_left (hB k g) (hA0 k))

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
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ := by
  choose C hC using fun i ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le hP he (he' i) φ
      (ψ i) s
  refine ⟨∑ i, |C i|, fun u ↦ ?_⟩
  -- `u = ∑ᵢ Ψᵢ u`, and each piece is estimated in the chart `eᵢ`.
  have hu : u = ∑ i,
      LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ((e' i).cutoffPullback (he' i) (ψ i) 1)) u :=
    ContMDiffMap.eq_sum_mulLeft_ofReal _ _ (subset_univ _) fun x _ ↦ hψ x
  conv_lhs => rw [hu, map_sum, map_sum, map_sum]
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (hC i u).trans ?_)
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (Finset.single_le_sum
    (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i))) (norm_nonneg _)

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
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ := by
  choose C hC using fun j ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum hP (he j) (φ j) he'
      ψ hψ s
  exact ⟨∑ j, C j, fun u ↦ (Finset.sum_le_sum fun j _ ↦ hC j u).trans_eq (Finset.sum_mul ..).symm⟩

end TauCeti
