/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.ChartQuantization
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp

/-!
# Sobolev estimates for pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ`, let `E` and `F` be smooth complex vector bundles over `M`
with finite-dimensional model fibres `V` and `W`, and let `P : Γ(E) → Γ(F)` be a classical
pseudodifferential operator of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`).
A smooth section `u` of `E` is read in a chart `e` of the maximal atlas and a trivialization `t`
of `E` through a cutoff `ψ` with compact support in the chart target, such that `e⁻¹(supp ψ)` lies
in the base set of `t`, as the Schwartz function `y ↦ ψ(y) t(u(e⁻¹ y))` with values in `V`
(`OpenPartialHomeomorph.sectionCutoffPushforwardSchwartz`). For finitely many charts `e'ᵢ`,
trivializations `tᵢ` and cutoffs `ψᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M` add up to `1`, the
sum `∑ᵢ ‖ψᵢ · tᵢ(u ∘ e'ᵢ⁻¹)‖_{H^s}` is a Sobolev norm of the sections of `E` over the compact
manifold `M`, as in Taylor. This file proves that `P` loses `m` orders in these norms: for every
real `s` there is a constant `C` such that

`∑ⱼ ‖φⱼ · t'ⱼ((P u) ∘ eⱼ⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ‖ψᵢ · tᵢ(u ∘ e'ᵢ⁻¹)‖_{H^s}`

for every smooth section `u` of `E`, where `(eⱼ, t'ⱼ, φⱼ)` is any finite family of charts,
trivializations of `F` and cutoffs
(`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_le_sum`).
This is the bundle form of the scalar estimate
`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`, and the
a priori estimate through which `P` extends to a bounded operator `H^s(M; E) → H^{s - m}(M; F)`.

## The argument

The estimate reduces to the scalar one through the matrix entries of `P`
(`TauCeti.sectionEntry`), which are scalar classical pseudodifferential operators of order `m` by
the definition of the class. Fix a basis `(bₖ)` of `V`, a basis `(cⱼ)` of `W`, and smooth functions
`ρ` and `ρ'` on `M`, supported in the base sets of `t` and `t'` and equal to `1` on `e'⁻¹(supp ψ)`
and `e⁻¹(supp φ)`.

* The `W`-valued reading of `P u` is `∑ⱼ cⱼ (cⱼ* ∘ reading)`, and its coordinate `cⱼ*` is the scalar
  reading of the cut-off frame coefficient `ρ' cⱼ*(t' (P u))`
  (`OpenPartialHomeomorph.postcompCLM_sectionCutoffPushforwardSchwartz`). Applying a continuous
  linear map to the values is bounded on `H^s` (`BesselPotentialSpace.norm_postcomp_le`).
* On the section side, `Ψ u` is `∑ₖ (Ψ gₖ) ρ t⁻¹ bₖ` with the scalar coefficients
  `gₖ = ρ bₖ*(t u)`, so the coefficient `ρ' cⱼ*(t' (P (Ψ u)))` is `∑ₖ Aⱼₖ (Ψ gₖ)` for the entries
  `Aⱼₖ : f ↦ ρ' cⱼ*(t' (P (f ρ t⁻¹ bₖ)))` of `P`
  (`TauCeti.cutoffFrameCoeff_map_smul_eq_sum_sectionEntry`).
* The scalar estimate between two charts
  (`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le`)
  bounds the reading of `Aⱼₖ (Ψ gₖ)` by that of `gₖ`, which is the coordinate `bₖ*` of the reading
  of `u`.

Summing over a partition `∑ᵢ Ψᵢ = 1` gives the estimate in one chart, and summing over the target
charts gives the full estimate.

## Main results

* `TauCeti.norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le` and
  `TauCeti.norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_le_sum`: the `H^s` norm
  of the reading of a section compared with those of its cut-off frame coefficients.
* `TauCeti.exists_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_smul_le`:
  the estimate between two charts.
* `TauCeti.exists_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_le_sum`: the
  reading of `P u` in one chart is bounded in `H^{s - m}` by the `H^s` norm of `u` for a partition.
* `TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_le_sum`:
  the Sobolev estimate `‖P u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}` in these norms.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces of sections of vector bundles over compact manifolds).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31)
  and §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (pseudodifferential operators between sections of vector bundles).
-/

public section

noncomputable section

open Bundle Set TauCeti
open scoped ContDiff Distributions Manifold SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯} {m : ℝ}

namespace TauCeti

open OpenPartialHomeomorph

/-! ### Readings of sections and of their frame coefficients -/

section Reading

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
  (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hψ : e.symm '' tsupport ψ ⊆ t.baseSet)
  {ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} (hρ : tsupport ρ ⊆ t.baseSet)
  (hρψ : ∀ y ∈ tsupport ψ, ρ (e.symm y) = 1)

include hρψ in
/-- **A frame coefficient is bounded by the section.** The reading `ψ · (g ∘ e⁻¹)` of the cut-off
frame coefficient `g = ρ ℓ(t u)` of a section `u`, for a cutoff `ρ` equal to `1` on `e⁻¹(supp ψ)`,
is bounded in `H^s` by `‖ℓ‖` times the reading `ψ · t(u ∘ e⁻¹)` of `u`. -/
theorem norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le (s : ℝ)
    (ℓ : V →L[ℂ] ℂ) (u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
        (e.cutoffPushforwardSchwartz he ψ (t.cutoffFrameCoeff ρ hρ ℓ u))‖ ≤
      ‖ℓ‖ * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
        (e.sectionCutoffPushforwardSchwartz he t ψ hψ u)‖ := by
  rw [← postcompCLM_sectionCutoffPushforwardSchwartz he t ψ hψ hρ hρψ,
    SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM]
  exact (BesselPotentialSpace.postcomp _ s 2 ℓ).le_of_opNorm_le
    (BesselPotentialSpace.norm_postcomp_le ℓ) _

include hρψ in
/-- **A section is bounded by its frame coefficients.** For a basis `(cⱼ)` of `V` with coordinate
functionals `cⱼ*`, the reading `ψ · t(u ∘ e⁻¹)` of a section `u` is bounded in `H^s` by the
readings of its cut-off frame coefficients `ρ cⱼ*(t u)`, for a cutoff `ρ` equal to `1` on
`e⁻¹(supp ψ)`. -/
theorem norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_le_sum (s : ℝ)
    {κ : Type*} [Fintype κ] (c : Module.Basis κ ℂ V) (u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e.sectionCutoffPushforwardSchwartz he t ψ hψ u)‖ ≤
      ∑ j, ‖ContinuousLinearMap.toSpanSingleton ℂ (c j)‖ *
        ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
          (e.cutoffPushforwardSchwartz he ψ
            (t.cutoffFrameCoeff ρ hρ (c.coord j).toContinuousLinearMap u))‖ := by
  rw [← BesselPotentialSpace.sum_postcomp_toSpanSingleton_coord c
    (SchwartzMap.toBesselPotentialSpaceCLM s 2 _)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
    postcompCLM_sectionCutoffPushforwardSchwartz he t ψ hψ hρ hρψ]
  exact (BesselPotentialSpace.postcomp _ s 2 _).le_of_opNorm_le
    (BesselPotentialSpace.norm_postcomp_le _) _

end Reading

/-! ### The Sobolev estimates -/

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **The Sobolev estimate between two charts.** Let `P : Γ(E) → Γ(F)` be a classical
pseudodifferential operator of order `m` between bundles, `φ` a cutoff in a chart `e` with
`e⁻¹(supp φ)` in the base set of a trivialization `t'` of `F`, and `ψ` a cutoff in a chart `e'`
with `e'⁻¹(supp ψ)` in the base set of a trivialization `t` of `E`; let `Ψ` be the smooth function
`ψ ∘ e'` on `M`, extended by `0`. For every real `s` there is a constant `C` such that for every
smooth section `u` of `E`, the reading `φ · t'(P (Ψ u) ∘ e⁻¹)` of `P (Ψ u)` satisfies

`‖φ · t'(P (Ψ u) ∘ e⁻¹)‖_{H^{s - m}} ≤ C ‖ψ · t(u ∘ e'⁻¹)‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_smul_le
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hφ : e.symm '' tsupport φ ⊆ t'.baseSet)
    {e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) (hψ : e'.symm '' tsupport ψ ⊆ t.baseSet) (s : ℝ) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (e.sectionCutoffPushforwardSchwartz he t' φ
          hφ (P (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1) • u)))‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
          (e'.sectionCutoffPushforwardSchwartz he' t ψ hψ u)‖ := by
  obtain ⟨ρ', hρ', hρ'φ⟩ := e.exists_tsupport_subset_eq_one he φ t'.open_baseSet hφ
  obtain ⟨ρ, hρ, hρψ⟩ := e'.exists_tsupport_subset_eq_one he' ψ t.open_baseSet hψ
  set b := Module.finBasis ℂ V
  set c := Module.finBasis ℂ W
  set Ψ := ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)
  -- The scalar estimate for each matrix entry `Aⱼₖ : f ↦ ρ' cⱼ*(t' (P (f ρ t⁻¹ bₖ)))`; the
  -- constants are replaced by `max (C j k) 0` below.
  choose C hC using fun j k ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le
      ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 t ρ hρ (b k) t' ρ' hρ'
        (c.coord j).toContinuousLinearMap) he he' φ ψ s
  simp only [LinearMap.mulLeft_apply] at hC
  refine ⟨∑ j, ∑ k, ‖ContinuousLinearMap.toSpanSingleton ℂ (c j)‖ * max (C j k) 0 *
    ‖(b.coord k).toContinuousLinearMap‖, fun u ↦ ?_⟩
  -- `ρ = 1` on the support `e'⁻¹(supp ψ)` of `Ψ`.
  have hρΨ (x : M) (hx : x ∈ tsupport (e'.cutoffPullback he' ψ 1)) : ρ x = 1 := by
    rw [tsupport_cutoffPullback_one] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hρψ y hy
  set R := SchwartzMap.toBesselPotentialSpaceCLM s 2
    (e'.sectionCutoffPushforwardSchwartz he' t ψ hψ u)
  -- The coefficient `ρ' cⱼ*(t' (P (Ψ u)))` is `∑ₖ Aⱼₖ (Ψ gₖ)` with `gₖ = ρ bₖ*(t u)`, and the
  -- reading of `gₖ` is bounded by that of `u`.
  have hj (j) : ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (e.cutoffPushforwardSchwartz he φ
      (t'.cutoffFrameCoeff ρ' hρ' (c.coord j).toContinuousLinearMap (P (Ψ • u))))‖ ≤
      ∑ k, max (C j k) 0 * (‖(b.coord k).toContinuousLinearMap‖ * ‖R‖) := by
    rw [cutoffFrameCoeff_map_smul_eq_sum_sectionEntry t ρ hρ t' ρ' hρ' _ P hρΨ b, map_sum, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ (hC j k _).trans ?_)
    gcongr
    · exact le_max_left _ _
    · exact norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le he' t ψ
        hψ hρ hρψ s _ u
  -- Expand the reading of `P (Ψ u)` in the basis `(cⱼ)` of `W`.
  refine (norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_le_sum he t' φ hφ hρ'
    hρ'φ (s - m) c _).trans ?_
  calc ∑ j, ‖ContinuousLinearMap.toSpanSingleton ℂ (c j)‖ *
        ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (e.cutoffPushforwardSchwartz he φ
          (t'.cutoffFrameCoeff ρ' hρ' (c.coord j).toContinuousLinearMap (P (Ψ • u))))‖
      ≤ ∑ j, ‖ContinuousLinearMap.toSpanSingleton ℂ (c j)‖ *
          ∑ k, max (C j k) 0 * (‖(b.coord k).toContinuousLinearMap‖ * ‖R‖) := by
        gcongr with j
        exact hj j
    _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- **The Sobolev estimate in one chart.** Let `P : Γ(E) → Γ(F)` be a classical pseudodifferential
operator of order `m` between bundles, and let `ψᵢ` be finitely many cutoffs in charts `e'ᵢ`, with
`e'ᵢ⁻¹(supp ψᵢ)` in the base set of a trivialization `tᵢ` of `E`, whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on
`M`, extended by `0`, add up to `1`. For a cutoff `φ` in a chart `e` with `e⁻¹(supp φ)` in the base
set of a trivialization `t'` of `F`, and every real `s`, there is a constant `C` such that every
smooth section `u` of `E` satisfies

`‖φ · t'((P u) ∘ e⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ‖ψᵢ · tᵢ(u ∘ e'ᵢ⁻¹)‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_le_sum
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hφ : e.symm '' tsupport φ ⊆ t'.baseSet)
    {ι : Type*} [Fintype ι] {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t : ι → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t i)]
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ i, (e' i).symm '' tsupport (ψ i) ⊆ (t i).baseSet)
    (hψ1 : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) (s : ℝ) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          (e.sectionCutoffPushforwardSchwartz he t' φ hφ (P u))‖ ≤
        C * ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
          ((e' i).sectionCutoffPushforwardSchwartz (he' i) (t i) (ψ i) (hψ i) u)‖ := by
  choose C hC using fun i ↦
    exists_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_smul_le hP he
      t' φ hφ (he' i) (t i) (ψ i) (hψ i) s
  refine ⟨∑ i, max (C i) 0, fun u ↦ ?_⟩
  -- `u = ∑ᵢ Ψᵢ u`.
  have hu : u = ∑ i, ContMDiffMap.ofReal ((e' i).cutoffPullback (he' i) (ψ i) 1) • u := by
    rw [← Finset.sum_smul, ← map_sum]
    ext x
    rw [ContMDiffSection.smul_apply_of_normedAlgebra, ContMDiffMap.ofReal_apply,
      ContMDiffMap.coe_sum, Finset.sum_apply, hψ1 x, Complex.ofReal_one, one_smul]
  conv_lhs => rw [hu, map_sum, map_sum, map_sum]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ hC i u).trans ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  gcongr
  · exact le_max_left _ _
  · exact Finset.single_le_sum (f := fun i ↦ ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
      ((e' i).sectionCutoffPushforwardSchwartz (he' i) (t i) (ψ i) (hψ i) u)‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)

/-- **Sobolev estimate for classical pseudodifferential operators between vector bundles.** Let
`P : Γ(E) → Γ(F)` be a classical pseudodifferential operator of order `m` between bundles, and let
`ψᵢ` be finitely many cutoffs in charts `e'ᵢ`, with `e'ᵢ⁻¹(supp ψᵢ)` in the base set of a
trivialization `tᵢ` of `E`, whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`,
which forces `M` to be compact. In the norm `∑ᵢ ‖ψᵢ · tᵢ(u ∘ e'ᵢ⁻¹)‖_{H^s}` of the sections of `E`,
`P` loses `m` orders: for finitely many cutoffs `φⱼ` in charts `eⱼ`, with `eⱼ⁻¹(supp φⱼ)` in the
base set of a trivialization `t'ⱼ` of `F`, and every real `s` there is a constant `C` such that
every smooth section `u` of `E` satisfies

`∑ⱼ ‖φⱼ · t'ⱼ((P u) ∘ eⱼ⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ‖ψᵢ · tᵢ(u ∘ e'ᵢ⁻¹)‖_{H^s}`. -/
theorem exists_sum_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_le_sum
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {κ : Type*} [Fintype κ] {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t' : κ → Trivialization W (π W F)) [∀ j, MemTrivializationAtlas (t' j)]
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ))
    (hφ : ∀ j, (e j).symm '' tsupport (φ j) ⊆ (t' j).baseSet)
    {ι : Type*} [Fintype ι] {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t : ι → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t i)]
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ i, (e' i).symm '' tsupport (ψ i) ⊆ (t i).baseSet)
    (hψ1 : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) (s : ℝ) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ∑ j, ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          ((e j).sectionCutoffPushforwardSchwartz (he j) (t' j) (φ j) (hφ j) (P u))‖ ≤
        C * ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
          ((e' i).sectionCutoffPushforwardSchwartz (he' i) (t i) (ψ i) (hψ i) u)‖ := by
  choose C hC using fun j ↦
    exists_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_le_sum hP (he j)
      (t' j) (φ j) (hφ j) he' t ψ hψ hψ1 s
  exact ⟨∑ j, C j, fun u ↦
    (Finset.sum_le_sum fun j _ ↦ hC j u).trans_eq (Finset.sum_mul _ _ _).symm⟩

end TauCeti
