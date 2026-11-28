/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.ChartPatching
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.UniformSobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Completion
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables

/-!
# Sobolev estimates for pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ`, let `E`, `F` be smooth complex vector bundles over `M`
with model fibres `V` (finite-dimensional) and `W`, and let `P : Γ(E) → Γ(F)` be a classical
pseudodifferential operator of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`).
A smooth section `u` of `E` is read in a chart `e'` of the maximal atlas, a trivialization `t` of
`E` and a cutoff `ψ` in the chart target through its frame coefficients: for a basis `(b_k)` of
`V` with coordinate functionals `b_k*`, these are the Schwartz functions

`ψ · (b_k*(t u) ∘ e'⁻¹)`

on `ℝⁿ`. Here `b_k*(t u)` is the cut-off frame coefficient `ρ · b_k*(t u)`
(`Bundle.Trivialization.cutoffFrameCoeff`) for a smooth `ρ` supported in the base set of `t` and
equal to `1` on `e'⁻¹(supp ψ)`, so the reading does not depend on `ρ`. Following Taylor, a Sobolev
norm of `u` on a compact manifold is `∑ᵢ ∑ₖ ‖ψᵢ · (b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{H^s}` for finitely many
charts `e'ᵢ`, trivializations `tᵢ` and cutoffs `ψᵢ` whose readings `ψᵢ ∘ e'ᵢ` on `M` add up to
`1`. These are the coordinates of the readings `ψᵢ · (tᵢ u ∘ e'ᵢ⁻¹)` with values in `V`. Such
data, together with the functions `ρᵢ`, exist on every compact manifold
(`TauCeti.exists_sum_cutoffPullback_eq_one_and_baseSet_cutoff`).

This file proves that `P` loses `m` orders in these norms: for every real `s` there is a constant
`C` such that

`∑ⱼ ∑ₗ ‖φⱼ · (χⱼ ℓₗ(t'ⱼ (P u)) ∘ eⱼ⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ∑ₖ ‖ψᵢ · (b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{H^s}`

for every smooth section `u` of `E`, where `(eⱼ, t'ⱼ, χⱼ, φⱼ)` is any finite family of charts,
trivializations of `F`, smooth functions `χⱼ` supported in their base sets and cutoffs, and `ℓₗ`
any finite family of functionals on `W` (the theorem
`exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`).
This is the a priori estimate through which `P` extends to a bounded operator
`H^s(M; E) → H^{s - m}(M; F)`, the starting point of the Fredholm theory of elliptic operators
between bundles on a compact manifold. It is the bundle form of the scalar estimate
`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`.

When `W` is finite-dimensional as well, the same estimate holds for the readings with values in the
model fibres. In a chart `e`, a trivialization `t` of `E` and a cutoff `ψ` with `e⁻¹(supp ψ)` in
the base set of `t`, the section `u` is read as the Schwartz function `y ↦ ψ(y) t(u(e⁻¹ y))` with
values in `V` (`OpenPartialHomeomorph.sectionCutoffPushforwardSchwartz`), and

`∑ⱼ ‖φⱼ · t'ⱼ((P u) ∘ eⱼ⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ‖ψᵢ · tᵢ(u ∘ e'ᵢ⁻¹)‖_{H^s}`

(`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_le_sum`).
Here no auxiliary functions `ρᵢ`, `χⱼ` or functionals enter the statement: the `H^{s,p}` norm of a
reading is comparable with those of its frame coefficients
(`TauCeti.norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le` and
`TauCeti.norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_le_sum`), and the matrix
entries of `P` act on these coefficients
(`TauCeti.cutoffFrameCoeff_map_smul_eq_sum_sectionEntry`).

**Extension to Sobolev spaces.** With `H^s(M; E)` the closure of the chart readings of smooth
sections in the Hilbert sum `⨁ᵢₖ H^s(ℝⁿ)` (`TauCeti.sectionChartSobolevSpace`), the estimate in
its Hilbert norm (`TauCeti.exists_norm_sectionChartReading_apply_le`) makes the continuous extension
`TauCeti.sectionChartSobolevExtension` of `P` to `H^s(M; E) → H^q(M; F)`, `q ≤ s - m`, agree with
`P` on smooth sections (`TauCeti.sectionChartSobolevExtension_toSectionChartSobolevSpace_of_mem`).
These extensions compose (`TauCeti.sectionChartSobolevExtension_comp_of_mem`), and by Rellich's
theorem they are compact when `q < s - m`
(`TauCeti.isCompactOperator_sectionChartSobolevExtension_of_mem`), in particular for operators of
negative order. Applied to the identity, an operator of order `0`, the estimate shows that
`H^s(M; E)` does not depend on the charts, trivializations, cutoffs and basis used to read
sections, up to an isomorphism that is the identity on smooth sections
(`TauCeti.sectionChartSobolevSpaceCongr`).

## The argument

The estimates are instances of the patching theorems of
`TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.ChartPatching` for the source norm
`H^s` and the target norm `H^{s - m}`. Their hypotheses hold because the inclusion of Schwartz
functions in `H^s` is injective (`SchwartzMap.toBesselPotentialSpaceCLM_injective`), localized
changes of variables are bounded on `H^s`
(`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`), and
`Op(a)` is bounded `H^s → H^{s - m}` for every uniform symbol `a` of order `m`
(`TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`).

## Main results

* `exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le`: the
  estimate between two charts.
* `exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`: one
  frame coefficient of `P u`, read in one chart, is bounded in `H^{s - m}` by the `H^s` norm
  of `u` for a partition.
* `exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`:
  the Sobolev estimate `‖P u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}` in these norms. Its left side is such a
  Sobolev norm of `P u` when the `φⱼ ∘ eⱼ` add up to `1`, each `χⱼ` equals `1` on
  `eⱼ⁻¹(supp φⱼ)` and the `ℓₗ` are the coordinate functionals of a basis of `W` (so `W` is
  finite-dimensional). For other data it bounds the readings `φⱼ · (χⱼ ℓₗ(t'ⱼ (P u)) ∘ eⱼ⁻¹)`
  of `P u`, without being a norm of `P u` (for an empty family of `ℓₗ` it is `0`).
* `norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le` and
  `norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_le_sum`: the
  `H^{s,p}` norm of the reading of a section compared with those of its cut-off frame coefficients.
* `exists_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_smul_le`,
  `exists_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_le_sum` and
  `exists_sum_norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_apply_le_sum`: the
  estimates between two charts, in one chart and on `M`, for the readings with values in `V`
  and `W`.
* `sectionChartSobolevExtension_toSectionChartSobolevSpace_of_mem`: `P` extends to a
  bounded operator `H^s(M; E) → H^q(M; F)` for `q ≤ s - m`.
* `isCompactOperator_sectionChartSobolevExtension_of_mem`: the extension is compact for
  `q < s - m`.
* `sectionChartSobolevExtension_comp_of_mem`: extensions compose.
* `sectionChartSobolevSpaceCongr`: the Sobolev spaces of two choices of chart and frame
  data are isomorphic.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces of sections of vector bundles on compact manifolds).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31)
  and §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (pseudodifferential operators between sections of vector bundles).
-/

public section

noncomputable section

open Bundle Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace ENNReal

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯} {m : ℝ}
  {ι : Type*} [Fintype ι]

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
is bounded in `H^{s,p}` by `‖ℓ‖` times the reading `ψ · t(u ∘ e⁻¹)` of `u`. -/
theorem norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le (s : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (ℓ : V →L[ℂ] ℂ) (u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM s p
        (e.cutoffPushforwardSchwartz he ψ (t.cutoffFrameCoeff ρ hρ ℓ u))‖ ≤
      ‖ℓ‖ * ‖SchwartzMap.toBesselPotentialSpaceCLM s p
        (e.sectionCutoffPushforwardSchwartz he t ψ hψ u)‖ := by
  rw [← postcompCLM_sectionCutoffPushforwardSchwartz he t ψ hψ hρ hρψ,
    SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM]
  exact (BesselPotentialSpace.postcomp _ s p ℓ).le_of_opNorm_le
    (BesselPotentialSpace.norm_postcomp_le ℓ) _

include hρψ in
/-- **A section is bounded by its frame coefficients.** For a basis `(cⱼ)` of `V` with coordinate
functionals `cⱼ*`, the reading `ψ · t(u ∘ e⁻¹)` of a section `u` is bounded in `H^{s,p}` by the
readings of its cut-off frame coefficients `ρ cⱼ*(t u)`, for a cutoff `ρ` equal to `1` on
`e⁻¹(supp ψ)`. -/
theorem norm_toBesselPotentialSpaceCLM_sectionCutoffPushforwardSchwartz_le_sum (s : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {κ : Type*} [Fintype κ] (c : Module.Basis κ ℂ V)
    (u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM s p (e.sectionCutoffPushforwardSchwartz he t ψ hψ u)‖ ≤
      ∑ j, ‖ContinuousLinearMap.toSpanSingleton ℂ (c j)‖ *
        ‖SchwartzMap.toBesselPotentialSpaceCLM s p
          (e.cutoffPushforwardSchwartz he ψ
            (t.cutoffFrameCoeff ρ hρ (c.coord j).toContinuousLinearMap u))‖ := by
  rw [← BesselPotentialSpace.sum_postcomp_toSpanSingleton_coord c
    (SchwartzMap.toBesselPotentialSpaceCLM s p _)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
    postcompCLM_sectionCutoffPushforwardSchwartz he t ψ hψ hρ hρψ]
  exact (BesselPotentialSpace.postcomp _ s p _).le_of_opNorm_le
    (BesselPotentialSpace.norm_postcomp_le _) _

end Reading

/-! ### The Sobolev estimates for frame coefficients -/

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **The Sobolev estimate between two charts.** Let `P` be a classical pseudodifferential
operator of order `m` between bundles, `φ` a cutoff in a chart `e`, `t'` a trivialization of `F`
with a cutoff `χ` and `ℓ` a functional on `W`, and `ψ` a cutoff in a chart `e'`, with `Ψ` the
smooth function `ψ ∘ e'` on `M`, extended by `0`. Let `t` be a trivialization of `E`, `ρ` a
smooth function supported in its base set and equal to `1` on `e'⁻¹(supp ψ)`, and `(b_k)` a basis
of `V`. For every real `s` there is a constant `C` such that for every smooth section `u` of `E`,

`‖φ · (χ ℓ(t' (P (Ψ u))) ∘ e⁻¹)‖_{H^{s - m}} ≤ C ∑ₖ ‖ψ · (ρ b_k*(t u) ∘ e'⁻¹)‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (t' : Trivialization W (π W F))
    [MemTrivializationAtlas t'] (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : tsupport ρ ⊆ t.baseSet)
    (hρψ : ∀ y ∈ tsupport ψ, ρ (e'.symm y) = 1) (b : Module.Basis ι ℂ V) (s : ℝ) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (e.cutoffPushforwardSchwartz he φ
          (t'.cutoffFrameCoeff χ hχ ℓ (P (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1) • u))))‖ ≤
        C * ∑ k, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e'.cutoffPushforwardSchwartz he' ψ
          (t.cutoffFrameCoeff ρ hρ (b.coord k).toContinuousLinearMap u))‖ :=
  exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le hP
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s 2)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs ENNReal.one_lt_two ENNReal.ofNat_ne_top s)
    _ (fun a ha ↦ (SchwartzMap.hasSobolevExtension_iff_exists_norm_le.1
      (Symbol.hasSobolevExtension_quantizeUniformCLM a ha.isUniform s)).imp fun _ h ↦ h.2)
    he he' φ t' χ hχ ℓ ψ t ρ hρ hρψ b

/-- **The Sobolev estimate in one chart.** Let `P` be a classical pseudodifferential operator of
order `m` between bundles, and let `ψᵢ` be finitely many cutoffs in charts `e'ᵢ` whose readings
`Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`, with trivializations `tᵢ` of `E` and
smooth functions `ρᵢ` supported in their base sets and equal to `1` on `e'ᵢ⁻¹(supp ψᵢ)`. Let
`(b_k)` be a basis of `V`. For a cutoff `φ` in a chart `e`, a trivialization `t'` of `F` with a
cutoff `χ`, a functional `ℓ` on `W` and every real `s`, there is a constant `C` such that every
smooth section `u` of `E` satisfies

`‖φ · (χ ℓ(t' (P u)) ∘ e⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (t' : Trivialization W (π W F))
    [MemTrivializationAtlas t'] (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ) {κ : Type*} [Fintype κ]
    {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (t : κ → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t i)]
    (ρ : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : ∀ i, tsupport (ρ i) ⊆ (t i).baseSet)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e' i).symm y) = 1) (b : Module.Basis ι ℂ V)
    (s : ℝ) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          (e.cutoffPushforwardSchwartz he φ (t'.cutoffFrameCoeff χ hχ ℓ (P u)))‖ ≤
        C * ∑ i, ∑ k, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
            ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ :=
  exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum hP
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s 2)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs ENNReal.one_lt_two ENNReal.ofNat_ne_top s)
    _ (fun a ha ↦ (SchwartzMap.hasSobolevExtension_iff_exists_norm_le.1
      (Symbol.hasSobolevExtension_quantizeUniformCLM a ha.isUniform s)).imp fun _ h ↦ h.2)
    he φ t' χ hχ ℓ he' ψ hψ t ρ hρ hρψ b

/-- **Sobolev estimate for classical pseudodifferential operators between bundles.** Let `P` be a
classical pseudodifferential operator of order `m` between bundles, and let `ψᵢ` be finitely many
cutoffs in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`,
which forces `M` to be compact, with trivializations `tᵢ` of `E` and smooth functions `ρᵢ`
supported in their base sets and equal to `1` on `e'ᵢ⁻¹(supp ψᵢ)`. Let `(b_k)` be a basis of `V`.
In the norm `∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{H^s}`, `P` loses `m` orders: for finitely
many cutoffs `φⱼ` in charts `eⱼ`, trivializations `t'ⱼ` of `F` with cutoffs `χⱼ`, finitely many
functionals `ℓₗ` on `W` and every real `s`, there is a constant `C` such that every smooth section
`u` of `E` satisfies

`∑ⱼ ∑ₗ ‖φⱼ · (χⱼ ℓₗ(t'ⱼ (P u)) ∘ eⱼ⁻¹)‖_{H^{s - m}} ≤ C ∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{H^s}`.
-/
theorem exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) {ν : Type*} [Fintype ν]
    {e : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) (t' : ν → Trivialization W (π W F))
    [∀ j, MemTrivializationAtlas (t' j)] (χ : ν → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : ∀ j, tsupport (χ j) ⊆ (t' j).baseSet) {μ : Type*} [Fintype μ] (ℓ : μ → W →L[ℂ] ℂ)
    {κ : Type*} [Fintype κ] {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (t : κ → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t i)]
    (ρ : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : ∀ i, tsupport (ρ i) ⊆ (t i).baseSet)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e' i).symm y) = 1) (b : Module.Basis ι ℂ V)
    (s : ℝ) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ∑ j, ∑ l, ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          ((e j).cutoffPushforwardSchwartz (he j) (φ j)
            ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ l) (P u)))‖ ≤
        C * ∑ i, ∑ k, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
            ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ :=
  exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum hP
    (SchwartzMap.toBesselPotentialSpaceCLM_injective s 2)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ
        hθc hθs ENNReal.one_lt_two ENNReal.ofNat_ne_top s)
    _ (fun a ha ↦ (SchwartzMap.hasSobolevExtension_iff_exists_norm_le.1
      (Symbol.hasSobolevExtension_quantizeUniformCLM a ha.isUniform s)).imp fun _ h ↦ h.2)
    he φ t' χ hχ ℓ he' ψ hψ t ρ hρ hρψ b

/-! ### The Sobolev estimates for readings with values in the model fibres -/

section FiberReading

variable [FiniteDimensional ℂ W]

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
        (c.coord j).toContinuousLinearMap) he he' φ ψ ENNReal.one_lt_two ENNReal.ofNat_ne_top s
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
  conv_lhs => rw [ContMDiffSection.eq_sum_ofReal_smul (σ := u) Finset.univ _ (subset_univ _)
    fun x _ ↦ hψ1 x, map_sum, map_sum, map_sum]
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

end FiberReading

/-! ### Extension to the Sobolev spaces of sections over a compact manifold -/

section Extension

variable [FiniteDimensional ℂ W] {κ ν μ : Type*} [Fintype κ] [Fintype ν] [Fintype μ]
  {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)} {t : κ → Trivialization V (π V E)}
  [∀ i, MemTrivializationAtlas (t i)] {ρ : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
  {hρ : ∀ i, tsupport (ρ i) ⊆ (t i).baseSet} {b : Module.Basis ι ℂ V}
  {e' : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
  {he' : ∀ j, e' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ : ∀ j, 𝓓(⟨(e' j).target, (e' j).open_target⟩, ℝ)} {t' : ν → Trivialization W (π W F)}
  [∀ j, MemTrivializationAtlas (t' j)] {χ : ν → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
  {hχ : ∀ j, tsupport (χ j) ⊆ (t' j).baseSet} {b' : Module.Basis μ ℂ W} {s q : ℝ}

/-- **The Sobolev estimate in the Hilbert norms of chart readings.** Let `P` be a classical
pseudodifferential operator of order `m` between bundles, and let `ψᵢ` be cutoffs in charts `eᵢ`
whose readings on `M` add up to `1`, with trivializations `tᵢ` of `E` and functions `ρᵢ` supported
in their base sets and equal to `1` on `eᵢ⁻¹(supp ψᵢ)`. For any finitely many cutoffs `φⱼ` in
charts `e'ⱼ`, trivializations `t'ⱼ` of `F` with cutoffs `χⱼ`, a basis `(b'ₗ)` of `W` and real
orders `q ≤ s - m`, there is a constant `C` such that every smooth section `u` of `E` satisfies

`‖(φⱼ · (χⱼ b'ₗ*(t'ⱼ (P u)) ∘ e'ⱼ⁻¹))ⱼₗ‖_{⨁ H^q} ≤ C ‖(ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ eᵢ⁻¹))ᵢₖ‖_{⨁ H^s}`. -/
theorem exists_norm_sectionChartReading_apply_le
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e i).symm y) = 1) (hq : q ≤ s - m) :
    ∃ C, ∀ u, ‖sectionChartReading he' φ t' χ hχ b' q (P u)‖ ≤
      C * ‖sectionChartReading he ψ t ρ hρ b s u‖ := by
  obtain ⟨C, hC⟩ :=
    exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum hP
      he' φ t' χ hχ (fun l ↦ (b'.coord l).toContinuousLinearMap) he ψ hψ t ρ hρ hρψ b s
  refine PiLp.exists_norm_le_mul_norm_of_sum_norm_le
    (f := fun u ↦ sectionChartReading he' φ t' χ hχ b' q (P u)) (C := C) fun u ↦ ?_
  simp only [sectionChartReading_apply, Fintype.sum_prod_type]
  refine (Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun l _ ↦ ?_).trans (hC u)
  rw [← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hq]
  exact BesselPotentialSpace.norm_inclusion_apply_le hq _

/-- **Pseudodifferential operators between bundles act on Sobolev spaces.** On a compact manifold,
with the Sobolev spaces `H^s(M; E)` of chart and frame data whose cutoffs add up to `1`
(`TauCeti.sectionChartSobolevSpace`), a classical pseudodifferential operator `P : Γ(E) → Γ(F)` of
order `m` extends to a continuous linear map `H^s(M; E) → H^q(M; F)` for every `q ≤ s - m`,
`TauCeti.sectionChartSobolevExtension`: the extension agrees with `P` on smooth sections. -/
theorem sectionChartSobolevExtension_toSectionChartSobolevSpace_of_mem
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e i).symm y) = 1) (hq : q ≤ s - m)
    (u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    sectionChartSobolevExtension he ψ t ρ hρ b he' φ t' χ hχ b' P s q
        (toSectionChartSobolevSpace he ψ t ρ hρ b s u) =
      toSectionChartSobolevSpace he' φ t' χ hχ b' q (P u) :=
  LinearMap.rangeClosureExtension_toRangeClosure
    (exists_norm_sectionChartReading_apply_le hP hψ hρψ hq) u

/-- **Operators gaining more than their order are compact.** On a compact manifold, the extension
of a classical pseudodifferential operator `P : Γ(E) → Γ(F)` of order `m` to
`H^s(M; E) → H^q(M; F)` is a compact operator when `q < s - m`: it factors through the compact
inclusion `H^{s - m}(M; F) ⊆ H^q(M; F)`. In particular operators of negative order are compact
from `H^s(M; E)` to `H^s(M; F)`. -/
theorem isCompactOperator_sectionChartSobolevExtension_of_mem
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e i).symm y) = 1) (hq : q < s - m) :
    IsCompactOperator (sectionChartSobolevExtension he ψ t ρ hρ b he' φ t' χ hχ b' P s q) := by
  rw [sectionChartSobolevExtension, ← LinearMap.rangeClosureMap_comp_rangeClosureExtension
    (piMap_inclusion_sectionChartReading he' φ t' χ hχ b' hq.le)
    (exists_norm_sectionChartReading_apply_le hP hψ hρψ le_rfl)]
  exact (isCompactOperator_sectionChartSobolevInclusion he' φ t' χ hχ b' hq).comp_clm _

/-- **Extensions of pseudodifferential operators between bundles compose.** If `P : Γ(E) → Γ(F)`
and `Q : Γ(F) → Γ(G)` are classical pseudodifferential operators of orders `m` and `m'`, with
`q ≤ s - m` and `r ≤ q - m'`, then the extension of `Q ∘ P` to `H^s(M; E) → H^r(M; G)` is the
extension of `P` to `H^s(M; E) → H^q(M; F)` followed by that of `Q` to `H^q(M; F) → H^r(M; G)`. -/
theorem sectionChartSobolevExtension_comp_of_mem {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [FiniteDimensional ℂ X] {G : M → Type*} [TopologicalSpace (TotalSpace X G)]
    [∀ x, AddCommGroup (G x)] [∀ x, Module ℝ (G x)] [∀ x, Module ℂ (G x)]
    [∀ x, TopologicalSpace (G x)] [FiberBundle X G] [VectorBundle ℝ X G] [VectorBundle ℂ X G]
    [ContMDiffVectorBundle ∞ X G 𝓘(ℝ, CoordinateSpace n)] {ν'' μ'' : Type*} [Fintype ν'']
    [Fintype μ''] {e'' : ν'' → OpenPartialHomeomorph M (CoordinateSpace n)}
    {he'' : ∀ l, e'' l ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
    {ϑ : ∀ l, 𝓓(⟨(e'' l).target, (e'' l).open_target⟩, ℝ)} {t'' : ν'' → Trivialization X (π X G)}
    [∀ l, MemTrivializationAtlas (t'' l)] {σ : ν'' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    {hσ : ∀ l, tsupport (σ l) ⊆ (t'' l).baseSet} {b'' : Module.Basis μ'' ℂ X}
    {Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); X, G⟯}
    {m' r : ℝ} (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators m')
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e i).symm y) = 1)
    (hφ : ∀ x, ∑ j, (e' j).cutoffPullback (he' j) (φ j) 1 x = 1)
    (hχφ : ∀ j, ∀ y ∈ tsupport (φ j), χ j ((e' j).symm y) = 1) (hq : q ≤ s - m)
    (hr : r ≤ q - m') :
    sectionChartSobolevExtension he' φ t' χ hχ b' he'' ϑ t'' σ hσ b'' Q q r ∘L
        sectionChartSobolevExtension he ψ t ρ hρ b he' φ t' χ hχ b' P s q =
      sectionChartSobolevExtension he ψ t ρ hρ b he'' ϑ t'' σ hσ b'' (Q ∘ₗ P) s r :=
  LinearMap.rangeClosureExtension_comp (exists_norm_sectionChartReading_apply_le hQ hφ hχφ hr)
    (exists_norm_sectionChartReading_apply_le hP hψ hρψ hq)

variable (he ψ t ρ hρ b)

/-- **Independence of the charts, frames and cutoffs.** The Sobolev spaces `H^s(M; E)` of two
families of chart and frame data for `E`, whose chart cutoffs add up to `1` and whose frame
cutoffs equal `1` over the chart cutoffs, are isomorphic Banach spaces, through the isomorphism
that is the identity on smooth sections (`LinearMap.rangeClosureCongr_toRangeClosure`). The
estimates both ways are the Sobolev estimate for the identity, a pseudodifferential operator of
order `0`. -/
abbrev sectionChartSobolevSpaceCongr {ν' μ' : Type*} [Fintype ν'] [Fintype μ']
    {e' : ν' → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ j, e' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e' j).target, (e' j).open_target⟩, ℝ)) (t' : ν' → Trivialization V (π V E))
    [∀ j, MemTrivializationAtlas (t' j)] (χ : ν' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : ∀ j, tsupport (χ j) ⊆ (t' j).baseSet) (b' : Module.Basis μ' ℂ V)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e i).symm y) = 1)
    (hφ : ∀ x, ∑ j, (e' j).cutoffPullback (he' j) (φ j) 1 x = 1)
    (hχφ : ∀ j, ∀ y ∈ tsupport (φ j), χ j ((e' j).symm y) = 1) (s : ℝ) :
    sectionChartSobolevSpace he ψ t ρ hρ b s ≃L[ℂ] sectionChartSobolevSpace he' φ t' χ hχ b' s :=
  (sectionChartReading he ψ t ρ hρ b s).rangeClosureCongr (sectionChartReading he' φ t' χ hχ b' s)
    (by
      simpa using exists_norm_sectionChartReading_apply_le (he' := he') (φ := φ) (b' := b')
        id_mem_sectionClassicalPseudodifferentialOperators hψ hρψ (sub_zero s).ge)
    (by
      simpa using exists_norm_sectionChartReading_apply_le (he' := he) (φ := ψ) (b' := b)
        id_mem_sectionClassicalPseudodifferentialOperators hφ hχφ (sub_zero s).ge)

end Extension

end TauCeti
