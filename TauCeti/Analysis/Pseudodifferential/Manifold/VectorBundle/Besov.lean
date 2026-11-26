/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Besov
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.ChartPatching
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LocalizedChangeOfVariables

/-!
# Hölder–Zygmund and Besov estimates for pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ`, let `E`, `F` be smooth complex vector bundles over `M`
with model fibres `V` (finite-dimensional) and `W`, and let `P : Γ(E) → Γ(F)` be a classical
pseudodifferential operator of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`).
A smooth section `u` of `E` is read in a chart `e'` of the maximal atlas, a trivialization `t` of
`E` and a cutoff `ψ` in the chart target through its frame coefficients
`ψ · (ρ b_k*(t u) ∘ e'⁻¹)`, for a basis `(b_k)` of `V`
(`Bundle.Trivialization.cutoffFrameCoeff`), as for the Sobolev estimates of
`TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Sobolev`.
Following Triebel, a Besov norm of `u` on a compact manifold is
`∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{B^s_{p,q}}` for finitely many charts `e'ᵢ`,
trivializations `tᵢ` and cutoffs `ψᵢ` whose readings `ψᵢ ∘ e'ᵢ` on `M` add up to `1`, the
Euclidean norms being those of the Littlewood–Paley partition of a fixed bump function `β`
(`TauCeti.BesovSpace`). For `p = q = ∞` these are the Hölder–Zygmund norms `𝒞^s = B^s_{∞,∞}`.

This file proves that `P` loses `m` orders on the scale `B^s_{p,∞}`: for every real `s` and
`1 ≤ p ≤ ∞` there is a constant `C` such that

`∑ⱼ ∑ₗ ‖φⱼ · (χⱼ ℓₗ(t'ⱼ (P u)) ∘ eⱼ⁻¹)‖_{B^{s - m}_{p,∞}}`
`  ≤ C ∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}}`

for every smooth section `u` of `E`, where `(eⱼ, t'ⱼ, χⱼ, φⱼ)` is any finite family of charts,
trivializations of `F`, smooth functions `χⱼ` supported in their base sets and cutoffs, and `ℓₗ`
any finite family of functionals on `W`
(`TauCeti.exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`).
For `p = ∞` this is the Zygmund estimate `‖P u‖_{𝒞^{s - m}(F)} ≤ C ‖u‖_{𝒞^s(E)}` on a compact
manifold, for every real `s` and `m`; operators of order `0` need not be bounded on `L^∞`. It is
the bundle form of the scalar estimate
`TauCeti.exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`.

The estimates are instances of the patching theorems of
`TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.ChartPatching` for the source norm
`B^s_{p,∞}` and the target norm `B^{s - m}_{p,∞}`. Their hypotheses hold because the inclusion of
Schwartz functions in `B^s_{p,∞}` is injective (`SchwartzMap.toBesovSpaceCLM_injective`),
localized changes of variables are bounded on `B^s_{p,∞}`
(`TauCeti.BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp`), and `Op(a)` is bounded
`B^s_{p,∞} → B^{s - m}_{p,∞}` for every symbol `a` of order `m` with compact spatial support
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le`).

## Main results

* `TauCeti.exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le`: the
  estimate between two charts.
* `TauCeti.exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`: one
  frame coefficient of `P u`, read in one chart, is bounded in `B^{s - m}_{p,∞}` by the
  `B^s_{p,∞}` norm of `u` for a partition.
* `TauCeti.exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`:
  the Besov estimate `‖P u‖_{B^{s - m}_{p,∞}} ≤ C ‖u‖_{B^s_{p,∞}}` in these norms, in particular
  the Hölder–Zygmund estimate for `p = ∞`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (3.32)–(3.34) (pseudodifferential operators on the Zygmund spaces) and §8.
* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, §7.2 (Besov spaces on manifolds,
  defined through charts and a partition of unity).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (pseudodifferential operators between sections of vector bundles).
-/

public section

noncomputable section

open Bundle Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap ENNReal

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
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

/-- **The Besov estimate between two charts for operators between bundles.** Let `P` be a
classical pseudodifferential operator of order `m` between bundles, `φ` a cutoff in a chart `e`,
`t'` a trivialization of `F` with a cutoff `χ` and `ℓ` a functional on `W`, and `ψ` a cutoff in a
chart `e'`, with `Ψ` the smooth function `ψ ∘ e'` on `M`, extended by `0`. Let `t` be a
trivialization of `E`, `ρ` a smooth function supported in its base set and equal to `1` on
`e'⁻¹(supp ψ)`, and `(b_k)` a basis of `V`. For every real `s` and `1 ≤ p ≤ ∞` there is a
constant `C` such that for every smooth section `u` of `E`,

`‖φ · (χ ℓ(t' (P (Ψ u))) ∘ e⁻¹)‖_{B^{s - m}_{p,∞}} ≤ C ∑ₖ ‖ψ · (ρ b_k*(t u) ∘ e'⁻¹)‖_{B^s_{p,∞}}`.
-/
theorem exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (t' : Trivialization W (π W F))
    [MemTrivializationAtlas t'] (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : tsupport ρ ⊆ t.baseSet)
    (hρψ : ∀ y ∈ tsupport ψ, ρ (e'.symm y) = 1) (b : Module.Basis ι ℂ V)
    (β : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ‖SchwartzMap.toBesovSpaceCLM ℂ β (s - m) p ∞ (e.cutoffPushforwardSchwartz he φ
          (t'.cutoffFrameCoeff χ hχ ℓ (P (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1) • u))))‖ ≤
        C * ∑ k, ‖SchwartzMap.toBesovSpaceCLM ℂ β s p ∞ (e'.cutoffPushforwardSchwartz he' ψ
          (t.cutoffFrameCoeff ρ hρ (b.coord k).toContinuousLinearMap u))‖ :=
  exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le hP
    (SchwartzMap.toBesovSpaceCLM_injective ℂ β s p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs β s p ∞)
    _ (fun _ ha ↦ (ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le β s).imp
      fun _ hA w ↦ hA.2 w)
    he he' φ t' χ hχ ℓ ψ t ρ hρ hρψ b

/-- **The Besov estimate in one chart for operators between bundles.** Let `P` be a classical
pseudodifferential operator of order `m` between bundles, and let `ψᵢ` be finitely many cutoffs in
charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1`, with
trivializations `tᵢ` of `E` and smooth functions `ρᵢ` supported in their base sets and equal to
`1` on `e'ᵢ⁻¹(supp ψᵢ)`. Let `(b_k)` be a basis of `V`. For a cutoff `φ` in a chart `e`, a
trivialization `t'` of `F` with a cutoff `χ`, a functional `ℓ` on `W`, every real `s` and
`1 ≤ p ≤ ∞`, there is a constant `C` such that every smooth section `u` of `E` satisfies

`‖φ · (χ ℓ(t' (P u)) ∘ e⁻¹)‖_{B^{s - m}_{p,∞}}`
`  ≤ C ∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}}`.
-/
theorem exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum
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
    (β : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ‖SchwartzMap.toBesovSpaceCLM ℂ β (s - m) p ∞
          (e.cutoffPushforwardSchwartz he φ (t'.cutoffFrameCoeff χ hχ ℓ (P u)))‖ ≤
        C * ∑ i, ∑ k, ‖SchwartzMap.toBesovSpaceCLM ℂ β s p ∞
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
            ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ :=
  exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum hP
    (SchwartzMap.toBesovSpaceCLM_injective ℂ β s p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs β s p ∞)
    _ (fun _ ha ↦ (ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le β s).imp
      fun _ hA w ↦ hA.2 w)
    he φ t' χ hχ ℓ he' ψ hψ t ρ hρ hρψ b

/-- **Besov and Hölder–Zygmund estimates for classical pseudodifferential operators between
bundles.** Let `P` be a classical pseudodifferential operator of order `m` between bundles, and
let `ψᵢ` be finitely many cutoffs in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended
by `0`, add up to `1`, which forces `M` to be compact, with trivializations `tᵢ` of `E` and smooth
functions `ρᵢ` supported in their base sets and equal to `1` on `e'ᵢ⁻¹(supp ψᵢ)`. Let `(b_k)` be
a basis of `V`. In the norm `∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}}`, `P` loses `m`
orders: for finitely many cutoffs `φⱼ` in charts `eⱼ`, trivializations `t'ⱼ` of `F` with cutoffs
`χⱼ`, finitely many functionals `ℓₗ` on `W`, every real `s` and `1 ≤ p ≤ ∞`, there is a constant
`C` such that every smooth section `u` of `E` satisfies

`∑ⱼ ∑ₗ ‖φⱼ · (χⱼ ℓₗ(t'ⱼ (P u)) ∘ eⱼ⁻¹)‖_{B^{s - m}_{p,∞}}`
`  ≤ C ∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{B^s_{p,∞}}`.

For `p = ∞` these are the Hölder–Zygmund norms `𝒞^s = B^s_{∞,∞}`. -/
theorem exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum
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
    (β : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ∑ j, ∑ l, ‖SchwartzMap.toBesovSpaceCLM ℂ β (s - m) p ∞
          ((e j).cutoffPushforwardSchwartz (he j) (φ j)
            ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ l) (P u)))‖ ≤
        C * ∑ i, ∑ k, ‖SchwartzMap.toBesovSpaceCLM ℂ β s p ∞
          ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
            ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ :=
  exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum hP
    (SchwartzMap.toBesovSpaceCLM_injective ℂ β s p ∞)
    (fun hκ hκ' _ hθ hθc hθs ↦
      BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs β s p ∞)
    _ (fun _ ha ↦ (ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le β s).imp
      fun _ hA w ↦ hA.2 w)
    he φ t' χ hχ ℓ he' ψ hψ t ρ hρ hρψ b

end TauCeti
