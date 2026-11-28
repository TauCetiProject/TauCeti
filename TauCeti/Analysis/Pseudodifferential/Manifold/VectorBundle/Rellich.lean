/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Sobolev
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Geometry.Manifold.Sobolev.ChartReading

/-!
# Rellich compactness for pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and let `E`, `F` be smooth complex vector bundles over `M`
with model fibres `V` (finite-dimensional) and `W`. A smooth section `u` of `E` is read in charts
`e'ᵢ`, trivializations `tᵢ` of `E` and cutoffs `ψᵢ` through its frame coefficients: for a basis
`(b_k)` of `V`, these are the Schwartz functions `ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)` on `ℝⁿ`, where
`ρᵢ` is a smooth function supported in the base set of `tᵢ` and equal to `1` on
`e'ᵢ⁻¹(supp ψᵢ)`. When the readings `ψᵢ ∘ e'ᵢ` of the cutoffs on `M` add up to `1`, which forces
`M` to be compact, `∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{H^s}` is a norm on the smooth sections,
defining the Sobolev space `H^s(M; E)` up to equivalence: a section all of whose readings vanish
is zero (`TauCeti.eq_zero_of_forall_cutoffPushforwardSchwartz_cutoffFrameCoeff_eq_zero`), since
over a point where `ψᵢ ∘ e'ᵢ` does not vanish its readings in the `i`-th chart are, up to a
nonzero factor, the coordinates of `tᵢ u` in the basis `(b_k)`.

This file proves the compactness statements of the Sobolev theory of pseudodifferential operators
between bundles on a compact manifold. They are the bundle forms of the scalar statements in
`TauCeti.Analysis.Pseudodifferential.Manifold.Rellich`.

* **Rellich's theorem for pseudodifferential operators.** If `P : Γ(E) → Γ(F)` is a classical
  pseudodifferential operator of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`)
  and `r < s - m`, the readings `φⱼ · (χⱼ ℓⱼ(t'ⱼ (P u)) ∘ eⱼ⁻¹)` in `H^r` of `P u`, over the
  sections `u` of `H^s` norm at most `B`, form a relatively compact set
  (`isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff`).
  Indeed `P` maps them to a bounded set of readings in `H^{s - m}`
  (`exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`),
  all supported in the fixed compact set `supp φⱼ`, and such sets are relatively compact in `H^r`
  (`isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_of_norm_le`).
  For `m < 0` and `r = s` this says that an operator of negative order is compact from
  `H^s(M; E)` to `H^s(M; F)`, on smooth sections.
* **Eigenspaces of operators of negative order are finite-dimensional.** If `M` is compact and
  `R : Γ(E) → Γ(E)` has negative order, then for `μ ≠ 0` the eigenspace `{u | R u = μ u}` is
  finite-dimensional
  (`TauCeti.finiteDimensional_eigenspace_of_mem_sectionClassicalPseudodifferentialOperators`).
  With the readings in `H⁰` as coordinates, the ball of radius `2` of the eigenspace lies in the
  image under `μ⁻¹ R` of a bounded set, which is relatively compact by Rellich's theorem, and a
  vector space with an injective linear map into a normed space sending a ball into a totally
  bounded set is finite-dimensional (`FiniteDimensional.of_injective_of_totallyBounded`, from
  Riesz's theorem).
* **Operators with a left parametrix have finite-dimensional kernels.** If `M` is compact and
  `Q ∘ P - 1` has negative order for some `Q : Γ(F) → Γ(E)`, the kernel of `P : Γ(E) → Γ(F)` is
  finite-dimensional
  (`TauCeti.finiteDimensional_ker_of_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators`),
  since it lies in the eigenspace of `1 - Q ∘ P` at `1`. This is how the kernel of an elliptic
  operator `P` of order `m` is shown to be finite-dimensional, with `Q` a parametrix of order `-m`
  for which `Q ∘ P - 1` has order `-1`.

## Main results

* `isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff`:
  Rellich's theorem for a classical pseudodifferential operator of order `m` between bundles on a
  compact manifold, from `H^s` to `H^r` for `r < s - m`.
* `TauCeti.finiteDimensional_eigenspace_of_mem_sectionClassicalPseudodifferentialOperators`: the
  eigenspaces of an operator of negative order at nonzero eigenvalues are finite-dimensional.
* `TauCeti.finiteDimensional_ker_of_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators`:
  an operator with a left inverse modulo negative order has a finite-dimensional kernel.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces of sections of vector bundles on compact manifolds and Rellich's theorem).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §§4 and 8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 and Theorem 19.2.1.
-/

public section

noncomputable section

open Bundle Filter Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology BesselPotentialSpace

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {m : ℝ}

/-- **Rellich's theorem for pseudodifferential operators between bundles.** Let `P` be a classical
pseudodifferential operator of order `m` from `E` to `F`, and let `ψᵢ` be finitely many cutoffs in
charts `e'ᵢ` whose readings `ψᵢ ∘ e'ᵢ` on `M` add up to `1`, with trivializations `tᵢ` of `E` and
smooth functions `ρᵢ` supported in their base sets and equal to `1` on `e'ᵢ⁻¹(supp ψᵢ)`, and let
`(b_k)` be a basis of `V`. Let `φⱼ` be cutoffs in charts `eⱼ`, `t'ⱼ` trivializations of `F` with
cutoffs `χⱼ`, and `ℓⱼ` functionals on `W`. For `r < s - m`, the readings
`(φⱼ · (χⱼ ℓⱼ(t'ⱼ (P u)) ∘ eⱼ⁻¹))ⱼ` in `H^r` of the sections `P u` with
`∑ᵢ ∑ₖ ‖ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹)‖_{H^s} ≤ B` form a set with compact closure. For `m < 0`,
`r = s` and `E = F`, with the readings of `P u` taken in the same charts, frames and cutoffs as
those of `u`, this is the compactness of `P` on smooth sections in the `H^s` norm. -/
theorem isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff
    {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) {ν : Type*}
    {e : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) (t' : ν → Trivialization W (π W F))
    [∀ j, MemTrivializationAtlas (t' j)] (χ : ν → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : ∀ j, tsupport (χ j) ⊆ (t' j).baseSet) (ℓ : ν → W →L[ℂ] ℂ)
    {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (t : κ → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t i)]
    (ρ : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : ∀ i, tsupport (ρ i) ⊆ (t i).baseSet)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e' i).symm y) = 1) (b : Module.Basis ι ℂ V)
    {r s : ℝ} (hrs : r < s - m) (B : ℝ) :
    IsCompact (closure ((fun u j ↦ SchwartzMap.toBesselPotentialSpaceCLM r 2
        ((e j).cutoffPushforwardSchwartz (he j) (φ j)
          ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ j) (P u)))) ''
      {u | ∑ i, ∑ k, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
        ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
          ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ ≤ B})) :=
  -- The readings of `P u` in `H^{s - m}` are bounded by those of `u` in `H^s`.
  isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_of_norm_le he φ
    (fun j u ↦ (t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ j) (P u))
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    (fun j ↦ exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum
      hP (he j) (φ j) (t' j) (χ j) (hχ j) (ℓ j) he' ψ hψ t ρ hρ hρψ b s) hrs B

omit [Fintype ι] in
/-- Eigenspaces of operators of negative order are finite-dimensional, for given chart cutoffs and
frames: the readings in `H⁰` are coordinates on the eigenspace in which its ball of radius `2` is
relatively compact. -/
private theorem finiteDimensional_eigenspace_of_sum_cutoffPullback_eq_one [Finite ι]
    {R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m) (hm : m < 0) {μ : ℂ} (hμ : μ ≠ 0)
    {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1)
    (t : κ → Trivialization V (π V E)) [∀ i, MemTrivializationAtlas (t i)]
    (ρ : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : ∀ i, tsupport (ρ i) ⊆ (t i).baseSet)
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e' i).symm y) = 1) (b : Module.Basis ι ℂ V) :
    FiniteDimensional ℂ (Module.End.eigenspace R μ) := by
  cases nonempty_fintype ι
  -- `u = R' u` on the eigenspace, for the operator `R' = μ⁻¹ R` of order `m`.
  have hRu (u : Module.End.eigenspace R μ) : (μ⁻¹ • R) u = u := by
    rw [LinearMap.smul_apply, Module.End.mem_eigenspace_iff.1 u.property, inv_smul_smul₀ hμ]
  -- The readings in `H⁰`, indexed by a chart and a basis vector, as coordinates on the eigenspace.
  let L : Module.End.eigenspace R μ →ₗ[ℂ] κ × ι → H^{(0 : ℝ)}(CoordinateSpace n, ℂ) :=
    (LinearMap.pi fun p ↦ (SchwartzMap.toBesselPotentialSpaceCLM 0 2 :
        𝓢(CoordinateSpace n, ℂ) →L[ℂ] H^{(0 : ℝ)}(CoordinateSpace n, ℂ)).toLinearMap ∘ₗ
      (e' p.1).cutoffPushforwardSchwartz (he' p.1) (ψ p.1) ∘ₗ
        (t p.1).cutoffFrameCoeff (ρ p.1) (hρ p.1) (b.coord p.2).toContinuousLinearMap) ∘ₗ
      (Module.End.eigenspace R μ).subtype
  have hLapply (u : Module.End.eigenspace R μ) (p : κ × ι) :
      L u p = SchwartzMap.toBesselPotentialSpaceCLM 0 2
        ((e' p.1).cutoffPushforwardSchwartz (he' p.1) (ψ p.1)
          ((t p.1).cutoffFrameCoeff (ρ p.1) (hρ p.1) (b.coord p.2).toContinuousLinearMap u)) :=
    rfl
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun u hu ↦ Subtype.ext ?_
    refine eq_zero_of_forall_cutoffPushforwardSchwartz_cutoffFrameCoeff_eq_zero he' ψ hψ t ρ hρ
      hρψ b fun i k ↦ (SchwartzMap.toBesselPotentialSpaceCLM_injective 0 2) ?_
    rw [← hLapply u (i, k), hu, Pi.zero_apply, map_zero]
  -- The readings of `R' u` for `u` in a bounded set have compact closure, by Rellich's theorem.
  let T := (fun u (p : κ × ι) ↦ SchwartzMap.toBesselPotentialSpaceCLM 0 2
      ((e' p.1).cutoffPushforwardSchwartz (he' p.1) (ψ p.1)
        ((t p.1).cutoffFrameCoeff (ρ p.1) (hρ p.1) (b.coord p.2).toContinuousLinearMap
          ((μ⁻¹ • R) u)))) ''
    {u | ∑ i, ∑ k, ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2
      ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
        ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ ≤
      ∑ _i : κ, ∑ _k : ι, (2 : ℝ)}
  have hT : IsCompact (closure T) :=
    isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff
      (Submodule.smul_mem _ μ⁻¹ hR) (fun p : κ × ι ↦ he' p.1) (fun p ↦ ψ p.1) (fun p ↦ t p.1)
      (fun p ↦ ρ p.1) (fun p ↦ hρ p.1) (fun p ↦ (b.coord p.2).toContinuousLinearMap) he' ψ hψ t ρ
      hρ hρψ b (r := 0) (s := 0) (by linarith) (∑ _i : κ, ∑ _k : ι, (2 : ℝ))
  -- So `L` sends the `u` with `‖L u‖ < 2` into `T`, a totally bounded set.
  refine .of_injective_of_totallyBounded hL hT.totallyBounded two_pos fun u hu ↦
    subset_closure ⟨u, ?_, funext fun p ↦ by simp only [hRu u, hLapply]⟩
  rw [Set.mem_ofPred_eq]
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k _ ↦ ?_
  rw [← hLapply u (i, k)]
  exact (norm_le_pi_norm (L u) (i, k)).trans hu.le

/-- **Eigenspaces of operators of negative order are finite-dimensional.** If `R` is a classical
pseudodifferential operator of negative order `m` on the smooth sections of a bundle `E` with
finite-dimensional fibres over a compact manifold, then for every nonzero `μ` the smooth sections
`u` with `R u = μ u` form a finite-dimensional complex vector space, as for compact operators. -/
theorem finiteDimensional_eigenspace_of_mem_sectionClassicalPseudodifferentialOperators
    [CompactSpace M]
    {R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m) (hm : m < 0) {μ : ℂ} (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (Module.End.eigenspace R μ) := by
  -- Cutoffs `ψᵢ` in charts whose readings on `M` add up to `1`, adapted to `E`.
  obtain ⟨N, c, ψ, ρ, hψ, hρ, hρψ⟩ :=
    exists_sum_cutoffPullback_eq_one_and_baseSet_cutoff (EM := CoordinateSpace n) (M := M)
      (F := V) (V := E)
  exact finiteDimensional_eigenspace_of_sum_cutoffPullback_eq_one hR hm hμ
    (fun i ↦ IsManifold.chart_mem_maximalAtlas (c i)) ψ hψ (fun i ↦ trivializationAt V E (c i))
    ρ hρ hρψ (Module.finBasis ℂ V)

omit [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)] in
/-- **An operator with a left parametrix has a finite-dimensional kernel.** Let `P` be a linear
operator from the smooth sections of `E` to those of `F`, over a compact manifold. If some
`Q : Γ(F) → Γ(E)` inverts `P` on the left up to a classical pseudodifferential operator of negative
order, that is `Q ∘ P - 1` has negative order, then the smooth sections `u` with `P u = 0` form a
finite-dimensional complex vector space. For an elliptic `P` of order `m`, a parametrix `Q` of
order `-m`, for which `Q ∘ P - 1` has order `-1`, is such an operator. -/
theorem finiteDimensional_ker_of_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators
    [CompactSpace M]
    {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    {Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}
    (hQP : Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators m) (hm : m < 0) :
    FiniteDimensional ℂ (LinearMap.ker P) := by
  -- The kernel lies in the eigenspace of `1 - Q P`, of order `m`, at `1`.
  have hR : LinearMap.id - Q ∘ₗ P ∈ sectionClassicalPseudodifferentialOperators m := by
    simpa using neg_mem hQP
  have := finiteDimensional_eigenspace_of_mem_sectionClassicalPseudodifferentialOperators hR hm
    one_ne_zero
  have hle : LinearMap.ker P ≤ Module.End.eigenspace (LinearMap.id - Q ∘ₗ P) 1 := fun u hu ↦
    Module.End.mem_eigenspace_iff.2 (by simp [LinearMap.mem_ker.1 hu])
  exact Submodule.finiteDimensional_of_le hle

end TauCeti
