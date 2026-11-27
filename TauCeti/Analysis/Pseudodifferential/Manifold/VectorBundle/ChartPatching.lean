/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartPatching
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Basic

/-!
# Patching chart estimates for pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ`, let `E`, `F` be smooth complex vector bundles over `M`
with model fibres `V` (finite-dimensional) and `W`, and let `P : Γ(E) → Γ(F)` be a classical
pseudodifferential operator of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`).
A smooth section `u` of `E` is read in a chart `e'` of the maximal atlas, a trivialization `t` of
`E` and a cutoff `ψ` in the chart target through its frame coefficients: for a basis `(b_k)` of
`V` with coordinate functionals `b_k*`, these are the Schwartz functions

`ψ · (ρ b_k*(t u) ∘ e'⁻¹)`

on `ℝⁿ`, where `ρ b_k*(t u)` is the cut-off frame coefficient
(`Bundle.Trivialization.cutoffFrameCoeff`) for a smooth `ρ` supported in the base set of `t` and
equal to `1` on `e'⁻¹(supp ψ)`.

This file patches Euclidean mapping estimates into estimates for `P` in these readings, for an
abstract source norm `‖Ls ·‖` and target norm `‖Lt ·‖` on `𝓢(ℝⁿ, ℂ)`, under the hypotheses of the
scalar patching theorem `TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le`:

* `Ls` is injective;
* every localized change of variables `u ↦ θ · (u ∘ κ)` is bounded in `‖Ls ·‖`;
* for every symbol `a` of order `m` with compact spatial support, `‖Lt (Op(a) w)‖ ≤ A ‖Ls w‖`.

If finitely many cutoffs `ψᵢ` in charts `e'ᵢ`, with trivializations `tᵢ` of `E`, have readings
`ψᵢ ∘ e'ᵢ` on `M` adding up to `1`, then for finitely many target readings
`φⱼ · (χⱼ ℓₗ(t'ⱼ (P u)) ∘ eⱼ⁻¹)` of `P u` there is a constant `C` with

`∑ⱼ ∑ₗ ‖Lt (φⱼ · (χⱼ ℓₗ(t'ⱼ (P u)) ∘ eⱼ⁻¹))‖ ≤ C ∑ᵢ ∑ₖ ‖Ls (ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹))‖`

for every smooth section `u` of `E`
(`TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`). For
`Ls = B^s_{p,∞}` and `Lt = B^{s - m}_{p,∞}` this gives the Besov and Hölder–Zygmund estimates of
`TauCeti.exists_sum_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`, and
for `Ls = H^s` and `Lt = H^{s - m}` the Sobolev estimates of
`TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Sobolev`.

## The argument

The operator `P` is pseudodifferential when its matrix entries in cut-off frames
`f ↦ χ · ℓ(t' (P (f · ρ t⁻¹ v)))` (`TauCeti.sectionEntry`) are scalar classical
pseudodifferential operators of order `m`. If `Ψ = ψ ∘ e'` and `ρ = 1` on the support of `Ψ`,
then

`Ψ u = ∑ₖ (Ψ · ρ b_k*(t u)) · ρ t⁻¹ b_k`

(`Bundle.Trivialization.smul_eq_sum_cutoffFrameCoeff_smul_cutoffFrameSection`), so the frame
coefficient `χ ℓ(t' (P (Ψ u)))` is the sum over `k` of the entries
`f ↦ χ ℓ(t' (P (f · ρ t⁻¹ b_k)))` applied to `Ψ · ρ b_k*(t u)`. The scalar estimate between two
charts bounds the reading of each term. The estimate for a partition then follows by writing
`u = ∑ᵢ Ψᵢ u`.

## Main results

* `TauCeti.exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le`: the estimate between
  two charts.
* `TauCeti.exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`: one frame coefficient
  of `P u`, read in one chart, is bounded in `‖Lt ·‖` by the `‖Ls ·‖` norms of the readings of `u`
  for a partition.
* `TauCeti.exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum`: the same for
  finitely many readings of `P u`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (pseudodifferential operators between sections of vector bundles).
-/

public section

noncomputable section

open Bundle Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap

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
  {X Y Gs Gt : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [SeminormedAddCommGroup Y]
  [NormedSpace ℂ Y] [FunLike Gs 𝓢(CoordinateSpace n, ℂ) X] [FunLike Gt 𝓢(CoordinateSpace n, ℂ) Y]
  [LinearMapClass Gs ℂ 𝓢(CoordinateSpace n, ℂ) X] [LinearMapClass Gt ℂ 𝓢(CoordinateSpace n, ℂ) Y]

/-- **Patching between two charts for operators between bundles.** Let `P` be a classical
pseudodifferential operator of order `m` between bundles, and let `Ls`, `Lt` satisfy the
hypotheses of the scalar estimate `TauCeti.exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le`.
Let `φ` be a cutoff in a chart `e`, `t'` a trivialization of `F` with a cutoff `χ` and `ℓ` a
functional on `W`, and `ψ` a cutoff in a chart `e'`, with `Ψ` the smooth function `ψ ∘ e'` on
`M`, extended by `0`. Let `t` be a trivialization of `E`, `ρ` a smooth function supported in its
base set and equal to `1` on `e'⁻¹(supp ψ)`, and `(b_k)` a basis of `V`. There is a constant `C`
such that for every smooth section `u` of `E`,

`‖Lt (φ · (χ ℓ(t' (P (Ψ u))) ∘ e⁻¹))‖ ≤ C ∑ₖ ‖Ls (ψ · (ρ b_k*(t u) ∘ e'⁻¹))‖`. -/
theorem exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {Ls : Gs} (hLs : Function.Injective Ls)
    (hcov : ∀ {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)},
      ContDiffOn ℝ ∞ κ κ.source → ContDiffOn ℝ ∞ κ.symm κ.target →
      ∀ {θ : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ κ.source → ∃ C, ∀ u v : 𝓢(CoordinateSpace n, ℂ),
          (∀ x, v x = θ x • u (κ x)) → ‖Ls v‖ ≤ C * ‖Ls u‖)
    (Lt : Gt) (hq : ∀ a : Symbol n ℂ ℂ m, ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Ls w‖)
    {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (t' : Trivialization W (π W F))
    [MemTrivializationAtlas t'] (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : tsupport ρ ⊆ t.baseSet)
    (hρψ : ∀ y ∈ tsupport ψ, ρ (e'.symm y) = 1) (b : Module.Basis ι ℂ V) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ‖Lt (e.cutoffPushforwardSchwartz he φ
          (t'.cutoffFrameCoeff χ hχ ℓ (P (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1) • u))))‖ ≤
        C * ∑ k, ‖Ls (e'.cutoffPushforwardSchwartz he' ψ
          (t.cutoffFrameCoeff ρ hρ (b.coord k).toContinuousLinearMap u))‖ := by
  -- The scalar estimate for each matrix entry `f ↦ χ ℓ(t' (P (f · ρ t⁻¹ b_k)))`.
  choose C hC using fun k ↦
    exists_norm_cutoffPushforwardSchwartz_apply_mulLeft_le
      ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 t ρ hρ (b k) t' χ hχ ℓ) hLs
      hcov Lt hq he he' φ ψ
  refine ⟨∑ k, |C k|, fun u ↦ ?_⟩
  -- `ρ = 1` wherever `Ψ = ψ ∘ e'` does not vanish.
  have hΨρ (x : M) (hx : e'.cutoffPullback he' ψ 1 x ≠ 0) : ρ x = 1 := by
    obtain ⟨y, hy, rfl⟩ := e'.tsupport_cutoffPullback_subset he' ψ 1 (subset_tsupport _ hx)
    exact hρψ y hy
  rw [t.smul_eq_sum_cutoffFrameCoeff_smul_cutoffFrameSection ρ hρ _ hΨρ b u, map_sum, map_sum,
    map_sum, map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  -- Each term is the `k`-th matrix entry applied to `Ψ · ρ b_k*(t u)`.
  rw [← sectionEntry_apply_eq_cutoffFrameCoeff]
  refine (hC k _).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (norm_nonneg _))
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ k)

/-- **Patching in one chart for operators between bundles.** Let `P`, `Ls` and `Lt` be as in
`TauCeti.exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le`, and let `ψᵢ` be finitely
many cutoffs in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to
`1`, with trivializations `tᵢ` of `E` and smooth functions `ρᵢ` supported in their base sets and
equal to `1` on `e'ᵢ⁻¹(supp ψᵢ)`. Let `(b_k)` be a basis of `V`. For a cutoff `φ` in a chart `e`,
a trivialization `t'` of `F` with a cutoff `χ` and a functional `ℓ` on `W`, there is a constant
`C` such that every smooth section `u` of `E` satisfies

`‖Lt (φ · (χ ℓ(t' (P u)) ∘ e⁻¹))‖ ≤ C ∑ᵢ ∑ₖ ‖Ls (ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹))‖`. -/
theorem exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {Ls : Gs} (hLs : Function.Injective Ls)
    (hcov : ∀ {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)},
      ContDiffOn ℝ ∞ κ κ.source → ContDiffOn ℝ ∞ κ.symm κ.target →
      ∀ {θ : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ κ.source → ∃ C, ∀ u v : 𝓢(CoordinateSpace n, ℂ),
          (∀ x, v x = θ x • u (κ x)) → ‖Ls v‖ ≤ C * ‖Ls u‖)
    (Lt : Gt) (hq : ∀ a : Symbol n ℂ ℂ m, ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Ls w‖)
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
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e' i).symm y) = 1) (b : Module.Basis ι ℂ V) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ‖Lt (e.cutoffPushforwardSchwartz he φ (t'.cutoffFrameCoeff χ hχ ℓ (P u)))‖ ≤
        C * ∑ i, ∑ k, ‖Ls ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
          ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ := by
  choose C hC using fun i ↦
    exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le hP hLs hcov Lt hq he (he' i) φ
      t' χ hχ ℓ (ψ i) (t i) (ρ i) (hρ i) (hρψ i) b
  refine ⟨∑ i, |C i|, fun u ↦ ?_⟩
  -- `u = ∑ᵢ Ψᵢ u`, and each piece is estimated in the chart `e'ᵢ`.
  have hu : u = ∑ i, ContMDiffMap.ofReal ((e' i).cutoffPullback (he' i) (ψ i) 1) • u := by
    ext x
    simp [ContMDiffSection.smul_apply_of_normedAlgebra, ← Finset.sum_smul, ← Complex.ofReal_sum,
      hψ x]
  conv_lhs => rw [hu, map_sum, map_sum, map_sum, map_sum]
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (hC i u).trans ?_)
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (Finset.single_le_sum
    (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i)))
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- **Patching chart estimates for operators between bundles.** Let `P`, `Ls` and `Lt` be as in
`TauCeti.exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le`, and let `ψᵢ` be finitely
many cutoffs in charts `e'ᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to
`1`, which forces `M` to be compact, with trivializations `tᵢ` of `E` and smooth functions `ρᵢ`
supported in their base sets and equal to `1` on `e'ᵢ⁻¹(supp ψᵢ)`. Let `(b_k)` be a basis of `V`.
For finitely many cutoffs `φⱼ` in charts `eⱼ`, trivializations `t'ⱼ` of `F` with cutoffs `χⱼ` and
finitely many functionals `ℓₗ` on `W`, there is a constant `C` such that every smooth section `u`
of `E` satisfies

`∑ⱼ ∑ₗ ‖Lt (φⱼ · (χⱼ ℓₗ(t'ⱼ (P u)) ∘ eⱼ⁻¹))‖ ≤ C ∑ᵢ ∑ₖ ‖Ls (ψᵢ · (ρᵢ b_k*(tᵢ u) ∘ e'ᵢ⁻¹))‖`. -/
theorem exists_sum_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {Ls : Gs} (hLs : Function.Injective Ls)
    (hcov : ∀ {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)},
      ContDiffOn ℝ ∞ κ κ.source → ContDiffOn ℝ ∞ κ.symm κ.target →
      ∀ {θ : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ κ.source → ∃ C, ∀ u v : 𝓢(CoordinateSpace n, ℂ),
          (∀ x, v x = θ x • u (κ x)) → ‖Ls v‖ ≤ C * ‖Ls u‖)
    (Lt : Gt) (hq : ∀ a : Symbol n ℂ ℂ m, ∀ ha : a.HasCompactSpatialSupport, ∃ A,
      ∀ w, ‖Lt (Symbol.quantizeUniformCLM a ha.isUniform w)‖ ≤ A * ‖Ls w‖)
    {ν : Type*} [Fintype ν] {e : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
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
    (hρψ : ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((e' i).symm y) = 1) (b : Module.Basis ι ℂ V) :
    ∃ C, ∀ u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
      ∑ j, ∑ l, ‖Lt ((e j).cutoffPushforwardSchwartz (he j) (φ j)
          ((t' j).cutoffFrameCoeff (χ j) (hχ j) (ℓ l) (P u)))‖ ≤
        C * ∑ i, ∑ k, ‖Ls ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i)
          ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ := by
  choose C hC using fun (j : ν) (l : μ) ↦
    exists_norm_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum hP hLs hcov Lt hq (he j) (φ j)
      (t' j) (χ j) (hχ j) (ℓ l) he' ψ hψ t ρ hρ hρψ b
  refine ⟨∑ j, ∑ l, C j l, fun u ↦ ?_⟩
  simp only [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun l _ ↦ hC j l u

end TauCeti
