/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Basic

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

## The argument

The operator `P` is pseudodifferential when its matrix entries in cut-off frames
`f ↦ χ · ℓ(t' (P (f · ρ t⁻¹ v)))` (`TauCeti.sectionEntry`) are scalar classical
pseudodifferential operators of order `m`. If `Ψ = ψ ∘ e'` and `ρ = 1` on the support of `Ψ`,
then

`Ψ u = ∑ₖ (Ψ · ρ b_k*(t u)) · ρ t⁻¹ b_k`

(`Bundle.Trivialization.smul_eq_sum_cutoffFrameCoeff_smul_cutoffFrameSection`),

so the frame coefficient `χ ℓ(t' (P (Ψ u)))` is the sum over `k` of the entries
`f ↦ χ ℓ(t' (P (f · ρ t⁻¹ b_k)))` applied to `Ψ · ρ b_k*(t u)`. The scalar estimate between two
charts (`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le`)
bounds the reading of each term through `φ` in `e` in `H^{s - m}` by the reading
`ψ · (ρ b_k*(t u) ∘ e'⁻¹)` in `H^s`. The estimate for a partition then follows by writing
`u = ∑ᵢ Ψᵢ u`.

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
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace

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
          (t.cutoffFrameCoeff ρ hρ (b.coord k).toContinuousLinearMap u))‖ := by
  -- The scalar estimate for each matrix entry `f ↦ χ ℓ(t' (P (f · ρ t⁻¹ b_k)))`.
  choose C hC using fun k ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_mulLeft_le
      ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 t ρ hρ (b k) t' χ hχ ℓ) he he'
      φ ψ ENNReal.one_lt_two ENNReal.ofNat_ne_top s
  refine ⟨∑ k, |C k|, fun u ↦ ?_⟩
  -- `ρ = 1` wherever `Ψ = ψ ∘ e'` does not vanish.
  have hΨρ (x : M) (hx : e'.cutoffPullback he' ψ 1 x ≠ 0) : ρ x = 1 := by
    obtain ⟨y, hy, rfl⟩ := e'.tsupport_cutoffPullback_subset he' ψ 1 (subset_tsupport _ hx)
    exact hρψ y hy
  rw [t.smul_eq_sum_cutoffFrameCoeff_smul_cutoffFrameSection ρ hρ _ hΨρ b u, map_sum, map_sum,
    map_sum, map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  -- Each term is the `k`-th matrix entry applied to `Ψ · ρ b_k*(t u)`.
  have hentry : t'.cutoffFrameCoeff χ hχ ℓ (P (LinearMap.mulLeft ℂ
      (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1))
      (t.cutoffFrameCoeff ρ hρ (b.coord k).toContinuousLinearMap u) •
        t.cutoffFrameSection ρ hρ (b k))) = sectionEntry t ρ hρ (b k) t' χ hχ ℓ P
      (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1))
        (t.cutoffFrameCoeff ρ hρ (b.coord k).toContinuousLinearMap u)) := by
    ext x
    simp
  rw [hentry]
  refine (hC k _).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (norm_nonneg _))
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ k)

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
            ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ := by
  choose C hC using fun i ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le hP
      he (he' i) φ t' χ hχ ℓ (ψ i) (t i) (ρ i) (hρ i) (hρψ i) b s
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
            ((t i).cutoffFrameCoeff (ρ i) (hρ i) (b.coord k).toContinuousLinearMap u))‖ := by
  choose C hC using fun (j : ν) (l : μ) ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_le_sum hP
      (he j) (φ j) (t' j) (χ j) (hχ j) (ℓ l) he' ψ hψ t ρ hρ hρψ b s
  refine ⟨∑ j, ∑ l, C j l, fun u ↦ ?_⟩
  simp only [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun l _ ↦ hC j l u

end TauCeti
