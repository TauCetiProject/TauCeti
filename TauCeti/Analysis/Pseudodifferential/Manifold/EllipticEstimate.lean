/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich

/-!
# The elliptic estimate on a compact manifold

Let `M` be a compact manifold modelled on `ℝⁿ` and `P` an elliptic classical pseudodifferential
operator of order `m` on `M` (`TauCeti.classicalPseudodifferentialOperators`,
`TauCeti.IsClassicalElliptic`). Read the complex-valued smooth functions `u` on `M` through
finitely many charts `eᵢ` and cutoffs `ψᵢ` whose readings `ψᵢ ∘ eᵢ` on `M` add up to `1`, and
write `‖u‖_s = ∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^s}` for the resulting Sobolev norm, as in
`TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev`.

**The elliptic estimate.** For all real `s` and `r` there is a constant `C` such that

`‖u‖_{s + m} ≤ C (‖P u‖_s + ‖u‖_r)`

for every smooth `u` on `M`
(`IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_le`).
So `P` gains back the `m` orders it loses, up to an arbitrarily weak norm of `u`. Choose `N ∈ ℕ`
with `s + m - N ≤ r` and a parametrix `Q` of order `-m` with `L = Q P - 1` of order `-N`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`).
Then `u = Q (P u) - L u`, and the Sobolev estimate on `M`
(`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`)
bounds `‖Q (P u)‖_{s + m}` by `‖P u‖_s` and `‖L u‖_{s + m}` by `‖u‖_{s + m - N} ≤ ‖u‖_r`.

The lower-order term cannot be dropped: on the circle, `P = -∂²` kills the constant `1`, whose
norm is positive.

**Finite-dimensional kernel.** The smooth solutions of `P u = 0` form a finite-dimensional
space (`TauCeti.IsClassicalElliptic.finiteDimensional_ker`), because on the kernel the estimate
reads `‖u‖_1 ≤ C ‖u‖_0`. A space `V` of smooth functions with `‖u‖_{s'} ≤ C ‖u‖_s` for some
`s < s'` is finite-dimensional
(`TauCeti.finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le`): the readings of the
elements of `V` with `‖u‖_s ≤ 1` are bounded in `H^{s'}` and supported in the fixed compact sets
`tsupport ψᵢ`, so by Rellich's theorem
(`BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq`) they lie in a compact
subset of `H^s`. Embedded into `(H^s)ⁱ` by its readings, `V` thus has a totally bounded unit
ball, and Riesz's theorem (`FiniteDimensional.of_totallyBounded_nhds_zero`) makes it
finite-dimensional. Compactness of `M` is needed: on a disjoint union of countably many
circles the operator `-∂²` is elliptic, and its kernel, the locally constant functions, is
infinite-dimensional.

## Main results

* `IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_le`:
  the elliptic estimate `‖u‖_{s + m} ≤ C (‖P u‖_s + ‖u‖_r)`.
* `TauCeti.finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le`: a space of smooth
  functions on which a Sobolev norm is bounded by a weaker one is finite-dimensional.
* `TauCeti.IsClassicalElliptic.finiteDimensional_ker`: an elliptic classical pseudodifferential
  operator on a compact manifold has a finite-dimensional space of smooth solutions of `P u = 0`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (4.6)–(4.11), and Lecture II, (3.1)–(3.8) (elliptic estimates from a parametrix).
* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §6 (finite-dimensional kernels of elliptic operators on compact manifolds).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.2.
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

/-- **The elliptic estimate on a compact manifold.** Let `P` be an elliptic classical
pseudodifferential operator of order `m` on `M`, and `ψᵢ` finitely many cutoffs in charts `eᵢ`
whose readings `ψᵢ ∘ eᵢ` on `M`, extended by `0`, add up to `1` (so `M` is compact). For all real
`s` and `r` there is a constant `C` such that every smooth `u` on `M` satisfies

`∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^{s + m}}`
`  ≤ C (∑ᵢ ‖ψᵢ · ((P u) ∘ eᵢ⁻¹)‖_{H^s} + ∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^r})`.
-/
theorem IsClassicalElliptic.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_le
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) {ι : Type*} [Fintype ι]
    {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (s r : ℝ) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
          ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖ ≤
        C * (∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
            ((e i).cutoffPushforwardSchwartz (he i) (ψ i) (P u))‖ +
          ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r 2
            ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖) := by
  have := compactSpace_of_sum_cutoffPullback_eq_one he ψ hψ
  -- A parametrix `Q` of order `-m` with `L = Q P - 1` of order `-N`, where `s + m - N ≤ r`.
  set N := ⌈s + m - r⌉₊
  obtain ⟨Q, hQ, -, hL⟩ :=
    hPe.exists_comp_sub_id_mem_classicalPseudodifferentialOperators hP N
  set L := Q ∘ₗ P - LinearMap.id
  have hN : s + m - N ≤ r := by linarith [Nat.le_ceil (s + m - r)]
  -- `Q` gains `m` orders and `L` gains `N` orders.
  obtain ⟨C₁, hC₁⟩ :=
    exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum hQ he ψ he ψ
      hψ s
  obtain ⟨C₂, hC₂⟩ :=
    exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum hL he ψ he ψ
      hψ (s + m - N)
  rw [sub_neg_eq_add] at hC₁
  rw [show s + m - N - -(N : ℝ) = s + m by ring] at hC₂
  refine ⟨max (max C₁ C₂) 0, fun u ↦ ?_⟩
  set K := max (max C₁ C₂) 0
  set A := ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
    ((e i).cutoffPushforwardSchwartz (he i) (ψ i) (P u))‖
  set B := ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r 2
    ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖
  -- The `H^{s + m - N}` norms of the readings are at most their `H^r` norms.
  have hB : ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m - N) 2
      ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖ ≤ B :=
    Finset.sum_le_sum fun i _ ↦ by
      rw [← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hN]
      exact BesselPotentialSpace.norm_inclusion_apply_le hN _
  -- `u = Q (P u) - L u`.
  have hu : u = Q (P u) - L u := by simp [L]
  calc ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
          ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖
      ≤ ∑ i, (‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
            ((e i).cutoffPushforwardSchwartz (he i) (ψ i) (Q (P u)))‖ +
          ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) 2
            ((e i).cutoffPushforwardSchwartz (he i) (ψ i) (L u))‖) :=
        Finset.sum_le_sum fun i _ ↦ by
          conv_lhs => rw [hu, map_sub, map_sub]
          exact norm_sub_le _ _
    _ ≤ K * A + K * B := by
        rw [Finset.sum_add_distrib]
        have hK₁ : C₁ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
        have hK₂ : C₂ ≤ K := (le_max_right _ _).trans (le_max_left _ _)
        have hK : 0 ≤ K := le_max_right _ _
        refine add_le_add ((hC₁ (P u)).trans (mul_le_mul_of_nonneg_right hK₁
          (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))) ((hC₂ u).trans ?_)
        exact (mul_le_mul_of_nonneg_right hK₂ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hB hK)
    _ = K * (A + B) := (mul_add _ _ _).symm

omit [T2Space M] in
/-- A reading `ψ · (u ∘ e⁻¹)` of a function is fixed by multiplication with a Schwartz function
`φ` equal to `1` on the support of `ψ`, also in `H^s`. -/
private theorem smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {φ : 𝓢(CoordinateSpace n, ℂ)}
    (hφ : ∀ y ∈ tsupport ψ, φ y = 1) (s : ℝ) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    BesselPotentialSpace.smulLeftCLM s φ
        (SchwartzMap.toBesselPotentialSpaceCLM s 2 (e.cutoffPushforwardSchwartz he ψ u)) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2 (e.cutoffPushforwardSchwartz he ψ u) := by
  have hφw : SchwartzMap.smulLeftCLM ℂ (φ : CoordinateSpace n → ℂ)
      (e.cutoffPushforwardSchwartz he ψ u) = e.cutoffPushforwardSchwartz he ψ u := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth, cutoffPushforwardSchwartz_apply]
    by_cases hy : ψ y = 0
    · simp [hy]
    · rw [hφ y (subset_tsupport _ hy), one_smul]
  conv_rhs => rw [← hφw]
  exact BesselPotentialSpace.ext (by
    simp [TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq])

/-- **A Rellich theorem on a compact manifold.** Let `ψᵢ` be finitely many cutoffs in charts
`eᵢ` whose readings `ψᵢ ∘ eᵢ` on `M`, extended by `0`, add up to `1`, and let `s < s'`. A space `V`
of smooth functions on `M` on which, for some constant `C`,

`∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^{s'}} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^s}`

is finite-dimensional. -/
theorem finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le {ι : Type*} [Fintype ι]
    {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    {V : Submodule ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {s s' C : ℝ} (hss' : s < s')
    (hV : ∀ u ∈ V, ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s' 2
        ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖ ≤
      C * ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
        ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖) :
    FiniteDimensional ℂ V := by
  classical
  -- The readings `T u = (ψᵢ · (u ∘ eᵢ⁻¹))ᵢ ∈ (H^s)ⁱ` embed `V`.
  let R (t : ℝ) (i : ι) : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      H^{t}(CoordinateSpace n, ℂ) :=
    (SchwartzMap.toBesselPotentialSpaceCLM t 2 : _ →L[ℂ] H^{t}(CoordinateSpace n, ℂ)).toLinearMap
      ∘ₗ (e i).cutoffPushforwardSchwartz (he i) (ψ i)
  let T : V →ₗ[ℂ] ι → H^{s}(CoordinateSpace n, ℂ) := LinearMap.pi (fun i ↦ R s i) ∘ₗ V.subtype
  have hT : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun u hu ↦ Subtype.ext ?_
    refine eq_zero_of_forall_cutoffPushforwardSchwartz_eq_zero he ψ hψ fun i ↦ ?_
    exact (SchwartzMap.toBesselPotentialSpaceCLM_injective s 2).eq_iff.1
      (by simpa [T, R] using congr_fun hu i)
  -- Schwartz functions `φᵢ` equal to `1` on the supports of the `ψᵢ`.
  have hφ (i : ι) : ∃ φ : 𝓢(CoordinateSpace n, ℂ), ∀ y ∈ tsupport (ψ i), φ y = 1 := by
    obtain ⟨φ, -, -, hφ⟩ := (ψ i).hasCompactSupport.isCompact.exists_schwartzMap_cutoff
      isOpen_univ (subset_univ _)
    exact ⟨φ, fun y hy ↦ hφ.self_of_nhdsSet y hy⟩
  choose φ hφ using hφ
  -- The `H^{s'}` readings of the `u ∈ V` with `‖T u‖ ≤ 1` are bounded by `C` times the number of
  -- charts, so by Rellich's theorem their images in `H^s` lie in a compact set.
  set S : ι → Set H^{s'}(CoordinateSpace n, ℂ) := fun i ↦ (fun u : V ↦ R s' i u) '' {u | ‖T u‖ ≤ 1}
  have hS (i : ι) : Bornology.IsBounded (S i) := by
    refine (Metric.isBounded_closedBall (x := 0) (r := max C 0 * Fintype.card ι)).subset ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_closedBall_zero_iff]
    have hle : ∑ j, ‖R s j u‖ ≤ Fintype.card ι := by
      calc ∑ j, ‖R s j u‖ = ∑ j, ‖T u j‖ := by simp [T]
        _ ≤ ∑ _j : ι, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦ (norm_le_pi_norm (T u) j).trans hu
        _ = Fintype.card ι := by simp
    exact (Finset.single_le_sum (f := fun j ↦ ‖R s' j u‖) (fun j _ ↦ norm_nonneg _)
      (Finset.mem_univ i)).trans <| (hV u u.property).trans <| (mul_le_mul_of_nonneg_right
        (le_max_left C 0) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hle (le_max_right C 0))
  have hK : IsCompact (univ.pi fun i ↦ closure
      (BesselPotentialSpace.inclusion hss'.le '' S i : Set H^{s}(CoordinateSpace n, ℂ))) :=
    isCompact_univ_pi fun i ↦
      BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq hss' (hS i)
        (φ := φ i) (by
          rintro _ ⟨u, -, rfl⟩
          exact smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz (he i) (ψ i)
            (hφ i) s' u)
  -- So the range of `T` has a totally bounded closed unit ball, and is finite-dimensional.
  have hW : FiniteDimensional ℂ (LinearMap.range T) := by
    refine .of_totallyBounded_nhds_zero ℂ
      (Metric.closedBall_mem_nhds (0 : LinearMap.range T) one_pos) ?_
    refine (totallyBounded_preimage isUniformEmbedding_subtypeVal.isUniformInducing
      hK.totallyBounded).subset ?_
    rintro ⟨_, u, rfl⟩ hu
    refine fun i _ ↦ subset_closure ⟨R s' i u, ⟨u, by simpa using hu, rfl⟩, ?_⟩
    simp [T, R, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]
  exact Module.Finite.equiv (LinearEquiv.ofInjective T hT).symm

/-- **The kernel of an elliptic operator is finite-dimensional.** On a compact manifold `M`, the
smooth solutions `u` of `P u = 0` of an elliptic classical pseudodifferential operator `P` of
order `m` form a finite-dimensional complex vector space. -/
theorem IsClassicalElliptic.finiteDimensional_ker [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    [CompactSpace M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) : FiniteDimensional ℂ (LinearMap.ker P) := by
  -- Chart cutoffs `ψᵢ` whose readings add up to `1`, and the elliptic estimate with `s + m = 1`
  -- and `r = 0`, which reads `‖u‖_1 ≤ C ‖u‖_0` on the kernel.
  obtain ⟨N, c, ψ, hψ⟩ := isCompact_univ.exists_sum_cutoffPullback_eq_one (M := M)
    (E := CoordinateSpace n)
  have he (i : Fin N) := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    (c i)
  have hψ' (x : M) := hψ x (mem_univ x)
  obtain ⟨C, hC⟩ :=
    hPe.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_le hP he ψ hψ' (1 - m) 0
  rw [sub_add_cancel] at hC
  refine finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le he ψ hψ' zero_lt_one
    (C := C) fun u hu ↦ ?_
  simpa [LinearMap.mem_ker.1 hu] using hC u

end TauCeti
