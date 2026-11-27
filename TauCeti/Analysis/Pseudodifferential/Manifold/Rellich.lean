/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Adjoint
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich
import TauCeti.Geometry.Manifold.Sobolev.ChartReading

/-!
# Rellich compactness and finite-dimensional kernels on a compact manifold

Let `M` be a manifold modelled on `ℝⁿ`. A complex-valued smooth function `u` on `M` is read in a
chart `e` of the maximal atlas through a cutoff `ψ` as the Schwartz function `ψ · (u ∘ e⁻¹)`
(`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). For finitely many charts `e'ᵢ` and cutoffs
`ψᵢ` whose readings `Ψᵢ = ψᵢ ∘ e'ᵢ` on `M` add up to `1`, which exist on a compact manifold
(`IsCompact.exists_sum_cutoffPullback_eq_one`), the sum `∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^s}` is a norm
defining `H^s(M)` up to equivalence, as in Taylor. It is a norm on the smooth functions: a function
all of whose readings vanish is zero, since `u = ∑ᵢ Ψᵢ u`
(`OpenPartialHomeomorph.eq_zero_of_forall_cutoffPushforwardSchwartz_eq_zero`).

**Rellich's theorem for pseudodifferential operators.** If `P` is a classical pseudodifferential
operator of order `m` (`TauCeti.classicalPseudodifferentialOperators`) and `r < s - m`, the readings
`(φⱼ · ((P u) ∘ eⱼ⁻¹))ⱼ` in `H^r`, for finitely many cutoffs `φⱼ` in charts `eⱼ`, of the functions
`P u` with `∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^s}` bounded form a relatively compact set
(`TauCeti.isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz`). Indeed
`P` maps them to a bounded set of readings in `H^{s - m}`
(`TauCeti.exists_sum_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum`), all
supported in the fixed compact set `supp φⱼ`, and such sets are relatively compact in `H^r` by
Rellich's theorem for a common compact support
(`BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq`). For `m < 0` and
`r = s` this says that operators of negative order are compact from `H^s(M)` to `H^s(M)`, on
smooth functions.

**Eigenspaces and kernels are finite-dimensional.** If `M` is compact and `R` has negative order,
then for `μ ≠ 0` the eigenspace `{u | R u = μ u}` is finite-dimensional
(`TauCeti.finiteDimensional_eigenspace_of_mem_classicalPseudodifferentialOperators`), as for a
compact operator. With the readings in `H⁰` as coordinates, the ball of radius `2` of the
eigenspace lies in the image under `μ⁻¹ R` of a bounded set, which is relatively compact by
Rellich's theorem, and a topological vector space with a totally bounded neighbourhood of `0` is
finite-dimensional (`FiniteDimensional.of_totallyBounded_nhds_zero`, Riesz's theorem).

If `P` is elliptic (`TauCeti.IsClassicalElliptic`), the functions `u` with `P u = 0` form a
finite-dimensional space (`TauCeti.IsClassicalElliptic.finiteDimensional_ker`): for a parametrix
`Q` of `P`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`), the
operator `1 - Q P` has order `-1` and fixes the kernel of `P`. A properly supported formal adjoint
of `P` is elliptic as well (`TauCeti.isClassicalElliptic_iff_of_forall_integral_inner_eq`), so its
kernel is also finite-dimensional
(`TauCeti.IsClassicalElliptic.finiteDimensional_ker_of_forall_integral_inner_eq`). The finiteness
of the kernel is one half of the Fredholm property of an elliptic operator on a compact manifold;
the other half concerns the range of its extension to the Sobolev spaces of `M`.

## Main results

* `TauCeti.isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz`: Rellich's
  theorem for a classical pseudodifferential operator of order `m` on a compact manifold, from
  `H^s` to `H^r` for `r < s - m`.
* `TauCeti.finiteDimensional_eigenspace_of_mem_classicalPseudodifferentialOperators`: the
  eigenspaces of an operator of negative order at nonzero eigenvalues are finite-dimensional.
* `TauCeti.IsClassicalElliptic.finiteDimensional_ker`: the kernel of an elliptic classical
  pseudodifferential operator on the smooth functions of a compact manifold is finite-dimensional.
* `TauCeti.IsClassicalElliptic.finiteDimensional_ker_of_forall_integral_inner_eq`: so is the
  kernel of a properly supported formal adjoint.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds and Rellich's theorem).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Theorem 19.2.1 (elliptic operators on compact manifolds are Fredholm).
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology BesselPotentialSpace

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **Rellich's theorem for pseudodifferential operators on a compact manifold.** Let `P` be a
classical pseudodifferential operator of order `m`, `φⱼ` finitely many cutoffs in charts `eⱼ`, and
`ψᵢ` finitely many cutoffs in charts `e'ᵢ` whose readings `ψᵢ ∘ e'ᵢ` on `M` add up to `1`. For
`r < s - m`, the readings `(φⱼ · ((P u) ∘ eⱼ⁻¹))ⱼ` in `H^r` of the functions `P u` with
`∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^s} ≤ B` form a set with compact closure. For `m < 0`, `r = s` and
`φ = ψ`, this is the compactness of `P`, on smooth functions, in the chart-reading `H^s` norm. -/
theorem isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz
    (hP : P ∈ classicalPseudodifferentialOperators m) {κ : Type*}
    {e : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ)) {ι : Type*} [Fintype ι]
    {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) {r s : ℝ} (hrs : r < s - m)
    (B : ℝ) :
    IsCompact (closure ((fun u j ↦ SchwartzMap.toBesselPotentialSpaceCLM r 2
        ((e j).cutoffPushforwardSchwartz (he j) (φ j) (P u))) ''
      {u | ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
        ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ ≤ B})) := by
  set U := {u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ | ∑ i,
    ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖
      ≤ B}
  choose C hC using fun j ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_apply_le_sum hP (he j) (φ j)
      he' ψ hψ ENNReal.one_lt_two ENNReal.ofNat_ne_top s
  -- The readings of `P u` in `H^{s - m}`, for `u ∈ U`, in the chart `eⱼ`, are bounded.
  let S (j : κ) : Set H^{s - m}(CoordinateSpace n, ℂ) := (fun u ↦
    SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 ((e j).cutoffPushforwardSchwartz (he j) (φ j)
      (P u))) '' U
  have hS (j : κ) : Bornology.IsBounded (S j) := by
    refine isBounded_iff_forall_norm_le.2 ⟨|C j| * B, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h0 : 0 ≤ ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
        ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖ :=
      Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    exact (hC j u).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) h0).trans
      (mul_le_mul_of_nonneg_left hu (abs_nonneg _)))
  choose χ hχ using fun j ↦
    exists_smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz (he j) (φ j)
  have hK (j : κ) : IsCompact (closure (BesselPotentialSpace.inclusion hrs.le '' S j)) :=
    BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq hrs (hS j)
      (φ := χ j) (by rintro _ ⟨u, -, rfl⟩; exact hχ j _ _)
  refine (isCompact_univ_pi hK).of_isClosed_subset isClosed_closure
    (closure_minimal ?_ (isClosed_set_pi fun j _ ↦ isClosed_closure))
  rintro _ ⟨u, hu, rfl⟩ j -
  refine subset_closure ⟨_, ⟨u, hu, rfl⟩, ?_⟩
  exact BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM _ _

/-- **Eigenspaces of operators of negative order are finite-dimensional.** If `P` is a classical
pseudodifferential operator of negative order `m` on the smooth functions of a compact manifold,
then for every nonzero `μ` the smooth functions `u` with `P u = μ u` form a finite-dimensional
complex vector space, as for compact operators. -/
theorem finiteDimensional_eigenspace_of_mem_classicalPseudodifferentialOperators [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hm : m < 0) {μ : ℂ} (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (Module.End.eigenspace P μ) := by
  -- Cutoffs `ψᵢ` in charts whose readings on `M` add up to `1`.
  obtain ⟨N, c, ψ, hψ⟩ :=
    IsCompact.exists_sum_cutoffPullback_eq_one (E := CoordinateSpace n) (isCompact_univ (X := M))
  have he (i : Fin N) : chartAt (CoordinateSpace n) (c i) ∈
      IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (c i)
  -- `u = R u` on the eigenspace, for the operator `R = μ⁻¹ P` of order `m`.
  set R := μ⁻¹ • P
  have hRu (u : Module.End.eigenspace P μ) : R u = u := by
    rw [LinearMap.smul_apply, Module.End.mem_eigenspace_iff.1 u.property, inv_smul_smul₀ hμ]
  -- The readings in `H⁰`, as coordinates on the eigenspace.
  let L : Module.End.eigenspace P μ →ₗ[ℂ] Fin N → H^{(0 : ℝ)}(CoordinateSpace n, ℂ) :=
    (LinearMap.pi fun i ↦ (SchwartzMap.toBesselPotentialSpaceCLM 0 2 :
        𝓢(CoordinateSpace n, ℂ) →L[ℂ] H^{(0 : ℝ)}(CoordinateSpace n, ℂ)).toLinearMap ∘ₗ
      (chartAt (CoordinateSpace n) (c i)).cutoffPushforwardSchwartz (he i) (ψ i)) ∘ₗ
      (Module.End.eigenspace P μ).subtype
  have hLapply (u : Module.End.eigenspace P μ) (i : Fin N) : L u i =
      SchwartzMap.toBesselPotentialSpaceCLM 0 2
        ((chartAt (CoordinateSpace n) (c i)).cutoffPushforwardSchwartz (he i) (ψ i) u) := rfl
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun u hu ↦ Subtype.ext ?_
    refine eq_zero_of_forall_cutoffPushforwardSchwartz_eq_zero he ψ (fun x ↦ hψ x (mem_univ x))
      fun i ↦ (SchwartzMap.toBesselPotentialSpaceCLM_injective 0 2) ?_
    rw [← hLapply, hu, Pi.zero_apply, map_zero]
  -- The readings of `R u` for `u` in a bounded set have compact closure, by Rellich's theorem.
  set T := (fun u j ↦ SchwartzMap.toBesselPotentialSpaceCLM 0 2
      ((chartAt (CoordinateSpace n) (c j)).cutoffPushforwardSchwartz (he j) (ψ j) (R u))) ''
    {u | ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2
      ((chartAt (CoordinateSpace n) (c i)).cutoffPushforwardSchwartz (he i) (ψ i) u)‖ ≤ 2 * N}
  have hT : IsCompact (closure T) :=
    isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz
      (Submodule.smul_mem _ μ⁻¹ hP) he ψ he ψ (fun x ↦ hψ x (mem_univ x)) (by linarith) _
  -- So the image of the eigenspace has a totally bounded neighbourhood of `0`, the preimage of
  -- `closure T`, which contains the ball of radius `2`.
  have hball (v : LinearMap.range L) (hv : ‖v‖ < 2) :
      (v : Fin N → H^{(0 : ℝ)}(CoordinateSpace n, ℂ)) ∈ T := by
    obtain ⟨v, hv'⟩ := v
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv'
    refine ⟨u, ?_, funext fun j ↦ by simp only [hRu u, hLapply]⟩
    calc ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2
          ((chartAt (CoordinateSpace n) (c i)).cutoffPushforwardSchwartz (he i) (ψ i) u)‖
        = ∑ i, ‖L u i‖ := by simp only [hLapply]
      _ ≤ ∑ _i : Fin N, (2 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦ (norm_le_pi_norm (L u) i).trans hv.le
      _ = 2 * N := by simp [mul_comm]
  have : FiniteDimensional ℂ (LinearMap.range L) :=
    .of_totallyBounded_nhds_zero ℂ (U := Subtype.val ⁻¹' closure T)
      (mem_of_superset (Metric.ball_mem_nhds 0 two_pos) fun v hv ↦
        subset_closure (hball v (mem_ball_zero_iff.1 hv)))
      (totallyBounded_preimage isUniformEmbedding_subtypeVal.isUniformInducing
        hT.totallyBounded)
  exact (LinearEquiv.ofInjective L hL).symm.finiteDimensional

/-- **The kernel of an elliptic operator on a compact manifold is finite-dimensional.** If `P` is
an elliptic classical pseudodifferential operator of order `m` on the smooth functions of a compact
manifold, the smooth functions `u` with `P u = 0` form a finite-dimensional complex vector space.
-/
theorem IsClassicalElliptic.finiteDimensional_ker [CompactSpace M]
    (hPe : IsClassicalElliptic m P) :
    FiniteDimensional ℂ (LinearMap.ker P) := by
  -- For a parametrix `Q`, the kernel lies in the eigenspace of `1 - Q P`, of order `-1`, at `1`.
  obtain ⟨Q, -, -, hQP⟩ := hPe.exists_comp_sub_id_mem_classicalPseudodifferentialOperators 1
  have hR : LinearMap.id - Q ∘ₗ P ∈ classicalPseudodifferentialOperators (-1) := by
    simpa using neg_mem hQP
  have := finiteDimensional_eigenspace_of_mem_classicalPseudodifferentialOperators hR
    neg_one_lt_zero one_ne_zero
  have hle : LinearMap.ker P ≤ Module.End.eigenspace (LinearMap.id - Q ∘ₗ P) 1 := fun u hu ↦
    Module.End.mem_eigenspace_iff.2 (by simp [LinearMap.mem_ker.1 hu])
  exact Submodule.finiteDimensional_of_le hle

/-- **The kernel of the formal adjoint of an elliptic operator is finite-dimensional.** If `P` is
an elliptic classical pseudodifferential operator of order `m` on a compact manifold with a measure
`μ` of smooth positive density, and `Q` is a properly supported formal adjoint of `P` for `μ`,
then the smooth functions `v` with `Q v = 0` form a finite-dimensional complex vector space. -/
theorem IsClassicalElliptic.finiteDimensional_ker_of_forall_integral_inner_eq [CompactSpace M]
    [MeasurableSpace M] {μ : MeasureTheory.Measure M}
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hQ : IsProperlySupported Q)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
      HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ) :
    FiniteDimensional ℂ (LinearMap.ker Q) :=
  ((isClassicalElliptic_iff_of_forall_integral_inner_eq hμ hP hQ hPQ).2 hPe).finiteDimensional_ker

end TauCeti
