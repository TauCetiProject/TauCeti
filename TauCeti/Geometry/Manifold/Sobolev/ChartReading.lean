/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Schwartz
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Normed.Operator.Compact.Pi
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Sobolev readings of a function on a manifold: change of chart and compactness

Let `M` be a manifold modelled on `ℝⁿ`. A complex-valued smooth function `u` on `M` is read in a
chart `e` of the maximal atlas through a cutoff `τ` as the Schwartz function `τ · (u ∘ e⁻¹)` on
`ℝⁿ` (`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). This file shows that the `H^s` norm of
such a reading is controlled by the reading in any other chart: if `Ψ` is a cutoff `ψ` in a chart
`e'` read on `M`, then for every real `s`

`‖τ · ((Ψ g) ∘ e⁻¹)‖_{H^s} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{H^s}`

(`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`). The
reading in `e` is `θ · (w ∘ κ)` for the reading `w` in `e'`, the transition map `κ = e' ∘ e⁻¹` and
a cutoff `θ` with compact support in the source of `κ` (`OpenPartialHomeomorph.overlapCutoff`),
and such localized changes of variables are bounded on `H^s`
(`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`).

The readings through a fixed cutoff `ψ` are all supported in the compact support of `ψ`. So by the
Rellich theorem, for `t < s` some compact operator `H^s → H^t` sends the `H^s` class of every
reading `ψ · (u ∘ e⁻¹)` to its `H^t` class
(`TauCeti.exists_isCompactOperator_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz`): it is
multiplication by a function equal to `1` on the support of `ψ`, followed by the inclusion
(`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`). Consequently, for cutoffs
`ψᵢ` whose readings on `M` add up to `1` and `r < t`, a space of smooth functions on which the
partition norm `∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^t}` is bounded by a multiple of the weaker norm
`∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^r}` is finite-dimensional
(`TauCeti.finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le`): the readings
identify it with a space carrying a compact operator bounded below
(`IsCompactOperator.finiteDimensional_of_norm_le_mul_norm`).

## Main results

* `TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`: changing
  the chart of a reading costs a constant in the `H^s` norm.
* `TauCeti.exists_isCompactOperator_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz`: the
  passage from the `H^s` class to the `H^t` class of the readings through a fixed cutoff, for
  `t < s`, is the restriction of a compact operator.
* `TauCeti.finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le`: a space of smooth
  functions on which a stronger Sobolev partition norm is bounded by a weaker one is
  finite-dimensional.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
-/

public section

noncomputable section

open Set TauCeti OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}

/-- **Changing the chart of a reading.** Let `ψ` be a cutoff in a chart `e'`, with `Ψ` the smooth
function `ψ ∘ e'` on `M`, extended by `0`, and `τ` a cutoff in a chart `e`. For every real `s`
there is a constant `C` such that for every smooth `g` on `M`, the reading `τ · ((Ψ g) ∘ e⁻¹)` of
`Ψ g` in `e` satisfies

`‖τ · ((Ψ g) ∘ e⁻¹)‖_{H^s} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (τ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) (s : ℝ) :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e.cutoffPushforwardSchwartz he τ
          (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g))‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e'.cutoffPushforwardSchwartz he' ψ g)‖ := by
  -- The reading in `e` is `θ · (w ∘ κ)` for the reading `w` in `e'`, the transition map
  -- `κ = e' ∘ e⁻¹` and `θ = τ · (ψ₁ ∘ κ)`, with `ψ₁ = 1` on the support of `ψ`.
  obtain ⟨ψ₁, hψ₁, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨e'.target, e'.open_target⟩) (n := ⊤) ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨hθ, hθc, hθs⟩ := overlapCutoff_spec he' he τ ψ₁
  obtain ⟨C, hC⟩ := BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp
    (F := ℂ) (contDiffOn_symm_trans_of_mem_maximalAtlas he he')
    (fun _ hz ↦ (contDiffAt_symm_trans_symm_of_mem_maximalAtlas he he' hz).contDiffWithinAt)
    hθ hθc hθs s
  refine ⟨C, fun g ↦ hC _ _ fun y ↦ ?_⟩
  rw [cutoffPushforwardSchwartz_apply, cutoffPushforwardSchwartz_apply, coe_trans,
    Function.comp_apply]
  by_cases hy : e.symm y ∈ e'.source
  · rw [overlapCutoff_apply_of_mem he' he τ ψ₁ hy, e'.left_inv hy]
    simp only [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
      ContMDiffMap.ofReal_apply, cutoffPullback_one_apply_of_mem he' _ hy]
    by_cases hψ : ψ (e' (e.symm y)) = 0
    · simp [hψ]
    · rw [hψ₁.self_of_nhdsSet _ (subset_tsupport _ hψ), mul_one, ← Complex.real_smul]
  · rw [overlapCutoff_apply he' he, cutoffPullback_apply_of_notMem he' _ _ hy]
    simp [cutoffPullback_apply_of_notMem he' _ _ hy]

omit [T2Space M] in
/-- **Rellich's theorem for readings in a chart.** Let `ψ` be a cutoff in a chart `e` and `t < s`.
Some compact operator `K : H^s → H^t` sends the `H^s` class of the reading `ψ · (u ∘ e⁻¹)` of every
smooth function `u` on `M` to its `H^t` class. So a family of smooth functions whose readings
through `ψ` are bounded in `H^s` has readings through `ψ` forming a relatively compact set in
`H^t`. -/
theorem exists_isCompactOperator_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {s t : ℝ} (h : t < s) :
    ∃ K : H^{s}(CoordinateSpace n, ℂ) →L[ℂ] H^{t}(CoordinateSpace n, ℂ), IsCompactOperator K ∧
      ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        K (SchwartzMap.toBesselPotentialSpaceCLM s 2 (e.cutoffPushforwardSchwartz he ψ u)) =
          SchwartzMap.toBesselPotentialSpaceCLM t 2 (e.cutoffPushforwardSchwartz he ψ u) := by
  -- `K` multiplies by `φ`, equal to `1` near the support of `ψ`, and includes `H^s` into `H^t`.
  obtain ⟨φ, -, -, hφ⟩ :=
    ψ.hasCompactSupport.isCompact.exists_schwartzMap_cutoff isOpen_univ (subset_univ _)
  refine ⟨BesselPotentialSpace.inclusion h.le ∘L BesselPotentialSpace.smulLeftCLM s φ,
    BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM φ h, fun u ↦ ?_⟩
  have hφu : SchwartzMap.smulLeftCLM ℂ (φ : CoordinateSpace n → ℂ)
      (e.cutoffPushforwardSchwartz he ψ u) = e.cutoffPushforwardSchwartz he ψ u := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth, cutoffPushforwardSchwartz_apply]
    by_cases hy : ψ y = 0
    · simp [hy]
    · simp [hφ.self_of_nhdsSet y (subset_tsupport _ hy)]
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.smulLeftCLM_toBesselPotentialSpaceCLM,
    hφu, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]

/-- **Finite-dimensionality from a reverse Sobolev estimate.** Let `ψᵢ` be finitely many cutoffs
in charts `eᵢ` whose readings `ψᵢ ∘ eᵢ` on `M`, extended by `0`, add up to `1`, and let `r < t`. A
space `V` of smooth functions on `M` on which the stronger partition norm is bounded by the weaker
one,

`∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^t} ≤ C ∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖_{H^r}` for all `u ∈ V`,

is finite-dimensional. This is how the elliptic estimate shows that the kernel of an elliptic
operator on a compact manifold is finite-dimensional. -/
theorem finiteDimensional_of_forall_sum_norm_toBesselPotentialSpaceCLM_le {ι : Type*} [Fintype ι]
    {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) {r t : ℝ} (hrt : r < t) {C : ℝ}
    {V : Submodule ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hV : ∀ u ∈ V, ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM t 2
        ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖ ≤
      C * ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r 2
        ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)‖) :
    FiniteDimensional ℂ V := by
  -- The `H^t` readings of `V` form an injective linear map `T`.
  let T : V →ₗ[ℂ] (ι → H^{t}(CoordinateSpace n, ℂ)) :=
    LinearMap.pi fun i ↦ (SchwartzMap.toBesselPotentialSpaceCLM t 2 : 𝓢(CoordinateSpace n, ℂ)
      →L[ℂ] H^{t}(CoordinateSpace n, ℂ)).toLinearMap ∘ₗ
        (e i).cutoffPushforwardSchwartz (he i) (ψ i) ∘ₗ V.subtype
  have hT (u : V) (i : ι) : T u i = SchwartzMap.toBesselPotentialSpaceCLM t 2
      ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u) := (rfl)
  have hTinj : Function.Injective T := fun u v huv ↦ Subtype.ext <|
    eq_of_forall_cutoffPushforwardSchwartz_eq he ψ hψ fun i ↦
      SchwartzMap.toBesselPotentialSpaceCLM_injective t 2 (by rw [← hT, ← hT, huv])
  -- Compact operators `Kᵢ : H^t → H^r` send the `H^t` readings to the `H^r` readings; together
  -- they form a compact operator `K'` on the range of `T`.
  choose K hK hKw using fun i ↦
    exists_isCompactOperator_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz (he i) (ψ i) hrt
  let K' : LinearMap.range T →L[ℂ] (ι → H^{r}(CoordinateSpace n, ℂ)) :=
    ContinuousLinearMap.pi fun i ↦
      K i ∘L ContinuousLinearMap.proj i ∘L (LinearMap.range T).subtypeL
  have hK'x (x : LinearMap.range T) (i : ι) :
      K' x i = K i ((x : ι → H^{t}(CoordinateSpace n, ℂ)) i) := by
    simp [K']
  have hK' : IsCompactOperator K' := IsCompactOperator.pi fun i ↦ by
    simpa [hK'x, Function.comp_def] using (hK i).comp_clm (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : ι ↦ H^{t}(CoordinateSpace n, ℂ)) i ∘L (LinearMap.range T).subtypeL)
  -- On the range of `T` the estimate reads `‖x‖ ≤ |C| (card ι) ‖K' x‖`, so the range is
  -- finite-dimensional, and `T` identifies `V` with it.
  have : FiniteDimensional ℂ (LinearMap.range T) :=
    hK'.finiteDimensional_of_norm_le_mul_norm (C := |C| * Fintype.card ι) fun x ↦ by
      obtain ⟨u, hu⟩ := x.property
      have hKx (i : ι) : K' x i = SchwartzMap.toBesselPotentialSpaceCLM r 2
          ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u) := by
        rw [hK'x, ← hu, hT, hKw]
      calc ‖x‖ ≤ ∑ i, ‖(x : ι → H^{t}(CoordinateSpace n, ℂ)) i‖ :=
            (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2 fun i ↦
              Finset.single_le_sum (f := fun j ↦ ‖(x : ι → H^{t}(CoordinateSpace n, ℂ)) j‖)
                (fun j _ ↦ norm_nonneg _) (Finset.mem_univ i)
        _ ≤ |C| * ∑ i, ‖K' x i‖ := by
            simp only [← hu, hT, hKx]
            exact (hV u u.property).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
              (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
        _ ≤ |C| * Fintype.card ι * ‖K' x‖ := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (by simpa using Pi.sum_norm_apply_le_norm (K' x))
              (abs_nonneg C)
  exact (LinearEquiv.ofInjective T hTinj).symm.finiteDimensional

end TauCeti
