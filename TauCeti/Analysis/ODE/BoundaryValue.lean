/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.MeasureTheory.Integral.IntervalIntegral.CauchySchwarz

/-!
# Linear equations with boundary values in two subspaces

Let `M : ℝ → (X →L[ℝ] X)` be a continuous path of bounded operators on a Banach space `X`, and let
`Ψ = TauCeti.dysonSeriesLeft M` be the propagator of `w' = M w`. Given two subspaces `F₀` and
`F₁` of `X` and a time `d ≥ 0`, consider the boundary value problem

`w' = M w + f`, `w 0 ∈ F₀`, `w d ∈ F₁`.

Its homogeneous problem (`f = 0`) has only the zero solution exactly when `Ψ(d) F₀ ∩ F₁ = 0`
(`TauCeti.disjoint_map_dysonSeriesLeft_iff`), since every solution of `w' = M w` is
`t ↦ Ψ(t) (w 0)`. For a path `S_t` of linearized Hamiltonian vector fields along a Hamiltonian
chord from a Lagrangian `L₀` to a Lagrangian `L₁`, with `F₀` and `F₁` the tangent spaces of the
Lagrangians at the ends of the chord, this is the nondegeneracy of the chord: the linearized flow
carries `T L₀` to a subspace meeting `T L₁` only at `0`.

By variation of constants, a boundary condition which bounds `w 0` by the deviation
`w d - Ψ(d) (w 0)` gives an a priori estimate
(`TauCeti.exists_forall_norm_le_mul_integral_norm_of_norm_le`). When `F₀` and `F₁` are
finite-dimensional and the homogeneous problem has only the zero solution, the injective linear
map `(v, u) ↦ Ψ(d) v - u` on `F₀ × F₁` is bounded below, and so `‖w t‖ ≤ C ∫₀ᵈ ‖f‖` for
`t ∈ [0, d]` (`TauCeti.exists_forall_norm_le_mul_integral_norm_of_disjoint`), with `C` depending
only on `M`, `d`, `F₀` and `F₁`. Integrating gives the `L²` estimate `∫₀ᵈ ‖w‖² ≤ C ∫₀ᵈ ‖f‖²`
(`TauCeti.exists_forall_integral_norm_sq_le_mul_integral_norm_sq_of_disjoint`), the passage from
the pointwise to the `L²` bound being `TauCeti.integral_norm_sq_le_of_forall_norm_le_mul`.

When moreover `dim F₀ + dim F₁ = dim X`, as for two Lagrangian subspaces of a symplectic space,
the injective map `(v, u) ↦ Ψ(d) v - u` is onto, and variation of constants solves the problem for
every continuous `f` (`TauCeti.exists_hasDerivAt_and_mem_of_disjoint`).

These are the path counterparts of the estimates for twisted periodic solutions in
`TauCeti.Analysis.ODE.Periodic`, where the boundary condition `w d = ε • w 0` couples the two ends
instead of constraining each end separately; both are derived from
`TauCeti.exists_forall_norm_le_mul_integral_norm_of_norm_le`.

## Main results

* `TauCeti.disjoint_map_dysonSeriesLeft_iff`: `Ψ(d) F₀ ∩ F₁ = 0` exactly when the homogeneous
  boundary value problem has only the zero solution.
* `TauCeti.exists_forall_norm_le_mul_integral_norm_of_disjoint`: the pointwise a priori estimate.
* `TauCeti.exists_forall_integral_norm_sq_le_mul_integral_norm_sq_of_disjoint`: the `L²` estimate.
* `TauCeti.exists_hasDerivAt_and_mem_of_disjoint`: when moreover `dim F₀ + dim F₁ = dim X`, the
  problem is solvable for every continuous `f`.

## References

* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, McGraw–Hill
  (1955), Chapter 11 (boundary value problems for linear systems).
-/

public section

open Set intervalIntegral

namespace TauCeti

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {M : ℝ → X →L[ℝ] X} {d : ℝ} {F₀ F₁ : Submodule ℝ X}

/-- **Nondegenerate boundary conditions.** For the propagator `Ψ = dysonSeriesLeft M` of
`w' = M w`, the subspaces `Ψ(d) F₀` and `F₁` meet only at `0` exactly when the only solution of
`w' = M w` with `w 0 ∈ F₀` and `w d ∈ F₁` is zero. -/
theorem disjoint_map_dysonSeriesLeft_iff (hM : Continuous M) :
    Disjoint (F₀.map (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) F₁ ↔
      ∀ ⦃w : ℝ → X⦄, (∀ t, HasDerivAt w (M t (w t)) t) → w 0 ∈ F₀ → w d ∈ F₁ → w = 0 := by
  rw [Submodule.disjoint_def]
  constructor
  · intro h w hw h₀ h₁
    have hw0 : dysonSeriesLeft M d (w 0) = 0 :=
      h _ ⟨w 0, h₀, rfl⟩ (eq_dysonSeriesLeft_apply hM hw d ▸ h₁)
    have h0 : w 0 = 0 := by
      have h1 : dysonSeries (-M) d (dysonSeriesLeft M d (w 0)) = 0 := by rw [hw0, map_zero]
      rwa [← mul_apply_eq_comp, dysonSeries_neg_mul_dysonSeriesLeft hM d,
        one_apply_eq_self] at h1
    funext t
    rw [eq_dysonSeriesLeft_apply hM hw t, h0, map_zero, Pi.zero_apply]
  · rintro h _ ⟨v, hv, rfl⟩ h₁
    simpa using congrFun (h (hasDerivAt_dysonSeriesLeft_apply hM v) (by simpa using hv) h₁) d

/-- The map `(v, u) ↦ Ψ(d) v - u` on `F₀ × F₁`, for the propagator `Ψ = dysonSeriesLeft M`. -/
private noncomputable def endpointMap (M : ℝ → X →L[ℝ] X) (d : ℝ) (F₀ F₁ : Submodule ℝ X) :
    F₀ × F₁ →ₗ[ℝ] X :=
  ((↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X) ∘ₗ F₀.subtype).coprod (-F₁.subtype)

omit [CompleteSpace X] in
private theorem endpointMap_apply (v : F₀) (u : F₁) :
    endpointMap M d F₀ F₁ (v, u) = dysonSeriesLeft M d v - u := by
  simp [endpointMap, sub_eq_add_neg]

/-- If `Ψ(d) F₀ ∩ F₁ = 0`, the map `(v, u) ↦ Ψ(d) v - u` on `F₀ × F₁` is injective. -/
private theorem ker_endpointMap_eq_bot (hM : Continuous M)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) F₁) :
    LinearMap.ker (endpointMap M d F₀ F₁) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun ⟨v, u⟩ h ↦ ?_
  have hvu : dysonSeriesLeft M d v = u := by
    rwa [endpointMap_apply, sub_eq_zero] at h
  have hu : (u : X) = 0 :=
    Submodule.disjoint_def.1 hP _ ⟨v, v.property, hvu⟩ u.property
  have hv : (v : X) = 0 := by
    have h' := (disjoint_map_dysonSeriesLeft_iff hM).1 hP
      (hasDerivAt_dysonSeriesLeft_apply hM (v : X)) (by simp) (by simp [hvu, hu])
    simpa using congrFun h' 0
  ext <;> simp [hu, hv]

/-- If `Ψ(d) F₀ ∩ F₁ = 0` for finite-dimensional `F₀` and `F₁`, the injective map
`(v, u) ↦ Ψ(d) v - u` on `F₀ × F₁` is bounded below: `‖v‖ ≤ K ‖Ψ(d) v - u‖`. -/
private theorem exists_forall_norm_le_mul_norm_dysonSeriesLeft_apply_sub [FiniteDimensional ℝ F₀]
    [FiniteDimensional ℝ F₁] (hM : Continuous M)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) F₁) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ F₀, ∀ u ∈ F₁, ‖v‖ ≤ K * ‖dysonSeriesLeft M d v - u‖ := by
  obtain ⟨K, -, hK⟩ := (endpointMap M d F₀ F₁).exists_antilipschitzWith
    (ker_endpointMap_eq_bot hM hP)
  refine ⟨K, K.coe_nonneg, fun v hv u hu ↦ ?_⟩
  have hb := ZeroHomClass.bound_of_antilipschitz (endpointMap M d F₀ F₁) hK (⟨v, hv⟩, ⟨u, hu⟩)
  calc ‖v‖ ≤ ‖((⟨v, hv⟩, ⟨u, hu⟩) : F₀ × F₁)‖ := by simp
    _ ≤ K * ‖endpointMap M d F₀ F₁ (⟨v, hv⟩, ⟨u, hu⟩)‖ := hb
    _ = K * ‖dysonSeriesLeft M d v - u‖ := by rw [endpointMap_apply]

/-- **Solvability of the boundary value problem.** Let `Ψ = dysonSeriesLeft M` be the propagator
of `w' = M w` on a finite-dimensional space `X`, and suppose that `Ψ(d) F₀ ∩ F₁ = 0` and
`dim F₀ + dim F₁ = dim X`. Then for every continuous `f` the equation `w' = M w + f` has a
solution with `w 0 ∈ F₀` and `w d ∈ F₁`. The solution is unique, by
`TauCeti.disjoint_map_dysonSeriesLeft_iff`. -/
theorem exists_hasDerivAt_and_mem_of_disjoint [FiniteDimensional ℝ X] (hM : Continuous M)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) F₁)
    (hdim : Module.finrank ℝ F₀ + Module.finrank ℝ F₁ = Module.finrank ℝ X) {f : ℝ → X}
    (hf : Continuous f) :
    ∃ w : ℝ → X, (∀ t, HasDerivAt w (M t (w t) + f t) t) ∧ w 0 ∈ F₀ ∧ w d ∈ F₁ := by
  -- The injective map `(v, u) ↦ Ψ(d) v - u` is onto by counting dimensions, so the initial value
  -- of the variation of constants formula can be chosen to meet the endpoint condition.
  have hsurj : Function.Surjective (endpointMap M d F₀ F₁) := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1
      (LinearMap.ker_eq_bot.1 (ker_endpointMap_eq_bot hM hP))
    rw [Module.finrank_prod, hdim]
  obtain ⟨⟨v, u⟩, hvu⟩ := hsurj (-dysonSeriesLeft M d (∫ s in 0..d, dysonSeries (-M) s (f s)))
  rw [endpointMap_apply] at hvu
  refine ⟨_, hasDerivAt_dysonSeriesLeft_apply_add_integral hM hf v, by simp [dysonSeriesLeft_zero],
    ?_⟩
  have : dysonSeriesLeft M d ((v : X) + ∫ s in 0..d, dysonSeries (-M) s (f s)) = u := by
    rw [map_add]
    linear_combination (norm := module) hvu
  simp only [this, SetLike.coe_mem]

/-- **An a priori estimate for boundary values in two subspaces.** Let `Ψ = dysonSeriesLeft M` be
the propagator of `w' = M w`, let `F₀` and `F₁` be finite-dimensional, and suppose that
`Ψ(d) F₀ ∩ F₁ = 0`. Then there is a constant `C ≥ 0` such that every solution of `w' = M w + f`,
with `f` continuous, `w 0 ∈ F₀` and `w d ∈ F₁`, satisfies `‖w t‖ ≤ C ∫₀ᵈ ‖f s‖ ds` for
`t ∈ [0, d]`. -/
theorem exists_forall_norm_le_mul_integral_norm_of_disjoint [FiniteDimensional ℝ F₀]
    [FiniteDimensional ℝ F₁] (hM : Continuous M) (hd : 0 ≤ d)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) F₁) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃w f : ℝ → X⦄, Continuous f → (∀ t, HasDerivAt w (M t (w t) + f t) t) →
      w 0 ∈ F₀ → w d ∈ F₁ → ∀ t ∈ Icc 0 d, ‖w t‖ ≤ C * ∫ s in 0..d, ‖f s‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_forall_norm_le_mul_norm_dysonSeriesLeft_apply_sub hM hP
  obtain ⟨C, hC, h⟩ := exists_forall_norm_le_mul_integral_norm_of_norm_le hM hd hK0
  -- The boundary conditions bound `w 0` by the deviation of `w d` from `Ψ(d) (w 0)`.
  exact ⟨C, hC, fun w f hf hw h₀ h₁ ↦ h hf hw (norm_sub_rev (w d) _ ▸ hK _ h₀ _ h₁)⟩

/-- **The `L²` estimate for boundary values in two subspaces.** If `F₀` and `F₁` are
finite-dimensional and `Ψ(d) F₀ ∩ F₁ = 0` for the propagator `Ψ = dysonSeriesLeft M`, then there
is a constant `C ≥ 0` such that every solution of `w' = M w + f`, with `f` continuous,
`w 0 ∈ F₀` and `w d ∈ F₁`, satisfies `∫₀ᵈ ‖w‖² ≤ C ∫₀ᵈ ‖f‖²`. -/
theorem exists_forall_integral_norm_sq_le_mul_integral_norm_sq_of_disjoint
    [FiniteDimensional ℝ F₀] [FiniteDimensional ℝ F₁] (hM : Continuous M) (hd : 0 ≤ d)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) F₁) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃w f : ℝ → X⦄, Continuous f → (∀ t, HasDerivAt w (M t (w t) + f t) t) →
      w 0 ∈ F₀ → w d ∈ F₁ → ∫ t in 0..d, ‖w t‖ ^ 2 ≤ C * ∫ t in 0..d, ‖f t‖ ^ 2 := by
  obtain ⟨B, _, hle⟩ := exists_forall_norm_le_mul_integral_norm_of_disjoint hM hd hP
  exact ⟨d ^ 2 * B ^ 2, by positivity, fun w f hf hw h₀ h₁ ↦
    integral_norm_sq_le_of_forall_norm_le_mul hd
      (continuous_iff_continuousAt.2 fun t ↦ (hw t).continuousAt) hf (hle hf hw h₀ h₁)⟩

end TauCeti
