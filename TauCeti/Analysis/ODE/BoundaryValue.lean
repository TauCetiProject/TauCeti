/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.MeasureTheory.Integral.Bochner.Basic

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

Two bounds hold for every solution of `w' = M w + f` on `[0, d]`, with constants depending only
on `M` and `d`: by variation of constants, `w` stays within `C ∫₀ᵈ ‖f‖` of the homogeneous
solution `t ↦ Ψ(t) (w 0)`
(`TauCeti.exists_forall_norm_sub_dysonSeriesLeft_apply_le_mul_integral_norm`), and hence
`‖w t‖ ≤ C (‖w 0‖ + ∫₀ᵈ ‖f‖)` (`TauCeti.exists_forall_norm_le_mul_norm_add_integral_norm`). A
boundary condition which determines `w 0` from the deviation `w d - Ψ(d) (w 0)` therefore gives
an a priori estimate. When `F₀` and `F₁` are finite-dimensional and the homogeneous problem has
only the zero solution, the injective linear map `(v, u) ↦ Ψ(d) v - u` on `F₀ × F₁` is bounded
below, and so `‖w t‖ ≤ C ∫₀ᵈ ‖f‖` for `t ∈ [0, d]`
(`TauCeti.exists_forall_norm_le_mul_integral_norm_of_disjoint`), with `C` depending only on `M`,
`d`, `F₀` and `F₁`. Integrating gives the `L²` estimate `∫₀ᵈ ‖w‖² ≤ C ∫₀ᵈ ‖f‖²`
(`TauCeti.exists_forall_integral_norm_sq_le_mul_integral_norm_sq_of_disjoint`), the passage from
the pointwise to the `L²` bound being `TauCeti.integral_norm_sq_le_of_forall_norm_le_mul`.

These are the path counterparts of the estimates for twisted periodic solutions in
`TauCeti.Analysis.ODE.Periodic`, where the boundary condition `w d = ε • w 0` couples the two ends
instead of constraining each end separately; both are derived from the two bounds above.

## Main results

* `TauCeti.exists_forall_norm_sub_dysonSeriesLeft_apply_le_mul_integral_norm`,
  `TauCeti.exists_forall_norm_le_mul_norm_add_integral_norm`: bounds for every solution by the
  initial value and the forcing.
* `TauCeti.disjoint_map_dysonSeriesLeft_iff`: `Ψ(d) F₀ ∩ F₁ = 0` exactly when the homogeneous
  boundary value problem has only the zero solution.
* `TauCeti.exists_forall_norm_le_mul_integral_norm_of_disjoint`: the pointwise a priori estimate.
* `TauCeti.exists_forall_integral_norm_sq_le_mul_integral_norm_sq_of_disjoint`: the `L²` estimate.

## References

* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, McGraw–Hill
  (1955), Chapter 11 (boundary value problems for linear systems).
-/

public section

open Set intervalIntegral

namespace TauCeti

variable {X : Type*} [NormedAddCommGroup X]

/-- **From a pointwise to an `L²` bound.** If `‖w t‖ ≤ B ∫₀ᵈ ‖f‖` for every `t ∈ [0, d]`, then
`∫₀ᵈ ‖w‖² ≤ d² B² ∫₀ᵈ ‖f‖²`, by the Cauchy–Schwarz inequality `(∫₀ᵈ ‖f‖)² ≤ d ∫₀ᵈ ‖f‖²`. -/
theorem integral_norm_sq_le_of_forall_norm_le_mul {d B : ℝ} (hd : 0 ≤ d) {w f : ℝ → X}
    (hw : Continuous w) (hf : Continuous f)
    (h : ∀ t ∈ Icc 0 d, ‖w t‖ ≤ B * ∫ s in 0..d, ‖f s‖) :
    ∫ t in 0..d, ‖w t‖ ^ 2 ≤ d ^ 2 * B ^ 2 * ∫ t in 0..d, ‖f t‖ ^ 2 := by
  set F := ∫ s in 0..d, ‖f s‖
  have hCS : F ^ 2 ≤ d * ∫ s in 0..d, ‖f s‖ ^ 2 := by
    have h := MeasureTheory.sq_setIntegral_le_measureReal_mul_setIntegral_sq
      (μ := MeasureTheory.volume) (fun s ↦ ‖f s‖) (Ioc 0 d) measure_Ioc_lt_top.ne
      ((hf.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    rwa [Real.volume_real_Ioc_of_le hd, sub_zero, ← integral_of_le hd, ← integral_of_le hd] at h
  calc ∫ t in 0..d, ‖w t‖ ^ 2 ≤ ∫ _ in 0..d, (B * F) ^ 2 :=
        integral_mono_on hd ((hw.norm.pow 2).intervalIntegrable _ _) intervalIntegrable_const
          fun t ht ↦ pow_le_pow_left₀ (norm_nonneg _) (h t ht) 2
    _ = d * B ^ 2 * F ^ 2 := by rw [integral_const, smul_eq_mul]; ring
    _ ≤ d * B ^ 2 * (d * ∫ s in 0..d, ‖f s‖ ^ 2) := by gcongr
    _ = d ^ 2 * B ^ 2 * ∫ s in 0..d, ‖f s‖ ^ 2 := by ring

variable [NormedSpace ℝ X] [CompleteSpace X] {M : ℝ → X →L[ℝ] X} {d : ℝ} {F₀ F₁ : Submodule ℝ X}

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

/-- If `Ψ(d) F₀ ∩ F₁ = 0` for finite-dimensional `F₀` and `F₁`, the injective map
`(v, u) ↦ Ψ(d) v - u` on `F₀ × F₁` is bounded below: `‖v‖ ≤ K ‖Ψ(d) v - u‖`. -/
private theorem exists_forall_norm_le_mul_norm_dysonSeriesLeft_apply_sub [FiniteDimensional ℝ F₀]
    [FiniteDimensional ℝ F₁] (hM : Continuous M)
    (hP : Disjoint (F₀.map (↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X)) F₁) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ F₀, ∀ u ∈ F₁, ‖v‖ ≤ K * ‖dysonSeriesLeft M d v - u‖ := by
  set Φ : F₀ × F₁ →ₗ[ℝ] X :=
    ((↑(dysonSeriesLeft M d) : X →ₗ[ℝ] X) ∘ₗ F₀.subtype).coprod (-F₁.subtype) with hΦ
  have hker : LinearMap.ker Φ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun ⟨v, u⟩ h ↦ ?_
    have hvu : dysonSeriesLeft M d v = u := by
      simpa [hΦ, ← sub_eq_add_neg, sub_eq_zero] using h
    have hu : (u : X) = 0 :=
      Submodule.disjoint_def.1 hP _ ⟨v, v.2, hvu⟩ u.2
    have hv : (v : X) = 0 := by
      have h' := (disjoint_map_dysonSeriesLeft_iff hM).1 hP
        (hasDerivAt_dysonSeriesLeft_apply hM (v : X)) (by simp) (by simp [hvu, hu])
      simpa using congrFun h' 0
    ext <;> simp [hu, hv]
  obtain ⟨K, -, hK⟩ := Φ.exists_antilipschitzWith hker
  refine ⟨K, K.coe_nonneg, fun v hv u hu ↦ ?_⟩
  have hb := ZeroHomClass.bound_of_antilipschitz Φ hK (⟨v, hv⟩, ⟨u, hu⟩)
  calc ‖v‖ ≤ ‖((⟨v, hv⟩, ⟨u, hu⟩) : F₀ × F₁)‖ := by simp
    _ ≤ K * ‖Φ (⟨v, hv⟩, ⟨u, hu⟩)‖ := hb
    _ = K * ‖dysonSeriesLeft M d v - u‖ := by simp [hΦ, sub_eq_add_neg]

/-- **The deviation from the homogeneous solution.** For `d ≥ 0` there is a constant `C ≥ 0`
such that every solution of `w' = M w + f` with `f` continuous stays within `C ∫₀ᵈ ‖f‖` of the
solution `t ↦ Ψ(t) (w 0)` of `w' = M w` on `[0, d]`, where `Ψ = dysonSeriesLeft M`. -/
theorem exists_forall_norm_sub_dysonSeriesLeft_apply_le_mul_integral_norm (hM : Continuous M)
    (d : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃w f : ℝ → X⦄, Continuous f → (∀ t, HasDerivAt w (M t (w t) + f t) t) →
      ∀ t ∈ Icc 0 d, ‖w t - dysonSeriesLeft M t (w 0)‖ ≤ C * ∫ s in 0..d, ‖f s‖ := by
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := 0) (b := d)).exists_bound_of_continuousOn
    (continuous_dysonSeriesLeft hM).continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := 0) (b := d)).exists_bound_of_continuousOn
    (continuous_dysonSeries hM.neg).continuousOn
  refine ⟨|A| * |B|, by positivity, fun w f hf hw t ht ↦ ?_⟩
  -- By variation of constants, `w t - Ψ(t) (w 0) = Ψ(t) (∫₀ᵗ Ψ(s)⁻¹ (f s) ds)`.
  rw [eq_dysonSeriesLeft_apply_add_integral hM hf hw t, map_add, add_sub_cancel_left]
  calc _ ≤ |A| * ‖∫ s in 0..t, dysonSeries (-M) s (f s)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right ((hA t ht).trans (le_abs_self _)) (norm_nonneg _))
    _ ≤ |A| * ∫ s in 0..t, |B| * ‖f s‖ := by
        refine mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le ht.1
          (Filter.Eventually.of_forall fun s hs ↦ ?_)
          ((continuous_const.mul hf.norm).intervalIntegrable _ _)) (abs_nonneg _)
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          ((hB s ⟨hs.1.le, hs.2.trans ht.2⟩).trans (le_abs_self _)) (norm_nonneg _))
    _ = |A| * |B| * ∫ s in 0..t, ‖f s‖ := by rw [integral_const_mul]; ring
    _ ≤ |A| * |B| * ∫ s in 0..d, ‖f s‖ := mul_le_mul_of_nonneg_left (integral_mono_interval
        le_rfl ht.1 ht.2 (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        (hf.norm.intervalIntegrable _ _)) (by positivity)

/-- **A bound by the initial value and the forcing.** For `d ≥ 0` there is a constant `C ≥ 0`
such that every solution of `w' = M w + f` with `f` continuous satisfies
`‖w t‖ ≤ C (‖w 0‖ + ∫₀ᵈ ‖f‖)` on `[0, d]`. -/
theorem exists_forall_norm_le_mul_norm_add_integral_norm (hM : Continuous M) (d : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃w f : ℝ → X⦄, Continuous f → (∀ t, HasDerivAt w (M t (w t) + f t) t) →
      ∀ t ∈ Icc 0 d, ‖w t‖ ≤ C * (‖w 0‖ + ∫ s in 0..d, ‖f s‖) := by
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := 0) (b := d)).exists_bound_of_continuousOn
    (continuous_dysonSeriesLeft hM).continuousOn
  obtain ⟨C, -, hdev⟩ := exists_forall_norm_sub_dysonSeriesLeft_apply_le_mul_integral_norm hM d
  refine ⟨max |A| C, le_max_of_le_left (abs_nonneg A), fun w f hf hw t ht ↦ ?_⟩
  have hΨ : ‖dysonSeriesLeft M t (w 0)‖ ≤ |A| * ‖w 0‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ((hA t ht).trans (le_abs_self _)) (norm_nonneg _))
  have hI : 0 ≤ ∫ s in 0..d, ‖f s‖ :=
    intervalIntegral.integral_nonneg (le_trans ht.1 ht.2) fun _ _ ↦ norm_nonneg _
  calc ‖w t‖ ≤ ‖dysonSeriesLeft M t (w 0)‖ + ‖w t - dysonSeriesLeft M t (w 0)‖ :=
        norm_le_insert' _ _
    _ ≤ max |A| C * ‖w 0‖ + max |A| C * ∫ s in 0..d, ‖f s‖ :=
        add_le_add (hΨ.trans (by gcongr; exact le_max_left _ _))
          ((hdev hf hw t ht).trans (by gcongr; exact le_max_right _ _))
    _ = max |A| C * (‖w 0‖ + ∫ s in 0..d, ‖f s‖) := by ring

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
  obtain ⟨C, hC, hdev⟩ := exists_forall_norm_sub_dysonSeriesLeft_apply_le_mul_integral_norm hM d
  obtain ⟨B, hB, hle⟩ := exists_forall_norm_le_mul_norm_add_integral_norm hM d
  obtain ⟨K, hK0, hK⟩ := exists_forall_norm_le_mul_norm_dysonSeriesLeft_apply_sub hM hP
  refine ⟨B * (K * C + 1), mul_nonneg hB (add_nonneg (mul_nonneg hK0 hC) zero_le_one),
    fun w f hf hw h₀ h₁ t ht ↦ ?_⟩
  -- The boundary conditions bound `w 0` by the deviation of `w d` from `Ψ(d) (w 0)`.
  have h0 : ‖w 0‖ ≤ K * (C * ∫ s in 0..d, ‖f s‖) := by
    calc ‖w 0‖ ≤ K * ‖dysonSeriesLeft M d (w 0) - w d‖ := hK _ h₀ _ h₁
      _ = K * ‖w d - dysonSeriesLeft M d (w 0)‖ := by rw [norm_sub_rev]
      _ ≤ K * (C * ∫ s in 0..d, ‖f s‖) :=
          mul_le_mul_of_nonneg_left (hdev hf hw d ⟨hd, le_rfl⟩) hK0
  calc ‖w t‖ ≤ B * (‖w 0‖ + ∫ s in 0..d, ‖f s‖) := hle hf hw t ht
    _ ≤ B * (K * (C * ∫ s in 0..d, ‖f s‖) + ∫ s in 0..d, ‖f s‖) := by gcongr
    _ = B * (K * C + 1) * ∫ s in 0..d, ‖f s‖ := by ring

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
