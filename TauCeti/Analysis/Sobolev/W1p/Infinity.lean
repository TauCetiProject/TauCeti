/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Calculus.FDeriv.InfDist
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# The distance to the boundary is far from `W^{1,∞}_0`

Let `Ω` be a nonempty open subset of a finite-dimensional real inner product space `E`, other than
`E` itself, and let `d(x) = infDist x Ωᶜ` be the distance to its complement. It is `1`-Lipschitz
and vanishes off `Ω`, so it is continuous on the closure of `Ω` and zero on the frontier, and for
bounded `Ω` it is represented by an element of `W^{1,∞}(Ω)`
(`TauCeti.W1p.exists_value_ae_eq_infDist_compl`). Nevertheless every such representative is at
`W^{1,∞}` distance at least `1` from the closure `W^{1,∞}_0(Ω)` of the test functions
(`TauCeti.W1p.one_le_dist_of_value_ae_eq_infDist_compl`). So at the infinite exponent, unlike for
`p < ∞` (`TauCeti.W1p.mem_w1p0Submodule_of_continuousOn_closure`), vanishing on the boundary does
not give membership in `W^{1,∞}_0(Ω)`: the full norm also controls the gradient up to the boundary.
This is the multidimensional form of the interval obstruction
`TauCeti.W1p.exists_intervalTraceL_eq_zero_notMem_w1p0Submodule_top`, and it shows that the kernel
of a trace operator at the infinite exponent is in general larger than `W^{1,∞}_0(Ω)`.

## The argument

The distance function solves the eikonal equation: its derivative has norm one almost everywhere
off `Ωᶜ`, that is on `Ω` (`TauCeti.norm_fderiv_infDist_ae_eq_indicator`). It is the weak
derivative of `d`, so the weak gradient of `u` has norm one almost everywhere on `Ω`. Let `φ` be a
test function with support `K ⊆ Ω`. The set `Ω` is open and not the whole space, while `K` is
closed, so `Ω ∖ K` is a nonempty open set and has positive measure. There the gradient of `φ`
vanishes, so `1 = ‖∇u - ∇φ‖ ≤ ‖u - φ‖` at some point of `Ω ∖ K`. The set of `v` with
`1 ≤ dist u v` is closed, so the bound passes from the test functions to their closure.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §3, for the distinction between
  zero trace and approximation by test functions at the infinite exponent.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Distributions Gradient

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

/-- **The distance to the complement is a `W^{1,∞}` function.** On a bounded open set `Ω`, the
distance `x ↦ infDist x Ωᶜ` to the complement is represented by an element of `W^{1,∞}(Ω)`. -/
theorem W1p.exists_value_ae_eq_infDist_compl (hb : Bornology.IsBounded (Omega : Set E)) :
    ∃ u : W1p mu Omega ∞,
      W1p.value u =ᵐ[mu.restrict Omega] fun x ↦ infDist x (Omega : Set E)ᶜ := by
  have hlip : LipschitzWith 1 fun x ↦ infDist x (Omega : Set E)ᶜ := lipschitz_infDist_pt _
  obtain ⟨C, hC⟩ := (hlip.isBounded_image hb).exists_norm_le
  have hu : MemLp (fun x ↦ infDist x (Omega : Set E)ᶜ) ∞ (mu.restrict Omega) :=
    memLp_top_of_bound hlip.continuous.aestronglyMeasurable C
      ((ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx ↦ hC _ (mem_image_of_mem _ hx))
  have hD : MemLp (fderiv ℝ fun x ↦ infDist x (Omega : Set E)ᶜ) ∞ (mu.restrict Omega) :=
    memLp_top_of_bound (measurable_fderiv ℝ _).aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by simpa using norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x))
  obtain ⟨u, hu', -⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn hu hD
    (hlip.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv)
  exact ⟨u, hu'⟩

/-- **The distance to the boundary is far from `W^{1,∞}_0`.** Let `Ω` be a nonempty open set other
than the whole space, and let `u ∈ W^{1,∞}(Ω)` represent the distance `x ↦ infDist x Ωᶜ` to the
complement, which vanishes on the frontier. Then `u` is at distance at least `1` from every
element of `W^{1,∞}_0(Ω)`. -/
theorem W1p.one_le_dist_of_value_ae_eq_infDist_compl (hne : (Omega : Set E).Nonempty)
    (hΩ : (Omega : Set E) ≠ univ) {u : W1p mu Omega ∞}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] fun x ↦ infDist x (Omega : Set E)ᶜ)
    {v : W1p mu Omega ∞} (hv : v ∈ w1p0Submodule mu Omega ∞) : 1 ≤ dist u v := by
  have hlip : LipschitzWith 1 fun x ↦ infDist x (Omega : Set E)ᶜ := lipschitz_infDist_pt _
  -- The weak gradient of `u` is the derivative of the distance, which has norm one on `Ω`.
  have hgrad : ∀ᵐ x ∂mu.restrict Omega, ‖W1p.gradient u x‖ = 1 := by
    have hU := ((W1p.hasWeakFDerivOn u).congr_ae hu).ae_eq
      hlip.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv
    filter_upwards [hU, ae_restrict_of_ae
      (norm_fderiv_infDist_ae_eq_indicator (μ := mu) (nonempty_compl.2 hΩ)),
      ae_restrict_mem Omega.isOpen.measurableSet] with x hx hnorm hxΩ
    rw [← innerSL_apply_norm ℝ, hx, hnorm]
    simp [Omega.isOpen.isClosed_compl.closure_eq, hxΩ]
  -- The bound is closed in `v`, so it suffices to test it on test functions.
  refine w1p0Submodule_subset_of_isClosed
    (isClosed_le continuous_const (continuous_const.dist continuous_id)) (fun φ ↦ ?_) hv
  -- Outside the support of `φ` the gradient of `u - φ` is that of `u`. That region of `Ω` is a
  -- nonempty open set, since `Ω` is not compact: otherwise it would be clopen.
  set U := (Omega : Set E) \ tsupport φ
  have hUne : U.Nonempty := φ.sdiff_tsupport_nonempty_of_not_isCompact fun hc ↦
    hΩ (IsClopen.eq_univ ⟨hc.isClosed, Omega.isOpen⟩ hne)
  have hUΩ : U ⊆ Omega := sdiff_subset
  have : (ae (mu.restrict U)).NeBot := ae_restrict_neBot.2
    ((Omega.isOpen.sdiff (isClosed_tsupport _)).measure_ne_zero mu hUne)
  set w := W1p.ofTestFunctionₗ mu Omega ∞ φ
  have hw : W1p.gradient w =ᵐ[mu.restrict Omega] ∇ (φ : E → ℝ) := by
    rw [W1p.gradient_ofTestFunctionₗ]
    exact gradientTestFunctionLp_apply_ae ∞ φ
  have hall : ∀ᵐ x ∂mu.restrict U, x ∈ U ∧ ‖W1p.gradient u x‖ = 1 ∧
      ‖W1p.gradient u x - W1p.gradient w x‖ ≤ dist u w ∧ W1p.gradient w x = ∇ (φ : E → ℝ) x := by
    filter_upwards [ae_restrict_mem (Omega.isOpen.sdiff (isClosed_tsupport _)).measurableSet,
      ae_restrict_of_ae_restrict_of_subset hUΩ hgrad,
      ae_restrict_of_ae_restrict_of_subset hUΩ (W1p.ae_norm_gradient_sub_le_dist u w),
      ae_restrict_of_ae_restrict_of_subset hUΩ hw] with x h₁ h₂ h₃ h₄
    exact ⟨h₁, h₂, h₃, h₄⟩
  obtain ⟨x, hx, hxg, hxd, hxw⟩ := hall.exists
  rw [hxw, gradient_of_notMem_tsupport hx.2, sub_zero, hxg] at hxd
  exact hxd

/-- A representative of the distance to the complement of a nonempty open set other than the
whole space does not lie in `W^{1,∞}_0(Ω)`. -/
theorem W1p.notMem_w1p0Submodule_of_value_ae_eq_infDist_compl (hne : (Omega : Set E).Nonempty)
    (hΩ : (Omega : Set E) ≠ univ) {u : W1p mu Omega ∞}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] fun x ↦ infDist x (Omega : Set E)ᶜ) :
    u ∉ w1p0Submodule mu Omega ∞ := fun h ↦ by
  have h1 := W1p.one_le_dist_of_value_ae_eq_infDist_compl hne hΩ hu h
  rw [dist_self] at h1
  exact absurd h1 (by norm_num)

end TauCeti
