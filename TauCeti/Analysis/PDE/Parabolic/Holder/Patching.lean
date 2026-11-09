/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Bilinear
public import TauCeti.Analysis.PDE.Parabolic.Holder.Cutoff
public import TauCeti.Analysis.Holder.Patching

/-!
# Patching local bounds for order-two parabolic Hölder norms

The derivative fields of a map in the bounded order-two parabolic Hölder space
`C_b^{2+α,1+α/2}` on a slab `E × [a, b]` are local: two maps that agree on an open subset of the
slab have the same spatial gradient, spatial Hessian and time derivative there, including the
one-sided time derivatives at the endpoints of `[a, b]`.

Consequently the order-two norm is controlled by local data. Let `r > 0`. If around every point
`p` of the slab the map `u` agrees, on the parabolic ball of radius `r` about `p`, with a map of
norm at most `M`, then

`‖u‖ ≤ (6 + 4 r^(-α)) M`.

The supremum norms of the four fields are bounded pointwise by the local pieces, and the parabolic
Hölder seminorms of the Hessian and of the time derivative by the patching estimate for bounded
Hölder functions (`TauCeti.HolderSpace.norm_le_of_forall_eqOn_ball`).

The local pieces are usually localizations `χ_p u` by space-time cutoffs `χ_p` equal to one near
`p`. Smooth cutoffs centred at every point of the slab, with one norm bound for all centres and
all slabs, are one on the parabolic ball of radius `ρ / 2` about their centre and vanish off the
parabolic ball of radius `2 ρ`. With them, a bound on `‖χ_p u‖` uniform in the centre `p` bounds
`‖u‖` with a constant depending only on `α` and `ρ`, and the spatial Hessian of `χ_p u` vanishes
at parabolic distance greater than `2 ρ` from `p`. This is how a global parabolic Schauder
estimate is assembled from estimates of localizations, to which a constant-coefficient estimate
applies after freezing the coefficients at `p`.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.eqOn_spatialFDerivL_of_eqOn`,
  `TauCeti.ParabolicC2HolderSpace.eqOn_spatialSecondFDerivL_of_eqOn` and
  `TauCeti.ParabolicC2HolderSpace.eqOn_timeDerivL_of_eqOn`: the derivative fields are local.
* `TauCeti.ParabolicC2HolderSpace.spatialSecondFDerivL_eq_zero_of_forall_lt_dist`: a map vanishing
  away from a point has spatial Hessian vanishing there.
* `TauCeti.ParabolicC2HolderSpace.norm_le_of_forall_eqOn_ball`: the patching estimate.
* `TauCeti.ParabolicC2HolderSpace.norm_le_of_forall_norm_compParabolicC2Holder₂_le`: the patching
  estimate for localizations by cutoffs.
* `TauCeti.ParabolicC2HolderSpace.exists_cutoff_family`: cutoffs centred at every point of a slab.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (passing from local to global Schauder estimates).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8 (parabolic Schauder estimates).
-/

public section

noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Metric Filter Topology ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-! ### Locality of the derivative fields -/

section Locality

variable {f g : ParabolicC2HolderSpace α E F hab} {U : Set (slab (E := E) a b)}

/-- The spatial gradient is local: maps that agree on an open subset of the slab have the same
spatial gradient there. -/
theorem eqOn_spatialFDerivL_of_eqOn (hU : IsOpen U) (h : EqOn f g U) :
    EqOn (spatialFDerivL f) (spatialFDerivL g) U := by
  intro p hp
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  have hev : (fun y ↦ f (slabMk y t)) =ᶠ[𝓝 x] fun y ↦ g (slabMk y t) :=
    eventually_of_mem ((hU.preimage (spatialSlice t).continuous).mem_nhds (by simpa using hp))
      fun _ hy ↦ h (by simpa using hy)
  rw [← f.fderiv_eq, ← g.fderiv_eq, hev.fderiv_eq]

/-- The spatial Hessian is local: maps that agree on an open subset of the slab have the same
spatial Hessian there. -/
theorem eqOn_spatialSecondFDerivL_of_eqOn (hU : IsOpen U) (h : EqOn f g U) :
    EqOn (spatialSecondFDerivL f) (spatialSecondFDerivL g) U := by
  have hx := eqOn_spatialFDerivL_of_eqOn hU h
  intro p hp
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  have hev : (fun y ↦ spatialFDerivL f (slabMk y t)) =ᶠ[𝓝 x]
      fun y ↦ spatialFDerivL g (slabMk y t) :=
    eventually_of_mem ((hU.preimage (spatialSlice t).continuous).mem_nhds (by simpa using hp))
      fun _ hy ↦ hx (by simpa using hy)
  rw [← f.fderiv_spatialFDeriv_eq, ← g.fderiv_spatialFDeriv_eq, hev.fderiv_eq]

/-- The time derivative is local: maps that agree on an open subset of the slab have the same
time derivative there, also at the endpoints of the time interval. -/
theorem eqOn_timeDerivL_of_eqOn (hU : IsOpen U) (h : EqOn f g U) :
    EqOn (timeDerivL f) (timeDerivL g) U := by
  intro p hp
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  -- The times `s ∈ [a, b]` with `(x, s) ∈ U` form a neighbourhood of `t` within `[a, b]`.
  have hU' : (↑) '' (timeSlice x ⁻¹' U) ∈ 𝓝[Icc a b] (t : ℝ) :=
    mem_nhds_subtype_iff_nhdsWithin.1
      ((hU.preimage (timeSlice x).continuous).mem_nhds (by simpa using hp))
  have hev : timeExtension hab.le f x =ᶠ[𝓝[Icc a b] (t : ℝ)] timeExtension hab.le g x := by
    filter_upwards [hU'] with _ ⟨s, hs, hst⟩
    rw [← hst, timeExtension_of_mem, timeExtension_of_mem]
    exact h (by simpa using hs)
  rw [← f.derivWithin_eq, ← g.derivWithin_eq,
    hev.derivWithin_eq (by rw [timeExtension_of_mem, timeExtension_of_mem]; exact h hp)]

/-- A map vanishing at parabolic distance greater than `r` from `z` has spatial Hessian vanishing
there. This is the support condition under which a principal coefficient can be frozen at `z`
(`TauCeti.ParabolicC2HolderSpace.norm_spatialOperatorL_sub_const_apply_le`). -/
theorem spatialSecondFDerivL_eq_zero_of_forall_lt_dist {z : slab (E := E) a b} {r : ℝ}
    (h : ∀ q, r < dist q z → f q = 0) (p : slab (E := E) a b) (hp : r < dist p z) :
    spatialSecondFDerivL f p = 0 := by
  have hU : IsOpen {q : slab (E := E) a b | r < dist q z} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have h0 : EqOn f (0 : ParabolicC2HolderSpace α E F hab) {q | r < dist q z} := fun q hq ↦ by
    rw [h q hq, zero_apply]
  rw [eqOn_spatialSecondFDerivL_of_eqOn hU h0 hp, map_zero, HolderSpace.zero_apply]

end Locality

/-! ### Patching -/

/-- **Patching local bounds for the order-two parabolic Hölder norm.** Let `r > 0`. If around
every point `p` of the slab the map `f` agrees, on the parabolic ball of radius `r` about `p`,
with a map of norm at most `M`, then `‖f‖ ≤ (6 + 4 r^(-α)) M`. -/
theorem norm_le_of_forall_eqOn_ball {f : ParabolicC2HolderSpace α E F hab} {r M : ℝ}
    (hr : 0 < r) (h : ∀ p, ∃ g : ParabolicC2HolderSpace α E F hab, ‖g‖ ≤ M ∧ EqOn f g (ball p r)) :
    ‖f‖ ≤ (6 + 4 * r ^ (-(α : ℝ))) * M := by
  have : Nonempty (slab (E := E) a b) := ⟨slabMk 0 ⟨a, left_mem_Icc.2 hab.le⟩⟩
  have hM : 0 ≤ M := by
    obtain ⟨g, hg, -⟩ := h (Classical.arbitrary _)
    exact (norm_nonneg g).trans hg
  -- At its centre, each field of `f` is the corresponding field of the local piece.
  have hval : ‖valueL f‖ ≤ M := (BoundedContinuousFunction.norm_le hM).2 fun p ↦ by
    obtain ⟨g, hg, hfg⟩ := h p
    rw [valueL_apply, hfg (mem_ball_self hr)]
    exact ((valueL g).norm_coe_le_norm p).trans ((norm_valueL_le g).trans hg)
  have hgrad : ‖spatialFDerivL f‖ ≤ M := (BoundedContinuousFunction.norm_le hM).2 fun p ↦ by
    obtain ⟨g, hg, hfg⟩ := h p
    rw [eqOn_spatialFDerivL_of_eqOn isOpen_ball hfg (mem_ball_self hr)]
    refine ((spatialFDerivL g).norm_coe_le_norm p).trans (le_trans ?_ hg)
    rw [norm_eq g]
    linarith [norm_nonneg (valueL g), norm_nonneg (spatialSecondFDerivL g),
      norm_nonneg (timeDerivL g)]
  -- The two Hölder fields are patched as bounded Hölder functions.
  have hxx : ‖spatialSecondFDerivL f‖ ≤ 2 * (1 + r ^ (-(α : ℝ))) * M :=
    HolderSpace.norm_le_of_forall_eqOn_ball hr fun p ↦ by
      obtain ⟨g, hg, hfg⟩ := h p
      exact ⟨spatialSecondFDerivL g, (norm_spatialSecondFDerivL_le g).trans hg,
        eqOn_spatialSecondFDerivL_of_eqOn isOpen_ball hfg⟩
  have ht : ‖timeDerivL f‖ ≤ 2 * (1 + r ^ (-(α : ℝ))) * M :=
    HolderSpace.norm_le_of_forall_eqOn_ball hr fun p ↦ by
      obtain ⟨g, hg, hfg⟩ := h p
      exact ⟨timeDerivL g, (norm_timeDerivL_le g).trans hg,
        eqOn_timeDerivL_of_eqOn isOpen_ball hfg⟩
  rw [norm_eq]
  linarith

/-- **Patching localizations by cutoffs.** Let `B` be a bilinear map with `B 1 y = y`, such as
scalar multiplication or the multiplication of `ℝ`, and let each scalar map `χ p` be one on the
parabolic ball of radius `r > 0` about `p`. If the localizations `B (χ p) f` all have norm at most
`M`, then `‖f‖ ≤ (6 + 4 r^(-α)) M`. -/
theorem norm_le_of_forall_norm_compParabolicC2Holder₂_le (hα : α ≤ 1)
    (B : ℝ →L[ℝ] F →L[ℝ] F) (hB : ∀ y, B 1 y = y) {r M : ℝ} (hr : 0 < r)
    {χ : slab (E := E) a b → ParabolicC2HolderSpace α E ℝ hab}
    (hχ : ∀ p, ∀ q ∈ ball p r, χ p q = 1) {f : ParabolicC2HolderSpace α E F hab}
    (hM : ∀ p, ‖B.compParabolicC2Holder₂ hα (χ p) f‖ ≤ M) :
    ‖f‖ ≤ (6 + 4 * r ^ (-(α : ℝ))) * M :=
  norm_le_of_forall_eqOn_ball hr fun p ↦
    ⟨_, hM p, fun q hq ↦ by rw [ContinuousLinearMap.compParabolicC2Holder₂_apply, hχ p q hq, hB]⟩

/-! ### Cutoffs centred at every point -/

/-- **Cutoffs centred at every point of a slab.** For `α ≤ 1` and `ρ > 0` there is a constant
`C` such that on every slab there are scalar maps `χ p`, one for each point `p`, with
`‖χ p‖ ≤ C`, values in `[0, 1]`, equal to one on the parabolic ball of radius `ρ / 2` about `p`
and vanishing at parabolic distance at least `2 ρ` from `p`. -/
theorem exists_cutoff_family [FiniteDimensional ℝ E] (hα : α ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ) (hab : a < b),
      ∃ χ : slab (E := E) a b → ParabolicC2HolderSpace α E ℝ hab,
        (∀ p, ‖χ p‖ ≤ C) ∧ (∀ p q, χ p q ∈ Icc 0 1) ∧
        (∀ p, ∀ q ∈ ball p (ρ / 2), χ p q = 1) ∧
        ∀ p q, 2 * ρ ≤ dist q p → χ p q = 0 := by
  obtain ⟨C, hC, hχ⟩ := exists_cutoff (E := E) hα hρ
  refine ⟨C, hC, fun a b hab ↦ ?_⟩
  choose χ hnorm hmem hone hzero _ using fun p : slab (E := E) a b ↦
    hχ (p : ParabolicSpaceTime E).space (p : ParabolicSpaceTime E).time a b hab
  refine ⟨χ, hnorm, hmem, fun p q hq ↦ hone p q ?_ ?_, fun p q hq ↦ hzero p q ?_⟩
  · -- Inside the parabolic ball of radius `ρ / 2`, the spatial distance is at most `ρ / 2` ...
    exact (dist_space_le _ _).trans (mem_ball.1 hq).le
  · -- ... and the time distance at most `ρ² / 4`.
    have hs := (sqrt_abs_time_sub_le_dist (q : ParabolicSpaceTime E) p).trans (mem_ball.1 hq).le
    have hτ := Real.sq_sqrt (abs_nonneg ((q : ParabolicSpaceTime E).time -
      (p : ParabolicSpaceTime E).time))
    nlinarith [Real.sqrt_nonneg |(q : ParabolicSpaceTime E).time -
      (p : ParabolicSpaceTime E).time|]
  · -- At parabolic distance at least `2 ρ`, either the spatial distance is at least `ρ` or the
    -- time distance is at least `ρ²`.
    rw [Subtype.dist_eq, dist_eq] at hq
    by_contra! hlt
    obtain ⟨hx, ht⟩ := hlt
    have hs : √|(q : ParabolicSpaceTime E).time - (p : ParabolicSpaceTime E).time| < ρ :=
      (Real.sqrt_lt' hρ).2 ht
    linarith

end TauCeti.ParabolicC2HolderSpace
