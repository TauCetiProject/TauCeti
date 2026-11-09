/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Basic
public import TauCeti.Analysis.PDE.HeatKernel.CauchyPotential
import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Holder

/-!
# The initial time derivative of the Duhamel heat potential

For bounded measurable forcing that is uniformly α-Hölder in space and approaches its initial
slice at rate `t^(α/2)`, the Duhamel potential satisfies

`‖w(t, x) - t • f(0, x)‖ ≤ (H M_α + L) t^(1 + α/2)`.

Here `H` is the spatial Hölder constant, `L` controls the approach to the initial slice, and
`M_α` is the moment `TauCeti.heatKernelMoment`. In particular, `w(t, ·) / t` converges uniformly
to `f(0, ·)`, and the right time derivative at zero is `f(0, x)`. Only almost-everywhere bounds
on positive-time slices are needed. These endpoint identities are needed when extending the
inhomogeneous heat equation to a closed time slab; the interior time derivative is a separate
statement.

The estimate combines the spatial approximate-identity bound for the Cauchy potential with
the temporal modulus of the forcing, before integrating in time.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3
  (the volume potential).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Chapter 4 (closed-slab heat potentials).
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Real Set Topology
open scoped Convolution NNReal Interval

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ → E → F} {M t T : ℝ} {H L α : ℝ≥0}

/-- The Duhamel potential has first-order expansion `t • f(0, x)`, uniformly in space, with
remainder of order `t^(1 + α/2)`. The forcing need only approach its initial slice at the
parabolic Hölder rate; no time derivative of the forcing is assumed. -/
theorem norm_heatDuhamelPotential_sub_smul_le
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s))
    (hL : ∀ᵐ s ∂volume.restrict (Ioo 0 t),
      ∀ x, ‖f s x - f 0 x‖ ≤ L * s ^ ((α : ℝ) / 2))
    (hα : 0 < α) (ht : 0 ≤ t) (x : E) :
    ‖heatDuhamelPotential f t x - t • f 0 x‖ ≤
      (H * heatKernelMoment E α + L) * t ^ (1 + (α : ℝ) / 2) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [zero_rpow (by positivity : (1 + (α : ℝ) / 2) ≠ 0)]
  have hi := intervalIntegrable_heatKernel_convolution hf hfM ht x
  have hae : ∀ᵐ s ∂volume.restrict (Ι 0 t), s ∈ Ioo 0 t ∧
      HolderWith H α (f s) ∧ ∀ y, ‖f s y - f 0 y‖ ≤ L * s ^ ((α : ℝ) / 2) := by
    rw [uIoc_of_le ht.le, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hH, hL] with s hs hsH hsL
    exact ⟨hs, hsH, hsL⟩
  have hbound : ∀ᵐ s ∂volume.restrict (Ι 0 t),
      ‖(heatKernel (t - s) ⋆ f s) x - f 0 x‖ ≤
        (H * heatKernelMoment E α + L) * t ^ ((α : ℝ) / 2) := by
    filter_upwards [hae] with s ⟨hs, hsH, hsL⟩
    have happrox := norm_heatCauchyPotential_sub_le hsH (hsH.continuous hα)
      (sub_pos.mpr hs.2).le x
    rw [heatCauchyPotential_eq_convolution _ (sub_pos.mpr hs.2)] at happrox
    calc
      ‖(heatKernel (t - s) ⋆ f s) x - f 0 x‖ ≤
          ‖(heatKernel (t - s) ⋆ f s) x - f s x‖ + ‖f s x - f 0 x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ H * heatKernelMoment E α * (t - s) ^ ((α : ℝ) / 2) +
          L * s ^ ((α : ℝ) / 2) := add_le_add happrox (hsL x)
      _ ≤ H * heatKernelMoment E α * t ^ ((α : ℝ) / 2) +
          L * t ^ ((α : ℝ) / 2) := by
        gcongr <;> linarith [hs.1, hs.2]
      _ = (H * heatKernelMoment E α + L) * t ^ ((α : ℝ) / 2) := by ring
  have hconst : t • f 0 x = ∫ s in 0..t, f 0 x := by simp
  rw [heatDuhamelPotential_def, hconst,
    ← intervalIntegral.integral_sub hi intervalIntegrable_const]
  refine (intervalIntegral.norm_integral_le_of_norm_le
    (g := fun _ => (H * heatKernelMoment E α + L) * t ^ ((α : ℝ) / 2)) ht.le ?_
    intervalIntegrable_const).trans_eq ?_
  · rwa [uIoc_of_le ht.le, ae_restrict_iff' measurableSet_Ioc] at hbound
  · rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      rpow_add ht, rpow_one]
    ring

/-- For bounded forcing uniformly Hölder in space and approaching its initial slice at rate
`t^(α/2)` on a positive time horizon, `w(t, ·) / t` converges uniformly to `f(0, ·)`. -/
theorem tendstoUniformly_inv_smul_heatDuhamelPotential
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s))
    (hL : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      ∀ x, ‖f s x - f 0 x‖ ≤ L * s ^ ((α : ℝ) / 2))
    (hα : 0 < α) (hT : 0 < T) :
    TendstoUniformly (fun t x => t⁻¹ • heatDuhamelPotential f t x) (f 0) (𝓝[>] 0) := by
  have hp : (0 : ℝ) < (α : ℝ) / 2 := by positivity
  have hlim : Tendsto (fun t : ℝ => (H * heatKernelMoment E α + L) * t ^ ((α : ℝ) / 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa [zero_rpow hp.ne'] using ((continuousAt_rpow_const 0 _ (Or.inr hp.le)).tendsto
      |>.mono_left nhdsWithin_le_nhds).const_mul
        ((H : ℝ) * heatKernelMoment E α + L)
  refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
  filter_upwards [hlim.eventually (gt_mem_nhds hε), self_mem_nhdsWithin,
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t hεt (ht : 0 < t) htT x
  have hsub : Ioo 0 t ⊆ Ioo 0 T := Ioo_subset_Ioo_right htT.le
  have hbound := norm_heatDuhamelPotential_sub_smul_le hf
    (ae_restrict_of_ae_restrict_of_subset hsub hfM)
    (ae_restrict_of_ae_restrict_of_subset hsub hH)
    (ae_restrict_of_ae_restrict_of_subset hsub hL) hα ht.le x
  have heq : t⁻¹ • heatDuhamelPotential f t x - f 0 x =
      t⁻¹ • (heatDuhamelPotential f t x - t • f 0 x) := by
    rw [smul_sub, inv_smul_smul₀ ht.ne']
  rw [dist_comm, dist_eq_norm, heq,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
  refine (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr ht.le)).trans_lt ?_
  convert hεt using 1
  rw [rpow_add ht, rpow_one]
  field_simp

/-- At time zero, the right time derivative of the Duhamel potential is the initial forcing.
Together with its zero initial value this gives the initial endpoint identity for the
inhomogeneous heat equation. -/
theorem hasDerivWithinAt_heatDuhamelPotential_zero
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s))
    (hL : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      ∀ x, ‖f s x - f 0 x‖ ≤ L * s ^ ((α : ℝ) / 2))
    (hα : 0 < α) (hT : 0 < T) (x : E) :
    HasDerivWithinAt (fun t => heatDuhamelPotential f t x) (f 0 x) (Ici 0) 0 := by
  apply HasDerivWithinAt.Ici_of_Ioi
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have hslope : slope (fun t => heatDuhamelPotential f t x) 0 =
      fun t => t⁻¹ • heatDuhamelPotential f t x := by
    funext t
    simp [slope_def_module]
  simpa only [hslope] using
    (tendstoUniformly_inv_smul_heatDuhamelPotential hf hfM hH hL hα hT).tendsto_at x

/-- Parabolic Hölder forcing on a closed slab gives the initial time derivative `f(0, x)`
of the Duhamel potential within that slab. -/
theorem hasDerivWithinAt_heatDuhamelPotential_zero_of_holderOnWith
    (hf : StronglyMeasurable (Function.uncurry f))
    (hfM : ∀ᵐ s ∂volume.restrict (Ioo 0 T), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hpar : HolderOnWith H α (fun p : ParabolicSpaceTime E => f p.time p.space)
      (ParabolicSpaceTime.slab 0 T))
    (hα : 0 < α) (hT : 0 < T) (x : E) :
    HasDerivWithinAt (fun t => heatDuhamelPotential f t x) (f 0 x) (Icc 0 T) 0 := by
  have hmem {s : ℝ} (hs : s ∈ Icc 0 T) (y : E) :
      ParabolicSpaceTime.ofCoords y s ∈ ParabolicSpaceTime.slab 0 T := by
    simpa using hs
  have hH : ∀ᵐ s ∂volume.restrict (Ioo 0 T), HolderWith H α (f s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact ParabolicSpaceTime.holderWith_of_holderOnWith_slab hpar ⟨hs.1.le, hs.2.le⟩
  have hL : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      ∀ y, ‖f s y - f 0 y‖ ≤ H * s ^ ((α : ℝ) / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs y
    simpa [ParabolicSpaceTime.dist_ofCoords_ofCoords_same_space, dist_eq_norm,
      abs_of_pos hs.1, ← rpow_div_two_eq_sqrt _ hs.1.le] using
      hpar.dist_le (x := ParabolicSpaceTime.ofCoords y s) (y := ParabolicSpaceTime.ofCoords y 0)
        (hmem ⟨hs.1.le, hs.2.le⟩ y) (hmem ⟨le_rfl, hT.le⟩ y)
  exact (hasDerivWithinAt_heatDuhamelPotential_zero hf hfM hH hL hα hT x).mono
    Icc_subset_Ici_self

end TauCeti
