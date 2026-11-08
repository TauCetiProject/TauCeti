/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Prevertex
public import TauCeti.Analysis.SpecialFunctions.Pow.Sector

import TauCeti.Analysis.Complex.Conformal.Reflection.Corner
import TauCeti.Analysis.Complex.Conformal.Reflection.Injective
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Straightening a conformal corner

Suppose that, after translation, a conformal map takes the upper half of a neighbourhood of a
real point into a sector of opening `βπ`, centred on the positive real axis.  The principal power
`(f - w) ^ (1 / β)` maps that sector into the right half-plane, and multiplication by `I` maps it
into the upper half-plane.  If the two boundary sides go to the real axis, Schwarz reflection
extends this straightened coordinate holomorphically across the corner.  Injectivity makes its
zero at the corner simple.  Rotating back gives a holomorphic base `h` with

`f = w + h ^ β`.

This is the local analytic bridge between polygonal boundary geometry and the corner-power
hypothesis used to compute the pre-Schwarzian residue.  The second theorem feeds the constructed
base directly to that residue theorem.

## Main results

* `TauCeti.exists_corner_power_of_arg_mem_sector` -- Schwarz reflection produces a holomorphic
  simple-zero base for the corner power.
* `TauCeti.tendsto_sub_mul_nhdsNE_of_arg_mem_sector` -- a continued pre-Schwarzian has residue
  `β - 1` at such a corner.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Complex Filter Set Topology
open scoped ComplexConjugate

namespace TauCeti

private theorem pi_mul_div_two_lt_pi {β : ℝ} (hβ : β < 2) :
    Real.pi * β / 2 < Real.pi := by
  nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hβ)]

/-- The closed upper part of the corner stays in the closed sector: the argument condition on the
open upper part passes to its closure by continuity of `f`. -/
private theorem arg_sub_mem_Icc_of_arg_mem_sector {Ω : Set ℂ} {f : ℂ → ℂ} {w : ℂ} {β : ℝ}
    (hΩopen : IsOpen Ω) (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hfcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hsector_open : ∀ z ∈ Ω ∩ {z : ℂ | 0 < z.im},
      (f z - w).arg ∈ Ioo (-(Real.pi * β / 2)) (Real.pi * β / 2))
    {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}) :
    (f z - w).arg ∈ Icc (-(Real.pi * β / 2)) (Real.pi * β / 2) := by
  have hangle : Real.pi * β / 2 ∈ Icc (0 : ℝ) Real.pi :=
    ⟨div_nonneg (mul_nonneg Real.pi_pos.le hβ.1.le) (by norm_num),
      (pi_mul_div_two_lt_pi hβ.2).le⟩
  have hzclosure : z ∈ closure (Ω ∩ {y : ℂ | 0 < y.im}) := by
    apply hΩopen.inter_closure
    exact ⟨hz.1, by simpa only [Complex.closure_setOfPred_lt_im, mem_ofPred_eq] using hz.2⟩
  have hqcont : ContinuousWithinAt (fun y => f y - w) (Ω ∩ {y : ℂ | 0 < y.im}) z :=
    ((hfcont z hz).sub continuousWithinAt_const).mono fun y hy =>
      ⟨hy.1, by simpa only [mem_ofPred_eq] using hy.2.le⟩
  have htarget : IsClosed {q : ℂ | ‖q‖ * Real.cos (Real.pi * β / 2) ≤ q.re} :=
    isClosed_le (continuous_norm.mul continuous_const) Complex.continuous_re
  apply (arg_mem_Icc_iff_norm_mul_cos_le_re hangle).2
  have hmem : f z - w ∈ closure {q : ℂ | ‖q‖ * Real.cos (Real.pi * β / 2) ≤ q.re} := by
    apply hqcont.mem_closure hzclosure
    intro y hy
    exact (arg_mem_Icc_iff_norm_mul_cos_le_re hangle).1
      (Ioo_subset_Icc_self (hsector_open y hy))
  simpa only [htarget.closure_eq, mem_ofPred_eq] using hmem

/-- A point of the open upper part lies in the closed upper part, and is not the corner. -/
private theorem mem_closed_and_ne_of_mem_upper {Ω : Set ℂ} {f : ℂ → ℂ} {x : ℝ} {w : ℂ}
    (hq_ne : ∀ z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}, z ≠ (x : ℂ) → f z - w ≠ 0) {z : ℂ}
    (hz : z ∈ Ω ∩ {z : ℂ | 0 < z.im}) :
    z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im} ∧ f z - w ≠ 0 := by
  have hzclosed : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im} :=
    ⟨hz.1, by simpa only [mem_ofPred_eq] using hz.2.le⟩
  exact ⟨hzclosed, hq_ne z hzclosed fun h => by simpa [h] using hz.2⟩

/-- **Power-map straightening of a conformal corner.**  Let `f` be continuous and injective on
the closed upper part of a conjugation-symmetric neighbourhood `Ω`, holomorphic on its open upper
part, and send a real point `x` to the corner `w`.  Assume the translated interior values lie
strictly inside the sector of opening `βπ`, and that the straightened coordinate

`I * (f z - w) ^ (1 / β)`

is real on the boundary.  Then there is a holomorphic function `h` on `Ω`, with a simple zero at
`x`, whose values above the axis lie in the slit plane and satisfy `f = w + h ^ β`. -/
theorem exists_corner_power_of_arg_mem_sector {Ω : Set ℂ} {f : ℂ → ℂ} {x : ℝ} {w : ℂ} {β : ℝ}
    (hΩopen : IsOpen Ω) (hΩconj : MapsTo (starRingEnd ℂ) Ω Ω) (hxΩ : (x : ℂ) ∈ Ω)
    (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hfcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hfd : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 →
      (I * (f z - w) ^ ((β⁻¹ : ℝ) : ℂ)).im = 0)
    (hfinj : InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im})) (hfx : f x = w)
    (hsector_open : ∀ z ∈ Ω ∩ {z : ℂ | 0 < z.im},
      (f z - w).arg ∈ Ioo (-(Real.pi * β / 2)) (Real.pi * β / 2)) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h Ω ∧ h x = 0 ∧ deriv h x ≠ 0 ∧
      (∀ z ∈ Ω ∩ {z : ℂ | 0 < z.im}, h z ∈ slitPlane) ∧
      EqOn f (fun z => w + h z ^ (β : ℂ)) (Ω ∩ {z : ℂ | 0 < z.im}) := by
  let g : ℂ → ℂ := fun z => I * (f z - w) ^ ((β⁻¹ : ℝ) : ℂ)
  have hxclosed : (x : ℂ) ∈ Ω ∩ {z : ℂ | 0 ≤ z.im} := ⟨hxΩ, by simp⟩
  have hq_ne : ∀ z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}, z ≠ (x : ℂ) → f z - w ≠ 0 := fun z hz hzx h =>
    hzx (hfinj hz hxclosed ((sub_eq_zero.mp h).trans hfx.symm))
  have hsector_closed := fun z (hz : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}) =>
    arg_sub_mem_Icc_of_arg_mem_sector hΩopen hβ hfcont hsector_open hz
  have hrecover : ∀ z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im},
      ((f z - w) ^ ((β⁻¹ : ℝ) : ℂ)) ^ (β : ℂ) = f z - w := fun z hz => by
    refine cpow_inv_cpow_of_arg_mem_Ioc hβ.1 (Icc_subset_Ioc ?_ ?_ (hsector_closed z hz)) <;>
      linarith [mul_pos Real.pi_pos hβ.1, pi_mul_div_two_lt_pi hβ.2]
  -- The shared straightening of a corner, applied to the translated map `f - w`.
  obtain ⟨hgcont, hgd, hgupper⟩ := straighten_sector (f := fun z => f z - w) hβ
    (hfcont.sub continuousOn_const) (hfd.sub_const w)
    (fun z hz hzim => (mem_closed_and_ne_of_mem_upper hq_ne ⟨hz, hzim⟩).2)
    (fun z hz hzim => by
      have := hsector_open z ⟨hz, hzim⟩
      rw [abs_lt]
      constructor <;> linarith [this.1, this.2])
    (fun z hz => by
      have := hsector_closed z hz
      rw [abs_le]
      constructor <;> linarith [this.1, this.2])
  have hginj := injOn_I_mul_cpow_inv (f := fun z => f z - w)
    (fun z hz y hy hzy => hfinj hz hy (sub_left_inj.mp hzy)) hrecover
  have hGd := differentiableOn_schwarzReflection_of_symmetric hΩopen hΩconj hgcont hgd hreal
  have hG_eq_g {z : ℂ} (hz : 0 ≤ z.im) : schwarzReflection g z = g z :=
    schwarzReflection_of_im_nonneg (f := g) hz
  have hGx : schwarzReflection g x = 0 := by
    rw [hG_eq_g (by simp)]
    simp [g, hfx, hβ.1.ne']
  have hGderiv := deriv_schwarzReflection_ne_zero hΩopen hΩconj hgcont hgd hreal hgupper hginj hxΩ
  let h : ℂ → ℂ := fun z => -I * schwarzReflection g z
  have hhd : DifferentiableOn ℂ h Ω := hGd.const_mul (-I)
  have hhx : h x = 0 := by
    dsimp only [h]
    rw [hGx, mul_zero]
  have hdh : deriv h x ≠ 0 := by
    dsimp only [h]
    rw [deriv_const_mul_field]
    exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hGderiv
  have hhroot {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 < z.im}) :
      h z = (f z - w) ^ ((β⁻¹ : ℝ) : ℂ) := by
    dsimp only [h]
    rw [hG_eq_g hz.2.le]
    simp [g, ← mul_assoc]
  refine ⟨h, hhd, hhx, hdh, fun z hz => ?_, fun z hz => ?_⟩
  · rw [hhroot hz, mem_slitPlane_iff]
    exact Or.inl (cpow_inv_re_pos_of_arg_mem_sector hβ.1
      (mem_closed_and_ne_of_mem_upper hq_ne hz).2 (hsector_open z hz))
  · dsimp only
    rw [hhroot hz, hrecover z (mem_closed_and_ne_of_mem_upper hq_ne hz).1]
    ring

/-- **The pre-Schwarzian residue after sector straightening.**  Under the hypotheses of
`exists_corner_power_of_arg_mem_sector`, a conjugation-symmetric holomorphic continuation `φ` of
the pre-Schwarzian derivative has residue `β - 1` at the corner. -/
theorem tendsto_sub_mul_nhdsNE_of_arg_mem_sector {Ω : Set ℂ} {f φ : ℂ → ℂ} {x r : ℝ}
    {w : ℂ} {β : ℝ} (hΩopen : IsOpen Ω) (hΩconj : MapsTo (starRingEnd ℂ) Ω Ω)
    (hxΩ : (x : ℂ) ∈ Ω) (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hfcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hfd : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 →
      (I * (f z - w) ^ ((β⁻¹ : ℝ) : ℂ)).im = 0)
    (hfinj : InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im})) (hfx : f x = w)
    (hsector_open : ∀ z ∈ Ω ∩ {z : ℂ | 0 < z.im},
      (f z - w).arg ∈ Ioo (-(Real.pi * β / 2)) (Real.pi * β / 2))
    (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball (x : ℂ) r \ {(x : ℂ)}))
    (hφconj : ∀ z ∈ Metric.ball (x : ℂ) r \ {(x : ℂ)},
      φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hφf : EqOn φ (logDeriv (deriv f))
      (Ω ∩ {z : ℂ | 0 < z.im})) :
    Tendsto (fun z => (z - (x : ℂ)) * φ z) (𝓝[≠] ((x : ℝ) : ℂ))
      (𝓝 ((β : ℂ) - 1)) := by
  obtain ⟨h, hhd, hhx, hdh, hslit, hfh⟩ := exists_corner_power_of_arg_mem_sector hΩopen hΩconj
    hxΩ hβ hfcont hfd hreal hfinj hfx hsector_open
  have hφf' : EqOn φ (logDeriv (deriv f)) (UpperHalfPlane.upperHalfPlaneSet ∩ Ω) := by
    intro z hz
    exact hφf ⟨hz.2, hz.1⟩
  have hslit' : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet ∩ Ω, h z ∈ slitPlane := by
    intro z hz
    exact hslit z ⟨hz.2, hz.1⟩
  have hfh' : EqOn f (fun z => w + h z ^ (β : ℂ))
      (UpperHalfPlane.upperHalfPlaneSet ∩ Ω) := by
    intro z hz
    exact hfh ⟨hz.2, hz.1⟩
  apply tendsto_sub_mul_nhdsNE_of_eqOn_add_cpow hr hφ hφconj
      hφf' hΩopen hxΩ hhd hhx hdh hslit' (by exact_mod_cast hβ.1.ne') hfh'

end TauCeti

end
