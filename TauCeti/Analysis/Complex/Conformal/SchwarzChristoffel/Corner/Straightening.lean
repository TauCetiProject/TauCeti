/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Prevertex
public import TauCeti.Analysis.SpecialFunctions.Pow.Sector

import TauCeti.Analysis.Complex.Conformal.Reflection.Injective

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
  have hq_ne {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}) (hzx : z ≠ (x : ℂ)) :
      f z - w ≠ 0 := by
    rw [sub_ne_zero]
    intro hzw
    exact hzx (hfinj hz hxclosed (hzw.trans hfx.symm))
  have hangle : Real.pi * β / 2 ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · exact div_nonneg (mul_nonneg Real.pi_pos.le hβ.1.le) (by norm_num)
    · nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hβ.2)]
  have hsector_closed {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}) :
      (f z - w).arg ∈ Icc (-(Real.pi * β / 2)) (Real.pi * β / 2) := by
    have hzclosure : z ∈ closure (Ω ∩ {y : ℂ | 0 < y.im}) := by
      apply hΩopen.inter_closure
      exact ⟨hz.1, by simpa only [Complex.closure_setOfPred_lt_im, mem_ofPred_eq] using hz.2⟩
    have hqcont : ContinuousWithinAt (fun y => f y - w) (Ω ∩ {y : ℂ | 0 < y.im}) z :=
      ((hfcont z hz).sub continuousWithinAt_const).mono fun y hy =>
        ⟨hy.1, by simpa only [mem_ofPred_eq] using hy.2.le⟩
    have htarget : IsClosed {q : ℂ | ‖q‖ * Real.cos (Real.pi * β / 2) ≤ q.re} :=
      isClosed_le (continuous_norm.mul continuous_const) Complex.continuous_re
    apply (arg_mem_Icc_iff_norm_mul_cos_le_re hangle).2
    have hmem : f z - w ∈ closure {q : ℂ |
        ‖q‖ * Real.cos (Real.pi * β / 2) ≤ q.re} := by
      apply hqcont.mem_closure hzclosure
      intro y hy
      exact (arg_mem_Icc_iff_norm_mul_cos_le_re hangle).1
        (Ioo_subset_Icc_self (hsector_open y hy))
    simpa only [htarget.closure_eq, mem_ofPred_eq] using hmem
  have hsector_upper_lt_pi : Real.pi * β / 2 < Real.pi := by
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hβ.2)]
  have hrecover {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}) :
      ((f z - w) ^ ((β⁻¹ : ℝ) : ℂ)) ^ (β : ℂ) = f z - w := by
    apply cpow_inv_cpow_of_sector hβ.1
    rw [abs_le]
    simpa only [mem_Icc, mul_comm β Real.pi] using hsector_closed hz
  have hgcont : ContinuousOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz
    have hbase : 0 ≤ (f z - w).re ∨ (f z - w).im ≠ 0 := by
      rcases eq_or_ne z (x : ℂ) with rfl | hzx
      · simp [hfx]
      · have hslit : f z - w ∈ slitPlane := Complex.mem_slitPlane_iff_arg.mpr
          ⟨ne_of_lt ((hsector_closed hz).2.trans_lt hsector_upper_lt_pi), hq_ne hz hzx⟩
        exact (Complex.mem_slitPlane_iff.mp hslit).imp le_of_lt id
    have hqcont : ContinuousWithinAt (fun y => f y - w)
        (Ω ∩ {z : ℂ | 0 ≤ z.im}) z := (hfcont z hz).sub continuousWithinAt_const
    have hpowcont : ContinuousAt (fun q : ℂ => q ^ ((β⁻¹ : ℝ) : ℂ)) (f z - w) :=
      Complex.continuousAt_cpow_const_of_re_pos hbase (by
        simpa only [ofReal_re] using inv_pos.mpr hβ.1)
    have hroot : ContinuousWithinAt (fun y => (f y - w) ^ ((β⁻¹ : ℝ) : ℂ))
        (Ω ∩ {z : ℂ | 0 ≤ z.im}) z :=
      hpowcont.comp_continuousWithinAt (f := fun y => f y - w) hqcont
    exact continuousWithinAt_const.mul hroot
  have hgd : DifferentiableOn ℂ g (Ω ∩ {z : ℂ | 0 < z.im}) := by
    intro z hz
    have hzx : z ≠ (x : ℂ) := fun h => by simpa [h] using hz.2
    have hzclosed : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im} :=
      ⟨hz.1, by simpa only [mem_ofPred_eq] using hz.2.le⟩
    have hslit : f z - w ∈ slitPlane := Complex.mem_slitPlane_iff_arg.mpr
      ⟨ne_of_lt ((hsector_open z hz).2.trans hsector_upper_lt_pi), hq_ne hzclosed hzx⟩
    exact ((hfd z hz).sub_const w).cpow_const hslit |>.const_mul I
  have hgupper : MapsTo g (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hzx : z ≠ (x : ℂ) := fun h => by simpa [h] using hz.2
    have hzclosed : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im} :=
      ⟨hz.1, by simpa only [mem_ofPred_eq] using hz.2.le⟩
    have hpos := cpow_inv_re_pos_of_arg_mem_sector hβ.1
      (hq_ne hzclosed hzx) (hsector_open z hz)
    simpa only [mem_ofPred_eq, g, mul_im, I_re, I_im, zero_mul, one_mul, zero_add] using hpos
  have hginj : InjOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz y hy hzy
    have hroot : (f z - w) ^ ((β⁻¹ : ℝ) : ℂ) =
        (f y - w) ^ ((β⁻¹ : ℝ) : ℂ) := by
      have hzy' : I * (f z - w) ^ ((β⁻¹ : ℝ) : ℂ) =
          I * (f y - w) ^ ((β⁻¹ : ℝ) : ℂ) := by
        simpa only [g] using hzy
      exact mul_left_cancel₀ I_ne_zero hzy'
    have hpow := congrArg (fun q : ℂ => q ^ (β : ℂ)) hroot
    rw [hrecover hz, hrecover hy] at hpow
    exact hfinj hz hy (sub_left_inj.mp hpow)
  let G : ℂ → ℂ := schwarzReflection g
  have hG_eq_g {z : ℂ} (hz : 0 ≤ z.im) : G z = g z := by
    simpa only [G] using schwarzReflection_of_im_nonneg (f := g) hz
  have hGd : DifferentiableOn ℂ G Ω := by
    simpa only [G] using
      differentiableOn_schwarzReflection_of_symmetric hΩopen hΩconj hgcont hgd hreal
  have hGx : G x = 0 := by
    rw [hG_eq_g (by simp)]
    simp [g, hfx, hβ.1.ne']
  have hGderiv : deriv G x ≠ 0 := by
    simpa only [G] using
      deriv_schwarzReflection_ne_zero hΩopen hΩconj hgcont hgd hreal hgupper hginj hxΩ
  let h : ℂ → ℂ := fun z => -I * G z
  have hhd : DifferentiableOn ℂ h Ω := fun z hz => by
    simpa only [h] using (hGd z hz).const_mul (-I)
  have hhx : h x = 0 := by simp [h, hGx]
  have hdh : deriv h x ≠ 0 := by
    have hderiv : deriv h x = -I * deriv G x := by
      simpa only [h] using
        ((hGd.differentiableAt (hΩopen.mem_nhds hxΩ)).hasDerivAt.const_mul (-I)).deriv
    rw [hderiv]
    exact mul_ne_zero (by simp) hGderiv
  have hhroot {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 < z.im}) :
      h z = (f z - w) ^ ((β⁻¹ : ℝ) : ℂ) := by
    dsimp only [h]
    rw [hG_eq_g hz.2.le]
    simp [g, ← mul_assoc]
  refine ⟨h, hhd, hhx, hdh, ?_, ?_⟩
  · intro z hz
    have hzclosed : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im} :=
      ⟨hz.1, by simpa only [mem_ofPred_eq] using hz.2.le⟩
    rw [hhroot hz, mem_slitPlane_iff]
    exact Or.inl (cpow_inv_re_pos_of_arg_mem_sector hβ.1
      (hq_ne hzclosed (fun h => by simpa [h] using hz.2)) (hsector_open z hz))
  · intro z hz
    have hzclosed : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im} :=
      ⟨hz.1, by simpa only [mem_ofPred_eq] using hz.2.le⟩
    dsimp only
    rw [hhroot hz, hrecover hzclosed]
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
