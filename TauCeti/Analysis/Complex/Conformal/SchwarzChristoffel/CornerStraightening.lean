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
part, and send a real point `x` to the corner `w`.  Assume the translated values lie in the closed
sector of opening `βπ` on the closed upper part, strictly inside that sector in the open upper
part, and that the straightened coordinate

`I * (f z - w) ^ (1 / β)`

is real on the boundary.  Continuity of `f` and the closed-sector bound make the principal root
continuous even at the corner.  Schwarz reflection then produces a holomorphic function `h` on
`Ω`, with a simple zero at `x`, such that `f = w + h ^ β` above the axis.  The base stays in the
slit plane there, so the principal power is holomorphic on the region where the identity is used. -/
theorem exists_corner_power_of_arg_mem_sector {Ω : Set ℂ} {f : ℂ → ℂ} {x : ℝ} {w : ℂ} {β : ℝ}
    (hΩopen : IsOpen Ω) (hΩconj : MapsTo (starRingEnd ℂ) Ω Ω) (hxΩ : (x : ℂ) ∈ Ω)
    (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hfcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hfd : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 →
      (I * (f z - w) ^ ((β⁻¹ : ℝ) : ℂ)).im = 0)
    (hfinj : InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im})) (hfx : f x = w)
    (hsector : ∀ z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}, z ≠ (x : ℂ) →
      (f z - w).arg ∈ Icc (-(Real.pi * β / 2)) (Real.pi * β / 2))
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
  have hrecover {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}) :
      ((f z - w) ^ ((β⁻¹ : ℝ) : ℂ)) ^ (β : ℂ) = f z - w := by
    rcases eq_or_ne z (x : ℂ) with rfl | hzx
    · simp [hfx, hβ.1.ne']
    · exact Complex.cpow_inv_cpow_eq_of_arg_mem_closed_sector hβ.1 (hsector z hz hzx)
  have hgcont : ContinuousOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz
    have hbase : 0 ≤ (f z - w).re ∨ (f z - w).im ≠ 0 := by
      rcases eq_or_ne z (x : ℂ) with rfl | hzx
      · simp [hfx]
      · have hslit := Complex.mem_slitPlane_of_arg_mem_closed_sector hβ.2 (hq_ne hz hzx)
          (hsector z hz hzx)
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
    have hslit : f z - w ∈ slitPlane :=
      Complex.mem_slitPlane_of_arg_mem_sector hβ.2
        (hq_ne ⟨hz.1, (show 0 ≤ z.im from (show 0 < z.im from hz.2).le)⟩ hzx)
        (hsector_open z hz)
    exact ((hfd z hz).sub_const w).cpow_const hslit |>.const_mul I
  have hgupper : MapsTo g (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hzx : z ≠ (x : ℂ) := fun h => by simpa [h] using hz.2
    have hpos := Complex.cpow_inv_re_pos_of_arg_mem_sector hβ.1
      (hq_ne ⟨hz.1, (show 0 ≤ z.im from (show 0 < z.im from hz.2).le)⟩ hzx)
      (hsector_open z hz)
    change 0 < (I * (f z - w) ^ ((β⁻¹ : ℝ) : ℂ)).im
    simpa only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add] using hpos
  have hginj : InjOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz y hy hzy
    have hroot : (f z - w) ^ ((β⁻¹ : ℝ) : ℂ) =
        (f y - w) ^ ((β⁻¹ : ℝ) : ℂ) := by
      change I * (f z - w) ^ ((β⁻¹ : ℝ) : ℂ) =
        I * (f y - w) ^ ((β⁻¹ : ℝ) : ℂ) at hzy
      exact mul_left_cancel₀ I_ne_zero hzy
    have hpow := congrArg (fun q : ℂ => q ^ (β : ℂ)) hroot
    rw [hrecover hz, hrecover hy] at hpow
    exact hfinj hz hy (sub_left_inj.mp hpow)
  let G : ℂ → ℂ := schwarzReflection g
  have hGd : DifferentiableOn ℂ G Ω :=
    differentiableOn_schwarzReflection_of_symmetric hΩopen hΩconj hgcont hgd hreal
  have hGx : G x = 0 := by
    rw [show G x = g x by
      change schwarzReflection g (x : ℂ) = g x
      exact schwarzReflection_of_im_nonneg (by simp)]
    simp [g, hfx, hβ.1.ne']
  have hGderiv : deriv G x ≠ 0 :=
    deriv_schwarzReflection_ne_zero hΩopen hΩconj hgcont hgd hreal hgupper hginj hxΩ
  let h : ℂ → ℂ := fun z => -I * G z
  have hhd : DifferentiableOn ℂ h Ω := fun z hz => (hGd z hz).const_mul (-I)
  have hhx : h x = 0 := by simp [h, hGx]
  have hdh : deriv h x ≠ 0 := by
    rw [show deriv h x = -I * deriv G x by
      exact ((hGd.differentiableAt (hΩopen.mem_nhds hxΩ)).hasDerivAt.const_mul (-I)).deriv]
    exact mul_ne_zero (by simp) hGderiv
  have hhroot {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 < z.im}) :
      h z = (f z - w) ^ ((β⁻¹ : ℝ) : ℂ) := by
    change -I * G z = _
    rw [show G z = g z by
      change schwarzReflection g z = g z
      exact schwarzReflection_of_im_nonneg (show 0 ≤ z.im from
        (show 0 < z.im from hz.2).le)]
    dsimp only [g]
    rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  refine ⟨h, hhd, hhx, hdh, ?_, ?_⟩
  · intro z hz
    rw [hhroot hz, mem_slitPlane_iff]
    exact Or.inl (Complex.cpow_inv_re_pos_of_arg_mem_sector hβ.1
      (hq_ne ⟨hz.1, (show 0 ≤ z.im from (show 0 < z.im from hz.2).le)⟩
        (fun h => by simpa [h] using hz.2)) (hsector_open z hz))
  · intro z hz
    change f z = w + h z ^ (β : ℂ)
    rw [hhroot hz, hrecover ⟨hz.1, (show 0 ≤ z.im from (show 0 < z.im from hz.2).le)⟩]
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
    (hsector : ∀ z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}, z ≠ (x : ℂ) →
      (f z - w).arg ∈ Icc (-(Real.pi * β / 2)) (Real.pi * β / 2))
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
    hxΩ hβ hfcont hfd hreal hfinj hfx hsector hsector_open
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
