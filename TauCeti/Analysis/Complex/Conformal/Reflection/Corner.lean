/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Injective
public import TauCeti.Analysis.SpecialFunctions.Pow.Sector
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power coordinates at a polygonal corner

A holomorphic injection meeting the two rays of a sector of opening `β * π`, with
`0 < β < 2`, has a power representation `f = h ^ β`, where `h` extends holomorphically
across the source boundary and has a simple zero at the prevertex. The sector is centered on
the positive real axis; translating the vertex and rotating its bisector gives this
normalization for any polygonal corner, including a reentrant corner.

The map `I * f ^ (1 / β)` straightens the corner to the upper half-plane. Schwarz reflection
then supplies a holomorphic injection across the real axis. In particular the nonzero
derivative of the corner coordinate is a conclusion, not a boundary regularity assumption.
This power coordinate is the input for computing the pre-Schwarzian residue at a prevertex.

The same straightening, without any injectivity assumption, reduces isolated boundary zeros of a
sector-valued map to those of a map real on the axis: a map into the sector, nonzero in the open
upper half-disc about a real point, has no zeros on the closed half-disc near that point other than
the point itself (`TauCeti.eventually_ne_zero_of_sector`).

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Complex Filter Set Topology

namespace TauCeti

/-- The boundary condition of a map into the sector of opening `β * π`: on the closed upper part,
its values lie in the closed sector `|arg| ≤ β * π / 2`. -/
private theorem abs_arg_le_of_sector {Ω : Set ℂ} {f : ℂ → ℂ} {β : ℝ} (hβ : 0 < β)
    (hsector : ∀ z ∈ Ω, 0 < z.im → |(f z).arg| < β * Real.pi / 2)
    (hrays : ∀ z ∈ Ω, z.im = 0 → f z ≠ 0 → |(f z).arg| = β * Real.pi / 2) :
    ∀ z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}, |(f z).arg| ≤ β * Real.pi / 2 := by
  intro z hz
  have hz0 : 0 ≤ z.im := hz.2
  rcases hz0.lt_or_eq with hpos | hzero
  · exact (hsector z hz.1 hpos).le
  · by_cases hfz : f z = 0
    · simpa only [hfz, arg_zero, abs_zero] using
        (div_nonneg (mul_pos hβ Real.pi_pos).le (by norm_num : (0 : ℝ) ≤ 2))
    · exact (hrays z hz.1 hzero.symm hfz).le

/-- **Straightening a corner.**  For a map `f` into the sector of opening `β * π`, with
`0 < β < 2`, nonzero on the open upper part and with its nonzero boundary values on the two
bounding rays, the power coordinate `I * f ^ (1 / β)` is continuous on the closed upper part,
holomorphic on the open upper part, real on the axis, and carries the open upper part into the
upper half-plane. -/
private theorem straighten_sector {Ω : Set ℂ} {f : ℂ → ℂ} {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hne : ∀ z ∈ Ω, 0 < z.im → f z ≠ 0)
    (hsector : ∀ z ∈ Ω, 0 < z.im → |(f z).arg| < β * Real.pi / 2)
    (hrays : ∀ z ∈ Ω, z.im = 0 → f z ≠ 0 → |(f z).arg| = β * Real.pi / 2) :
    ContinuousOn (fun z => I * f z ^ ((β⁻¹ : ℝ) : ℂ)) (Ω ∩ {z : ℂ | 0 ≤ z.im}) ∧
      DifferentiableOn ℂ (fun z => I * f z ^ ((β⁻¹ : ℝ) : ℂ)) (Ω ∩ {z : ℂ | 0 < z.im}) ∧
      (∀ z ∈ Ω, z.im = 0 → (I * f z ^ ((β⁻¹ : ℝ) : ℂ)).im = 0) ∧
      MapsTo (fun z => I * f z ^ ((β⁻¹ : ℝ) : ℂ)) (Ω ∩ {z : ℂ | 0 < z.im})
        {z : ℂ | 0 < z.im} := by
  have hβc : (β : ℂ) ≠ 0 := ofReal_ne_zero.mpr hβ.1.ne'
  have hβinv : 0 < β⁻¹ := inv_pos.mpr hβ.1
  have hangle : β * Real.pi / 2 < Real.pi := by nlinarith [Real.pi_pos, hβ.2]
  have hbound := abs_arg_le_of_sector hβ.1 hsector hrays
  have hslit : ∀ z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}, f z ≠ 0 → f z ∈ slitPlane := by
    intro z hz hfz
    refine mem_slitPlane_iff_arg.mpr ⟨?_, hfz⟩
    have := (le_abs_self (f z).arg).trans (hbound z hz) |>.trans_lt hangle
    exact this.ne
  refine ⟨?_, ?_, ?_, ?_⟩
  -- The root is continuous even at the vertex and holomorphic away from it.
  · intro z hz
    have hc : ContinuousAt (fun w : ℂ => w ^ ((β⁻¹ : ℝ) : ℂ)) (f z) := by
      by_cases hfz : f z = 0
      · apply continuousAt_cpow_const_of_re_pos
        · simp [hfz]
        · simpa using hβinv
      · exact continuousAt_cpow_const (hslit z hz hfz)
    exact hc.continuousWithinAt.comp (hcont z hz) (mapsTo_univ _ _) |>.const_mul I
  · intro z hz
    have hz0 : 0 < z.im := hz.2
    exact ((hholo z hz).cpow_const (hslit z ⟨hz.1, hz0.le⟩ (hne z hz.1 hz0))).const_mul I
  -- The two rays become the real axis; the strict sector interior becomes the upper half-plane.
  · intro z hz hzim
    by_cases hfz : f z = 0
    · simp [hfz, hβc]
    · have heq : |(f z).arg * β⁻¹| = Real.pi / 2 := by
        rw [abs_mul, abs_of_pos hβinv, hrays z hz hzim hfz]
        field_simp [hβ.1.ne']
      simp only [I_mul_im, cpow_ofReal_re]
      rw [← Real.cos_abs, heq, Real.cos_pi_div_two, mul_zero]
  · intro z hz
    have hb : |(f z).arg * β⁻¹| < Real.pi / 2 := by
      rw [← div_eq_mul_inv, abs_div, abs_of_pos hβ.1, div_lt_iff₀ hβ.1]
      nlinarith [hsector z hz.1 hz.2]
    obtain ⟨hl, hu⟩ := abs_lt.mp hb
    have hpos := mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr (hne z hz.1 hz.2)) β⁻¹)
      (Real.cos_pos_of_mem_Ioo ⟨hl, hu⟩)
    simpa only [mem_ofPred_eq, I_mul_im, cpow_ofReal_re] using hpos

/-- **Power coordinate at a corner.** Suppose `f` is continuous and injective on the closed
upper part of a symmetric open set, holomorphic on its open upper part, and takes a real point
`x` to the vertex `0`. Its interior values lie strictly between the rays of arguments
`± β * π / 2`, and its nonzero boundary values lie on those rays. For every opening
`0 < β * π < 2 * π`, there is an injective holomorphic coordinate `h`, with a simple zero at
`x`, such that `f = h ^ β` on the closed upper part. The coordinate has positive real part
on the open upper part, fixing the branch of the power. On the closed upper part it equals the
principal `β`-th root of `f`, and conjugating the source negates the conjugate of the coordinate.
In particular, the coordinate is purely imaginary on the real axis. -/
theorem exists_differentiableOn_injOn_cpow_eq_of_sector
    {Ω : Set ℂ} {f : ℂ → ℂ} {x β : ℝ}
    (hβ : β ∈ Ioo (0 : ℝ) 2) (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hx : (x : ℂ) ∈ Ω) (hfx : f x = 0)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hinj : InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hsector : ∀ z ∈ Ω, 0 < z.im → |(f z).arg| < β * Real.pi / 2)
    (hrays : ∀ z ∈ Ω, z.im = 0 → f z ≠ 0 → |(f z).arg| = β * Real.pi / 2) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ InjOn h Ω ∧ h x = 0 ∧ deriv h x ≠ 0 ∧
      EqOn (fun z => h z ^ (β : ℂ)) f (Ω ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ Ω, 0 < z.im → 0 < (h z).re) ∧
      (∀ z ∈ Ω, h ((starRingEnd ℂ) z) = -(starRingEnd ℂ) (h z)) ∧
      EqOn h (fun z => f z ^ ((β⁻¹ : ℝ) : ℂ)) (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
  have hβc : (β : ℂ) ≠ 0 := ofReal_ne_zero.mpr hβ.1.ne'
  have hne : ∀ z ∈ Ω, 0 < z.im → f z ≠ 0 := by
    intro z hz hzim hfz
    have hzx := hinj ⟨hz, hzim.le⟩ ⟨hx, by simp⟩ (hfz.trans hfx.symm)
    simp [hzx] at hzim
  let g : ℂ → ℂ := fun z => I * f z ^ ((β⁻¹ : ℝ) : ℂ)
  obtain ⟨hgcont, hgholo, hgreal, hgupper⟩ := straighten_sector hβ hcont hholo hne hsector hrays
  have hpow : ∀ z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im},
      (f z ^ ((β⁻¹ : ℝ) : ℂ)) ^ (β : ℂ) = f z :=
    fun z hz => cpow_inv_cpow_of_sector hβ.1 (abs_arg_le_of_sector hβ.1 hsector hrays z hz)
  have hginj : InjOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz w hw hzw
    have hp : f z ^ ((β⁻¹ : ℝ) : ℂ) = f w ^ ((β⁻¹ : ℝ) : ℂ) :=
      mul_left_cancel₀ I_ne_zero hzw
    exact hinj hz hw (by rw [← hpow z hz, ← hpow w hw, hp])
  -- Reflect the straightened map, then undo its quarter-turn.
  obtain ⟨F, hd, hi, hF, hconj⟩ :=
    exists_differentiableOn_injOn_eqOn_conj_of_symmetric
      hΩopen hΩ hgcont hgholo hgreal hgupper hginj
  let h : ℂ → ℂ := fun z => -I * F z
  have heq : EqOn h (fun z => f z ^ ((β⁻¹ : ℝ) : ℂ))
      (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz
    simp [h, hF hz, ← mul_assoc]
  have hdh : DifferentiableOn ℂ h Ω := hd.const_mul (-I)
  have hih : InjOn h Ω := by
    intro z hz w hw hzw
    exact hi hz hw (mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero) hzw)
  refine ⟨h, hdh, hih, ?_, deriv_ne_zero_of_injOn hdh hΩopen hih hx, ?_, ?_, ?_, heq⟩
  · simpa only [hfx, ofReal_inv, zero_cpow (inv_ne_zero hβc)] using heq ⟨hx, by simp⟩
  · intro z hz
    simpa only [heq hz] using hpow z hz
  · intro z hz hzim
    have := hgupper ⟨hz, hzim⟩
    simpa [g, heq ⟨hz, hzim.le⟩] using this
  · intro z hz
    simp [h, hconj z hz]

/-- **Boundary zeros of a sector-valued map are isolated.**  Let `f` be continuous on the closed
upper half-disc about a real point `x` and holomorphic and nonzero on the open upper half-disc,
with values there in the open sector `|arg| < β * π / 2` of opening `β * π`, where `0 < β < 2`,
and with its nonzero values on the diameter on the two bounding rays.  Then near `x` the map `f`
has no zeros on the closed upper half-plane other than possibly `x` itself.

This is the sector form of `TauCeti.eventually_ne_zero_of_real_on_axis`, the case `β = 1` up to a
quarter-turn. -/
theorem eventually_ne_zero_of_sector {f : ℂ → ℂ} {x r β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hr : 0 < r) (hcont : ContinuousOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hne : ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → f z ≠ 0)
    (hsector : ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → |(f z).arg| < β * Real.pi / 2)
    (hrays : ∀ z ∈ Metric.ball (x : ℂ) r, z.im = 0 → f z ≠ 0 →
      |(f z).arg| = β * Real.pi / 2) :
    ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ), f z ≠ 0 := by
  -- the straightened map is real on the diameter, so its zeros there are isolated
  obtain ⟨hgc, hgd, hgr, hgu⟩ := straighten_sector hβ hcont hholo hne hsector hrays
  have hgne : ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → I * f z ^ ((β⁻¹ : ℝ) : ℂ) ≠ 0 := by
    intro z hz hzH h
    have him : 0 < (I * f z ^ ((β⁻¹ : ℝ) : ℂ)).im := hgu ⟨hz, hzH⟩
    rw [h, zero_im] at him
    exact lt_irrefl 0 him
  filter_upwards [eventually_ne_zero_of_real_on_axis hr hgc hgd hgr hgne] with z hz hfz
  exact hz (by simp [hfz, hβ.1.ne'])

end TauCeti
