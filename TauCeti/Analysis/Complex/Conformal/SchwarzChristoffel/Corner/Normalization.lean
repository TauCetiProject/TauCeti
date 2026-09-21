/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Prevertex
import TauCeti.Analysis.Complex.Conformal.Reflection.Injective
import TauCeti.Analysis.Complex.UpperLogContinuity
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Power normalization of a conformal corner

A conformal map meeting two straight boundary edges at an angle `βπ` can be straightened by
the power `z ↦ z ^ (1 / β)`.  For a convex corner, `0 < β ≤ 1`, the normalized corner lies in
the closed upper half-plane, so the principal power is continuous up to both edges.  It maps the
open corner to the upper half-plane and both edges to the real axis.  Schwarz reflection therefore
extends it through the prevertex.

This file proves that the reflected power coordinate is holomorphic and injective, vanishes
simply at the prevertex, and recovers the original map in the corner-power form `w + h ^ β`.
The simple-zero coordinate is the local input used to compute the pre-Schwarzian residue at a
Schwarz--Christoffel prevertex.

## Main result

* `TauCeti.exists_differentiableOn_injOn_eqOn_add_cpow_of_convex_corner` -- a conformal convex
  corner admits a holomorphic simple-zero power coordinate across its prevertex.
* `TauCeti.tendsto_sub_mul_nhdsNE_of_convex_corner` -- the continued pre-Schwarzian derivative
  has residue `β - 1` at such a corner.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Filter Set Topology

namespace TauCeti

/-- **A convex conformal corner has a holomorphic simple-zero power coordinate.**

Let `f` be continuous and injective on the closed upper part of a conjugation-symmetric open set
and holomorphic on its open upper part.  Suppose `f x = w` at a real boundary point and `f - w`
lies in the closed sector from angle `0` to angle `βπ`, taking interior points to the open sector
and boundary points to one of its two rays.  If `0 < β ≤ 1`, then the principal power
`(f - w) ^ (1 / β)` straightens the sector to the upper half-plane.  Its Schwarz reflection is a
holomorphic injection `h` through `x`, has a simple zero there, and satisfies
`f = w + h ^ β` on the open upper part.

The bound `β ≤ 1` is the convex-corner condition.  It ensures that the original sector is contained
in the closed upper half-plane, including the one-sided principal-power continuity on its second
edge. -/
theorem exists_differentiableOn_injOn_eqOn_add_cpow_of_convex_corner
    {f : ℂ → ℂ} {Ω : Set ℂ} {x : ℝ} {w : ℂ} {β : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hΩopen : IsOpen Ω)
    (hΩconj : MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hxΩ : (x : ℂ) ∈ Ω) (hfx : f (x : ℂ) = w)
    (hinterior : ∀ z ∈ Ω ∩ {z : ℂ | 0 < z.im},
      Complex.arg (f z - w) ∈ Ioo 0 (β * Real.pi))
    (hedges : ∀ z ∈ Ω, z.im = 0 →
      Complex.arg (f z - w) = 0 ∨ Complex.arg (f z - w) = β * Real.pi)
    (hinj : InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im})) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ InjOn h Ω ∧ h (x : ℂ) = 0 ∧
      deriv h (x : ℂ) ≠ 0 ∧ MapsTo h (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} ∧
      EqOn f (fun z => w + h z ^ (β : ℂ)) (Ω ∩ {z : ℂ | 0 < z.im}) := by
  let g : ℂ → ℂ := fun z => (f z - w) ^ ((β⁻¹ : ℝ) : ℂ)
  have hβinv : 0 < β⁻¹ := inv_pos.mpr hβ
  have hsector : ∀ z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}, 0 ≤ (f z - w).im := by
    intro z hz
    apply Complex.arg_nonneg_iff.mp
    have hzim : 0 ≤ z.im := hz.2
    rcases hzim.eq_or_lt with haxis | hpos
    · rcases hedges z hz.1 haxis.symm with harg | harg
      · rw [harg]
      · rw [harg]
        positivity
    · exact (hinterior z ⟨hz.1, hpos⟩).1.le
  have hcontg : ContinuousOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
    exact (continuousOn_cpow_const_im_nonneg (by simpa using hβinv)).comp
      (hcont.sub continuousOn_const) hsector
  have harg_le_pi {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 < z.im}) :
      Complex.arg (f z - w) < Real.pi :=
    (hinterior z hz).2.trans_le (mul_le_of_le_one_left Real.pi_nonneg hβ1)
  have him_pos {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 < z.im}) : 0 < (f z - w).im := by
    rw [← Complex.norm_mul_sin_arg (f z - w)]
    exact mul_pos (norm_pos_iff.mpr fun h => by
      have := (hinterior z hz).1
      rw [h, Complex.arg_zero] at this
      exact this.false) (Real.sin_pos_of_pos_of_lt_pi (hinterior z hz).1 (harg_le_pi hz))
  have hdiffg : DifferentiableOn ℂ g (Ω ∩ {z : ℂ | 0 < z.im}) := by
    intro z hz
    exact ((hholo z hz).sub (differentiableAt_const w).differentiableWithinAt).cpow_const
      (Or.inr (him_pos hz).ne')
  have hupper : MapsTo g (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hne : f z - w ≠ 0 := ne_of_apply_ne Complex.arg (by
      simpa using (hinterior z hz).1.ne')
    have hang0 : 0 < Complex.arg (f z - w) * β⁻¹ :=
      mul_pos (hinterior z hz).1 hβinv
    have hangpi : Complex.arg (f z - w) * β⁻¹ < Real.pi := calc
      _ < (β * Real.pi) * β⁻¹ := mul_lt_mul_of_pos_right (hinterior z hz).2 hβinv
      _ = Real.pi := by field_simp
    -- Expose the local abbreviation so the power's imaginary-part formula can rewrite the goal.
    change 0 < (g z).im
    dsimp only [g]
    rw [Complex.cpow_ofReal_im]
    exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hne) _) <|
      Real.sin_pos_of_pos_of_lt_pi hang0 hangpi
  have hreal : ∀ z ∈ Ω, z.im = 0 → (g z).im = 0 := by
    intro z hz hzim
    rcases hedges z hz hzim with harg | harg
    · dsimp only [g]
      rw [Complex.cpow_ofReal_im, harg, zero_mul, Real.sin_zero, mul_zero]
    · dsimp only [g]
      rw [Complex.cpow_ofReal_im, harg]
      have : β * Real.pi * β⁻¹ = Real.pi := by field_simp
      rw [this, Real.sin_pi, mul_zero]
  have hrecover {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}) :
      g z ^ (β : ℂ) = f z - w := by
    refine cpow_inv_cpow_of_arg_mem_Icc hβ ⟨?_, ?_⟩
    · exact Complex.arg_nonneg_iff.mpr (hsector z hz)
    · have hzim : 0 ≤ z.im := hz.2
      rcases hzim.eq_or_lt with haxis | hpos
      · rcases hedges z hz.1 haxis.symm with harg | harg
        · rw [harg]
          positivity
        · exact harg.le
      · exact (hinterior z ⟨hz.1, hpos⟩).2.le
  have hinjg : InjOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz y hy hzy
    apply hinj hz hy
    have hsub : f z - w = f y - w := by rw [← hrecover hz, ← hrecover hy, hzy]
    exact sub_left_injective hsub
  let h := schwarzReflection g
  have hhdiff : DifferentiableOn ℂ h Ω :=
    differentiableOn_schwarzReflection_of_symmetric hΩopen hΩconj hcontg hdiffg hreal
  have hhinj : InjOn h Ω :=
    injOn_schwarzReflection_of_symmetric hΩconj hupper
      (fun z hz hzim => (hreal z hz hzim).ge) hinjg
  have hheq : EqOn h g (Ω ∩ {z : ℂ | 0 ≤ z.im}) :=
    eqOn_schwarzReflection_of_subset_im_nonneg fun _ hz => hz.2
  refine ⟨h, hhdiff, hhinj, ?_, ?_, ?_, ?_⟩
  · rw [hheq ⟨hxΩ, by simp⟩]
    dsimp only [g]
    rw [hfx, sub_self]
    exact Complex.zero_cpow (ofReal_ne_zero.mpr hβinv.ne')
  · exact deriv_schwarzReflection_ne_zero hΩopen hΩconj hcontg hdiffg hreal hupper hinjg
      hxΩ
  · intro z hz
    have hzim : 0 ≤ z.im := hz.2.le
    rw [hheq ⟨hz.1, hzim⟩]
    exact hupper hz
  · intro z hz
    -- Expose `EqOn`'s pointwise goal so the two characteristic equalities can rewrite it.
    change f z = w + h z ^ (β : ℂ)
    have hzim : 0 ≤ z.im := hz.2.le
    rw [hheq ⟨hz.1, hzim⟩, hrecover ⟨hz.1, hzim⟩]
    ring

/-- **The pre-Schwarzian residue at a convex conformal corner.** Under the geometric sector
hypotheses of
`TauCeti.exists_differentiableOn_injOn_eqOn_add_cpow_of_convex_corner`, a conjugation-symmetric
holomorphic continuation `φ` of the pre-Schwarzian derivative has residue `β - 1` at the
prevertex. This discharges the abstract corner-power-coordinate hypotheses of
`TauCeti.tendsto_sub_mul_nhdsNE_of_eqOn_add_cpow`. -/
theorem tendsto_sub_mul_nhdsNE_of_convex_corner {φ f : ℂ → ℂ} {Ω : Set ℂ}
    {x r β : ℝ} {w : ℂ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (Metric.ball (x : ℂ) r \ {(x : ℂ)}))
    (hφconj : ∀ z ∈ Metric.ball (x : ℂ) r \ {(x : ℂ)},
      φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hφf : EqOn φ (logDeriv (deriv f)) ({z : ℂ | 0 < z.im} ∩ Ω))
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hΩopen : IsOpen Ω)
    (hΩconj : MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hxΩ : (x : ℂ) ∈ Ω) (hfx : f (x : ℂ) = w)
    (hinterior : ∀ z ∈ Ω ∩ {z : ℂ | 0 < z.im},
      Complex.arg (f z - w) ∈ Ioo 0 (β * Real.pi))
    (hedges : ∀ z ∈ Ω, z.im = 0 →
      Complex.arg (f z - w) = 0 ∨ Complex.arg (f z - w) = β * Real.pi)
    (hinj : InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im})) :
    Tendsto (fun z => (z - (x : ℂ)) * φ z) (nhdsWithin (x : ℂ) {(x : ℂ)}ᶜ)
      (nhds ((β : ℂ) - 1)) := by
  obtain ⟨h, hhdiff, -, hhx, hdh, hupper, hfh⟩ :=
    exists_differentiableOn_injOn_eqOn_add_cpow_of_convex_corner hβ hβ1 hΩopen hΩconj
      hcont hholo hxΩ hfx hinterior hedges hinj
  apply tendsto_sub_mul_nhdsNE_of_eqOn_add_cpow (w := w) (β := (β : ℂ))
    hr hφ hφconj hφf hΩopen hxΩ hhdiff hhx hdh
  · intro z hz
    exact Or.inr (hupper ⟨hz.2, hz.1⟩).ne'
  · exact ofReal_ne_zero.mpr hβ.ne'
  · simpa [inter_comm] using hfh

end TauCeti

end
