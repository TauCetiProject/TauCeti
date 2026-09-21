/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Converse
-- Non-public: the corner asymptotic, the conjugation-symmetric limit transfer, the branch facts
-- for a power with a real base point, and partial fractions are used only in proofs.
import TauCeti.Analysis.Complex.Conformal.PreSchwarzian
import TauCeti.Analysis.Complex.Conformal.Reflection.Basic
import TauCeti.Analysis.Complex.Conformal.Reflection.Corner
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.Analysis.Contour.PolarPart.PartialFraction

/-!
# The prevertex residues of the pre-Schwarzian derivative

A conformal map of the upper half-plane onto a polygon is holomorphic across each open boundary
interval between two consecutive prevertices, and its pre-Schwarzian derivative
`logDeriv (deriv f) = f'' / f'` continues across those intervals to a conjugation-symmetric
function `φ` holomorphic off the prevertices.  This file computes the residue of `φ` at a
prevertex and turns the resulting partial-fraction expansion into the Schwarz--Christoffel
formula.

At a prevertex the map has a **corner power form**: `f = w + h ^ β` near the prevertex inside the
upper half-plane, for a holomorphic `h` with a simple zero there, where `β` is the interior angle
divided by `π`.  The pre-Schwarzian derivative of such an `f` has residue asymptotic
`(z - x) * f''(z) / f'(z) → β - 1` from above, and conjugation symmetry propagates that
asymptotic to the punctured neighbourhood, so `β - 1` is the residue of `φ` at the prevertex.
Once each prevertex contributes its residue and `φ` decays at infinity, partial fractions identify
`φ` with `∑ i, e i / (z - a i)` and the integration theorem identifies `f` itself with an affine
image of the Schwarz--Christoffel primitive.

## Main results

* `TauCeti.tendsto_sub_mul_nhdsNE_of_eqOn_add_cpow` -- the continuation of the pre-Schwarzian
  derivative of a map with a corner power form has residue asymptotic `β - 1` at the
  corner.
* `TauCeti.tendsto_sub_mul_nhdsNE_of_sector` -- the same residue, derived from the geometric
  sector and boundary-ray conditions at a polygonal corner.
* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_tendsto` -- a map of the upper
  half-plane whose pre-Schwarzian derivative continues with at most simple poles of residues
  `e i` at the prevertices `a i` and decays at infinity is an affine image of the
  Schwarz--Christoffel primitive for those data.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

/-! ### The residue at a single corner -/

/-- **The pre-Schwarzian derivative has residue asymptotic `β - 1` at a corner.**  Let `φ`
be holomorphic on a punctured disc about a real point `x`, symmetric under conjugation, and agree
with the pre-Schwarzian derivative of `f` above the axis near `x`.  If `f` has the corner power
form `w + h ^ β` there, with `h` holomorphic and having a simple zero at `x`, then `(z - x) * φ z`
tends to `β - 1` as `z` tends to `x` from any direction. -/
theorem tendsto_sub_mul_nhdsNE_of_eqOn_add_cpow {φ f h : ℂ → ℂ} {x r : ℝ} {U : Set ℂ} {w β : ℂ}
    (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball (x : ℂ) r \ {(x : ℂ)}))
    (hφconj : ∀ z ∈ Metric.ball (x : ℂ) r \ {(x : ℂ)},
      φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hφf : EqOn φ (logDeriv (deriv f)) (upperHalfPlaneSet ∩ U))
    (hU : IsOpen U) (hxU : (x : ℂ) ∈ U) (hh : DifferentiableOn ℂ h U) (hhx : h (x : ℂ) = 0)
    (hdh : deriv h (x : ℂ) ≠ 0) (hslit : ∀ z ∈ upperHalfPlaneSet ∩ U, h z ∈ slitPlane)
    (hβ : β ≠ 0) (hf : EqOn f (fun z => w + h z ^ β) (upperHalfPlaneSet ∩ U)) :
    Tendsto (fun z => (z - (x : ℂ)) * φ z) (𝓝[≠] ((x : ℝ) : ℂ)) (𝓝 (β - 1)) := by
  -- `U` is a neighbourhood of `x`, so that filter is the whole upper half-plane filter.
  have hfilter : 𝓝[upperHalfPlaneSet ∩ U] ((x : ℝ) : ℂ) = 𝓝[upperHalfPlaneSet] ((x : ℝ) : ℂ) := by
    rw [inter_comm]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU))
  have hne : (𝓝[upperHalfPlaneSet ∩ U] ((x : ℝ) : ℂ)).NeBot := by
    rw [hfilter]
    exact Real.nhdsWithin_upperHalfPlaneSet_neBot x
  -- The corner asymptotic, taken along the part of the upper half-plane inside `U`.
  have hcorner := tendsto_sub_mul_logDeriv_deriv_of_eqOn_add_cpow hU hxU hh hhx hdh
    (isOpen_upperHalfPlaneSet.inter hU) hne inter_subset_right hslit hβ hf
  have hcornerφ : Tendsto (fun z => (z - (x : ℂ)) * φ z)
      (𝓝[upperHalfPlaneSet ∩ U] ((x : ℝ) : ℂ)) (𝓝 (β - 1)) := hcorner.congr' (by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hφf hz])
  rw [hfilter] at hcornerφ
  have hmul : DifferentiableOn ℂ (fun z => (z - (x : ℂ)) * φ z)
      (Metric.ball (x : ℂ) r \ {(x : ℂ)}) :=
    (by fun_prop : Differentiable ℂ fun z : ℂ => z - (x : ℂ)).differentiableOn.mul hφ
  have hconj : ∀ z ∈ Metric.ball (x : ℂ) r \ {(x : ℂ)},
      ((starRingEnd ℂ) z - (x : ℂ)) * φ ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) ((z - (x : ℂ)) * φ z) := fun z hz =>
    calc ((starRingEnd ℂ) z - (x : ℂ)) * φ ((starRingEnd ℂ) z)
        = ((starRingEnd ℂ) z - (starRingEnd ℂ) ((x : ℝ) : ℂ)) * (starRingEnd ℂ) (φ z) := by
          rw [Complex.conj_ofReal x, hφconj z hz]
      _ = (starRingEnd ℂ) ((z - (x : ℂ)) * φ z) := by rw [← map_sub, ← map_mul]
  exact tendsto_nhdsNE_of_tendsto_nhdsWithin_im_pos hr hmul hconj hcornerφ

/-- **The pre-Schwarzian residue at a polygonal corner is its normalized angle minus one.**
After translating the vertex `f x` and rotating and scaling by `b`, suppose a holomorphic
injection takes the upper part of a neighborhood of `x` into the sector
`|arg w| < β * π / 2`, with continuous boundary values on its two rays.
If its pre-Schwarzian has a conjugation-symmetric holomorphic continuation `φ` to a punctured
disc about `x`, then `(z - x) * φ z → β - 1` from every direction. Both convex and reentrant
corners are allowed. No power representation or boundary differentiability is assumed. -/
theorem tendsto_sub_mul_nhdsNE_of_sector {φ f : ℂ → ℂ} {x r β : ℝ} {Ω : Set ℂ} {b : ℂ}
    (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball (x : ℂ) r \ {(x : ℂ)}))
    (hφconj : ∀ z ∈ Metric.ball (x : ℂ) r \ {(x : ℂ)},
      φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hφf : EqOn φ (logDeriv (deriv f)) (upperHalfPlaneSet ∩ Ω))
    (hβ : β ∈ Ioo (0 : ℝ) 2) (hb : b ≠ 0) (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hx : (x : ℂ) ∈ Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hinj : InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hsector : ∀ z ∈ Ω, 0 < z.im → |((f z - f x) / b).arg| < β * Real.pi / 2)
    (hrays : ∀ z ∈ Ω, z.im = 0 → f z ≠ f x →
      |((f z - f x) / b).arg| = β * Real.pi / 2) :
    Tendsto (fun z => (z - (x : ℂ)) * φ z) (𝓝[≠] (x : ℂ)) (𝓝 ((β : ℂ) - 1)) := by
  let g : ℂ → ℂ := fun z => (f z - f x) / b
  have hginj : InjOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz w hw hzw
    exact hinj hz hw (by simpa [g, div_left_inj' hb] using hzw)
  obtain ⟨h, hh, -, hhx, hdh, hpow, hright⟩ :=
    exists_differentiableOn_injOn_cpow_eq_of_sector (f := g) hβ hΩopen hΩ hx
      (by simp [g]) ((hcont.sub continuousOn_const).div_const b)
      ((hholo.sub_const (f x)).div_const b) hginj hsector
      (fun z hz hzim hgz => hrays z hz hzim (fun heq => hgz (by simp [g, heq])))
  have hderiv : deriv g = fun z => deriv f z / b := by
    ext z
    simp only [g, deriv_div_const, deriv_sub_const]
  have hφg : EqOn φ (logDeriv (deriv g)) (upperHalfPlaneSet ∩ Ω) := by
    intro z hz
    rw [hderiv, hφf hz]
    simp only [div_eq_mul_inv, logDeriv_mul_const z b⁻¹ (inv_ne_zero hb)]
  apply tendsto_sub_mul_nhdsNE_of_eqOn_add_cpow (f := g) (h := h) (w := 0)
    hr hφ hφconj hφg hΩopen hx hh hhx hdh
  · intro z hz
    exact mem_slitPlane_iff.mpr (Or.inl (hright z hz.2 hz.1))
  · exact ofReal_ne_zero.mpr hβ.1.ne'
  · intro z hz
    have hz0 : 0 < z.im := hz.1
    simpa only [zero_add] using (hpow ⟨hz.2, hz0.le⟩).symm

/-! ### Assembling the Schwarz--Christoffel formula -/

/-- **The converse Schwarz--Christoffel theorem from the prevertex residues.**  Let `f` be
holomorphic with nonvanishing derivative on the upper half-plane and suppose its pre-Schwarzian
derivative continues to a function `φ` holomorphic off the distinct real prevertices `a i`, with
singularities at worst simple poles of residues `e i`, and decaying at infinity.  Then `f` is the
affine image `A * F + B` of the normalized Schwarz--Christoffel primitive `F` for the data `a` and
`e`, with `A` and `B` read off at the normalization point. -/
theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_of_tendsto {ι : Type*} [Fintype ι]
    (a e : ι → ℝ) (ha : Function.Injective a) (z₀ : UpperHalfPlane) {f φ : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0)
    (hφ : DifferentiableOn ℂ φ (range fun i => ((a i : ℝ) : ℂ))ᶜ)
    (hφf : EqOn φ (logDeriv (deriv f)) upperHalfPlaneSet)
    (hpole : ∀ i, Tendsto (fun z => (z - (a i : ℂ)) * φ z) (𝓝[≠] ((a i : ℝ) : ℂ))
      (𝓝 ((e i : ℝ) : ℂ)))
    (hinfty : Tendsto φ (cobounded ℂ) (𝓝 0)) :
    EqOn f (fun z => deriv f z₀ / schwarzChristoffelIntegrand a e z₀ *
      schwarzChristoffelPrimitive a e z₀ z + f z₀) upperHalfPlaneSet := by
  classical
  have hcast : ∀ i j : ι, ((a i : ℝ) : ℂ) = ((a j : ℝ) : ℂ) ↔ i = j := fun i j => by
    rw [Complex.ofReal_inj, ha.eq_iff]
  set S : Finset ℂ := Finset.univ.image fun i => ((a i : ℝ) : ℂ) with hS
  have hSc : (↑S : Set ℂ) = range fun i => ((a i : ℝ) : ℂ) := by simp [hS]
  -- The residue function, read off the prevertex the point comes from.
  set c : ℂ → ℂ := fun z => ∑ i, if ((a i : ℝ) : ℂ) = z then ((e i : ℝ) : ℂ) else 0 with hc
  have hcval : ∀ i, c ((a i : ℝ) : ℂ) = ((e i : ℝ) : ℂ) := fun i => by simp [hc, hcast]
  have hpoleS : ∀ s ∈ S, Tendsto (fun z => (z - s) * φ z) (𝓝[≠] s) (𝓝 (c s)) := by
    intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    rw [hcval i]
    exact hpole i
  have hsum : EqOn φ (fun z => ∑ s ∈ S, c s / (z - s)) (↑S : Set ℂ)ᶜ :=
    Contour.eqOn_sum_div_sub_of_tendsto (by rwa [hSc]) hpoleS hinfty
  have hpre : EqOn (logDeriv (deriv f))
      (fun z => ∑ i, ((e i : ℝ) : ℂ) / (z - ((a i : ℝ) : ℂ))) upperHalfPlaneSet := by
    intro z hz
    have hzS : z ∈ (↑S : Set ℂ)ᶜ := by
      rw [hSc]
      rintro ⟨i, rfl⟩
      simp at hz
    rw [← hφf hz, hsum hzS]
    simp only [hS]
    rw [Finset.sum_image fun i _ j _ hij => (hcast i j).mp hij]
    exact Finset.sum_congr rfl fun i _ => by rw [hcval i]
  exact eqOn_const_mul_schwarzChristoffelPrimitive_add_of_logDeriv_deriv_eqOn a e z₀ hf hfn hpre

end TauCeti

end
