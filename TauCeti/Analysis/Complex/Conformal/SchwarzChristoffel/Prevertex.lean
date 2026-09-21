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
import TauCeti.Analysis.Complex.UpperHalfPlane.Cpow
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
divided by `π`.  The pre-Schwarzian derivative of such an `f` blows up like `(β - 1) / (z - x)`
from above, and conjugation symmetry propagates that asymptotic to the punctured neighbourhood,
so `β - 1` is the residue of `φ` at the prevertex.  Once each prevertex contributes its residue
and `φ` decays at infinity, partial fractions identify `φ` with `∑ i, e i / (z - a i)` and the
integration theorem identifies `f` itself with an affine image of the Schwarz--Christoffel
primitive.

## Main results

* `TauCeti.tendsto_sub_mul_nhdsNE_of_eqOn_add_cpow` -- the continuation of the pre-Schwarzian
  derivative of a map with a corner power form has a simple pole of residue `β - 1` at the
  corner.
* `TauCeti.tendsto_sub_mul_logDeriv_deriv_cpow_sub` -- the model corner map `w + (z - x) ^ β` has
  that asymptotic from above.
* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_tendsto` -- a map of the upper
  half-plane whose pre-Schwarzian derivative continues with simple poles of residues `e i` at the
  prevertices `a i` and decays at infinity is an affine image of the Schwarz--Christoffel
  primitive for those data.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

/-! ### The residue at a single corner -/

/-- **The pre-Schwarzian derivative has a simple pole of residue `β - 1` at a corner.**  Let `φ`
be holomorphic on a punctured disc about a real point `x`, symmetric under conjugation, and equal
to the pre-Schwarzian derivative of `f` on the upper half-plane.  If `f` has the corner power form
`w + h ^ β` above the axis near `x`, with `h` holomorphic and having a simple zero at `x`, then
`(z - x) * φ z` tends to `β - 1` as `z` tends to `x` from any direction. -/
theorem tendsto_sub_mul_nhdsNE_of_eqOn_add_cpow {φ f h : ℂ → ℂ} {x r : ℝ} {U : Set ℂ} {w β : ℂ}
    (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball (x : ℂ) r \ {(x : ℂ)}))
    (hφconj : ∀ z, φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hφf : EqOn φ (logDeriv (deriv f)) upperHalfPlaneSet)
    (hU : IsOpen U) (hxU : (x : ℂ) ∈ U) (hh : DifferentiableOn ℂ h U) (hhx : h (x : ℂ) = 0)
    (hdh : deriv h (x : ℂ) ≠ 0) (hslit : ∀ z ∈ upperHalfPlaneSet ∩ U, h z ∈ slitPlane)
    (hβ : β ≠ 0) (hf : EqOn f (fun z => w + h z ^ β) (upperHalfPlaneSet ∩ U)) :
    Tendsto (fun z => (z - (x : ℂ)) * φ z) (𝓝[≠] ((x : ℝ) : ℂ)) (𝓝 (β - 1)) := by
  -- The corner asymptotic, taken along the part of the upper half-plane inside `U`.
  have hcorner := tendsto_sub_mul_logDeriv_deriv_of_eqOn_add_cpow hU hxU hh hhx hdh
    (isOpen_upperHalfPlaneSet.inter hU) inter_subset_right hslit hβ hf
  -- `U` is a neighbourhood of `x`, so that filter is the whole upper half-plane filter.
  have hfilter : 𝓝[upperHalfPlaneSet ∩ U] ((x : ℝ) : ℂ) = 𝓝[upperHalfPlaneSet] ((x : ℝ) : ℂ) := by
    rw [inter_comm]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU))
  rw [hfilter] at hcorner
  have hmul : DifferentiableOn ℂ (fun z => (z - (x : ℂ)) * φ z)
      (Metric.ball (x : ℂ) r \ {(x : ℂ)}) :=
    (by fun_prop : Differentiable ℂ fun z : ℂ => z - (x : ℂ)).differentiableOn.mul hφ
  have hconj : ∀ z : ℂ, ((starRingEnd ℂ) z - (x : ℂ)) * φ ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((z - (x : ℂ)) * φ z) := fun z =>
    calc ((starRingEnd ℂ) z - (x : ℂ)) * φ ((starRingEnd ℂ) z)
        = ((starRingEnd ℂ) z - (starRingEnd ℂ) ((x : ℝ) : ℂ)) * (starRingEnd ℂ) (φ z) := by
          rw [Complex.conj_ofReal x, hφconj z]
      _ = (starRingEnd ℂ) ((z - (x : ℂ)) * φ z) := by rw [← map_sub, ← map_mul]
  refine tendsto_nhdsNE_of_tendsto_nhdsWithin_im_pos hr hmul hconj (hcorner.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [hφf hz]

/-- **The model corner map.**  The pre-Schwarzian derivative of `w + (z - x) ^ β` at a real base
point `x` has the corner asymptotic with residue `β - 1` from above.  This is the local model
every Schwarz--Christoffel corner is compared with. -/
theorem tendsto_sub_mul_logDeriv_deriv_cpow_sub (x : ℝ) {β : ℂ} (hβ : β ≠ 0) (w : ℂ) :
    Tendsto (fun z => (z - (x : ℂ)) *
        logDeriv (deriv fun z : ℂ => w + (z - (x : ℂ)) ^ β) z)
      (𝓝[upperHalfPlaneSet] ((x : ℝ) : ℂ)) (𝓝 (β - 1)) :=
  tendsto_sub_mul_logDeriv_deriv_of_eqOn_add_cpow (h := fun z : ℂ => z - (x : ℂ)) isOpen_univ
    (mem_univ _) (by fun_prop) (by ring) (by simp) isOpen_upperHalfPlaneSet (subset_univ _)
    (fun z hz => sub_ofReal_mem_slitPlane_of_im_pos hz x) hβ fun _ _ => rfl

/-! ### Assembling the Schwarz--Christoffel formula -/

/-- **The converse Schwarz--Christoffel theorem from the prevertex residues.**  Let `f` be
holomorphic with nonvanishing derivative on the upper half-plane and suppose its pre-Schwarzian
derivative continues to a function `φ` holomorphic off the distinct real prevertices `a i`, with a
simple pole of residue `e i` at `a i`, and decaying at infinity.  Then `f` is the affine image
`A * F + B` of the normalized Schwarz--Christoffel primitive `F` for the data `a` and `e`, with
`A` and `B` read off at the normalization point. -/
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
