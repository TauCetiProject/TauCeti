/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Reflection
public import TauCeti.Analysis.Complex.LaplaceReflection
import TauCeti.Analysis.Sobolev.Local.Reflection.Odd
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Tangential weak derivatives across the real axis

For an open `Ω ⊆ ℂ`, let `g` have a weak derivative `g'` in a direction `v` tangent to the real
axis (`v.im = 0`) on the open upper part `Ω ∩ {0 < im}`, with `g` and `g'` integrable on compact
subsets of `Ω ∩ {0 ≤ im}`. Integration by parts in a tangential direction produces no boundary
term (`TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg`), so no boundary condition on
`g` is needed to glue across the axis:

* `TauCeti.HasWeakLineDerivOn.indicator_setOf_im_nonneg_of_im_eq_zero`: the extension of `g` by
  zero below the axis has the extension of `g'` by zero as weak derivative in the direction `v` on
  all of `Ω`. In a transverse direction this needs `g = 0` on the axis
  (`TauCeti.HasWeakLineDerivOn.indicator_setOf_im_nonneg`).
* `TauCeti.HasWeakLineDerivOn.twistedReflection_one`: on a conjugation-invariant `Ω`, for every
  continuous linear `L`, the twisted reflection `TauCeti.twistedReflection L g`, equal to `g` above
  the axis and to `L (g (conj z))` below it, has the twisted reflection of `g'` as weak derivative
  along the real axis on all of `Ω`. The full weak derivative of a twisted reflection exists only
  under a compatibility condition on the axis; the tangential one always does.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Complex
open scoped ComplexConjugate ENNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens ℂ}

/-- **Extension by zero in a tangential direction.** If `g'` is the weak derivative of `g` in a
direction `v` tangent to the real axis on the upper part of `Ω`, with `g` and `g'` integrable on
compact subsets of `Ω ∩ {0 ≤ im}`, then the extensions by zero below the axis satisfy the same
relation on all of `Ω`. No condition on `g` along the axis is needed. -/
theorem HasWeakLineDerivOn.indicator_setOf_im_nonneg_of_im_eq_zero {g g' : ℂ → F} {v : ℂ}
    (hv : v.im = 0)
    (hgW : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' v)
    (hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hg' : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g') :
    HasWeakLineDerivOn volume Ω ({z : ℂ | 0 ≤ z.im}.indicator g)
      ({z : ℂ | 0 ≤ z.im}.indicator g') v := by
  have := hgW.completeSpace
  exact hasWeakLineDerivOn_indicator_setOf_im_nonneg_of_setIntegral hg hg' fun φ hφ hφc hφΩ =>
    hgW.setIntegral_fderiv_smul_eq_neg hg hg' hφ hφc (fun z hz => hφΩ hz.1) (Or.inl hv)

/-- Off the real axis, the twisted reflection by `L` is the even reflection of `g`, plus the even
reflection of `L ∘ g - g` cut off below the axis. -/
private theorem twistedReflection_eq_planarReflection_add (L : F →L[ℝ] F) (g : ℂ → F) {z : ℂ}
    (hz : z.im ≠ 0) :
    twistedReflection L g z = (planarReflection (fun _ : Fin 1 => (1 : ℝ)) g +
      planarReflection (fun _ : Fin 1 => (1 : ℝ)) (fun w => L (g w) - g w) -
        {w : ℂ | 0 ≤ w.im}.indicator (fun w => L (g w) - g w)) z := by
  rcases lt_or_gt_of_ne hz with hz | hz
  · simp [twistedReflection_of_im_neg hz, planarReflection_of_neg _ _ hz,
      imDilation_higherReflectionNode_fin_one,
      indicator_of_notMem (show z ∉ {w : ℂ | 0 ≤ w.im} from not_le.2 hz)]
  · simp [twistedReflection_of_im_pos hz, planarReflection_of_nonneg _ _ hz.le,
      indicator_of_mem (show z ∈ {w : ℂ | 0 ≤ w.im} from hz.le)]

/-- **Tangential derivative of a twisted reflection.** On an open set `Ω` invariant under
conjugation, if `g'` is the weak derivative of `g` along the real axis on the upper part of `Ω`,
with `g` and `g'` integrable on compact subsets of `Ω ∩ {0 ≤ im}`, then for every continuous
linear `L` the twisted reflection `TauCeti.twistedReflection L g'` is the weak derivative of
`TauCeti.twistedReflection L g` along the real axis on all of `Ω`. -/
theorem HasWeakLineDerivOn.twistedReflection_one (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    {g g' : ℂ → F}
    (hgW : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' 1)
    (hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hg' : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g') (L : F →L[ℝ] F) :
    HasWeakLineDerivOn volume Ω (twistedReflection L g) (twistedReflection L g') 1 := by
  have := hgW.completeSpace
  have hΩ' := imDilation_higherReflectionNode_fin_one_mem (Ω := (Ω : Set ℂ))
    fun _ hz _ => hΩ hz
  have hdW := (hgW.clm_comp L).sub hgW
  have hd := (hg.clm_comp L).sub hg
  have hd' := (hg'.clm_comp L).sub hg'
  have h := ((hgW.planarReflection_one hΩ' hg hg' fun _ => 1).add
    (hdW.planarReflection_one hΩ' hd hd' fun _ => 1)).sub
    (hdW.indicator_setOf_im_nonneg_of_im_eq_zero (by simp) hd hd')
  refine (h.congr_ae ?_).congr_ae_deriv ?_ <;>
  · filter_upwards [ae_restrict_of_ae Complex.ae_im_ne_zero] with z hz
    exact (twistedReflection_eq_planarReflection_add L _ hz).symm

end TauCeti
