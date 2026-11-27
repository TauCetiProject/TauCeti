/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Complex conjugation on the completions of a CM field at its finite places

Let `E` be a CM field with complex conjugation `x ↦ conj x`, which permutes the finite places,
`w ↦ conj w`. Writing `σ` for the ring isomorphism underlying `complexConj E`, conjugation
extends to isomorphisms of completions `E_v ≃ E_w` whenever `|σ x|_w = |x|_v` for all `x ∈ E`,
that is whenever `w = conj v` (`IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr`). This
file records the two instances of that valuation condition used to compute the components of the
conjugate of a finite adele: `w = conj (conj w)` for every place, and `w = conj w` for a place
fixed by conjugation. At such a place conjugation is an automorphism `t ↦ conj t` of `E_w`, which
is an involution and moves the residue of every integer `y` with `y - conj y ∉ w`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuation_complexConj`: `|conj x|_w = |x|_{conj w}`, and
  `IsDedekindDomain.HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq`: conjugation preserves
  the valuation of a place fixed by conjugation.
* `IsDedekindDomain.HeightOneSpectrum.map_asIdeal_of_conjPlace_eq`: the ideal of a place fixed by
  conjugation is stable under conjugation of the integers.
* `IsDedekindDomain.FiniteAdeleRing.star_apply_eq_adicCompletionCongr`: the component of the
  conjugate of a finite adele at any place `w'` with `|conj x|_{w'} = |x|_w`, such as `w' = w`
  when `conj w = w`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr_complexConj_apply_apply`: at a place
  fixed by conjugation, `t ↦ conj t` is an involution of `E_w`.
* `IsDedekindDomain.HeightOneSpectrum.valued_algebraMap_sub_adicCompletionCongr_eq_one`: at such
  a place, `|y - conj y|_w = 1` for an integer `y` with `y - conj y ∉ w`.
-/

public section

open IsDedekindDomain NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- `|conj x|_w = |x|_{conj w}`: the valuation at `w` of a conjugate is the valuation at the
conjugate place. -/
theorem valuation_complexConj (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    w.valuation E ((complexConj E).toRingEquiv x) = w.conjPlace.valuation E x := by
  rw [AlgEquiv.coe_toRingEquiv, ← valuation_conjPlace w (complexConj E x),
    complexConj_apply_apply]

/-- At a place with `conj w = w`, complex conjugation preserves the `w`-adic valuation. -/
theorem valuation_complexConj_of_conjPlace_eq {w : HeightOneSpectrum (𝓞 E)}
    (h : w.conjPlace = w) (x : E) :
    w.valuation E ((complexConj E).toRingEquiv x) = w.valuation E x := by
  rw [valuation_complexConj, h]

/-- The ideal of a finite place fixed by conjugation is stable under conjugation of the
integers. -/
theorem map_asIdeal_of_conjPlace_eq {w : HeightOneSpectrum (𝓞 E)} (h : w.conjPlace = w) :
    w.asIdeal.map (ringOfIntegersComplexConj E) = w.asIdeal := by
  -- `conj w` is the transport of `w` along conjugation of the integers, whose ideal is the image
  -- of that of `w`
  have hw : w.conjPlace =
      equivOfRingEquiv (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv) w :=
    (eq_conjPlace_iff.2 (RingEquiv.valuation_equivOfRingEquiv _ w)).symm
  have := asIdeal_equivOfRingEquiv (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv) w
  rw [← hw, h] at this
  -- `ringOfIntegersComplexConj E` and `RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv`
  -- have the same underlying map, so the two images of `w.asIdeal` agree
  exact this.symm

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.FiniteAdeleRing

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- **Conjugation of finite adeles at a place, for any presentation of the conjugate place.** If
`|conj x|_{w'} = |x|_w` for all `x ∈ E`, so that `w'` is the conjugate place `conj w`, the component
at `w'` of the conjugate of a finite adele `a` is the image of `a_w` under the isomorphism
`E_w ≃ E_{w'}` extending the conjugation of `E`. With `w = conj w'` this computes every component
of `star a`, and at a place `w` with `conj w = w` it reads `(star a)_w = conj (a_w)` for the
automorphism `t ↦ conj t` of `E_w`. -/
theorem star_apply_eq_adicCompletionCongr {w w' : HeightOneSpectrum (𝓞 E)}
    (hw : ∀ x, w'.valuation E ((complexConj E).toRingEquiv x) = w.valuation E x) (a : 𝔸ᶠ[E]) :
    (star a) w' =
      HeightOneSpectrum.adicCompletionCongr w w' (complexConj E).toRingEquiv hw (a w) := by
  obtain rfl := HeightOneSpectrum.eq_conjPlace_iff.2 hw
  exact star_apply_conjPlace a w

end IsDedekindDomain.FiniteAdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- At a place with `conj w = w`, the automorphism `t ↦ conj t` of `E_w` extending the conjugation
of `E` is an involution. -/
@[simp]
theorem adicCompletionCongr_complexConj_apply_apply {w : HeightOneSpectrum (𝓞 E)}
    (h : w.conjPlace = w) (x : w.adicCompletion E) :
    adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)
      (adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h) x) = x := by
  -- both sides are continuous in `x` and agree on the dense image of `E`
  have hc := continuous_adicCompletionCongr (valuation_complexConj_of_conjPlace_eq h)
  refine congrFun ((w.denseRange_algebraMap E).equalizer (hc.comp hc) continuous_id
    (funext fun x ↦ ?_)) x
  simp only [Function.comp_apply, adicCompletionCongr_algebraMap, AlgEquiv.coe_toRingEquiv,
    complexConj_apply_apply, id]

/-- At a place with `conj w = w`, `y − conj y` has valuation `1` in `E_w` when it lies outside
`w`: conjugation `t ↦ conj t` of `E_w` acts nontrivially on the residue field. -/
theorem valued_algebraMap_sub_adicCompletionCongr_eq_one {w : HeightOneSpectrum (𝓞 E)}
    (h : w.conjPlace = w) {y : 𝓞 E} (hy : y - ringOfIntegersComplexConj E y ∉ w.asIdeal) :
    Valued.v (algebraMap (𝓞 E) (w.adicCompletion E) y -
      adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)
        (algebraMap (𝓞 E) (w.adicCompletion E) y)) = 1 := by
  have hτ : adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)
      (algebraMap (𝓞 E) (w.adicCompletion E) y) =
        algebraMap (𝓞 E) (w.adicCompletion E) (ringOfIntegersComplexConj E y) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E),
      IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E) (ringOfIntegersComplexConj E y),
      adicCompletionCongr_algebraMap]
    simp [← RingOfIntegers.coe_eq_algebraMap]
  rw [hτ, ← map_sub]
  exact (notMem_asIdeal_iff_valued_algebraMap_eq_one (K := E) w).1 hy

end IsDedekindDomain.HeightOneSpectrum
