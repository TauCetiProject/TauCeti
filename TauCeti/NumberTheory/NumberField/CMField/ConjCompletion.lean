/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.FinitePlace
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Complex conjugation on the completions of a CM field at its finite places

Let `E` be a CM field with complex conjugation `x ↦ conj x`, which permutes the finite places,
`w ↦ conj w`. Writing `σ` for the ring isomorphism underlying `complexConj E`, conjugation
extends to isomorphisms of completions `E_v ≃ E_w` whenever `|σ x|_w = |x|_v` for all `x ∈ E`,
that is whenever `w = conj v` (`IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr`). This
file proves that at a place fixed by conjugation the induced automorphism `t ↦ conj t` of `E_w`
is an involution and moves the residue of every integer `y` with `y - conj y ∉ w`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr_complexConj_apply_apply`: at a place
  fixed by conjugation, `t ↦ conj t` is an involution of `E_w`.
* `IsDedekindDomain.HeightOneSpectrum.valued_algebraMap_sub_adicCompletionCongr_eq_one`: at such
  a place, `|y - conj y|_w = 1` for an integer `y` with `y - conj y ∉ w`.
-/

public section

open IsDedekindDomain NumberField NumberField.IsCMField

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

/-- Complex conjugation restricted to the integers of a completion at a fixed place. -/
noncomputable def adicCompletionIntegersConj (w : HeightOneSpectrum (𝓞 E)) (h : w.conjPlace = w) :
    w.adicCompletionIntegers E →+* w.adicCompletionIntegers E :=
  (adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)).toRingHom.restrict _ _
    fun x hx ↦ by
      rw [mem_adicCompletionIntegers] at hx ⊢
      change Valued.v (adicCompletionCongr w w _ _ x) ≤ 1
      rwa [valued_adicCompletionCongr]

/-- Restricting conjugation to the completion integers agrees with conjugation in the field. -/
@[simp]
theorem coe_adicCompletionIntegersConj (w : HeightOneSpectrum (𝓞 E)) (h : w.conjPlace = w)
    (x : w.adicCompletionIntegers E) :
    (w.adicCompletionIntegersConj h x : w.adicCompletion E) =
      adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h) x :=
  RingHom.coe_restrict_apply _ _ _ _ x

/-- Conjugation of the completion integers at a fixed place is involutive. -/
@[simp]
theorem adicCompletionIntegersConj_apply_apply (w : HeightOneSpectrum (𝓞 E))
    (h : w.conjPlace = w) (x : w.adicCompletionIntegers E) :
    w.adicCompletionIntegersConj h (w.adicCompletionIntegersConj h x) = x := by
  apply Subtype.ext
  rw [coe_adicCompletionIntegersConj, coe_adicCompletionIntegersConj]
  exact adicCompletionCongr_complexConj_apply_apply h x

/-- The star structure given by conjugation at a fixed place. It is installed locally, since
the equality identifying the place with its conjugate must be supplied explicitly. -/
@[instance_reducible]
noncomputable def adicCompletionIntegersStarRing (w : HeightOneSpectrum (𝓞 E))
    (h : w.conjPlace = w) :
    StarRing (w.adicCompletionIntegers E) where
  star := w.adicCompletionIntegersConj h
  star_involutive := w.adicCompletionIntegersConj_apply_apply h
  star_mul x y := by rw [map_mul, mul_comm]
  star_add := map_add _

/-- With the fixed-place star structure, the inclusion of the integers commutes with
conjugation in the completion. -/
@[simp]
theorem coe_star_adicCompletionIntegers (w : HeightOneSpectrum (𝓞 E))
    (h : w.conjPlace = w) :
    letI := w.adicCompletionIntegersStarRing h
    ∀ x : w.adicCompletionIntegers E,
      ((star x : w.adicCompletionIntegers E) : w.adicCompletion E) =
        adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h) x :=
  w.coe_adicCompletionIntegersConj h

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
