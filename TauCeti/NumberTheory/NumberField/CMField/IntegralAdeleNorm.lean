/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.NumberTheory.NumberField.CMField.ConjCompletion
import TauCeti.NumberTheory.NumberField.CMField.ResidueField
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
import TauCeti.RingTheory.Henselian.InvolutionNorm

/-!
# Conjugation-fixed units of the integral finite adeles of a CM field are norms

Let `E` be a CM field with complex conjugation `x ↦ conj x`, and `Ô = ∏_w O_w` its integral
finite adeles, with conjugation `a ↦ conj a`, which carries the component at a finite place `w`
to the component at `conj w`. This file proves that every unit `u` of `Ô` with `conj u = u` is a
norm `conj y * y` of a unit `y` of `Ô`, provided every finite place `w` with `conj w = w` lies
over an odd prime and is unramified over the maximal real subfield `E⁺`, that is conjugation acts
nontrivially on its residue field. This holds when `E` contains a primitive fourth and a
primitive seventh root of unity, for instance a primitive `5040`-th root of unity
(`NumberField.IsCMField.two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot`). In particular `Ô`
then contains a unit `ν` with `conj ν * ν = -1`: in contrast with `E`, where a nonzero norm
`conj y * y` is totally positive, `-1` is a norm in `Ô`.

The proof is place by place.

* At a place `w` with `conj w = w`, conjugation is an automorphism `t ↦ conj t` of `O_w` of order
  two acting nontrivially on the finite residue field, and `2` is a unit of `O_w`. The units of the
  Henselian local ring `O_w` fixed by it are norms
  (`TauCeti.HenselianLocalRing.exists_apply_mul_self_eq`).
* The places `w` with `conj w ≠ w` come in pairs `{w, conj w}`, and the components of `conj u` at
  `w` and `conj w` are the conjugates of those of `u` at `conj w` and `w`. Taking `y_w = u_w` and
  `y_{conj w} = 1` for one place of each pair (chosen by a well-ordering of the places) gives
  `conj y * y = u` at both.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.exists_adicCompletionCongr_mul_self_eq`: at a place `w`
  with `conj w = w`, odd and unramified over `E⁺`, every unit of `O_w` fixed by conjugation is
  `conj y * y` for some `y ∈ O_w`.
* `NumberField.IsCMField.exists_star_mul_self_eq_of_forall_conjPlace_eq`: every unit `u` of `Ô`
  with `conj u = u` is `conj y * y` for a unit `y` of `Ô`, when every place fixed by conjugation is
  odd and unramified over `E⁺`.
* `NumberField.IsCMField.exists_star_mul_self_eq_of_isPrimitiveRoot`: the same when `E` contains a
  primitive fourth and a primitive seventh root of unity, and
  `NumberField.IsCMField.exists_star_mul_self_eq_neg_one`: then `conj ν * ν = -1` for a unit `ν`
  of `Ô`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2, Proposition 3 (the norm of an unramified extension
  maps the units onto the units).
* `grh-lean`, https://github.com/lsernau/grh-lean, file `src/Lib/Adelic/Witt/WittTheorem.lean`
  (declaration `New.exists_unit_star_mul_self_eq`); Apache 2.0, Copyright 2026 Anthropic, PBC. The
  statement, under the `5040` condition, follows that declaration; the proof here, place by place
  through Hensel's lemma and the norm of a finite field, is independent of that code.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- **Units of a completion fixed by conjugation are norms.** Let `w` be a finite place of a CM
field with `conj w = w`, not over `2` and unramified over the maximal real subfield, that is with
`conj x - x ∉ w` for some integer `x`. Then every `u ∈ E_w` with `|u|_w = 1` and `conj u = u` is
`conj y * y` for some `y ∈ O_w`, where `t ↦ conj t` is the automorphism of `E_w` extending the
conjugation of `E`. -/
theorem exists_adicCompletionCongr_mul_self_eq
    {w : HeightOneSpectrum (𝓞 E)} (h : w.conjPlace = w) (h2 : (2 : 𝓞 E) ∉ w.asIdeal)
    (hne : ∃ x, ringOfIntegersComplexConj E x - x ∉ w.asIdeal) {u : w.adicCompletion E}
    (hu₁ : Valued.v u = 1)
    (hσu : adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h) u = u) :
    ∃ y ∈ w.adicCompletionIntegers E,
      adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h) y * y = u := by
  set σ := adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)
  let σO := w.adicCompletionIntegersConj h
  have hσO := w.coe_adicCompletionIntegersConj h
  have hσσ := w.adicCompletionIntegersConj_apply_apply h
  -- `2` is a unit of `O_w`, and conjugation moves the image of `x` modulo `𝔪_w`
  have h2O : IsUnit (2 : w.adicCompletionIntegers E) := by
    rw [← map_ofNat (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) 2]
    exact (w.isUnit_algebraMap_adicCompletionIntegers_iff (K := E) 2).2 h2
  obtain ⟨x, hx⟩ := hne
  have hxO : IsUnit (σO (algebraMap (𝓞 E) _ x) - algebraMap (𝓞 E) _ x) := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one, AddSubgroupClass.coe_sub, hσO,
      ← Valuation.map_neg, neg_sub]
    refine valued_algebraMap_sub_adicCompletionCongr_eq_one h fun hmem ↦ hx ?_
    simpa using neg_mem hmem
  -- the norm of a Henselian local ring with an involution
  obtain ⟨y, hy⟩ := TauCeti.HenselianLocalRing.exists_apply_mul_self_eq h2O hσσ hxO
    (u := ⟨u, (mem_adicCompletionIntegers _ _ _).2 hu₁.le⟩)
    (adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hu₁)
    (Subtype.ext (by rw [hσO, hσu]))
  exact ⟨y, y.property, by
    have hh := congrArg Subtype.val hy
    change (σO y : w.adicCompletion E) * (y : w.adicCompletion E) = u at hh
    rwa [hσO] at hh⟩

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField.IsCMField

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

open Classical in
/-- At a split place `w`, a finite adele `y` equal to `a` at the first place of each split pair
`{v, conj v}` (for a well-ordering of the places) and to `1` at the second has
`(conj y * y)_w = a_w`, when `conj a = a`. -/
private theorem star_mul_apply_of_conjPlace_ne {a y : 𝔸ᶠ[E]} (ha : star a = a)
    (hy : ∀ v : HeightOneSpectrum (𝓞 E), v.conjPlace ≠ v →
      y v = if WellOrderingRel v v.conjPlace then a v else 1)
    {w : HeightOneSpectrum (𝓞 E)} (h : w.conjPlace ≠ w) : (star y * y) w = a w := by
  have h' : w.conjPlace.conjPlace ≠ w.conjPlace := by
    rw [HeightOneSpectrum.conjPlace_conjPlace]
    exact Ne.symm h
  rw [FiniteAdeleRing.mul_apply, star_apply_eq_adicCompletionCongr
    (HeightOneSpectrum.valuation_complexConj w), hy w h, hy _ h',
    HeightOneSpectrum.conjPlace_conjPlace]
  rcases trichotomous_of WellOrderingRel w w.conjPlace with hr | heq | hr
  · rw [ite_eq_left hr, ite_eq_right (asymm hr), map_one, one_mul]
  · exact absurd heq.symm h
  · rw [ite_eq_right (asymm hr), ite_eq_left hr, mul_one, ← star_apply_eq_adicCompletionCongr, ha]

/-- **Conjugation-fixed units of the integral finite adeles are norms.** Let `E` be a CM field in
which every finite place `w` with `conj w = w` lies over an odd prime and is unramified over the
maximal real subfield, that is `conj x - x ∉ w` for some integer `x`. Then every unit `u` of the
integral finite adeles `Ô` with `conj u = u` is `conj y * y` for a unit `y` of `Ô`. -/
theorem exists_star_mul_self_eq_of_forall_conjPlace_eq
    (h2 : ∀ w : HeightOneSpectrum (𝓞 E), w.conjPlace = w → (2 : 𝓞 E) ∉ w.asIdeal)
    (hne : ∀ w : HeightOneSpectrum (𝓞 E), w.conjPlace = w →
      ∃ x, ringOfIntegersComplexConj E x - x ∉ w.asIdeal)
    (u : (integralAdeles (𝓞 E) E)ˣ) (hu : star u = u) :
    ∃ y : (integralAdeles (𝓞 E) E)ˣ, star y * y = u := by
  classical
  set a : 𝔸ᶠ[E] := ((u : integralAdeles (𝓞 E) E) : 𝔸ᶠ[E]) with ha
  have ha_mem (w : HeightOneSpectrum (𝓞 E)) : a w ∈ w.adicCompletionIntegers E :=
    mem_integralAdeles.1 (u : integralAdeles (𝓞 E) E).property w
  have hstar : star a = a := by
    rw [ha, ← coe_star_integralAdeles, ← Units.coe_star, hu]
  -- the components of `a` are units of the `O_w`
  have ha_one (w : HeightOneSpectrum (𝓞 E)) : Valued.v (a w) = 1 := by
    simpa only [coe_integralProj_apply] using
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1
        (u.isUnit.map (integralProj E w))
  -- at the places fixed by conjugation, the local norms
  have hloc (w : HeightOneSpectrum (𝓞 E)) (h : w.conjPlace = w) :=
    HeightOneSpectrum.exists_adicCompletionCongr_mul_self_eq h (h2 w h) (hne w h)
      (ha_one w) (by rw [← star_apply_eq_adicCompletionCongr, hstar])
  choose z hz_mem hz using hloc
  -- the components of `y`: a local norm at `w = conj w`, and `u_w`, `1` on a split pair
  let Y (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletionIntegers E :=
    if h : w.conjPlace = w then ⟨z w h, hz_mem w h⟩
    else if WellOrderingRel w w.conjPlace then ⟨a w, ha_mem w⟩ else 1
  have hY_fix {w : HeightOneSpectrum (𝓞 E)} (h : w.conjPlace = w) :
      (Y w : w.adicCompletion E) = z w h := by
    simp only [Y, h, ↓reduceDIte]
  set y : 𝔸ᶠ[E] := integralEmbedding Y
  have hy_apply (w : HeightOneSpectrum (𝓞 E)) : y w = Y w := integralEmbedding_apply Y w
  have hy_mem : y ∈ integralAdeles (𝓞 E) E :=
    mem_integralAdeles.2 fun w ↦ by rw [hy_apply]; exact (Y w).property
  -- `conj y * y = a`, place by place
  have hya : star y * y = a := by
    ext w : 1
    by_cases h : w.conjPlace = w
    · rw [FiniteAdeleRing.mul_apply, star_apply_eq_adicCompletionCongr
        (HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq h), hy_apply, hY_fix h, hz]
    refine star_mul_apply_of_conjPlace_ne hstar (fun v hv ↦ ?_) h
    simp only [hy_apply, Y, hv, ↓reduceDIte]
    split_ifs <;> rfl
  -- `y` is a unit of `Ô`, since `conj y * y = u` is
  set y' : integralAdeles (𝓞 E) E := ⟨y, hy_mem⟩
  have hy' : star y' * y' = u := Subtype.ext hya
  have hunit : IsUnit y' := isUnit_of_mul_isUnit_right (hy' ▸ u.isUnit)
  exact ⟨hunit.unit, Units.ext (by rw [Units.val_mul, Units.coe_star, IsUnit.unit_spec, hy'])⟩

/-- **Conjugation-fixed units of the integral finite adeles are norms, under the `5040`
condition.** If the CM field `E` contains a primitive fourth and a primitive seventh root of unity
(for instance a primitive `5040`-th root of unity), every unit `u` of the integral finite adeles
`Ô` with `conj u = u` is `conj y * y` for a unit `y` of `Ô`. -/
theorem exists_star_mul_self_eq_of_isPrimitiveRoot {ζ₄ ζ₇ : E} (h₄ : IsPrimitiveRoot ζ₄ 4)
    (h₇ : IsPrimitiveRoot ζ₇ 7) (u : (integralAdeles (𝓞 E) E)ˣ) (hu : star u = u) :
    ∃ y : (integralAdeles (𝓞 E) E)ˣ, star y * y = u :=
  exists_star_mul_self_eq_of_forall_conjPlace_eq
    (fun w h ↦ (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w.asIdeal
      (HeightOneSpectrum.map_asIdeal_of_conjPlace_eq h)).1)
    (fun w h ↦ (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w.asIdeal
      (HeightOneSpectrum.map_asIdeal_of_conjPlace_eq h)).2)
    u hu

/-- **`-1` is a norm from the units of the integral finite adeles** of a CM field `E` containing a
primitive fourth and a primitive seventh root of unity: `conj ν * ν = -1` for a unit `ν` of `Ô`.
In `E` itself a nonzero norm `conj y * y` is totally positive, so `-1` is not one. -/
theorem exists_star_mul_self_eq_neg_one {ζ₄ ζ₇ : E} (h₄ : IsPrimitiveRoot ζ₄ 4)
    (h₇ : IsPrimitiveRoot ζ₇ 7) : ∃ ν : (integralAdeles (𝓞 E) E)ˣ, star ν * ν = -1 :=
  exists_star_mul_self_eq_of_isPrimitiveRoot h₄ h₇ (-1)
    (Units.ext (by rw [Units.coe_star, Units.val_neg, Units.val_one, star_neg, star_one]))

end NumberField.IsCMField
