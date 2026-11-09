/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.AdicCompletion.Regular
import Mathlib.Tactic.LinearCombination

/-!
# The principal localization–completion square

For a regular element `r` of a commutative ring `R`, the square with corners
`R`, `R[1/r]`, the `(r)`-adic completion `R̂` of `R`, and `R̂[1/r]` is a pullback.
The difference map `R[1/r] × R̂ → R̂[1/r]` is also surjective. Thus it gives the short exact
sequence used before further completion in a second parameter.

The results use the native `AdicCompletion` and `Localization.Away` carriers. No Noetherian,
separatedness or completeness hypothesis is imposed on `R`. In particular completion need not
be faithfully flat: localization retains the part invisible to completion.

## References

* Douglas–Francis–Henriques–Hill, *Topological Modular Forms*, Chapter 12, §8, for the
  localization/completion square in the comparison of ordinary and supersingular coefficients.
* The Stacks Project, Section 15.91, formal glueing.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {r : R}

/-- The localization–completion square of a regular element is cartesian: compatible elements
of `R[1/r]` and the `(r)`-adic completion come from a unique element of `R`. -/
theorem existsUnique_localization_lift (hr : IsRegular r)
    (a : Localization.Away r) (b : AdicCompletion (Ideal.span {r}) R)
    (hab : Localization.awayMap (algebraMap R (AdicCompletion (Ideal.span {r}) R)) r a =
      algebraMap _ (Localization.Away
        (algebraMap R (AdicCompletion (Ideal.span {r}) R) r)) b) :
    ∃! x : R, algebraMap R (Localization.Away r) x = a ∧
      algebraMap R (AdicCompletion (Ideal.span {r}) R) x = b := by
  let I : Ideal R := Ideal.span {r}
  let C := AdicCompletion I R
  let D := Localization.Away (algebraMap R C r)
  let f := Localization.awayMap (algebraMap R C) r
  have hrC : IsRegular (algebraMap R C r) := hr.adicCompletion
  have hinjC := IsLocalization.injective D
    (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hrC))
  have hinjR := IsLocalization.injective (Localization.Away r)
    (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hr))
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj r a
  have hcb : algebraMap R C c = algebraMap R C r ^ n * b := by
    apply hinjC
    have hf (y : R) : f (algebraMap R (Localization.Away r) y) =
        algebraMap C D (algebraMap R C y) :=
      IsLocalization.map_eq (Submonoid.powers r).le_comap_map y
    have h := congrArg f hc
    simp only [map_mul, map_pow, hf] at h
    rw [hab] at h
    rw [map_mul, map_pow]
    exact h.symm.trans (mul_comm _ _)
  -- Divisibility of the completed numerator descends through the residue modulo `r^n`.
  have hcI : algebraMap R C c ∈ (I ^ n).map (algebraMap R C) := by
    simp only [I, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton, map_pow]
    exact ⟨b, hcb⟩
  have hcR : c ∈ Ideal.span {r ^ n} := by
    rw [← Ideal.span_singleton_pow]
    exact (algebraMap_mem_map_pow_iff n).mp hcI
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hcR
  have ha : algebraMap R (Localization.Away r) x = a := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit r n).mul_left_injective
    simpa only [hx, map_mul, map_pow, mul_comm] using hc.symm
  have hb : algebraMap R C x = b := by
    apply (hrC.pow n).left
    simpa only [hx, map_mul, map_pow] using hcb
  exact ⟨x, ⟨ha, hb⟩, fun y hy ↦ hinjR (hy.1.trans ha.symm)⟩

/-- Every element of the localized completion is a difference of an element from the
localization and an element from the completion. This is the surjectivity at the right end of
the localization–completion short exact sequence, with no regularity hypothesis needed. -/
theorem exists_localization_sub_completion (r : R)
    (z : Localization.Away (algebraMap R (AdicCompletion (Ideal.span {r}) R) r)) :
    ∃ (a : Localization.Away r) (b : AdicCompletion (Ideal.span {r}) R),
      Localization.awayMap (algebraMap R (AdicCompletion (Ideal.span {r}) R)) r a -
        algebraMap _ (Localization.Away
          (algebraMap R (AdicCompletion (Ideal.span {r}) R) r)) b = z := by
  let I : Ideal R := Ideal.span {r}
  let C := AdicCompletion I R
  let D := Localization.Away (algebraMap R C r)
  let f := Localization.awayMap (algebraMap R C) r
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R C r) z
  obtain ⟨x, hx⟩ := exists_sub_algebraMap_mem_map_pow (Submodule.fg_span_singleton r) n c
  simp only [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton, map_pow] at hx
  obtain ⟨b, hb⟩ := hx
  let a : Localization.Away r := IsLocalization.mk' (Localization.Away r) x
    (⟨r ^ n, n, rfl⟩ : Submonoid.powers r)
  have ha : a * algebraMap R (Localization.Away r) r ^ n =
      algebraMap R (Localization.Away r) x := by
    simpa only [map_pow] using IsLocalization.mk'_spec (Localization.Away r) x
      (⟨r ^ n, n, rfl⟩ : Submonoid.powers r)
  refine ⟨a, -b, ?_⟩
  apply (IsLocalization.Away.algebraMap_pow_isUnit (algebraMap R C r) n).mul_left_injective
  have hf (y : R) : f (algebraMap R (Localization.Away r) y) =
      algebraMap C D (algebraMap R C y) :=
    IsLocalization.map_eq (Submonoid.powers r).le_comap_map y
  have hfa := congrArg f ha
  simp only [map_mul, map_pow, hf] at hfa
  have hbD := congrArg (algebraMap C D) hb
  simp only [map_sub, map_mul, map_pow] at hbD
  simp only [map_neg, sub_neg_eq_add]
  linear_combination hfa - hbD - hc

end AdicCompletion
