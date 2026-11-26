/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealOrCMSubfield

/-!
# Friendly places

Let `K` be a number field, `E_K` its largest totally real or CM subfield
(`TauCeti.NumberField.maximalRealOrCMSubfield K`) and `K⁺` its maximal real subfield, which is
also the maximal real subfield of `E_K`. A finite place `v` of `K` is **friendly** when it is
unramified over `ℚ` and, if `E_K` is CM, the place of `K⁺` below `v` is inert in the quadratic
extension `E_K / K⁺` (Lawrence–Venkatesh, §2.4, Definition 2.7).

Since `[E_K : K⁺] = 2`, the place `w` of `K⁺` below `v` is inert in `E_K` exactly when the place
`u` of `E_K` below `v` has inertia degree `2` over `w`. By multiplicativity of inertia degrees in
the tower `ℤ ⊆ 𝓞 K⁺ ⊆ 𝓞 E_K`, this is `f(u | ℤ) = 2 f(w | ℤ)`, which is the form used in the
definition: it only needs the rings of integers of `E_K` and `K⁺` as algebras under `𝓞 K`.
Unramified over `ℚ` means ramification index `1` over `ℤ`.

## Main definitions

* `TauCeti.NumberField.IsFriendly v`: the finite place `v` of `K` is friendly.

## Main results

* `TauCeti.NumberField.IsFriendly.ramificationIdx_eq_one`: a friendly place is unramified over
  `ℚ`.
* `TauCeti.NumberField.isFriendly_iff_of_not_isCMField`,
  `TauCeti.NumberField.isFriendly_iff_of_forall_not_isCMField`: if `K` has no CM subfield, a
  place is friendly exactly when it is unramified over `ℚ`.
* `TauCeti.NumberField.isFriendly_iff_of_isTotallyReal`: in particular for totally real `K`.
* `TauCeti.NumberField.isFriendly_rat`: every prime of `ℚ` is friendly.

## References

* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4,
  Definition 2.7.
-/

public section

open NumberField IsDedekindDomain

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- A finite place `v` of a number field `K` is **friendly** if it is unramified over `ℚ` and,
when the largest totally real or CM subfield `E_K` is CM, the place of the maximal real subfield
`K⁺` below `v` is inert in `E_K`. Inertness is expressed by inertia degrees over `ℤ`: the place
of `E_K` below `v` has twice the inertia degree of the place of `K⁺` below `v`, which says that
its relative inertia degree over `K⁺` is `[E_K : K⁺] = 2`. -/
def IsFriendly (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  v.asIdeal.ramificationIdx ℤ = 1 ∧
    (IsCMField (maximalRealOrCMSubfield K) →
      (v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))).inertiaDeg ℤ =
        2 * (v.asIdeal.under (𝓞 (maximalRealSubfield K))).inertiaDeg ℤ)

/-- Unfolding lemma for `IsFriendly`. -/
theorem isFriendly_iff (v : HeightOneSpectrum (𝓞 K)) :
    IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 ∧
      (IsCMField (maximalRealOrCMSubfield K) →
        (v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))).inertiaDeg ℤ =
          2 * (v.asIdeal.under (𝓞 (maximalRealSubfield K))).inertiaDeg ℤ) :=
  Iff.rfl

/-- A friendly place is unramified over `ℚ`. -/
theorem IsFriendly.ramificationIdx_eq_one {v : HeightOneSpectrum (𝓞 K)} (h : IsFriendly v) :
    v.asIdeal.ramificationIdx ℤ = 1 :=
  h.1

/-- If `E_K` is CM, a friendly place lies over a place of `K⁺` inert in `E_K`, in the form of
inertia degrees over `ℤ`. -/
theorem IsFriendly.inertiaDeg_eq {v : HeightOneSpectrum (𝓞 K)} (h : IsFriendly v)
    (hK : IsCMField (maximalRealOrCMSubfield K)) :
    (v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))).inertiaDeg ℤ =
      2 * (v.asIdeal.under (𝓞 (maximalRealSubfield K))).inertiaDeg ℤ :=
  h.2 hK

/-- If `E_K` is not CM, a place is friendly exactly when it is unramified over `ℚ`. -/
theorem isFriendly_iff_of_not_isCMField (hK : ¬IsCMField (maximalRealOrCMSubfield K))
    (v : HeightOneSpectrum (𝓞 K)) : IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ (hK h').elim⟩⟩

/-- **Fields without CM subfields.** If `K` has no CM subfield, a place of `K` is friendly
exactly when it is unramified over `ℚ`. -/
theorem isFriendly_iff_of_forall_not_isCMField (hK : ∀ F : Subfield K, ¬IsCMField F)
    (v : HeightOneSpectrum (𝓞 K)) : IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 :=
  isFriendly_iff_of_not_isCMField (fun h ↦ hK _ h) v

/-- In a totally real field `E_K = K⁺ = K` is not CM, so a place is friendly exactly when it is
unramified over `ℚ`. -/
theorem isFriendly_iff_of_isTotallyReal [IsTotallyReal K] (v : HeightOneSpectrum (𝓞 K)) :
    IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 := by
  refine isFriendly_iff_of_not_isCMField (fun h ↦ ?_) v
  rw [isCMField_maximalRealOrCMSubfield_iff_ne_maximalRealSubfield,
    IsTotallyReal.maximalRealSubfield_eq_top] at h
  exact h (eq_top_iff.mpr (IsTotallyReal.maximalRealSubfield_eq_top (K := K) ▸
    maximalRealSubfield_le_maximalRealOrCMSubfield K))

/-- `ℤ → 𝓞 ℚ` is surjective. -/
private theorem algebraMap_int_ringOfIntegers_rat_surjective :
    Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := fun z ↦
  ⟨Rat.ringOfIntegersEquiv z, by
    rw [show algebraMap ℤ (𝓞 ℚ) = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) from
      Subsingleton.elim _ _]
    exact Rat.ringOfIntegersEquiv.symm_apply_apply z⟩

/-- **Every prime of `ℚ` is friendly.** -/
theorem isFriendly_rat (v : HeightOneSpectrum (𝓞 ℚ)) : IsFriendly v := by
  rw [isFriendly_iff_of_isTotallyReal]
  have : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 ℚ))
      algebraMap_int_ringOfIntegers_rat_surjective
  have : Algebra.EssFiniteType ℤ (𝓞 ℚ) := inferInstance
  exact Ideal.ramificationIdx_eq_one v.asIdeal ℤ

end TauCeti.NumberField
