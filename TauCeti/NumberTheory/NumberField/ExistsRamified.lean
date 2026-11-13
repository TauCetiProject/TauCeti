/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Number fields unramified over a degree-one base

Mathlib's `Mathlib/NumberTheory/NumberField/ExistsRamified.lean` records Minkowski's theorem in
the form `NumberField.exists_not_isUnramifiedAt_int`: a number field of degree greater than one
over `ℚ` has a maximal ideal of its ring of integers that is ramified over `ℤ`. This file adds the
trivial converse and the relative form of Minkowski's theorem over a base of degree one.

The relative form is what a statement about extensions unramified over a subfield `ℚ(√d)` needs
in the degenerate case where `d` is a rational square: then the subfield is `ℚ`, and an extension
unramified over it at every finite prime is `ℚ` itself.

## Main results

* `NumberField.unramified_of_finrank_eq_one`: the ring of integers of a number field of degree
  one over `ℚ` is unramified over `ℤ`.
* `NumberField.finrank_eq_one_of_finrank_eq_one_of_isUnramifiedIn`: a number field that is
  unramified at every finite prime over a field of degree one over `ℚ` has degree one over `ℚ`.
-/

public section

open scoped NumberField

namespace NumberField

/-- **The ring of integers of a degree-one number field is unramified over `ℤ`.** If `F` has
degree one over `ℚ` and `𝒪` is the integral closure of `ℤ` in `F`, then `ℤ → 𝒪` is bijective,
since `𝒪` is free of rank `Module.finrank ℚ F = 1` over `ℤ`; so `𝒪` is unramified over `ℤ`, and
in particular every prime of `𝒪` is. This is the converse of
`NumberField.exists_not_isUnramifiedAt_int`. -/
theorem unramified_of_finrank_eq_one {F : Type*} (𝒪 : Type*) [Field F] [CharZero F] [CommRing 𝒪]
    [Algebra 𝒪 F] [IsIntegralClosure 𝒪 ℤ F] (h : Module.finrank ℚ F = 1) :
    Algebra.Unramified ℤ 𝒪 := by
  have : NumberField F := { to_finiteDimensional := Module.finite_of_finrank_eq_succ h }
  have := IsIntegralClosure.module_free ℤ ℚ F 𝒪
  have := IsIntegralClosure.finite ℤ ℚ F 𝒪
  have : Algebra.FormallyUnramified ℤ 𝒪 :=
    .of_surjective (Algebra.ofId ℤ 𝒪)
      (Module.Free.bijective_algebraMap_of_finrank_eq_one
        ((IsIntegralClosure.rank ℤ ℚ F 𝒪).trans h)).2
  exact ⟨inferInstance, inferInstance⟩

/-- **Minkowski's theorem over a degree-one base.** Let `M` be a number field that is an algebra
over a field `F` of degree one over `ℚ`. If `M` is unramified over `F` at every nonzero prime of
`𝓞 F`, then `M` has degree one over `ℚ`: every prime of `𝓞 M` is then unramified over `ℤ`, by
`NumberField.unramified_of_finrank_eq_one` and transitivity, which
`NumberField.exists_not_isUnramifiedAt_int` rules out unless `Module.finrank ℚ M = 1`. -/
theorem finrank_eq_one_of_finrank_eq_one_of_isUnramifiedIn {F M : Type*} [Field F] [CharZero F]
    [Field M] [NumberField M] [Algebra F M] (hF : Module.finrank ℚ F = 1)
    (hunr : ∀ q : Ideal (𝓞 F), q.IsPrime → q ≠ ⊥ → Algebra.IsUnramifiedIn (𝓞 M) q) :
    Module.finrank ℚ M = 1 := by
  by_contra H
  obtain ⟨P, _, hP⟩ := exists_not_isUnramifiedAt_int (K := M) (𝒪 := 𝓞 M) H
  have : Algebra.IsUnramifiedAt (𝓞 F) P := hunr (P.under (𝓞 F)) inferInstance
    (Ideal.under_ne_bot (𝓞 F) (Ideal.IsMaximal.ne_bot_of_isIntegral_int P)) P inferInstance
    inferInstance
  have := unramified_of_finrank_eq_one (𝓞 F) hF
  exact hP (Algebra.IsUnramifiedAt.comp (P.under (𝓞 F)) P)

end NumberField
