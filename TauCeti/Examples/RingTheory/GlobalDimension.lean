/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import TauCeti.RingTheory.TrivSqZeroExt

/-!
# Tests: global dimension and localizations of regular local rings

Serre's characterization says that a Noetherian local ring is regular exactly when it has finite
global dimension, and then the global dimension is the Krull dimension
(`TauCeti.isRegularLocalRing_tfae`). Consequently every localization of a regular local ring at a
prime is regular (`TauCeti.isRegularRing_of_isRegularLocalRing`). This file tests both
statements on small examples:

* a field has global dimension `0`;
* `ℤ` has global dimension `1`, realized by the cyclic module `ℤ ⧸ 2ℤ`, so the suprema over cyclic
  and over finite modules are both `1`;
* the dual numbers `k[ε] = k[x] ⧸ (x²)` over a field `k` are a Noetherian local ring which is not
  regular, so they have infinite global dimension;
* for the regular local ring `A = k[x, y]_(x, y)` and its prime `P = (x)`, the localization `A_P`
  is a discrete valuation ring, and it is the localization `k[x, y]_(x)`.
-/

open IsLocalRing Ideal MvPolynomial

namespace TauCeti

universe u

variable (k : Type u) [Field k]

/-- *globalDimension_field*: a field has global dimension `0`. -/
example : globalDimension.{u} k = 0 :=
  globalDimension_eq_zero_of_isSemisimpleRing k

section Integers

open CategoryTheory

/-- *globalDimension_int*: `ℤ` has global dimension `1`. -/
example : globalDimension.{0} ℤ = 1 :=
  globalDimension_eq_one_of_isPrincipalIdealRing Int.not_isField

/-- *projectiveDimension_int_quotient_two*: the cyclic `ℤ`-module `ℤ ⧸ 2ℤ` has projective
dimension `1`. -/
example : projectiveDimension (ModuleCat.of ℤ (ℤ ⧸ span {(2 : ℤ)})) = 1 := by
  rw [← projectiveDimension_eq_of_iso
    (Shrink.linearEquiv.{0} ℤ (ℤ ⧸ span {(2 : ℤ)})).toModuleIso]
  exact ModuleCat.projectiveDimension_quotient_span_singleton_eq_one two_ne_zero
    (by norm_num [Int.isUnit_iff])

/-- *globalDimension_int_iSup*: the global dimension `1` of `ℤ` is the supremum of the projective
dimensions of its cyclic modules and of its finite modules. -/
example : (⨆ I : Ideal ℤ, projectiveDimension
      (ModuleCat.of ℤ (Shrink.{0} (ℤ ⧸ I)))) = 1 ∧
    (⨆ (M : ModuleCat.{0} ℤ) (_ : Module.Finite ℤ M), projectiveDimension M) = 1 :=
  ⟨(globalDimension_eq_iSup_cyclic ℤ).symm.trans
      (globalDimension_eq_one_of_isPrincipalIdealRing Int.not_isField),
    (globalDimension_eq_iSup_finite ℤ).symm.trans
      (globalDimension_eq_one_of_isPrincipalIdealRing Int.not_isField)⟩

end Integers

section DualNumber

/-- *globalDimension_dualNumbers*: the dual numbers over a field are not a regular local ring, as
`ε² = 0` with `ε ≠ 0` while regular local rings are domains; so they have infinite global
dimension. -/
example : ¬ IsRegularLocalRing (DualNumber k) ∧ globalDimension.{u} (DualNumber k) = ⊤ := by
  have hreg : ¬ IsRegularLocalRing (DualNumber k) := fun _ ↦ by
    have hε : (DualNumber.eps : DualNumber k) = 0 := mul_self_eq_zero.mp DualNumber.eps_mul_eps
    simpa using congr_arg TrivSqZeroExt.snd hε
  exact ⟨hreg, not_lt_top_iff.mp (hreg ∘ isRegularLocalRing_iff_globalDimension_lt_top.mpr)⟩

end DualNumber

section Localization

attribute [local instance] isPrime_idealOfVars

/-- *localization_prime_example*: `k[x, y]_(x, y)` is a regular local ring. -/
example : IsRegularLocalRing (Localization.AtPrime (idealOfVars (Fin 2) k)) := inferInstance

/-- *localization_prime_example*: in `A = k[x, y]_(x, y)`, the ideal `P = x A` is a prime lying
over `(x)`. -/
example :
    letI P := (span {X 0} : Ideal (MvPolynomial (Fin 2) k)).map
      (algebraMap _ (Localization.AtPrime (idealOfVars (Fin 2) k)))
    P.IsPrime ∧ P.comap (algebraMap (MvPolynomial (Fin 2) k) _) = span {X 0} := by
  have : (span {X 0} : Ideal (MvPolynomial (Fin 2) k)).IsPrime :=
    (span_singleton_prime (X_ne_zero 0)).mpr prime_X
  have hle : span {X 0} ≤ idealOfVars (Fin 2) k := span_le.mpr
    (Set.singleton_subset_iff.mpr (subset_span ⟨0, rfl⟩))
  exact ⟨isPrime_map_of_isLocalizationAtPrime _ hle, under_map_of_isLocalizationAtPrime _ hle⟩

/-- *localization_prime_example*: let `A = k[x, y]_(x, y)` and let `P` be a prime of `A` lying over
the prime `(x)` of `k[x, y]`, such as `P = x A` (previous example). Then `A_P` is a discrete
valuation ring, and it is the localization `k[x, y]_(x)`. Regularity of `A_P` comes from the
localization theorem for regular local rings. -/
example (P : Ideal (Localization.AtPrime (idealOfVars (Fin 2) k))) [P.IsPrime]
    (hP : P.comap (algebraMap (MvPolynomial (Fin 2) k) _) = span {X 0}) :
    haveI : (span {X 0} : Ideal (MvPolynomial (Fin 2) k)).IsPrime :=
      (span_singleton_prime (X_ne_zero 0)).mpr prime_X
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      IsLocalization.AtPrime (Localization.AtPrime P) (span {X 0} : Ideal (MvPolynomial (Fin 2) k))
    := by
  have : (span {X 0} : Ideal (MvPolynomial (Fin 2) k)).IsPrime :=
    (span_singleton_prime (X_ne_zero 0)).mpr prime_X
  have hloc := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (idealOfVars (Fin 2) k).primeCompl (Localization.AtPrime P) P
  have hloc' : IsLocalization.AtPrime (Localization.AtPrime P)
      (span {X 0} : Ideal (MvPolynomial (Fin 2) k)) := by
    convert hloc
    exact hP.symm
  refine ⟨IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr ?_, hloc'⟩
  -- `A_P` is a localization of `k[x, y]` at `(x)`, a principal prime of height one.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (span {X 0} : Ideal (MvPolynomial (Fin 2) k))
      (Localization.AtPrime P),
    height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero 0)) (prime_X (R := k)).not_isUnit, WithBot.coe_one]

end Localization

end TauCeti
