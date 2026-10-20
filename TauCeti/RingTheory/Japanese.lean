/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.Transfer
import TauCeti.RingTheory.Localization.FractionRing

/-!
# N-1 and Japanese rings

A domain `R` with fraction field `K` is *N-1* if the integral closure of `R` in `K` is a finite
`R`-module, and *N-2*, or *Japanese*, if for every finite extension `L` of `K` the integral
closure of `R` in `L` is a finite `R`-module, inseparable extensions included. These finiteness
conditions on normalization are the building blocks of Nagata rings, whose quotients by primes are
Japanese, and through them of the finiteness of the normalization of excellent schemes.

## Main definitions

* `TauCeti.Ring.IsN1 R`: the integral closure of the domain `R` in its fraction field is a finite
  `R`-module.
* `TauCeti.Ring.IsJapanese R`: the integral closure of the domain `R` in every finite extension
  of its fraction field is a finite `R`-module.

## Main results

* `TauCeti.Ring.isN1_iff`: the N-1 condition may be tested in any fraction field of `R`.
* `TauCeti.Ring.IsN1.of_isIntegrallyClosed`: an integrally closed domain is N-1.
* `TauCeti.Ring.IsJapanese.isN1`: a Japanese domain is N-1.
* `TauCeti.Ring.IsJapanese.finite_integralClosure_of_isFractionRing`: the Japanese condition
  applies to finite extensions of any fraction field of `R`.
* `TauCeti.Ring.IsJapanese.of_field`: a field is Japanese.
* `TauCeti.Ring.isJapanese_of_isLocalization`: a localization of a Japanese domain is Japanese.
* `TauCeti.Ring.IsN1.finite_integralClosure_of_isSeparable`: for a Noetherian N-1 domain, the
  integral closure in every finite separable extension of the fraction field is finite.
* `TauCeti.Ring.isJapanese_iff_isN1_of_charZero`: a Noetherian domain of characteristic zero is
  Japanese if and only if it is N-1. In particular a Noetherian integrally closed domain of
  characteristic zero, such as `ℤ` or a Dedekind domain of characteristic zero, is Japanese
  (`TauCeti.Ring.IsJapanese.of_isIntegrallyClosed_of_charZero`).

## Implementation notes

The fraction field in both definitions is `FractionRing R`, and the extensions `L` in
`TauCeti.Ring.IsJapanese` range over fields in the universe of `R`; every finite extension of the
fraction field is isomorphic to one of these. Both conditions are only defined for domains.

## References

* The Stacks Project, Section 10.161, Definition 10.161.1 (032F) for N-1 and N-2 domains,
  Lemma 10.161.3 (032G) for localizations, Lemma 10.161.8 (032L) for the separable case and
  Lemma 10.161.11 (032M) for the comparison in characteristic zero.
-/

public section

universe u

namespace TauCeti.Ring

/-- A domain `R` is **N-1** if the integral closure of `R` in its fraction field is a finite
`R`-module. Stacks, Definition 10.161.1 (032F). -/
class IsN1 (R : Type u) [CommRing R] [IsDomain R] : Prop where
  /-- The integral closure of an N-1 domain in its fraction field is a finite module. -/
  finite_integralClosure : Module.Finite R (integralClosure R (FractionRing R))

/-- A domain `R` is **Japanese**, or **N-2**, if for every finite extension `L` of its fraction
field the integral closure of `R` in `L` is a finite `R`-module. Inseparable extensions are
included. The extensions range over fields in the universe of `R`; see
`TauCeti.Ring.IsJapanese.finite_integralClosure_of_isFractionRing` for extensions of an arbitrary
fraction field. Stacks, Definition 10.161.1 (032F). -/
class IsJapanese (R : Type u) [CommRing R] [IsDomain R] : Prop where
  /-- The integral closure of a Japanese domain in a finite extension of its fraction field is a
  finite module. -/
  finite_integralClosure (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Module.Finite R (integralClosure R L)

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The N-1 condition can be tested in any fraction field `K` of `R`. -/
theorem isN1_iff (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsN1 R ↔ Module.Finite R (integralClosure R K) := by
  let e := FractionRing.algEquiv R K
  -- `e` carries the integral closure in `FractionRing R` onto the integral closure in `K`
  have he : (integralClosure R (FractionRing R)).map (e : FractionRing R →ₐ[R] K) =
      integralClosure R K :=
    integralClosure_map_algEquiv e
  let f := (Subalgebra.equivMapOfInjective _ _ e.injective).trans (Subalgebra.equivOfEq _ _ he)
  exact ⟨fun h ↦ h.finite_integralClosure.equiv f.toLinearEquiv,
    fun h ↦ ⟨h.equiv f.symm.toLinearEquiv⟩⟩

/-- An integrally closed domain is N-1: its integral closure in its fraction field is `R`
itself. -/
instance IsN1.of_isIntegrallyClosed [IsIntegrallyClosed R] : IsN1 R :=
  ⟨by rw [IsIntegrallyClosed.integralClosure_eq_bot]; infer_instance⟩

/-- A Japanese domain is N-1. -/
instance IsJapanese.isN1 [IsJapanese R] : IsN1 R :=
  ⟨IsJapanese.finite_integralClosure (FractionRing R)⟩

/-- The integral closure of a Japanese domain `R` in a finite extension `L` of any fraction field
`K` of `R` is a finite `R`-module. -/
theorem IsJapanese.finite_integralClosure_of_isFractionRing [IsJapanese R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (L : Type u) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] : Module.Finite R (integralClosure R L) := by
  -- make `L` a finite extension of `FractionRing R` through the isomorphism with `K`
  let e := FractionRing.algEquiv R K
  let : Algebra (FractionRing R) K := (e : FractionRing R →+* K).toAlgebra
  let : Algebra (FractionRing R) L := ((algebraMap K L).comp e).toAlgebra
  have : IsScalarTower (FractionRing R) K L := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (FractionRing R) L := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply (FractionRing R) K L,
      RingHom.algebraMap_toAlgebra, RingHom.coe_coe, AlgEquiv.commutes]
  have : Module.Finite (FractionRing R) K := .of_surjective (Algebra.linearMap _ K) e.surjective
  have : FiniteDimensional (FractionRing R) L := Module.Finite.trans K L
  exact IsJapanese.finite_integralClosure L

/-- A field is Japanese: a finite extension of its fraction field is a finite-dimensional vector
space over it, so every subalgebra is finite. -/
instance IsJapanese.of_field (k : Type u) [Field k] : IsJapanese k where
  finite_integralClosure L _ _ _ _ _ := by
    have : Module.Finite k (FractionRing k) :=
      .of_surjective (Algebra.linearMap k (FractionRing k))
        (IsFractionRing.surjective_iff_isField.2 (Field.toIsField k))
    have : Module.Finite k L := .trans (FractionRing k) L
    exact .of_injective (integralClosure k L).val.toLinearMap Subtype.val_injective

/-- **Finiteness of the integral closure in a separable extension.** If `R` is a Noetherian N-1
domain with fraction field `K` and `L` is a finite separable extension of `K`, then the integral
closure of `R` in `L` is a finite `R`-module. Stacks, Lemma 10.161.8 (032L) for normal `R`,
applied to the integral closure of `R` in `K`. -/
theorem IsN1.finite_integralClosure_of_isSeparable [IsNoetherianRing R] [IsN1 R]
    (K L : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite R (integralClosure R L) := by
  -- `R'`, the integral closure of `R` in `K`, is a Noetherian integrally closed domain with
  -- fraction field `K`, so its integral closure in `L` is finite over `R'`, hence over `R`
  let R' := integralClosure R K
  have : Module.Finite R R' := (isN1_iff K).1 ‹_›
  have : IsNoetherianRing R' := .of_finite R R'
  have : IsFractionRing R' K := integralClosure.isFractionRing_of_finite_extension K K
  have : IsIntegrallyClosed R' := integralClosure.isIntegrallyClosedOfFiniteExtension (L := K) K
  have : Module.Finite R' (integralClosure R' L) :=
    IsIntegralClosure.finite R' K L (integralClosure R' L)
  have : Module.Finite R (integralClosure R' L) := .trans R' _
  -- since `R'` is integral over `R`, the integral closure of `R'` in `L` is that of `R`
  have : IsIntegralClosure (integralClosure R' L) R L := IsIntegralClosure.tower_bot (A := R')
  exact .equiv
    (IsIntegralClosure.equiv R (integralClosure R' L) L (integralClosure R L)).toLinearEquiv

/-- **A Noetherian domain of characteristic zero is Japanese if and only if it is N-1**: every
finite extension of its fraction field is separable. Stacks, Lemma 10.161.11 (032M). -/
theorem isJapanese_iff_isN1_of_charZero [IsNoetherianRing R] [CharZero R] :
    IsJapanese R ↔ IsN1 R := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨fun L _ _ _ _ _ ↦ ?_⟩⟩
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  exact IsN1.finite_integralClosure_of_isSeparable (FractionRing R) L

/-- **A localization of a Japanese domain is Japanese.** Stacks, Lemma 10.161.3 (032G). -/
theorem isJapanese_of_isLocalization [IsJapanese R] (M : Submonoid R) (S : Type u) [CommRing S]
    [IsDomain S] [Algebra R S] [IsLocalization M S] : IsJapanese S where
  finite_integralClosure L _ _ _ _ _ := by
    let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
    have : IsScalarTower R S L := .of_algebraMap_eq fun _ ↦ rfl
    have : IsScalarTower R (FractionRing S) L := .of_algebraMap_eq fun x ↦
      (IsScalarTower.algebraMap_apply R S L x).trans (IsScalarTower.algebraMap_apply S _ L _)
    have : IsFractionRing R (FractionRing S) :=
      IsFractionRing.of_isLocalization_of_isFractionRing M S _ <|
        le_nonZeroDivisors_of_noZeroDivisors fun h ↦
          not_isUnit_zero (M₀ := S) (by simpa using IsLocalization.map_units S (⟨0, h⟩ : M))
    -- a finite set `s` spans the integral closure of `R` in `L` over `R`
    obtain ⟨s, hs⟩ :=
      (IsJapanese.finite_integralClosure_of_isFractionRing (R := R) (FractionRing S) L).fg_top
    -- an element of `L` integral over `R` is integral over `S`
    let ι : integralClosure R L →ₗ[R] integralClosure S L :=
      { toFun x := ⟨x, x.2.tower_top⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    -- every `y` integral over `S` has a multiple `m • y` with `m ∈ M` integral over `R`, which
    -- lies in the span of `s`; since `m` is a unit of `S`, `y` lies in the `S`-span of `ι '' s`
    classical
    refine ⟨⟨s.image ι, eq_top_iff.2 fun y _ ↦ ?_⟩⟩
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M (y : L) y.2
    have h : ι ⟨_, hm⟩ ∈ Submodule.span S (s.image ι : Set (integralClosure S L)) := by
      rw [Finset.coe_image]
      refine Submodule.span_le_restrictScalars R S _ ?_
      rw [← Submodule.map_span ι, hs]
      exact Submodule.mem_map_of_mem Submodule.mem_top
    have hι : ι ⟨_, hm⟩ = algebraMap R S m • y := Subtype.ext <| by
      simp [ι, Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S L]
    rw [hι] at h
    exact (Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units S m)).1 h

/-- The localization of a Japanese domain at a prime is Japanese. -/
instance IsJapanese.localization_atPrime [IsJapanese R] (p : Ideal R) [p.IsPrime] :
    IsJapanese (Localization.AtPrime p) :=
  isJapanese_of_isLocalization p.primeCompl _

/-- A Noetherian integrally closed domain of characteristic zero is Japanese. -/
instance IsJapanese.of_isIntegrallyClosed_of_charZero [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CharZero R] : IsJapanese R :=
  isJapanese_iff_isN1_of_charZero.2 inferInstance

example : IsJapanese ℤ := inferInstance

end TauCeti.Ring
