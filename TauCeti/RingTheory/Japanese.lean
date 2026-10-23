/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.FieldTheory.Normal.FixedField
import TauCeti.RingTheory.IntegralClosure.Transfer
import TauCeti.RingTheory.Localization.FractionRing
import TauCeti.RingTheory.Localization.Integral

/-!
# N-1 and Japanese domains

A domain `R` with fraction field `K` is *N-1* if its integral closure in `K` is a finite
`R`-module, and *Japanese* (or *N-2*) if its integral closure in every finite extension `L` of
`K` is a finite `R`-module, inseparable extensions included (Stacks, Definition 10.161.1 (032F)).
These finiteness conditions are the input of finite normalization: they are what makes the
normalization of an integral scheme in a finite extension of its function field a finite
morphism, and Nagata rings, the Noetherian rings all of whose prime quotients are Japanese, are
defined from them.

For a Noetherian integrally closed domain, finiteness of the integral closure in a *separable*
extension is classical (Mathlib's `IsIntegralClosure.finite`, by the trace form). Inseparable
extensions are where Japanese rings differ from N-1 rings; when the fraction field is perfect, as
in characteristic zero, there are none, and the two notions agree for Noetherian domains. In
general a finite extension sits inside a normal one, which is separable over a purely inseparable
extension of the fraction field, so for Noetherian domains only the purely inseparable extensions
need to be tested.

## Main definitions and results

* `TauCeti.Ring.IsN1 R`: the domain `R` is N-1.
* `TauCeti.Ring.IsJapanese R`: the domain `R` is Japanese (N-2).
* `TauCeti.Ring.IsJapanese.finite_integralClosure`: the defining property of a Japanese ring for
  an arbitrary model `K` of its fraction field and a finite extension `L` of `K` in any universe.
* `TauCeti.Ring.IsN1.of_isIntegrallyClosed`: an integrally closed ring is N-1.
* `TauCeti.Ring.IsJapanese.of_field`: a field is Japanese.
* `TauCeti.Ring.IsJapanese.of_isIntegrallyClosed`: a Noetherian integrally closed domain with
  perfect fraction field (for instance of characteristic zero, such as `ℤ` or the ring of integers
  of a number field) is Japanese.
* `TauCeti.Ring.IsJapanese.of_finite`: a domain that is a finite extension of a Japanese domain
  is Japanese (Stacks, Lemma 10.161.5 (032I), finite case); in particular being Japanese is
  invariant under ring isomorphisms (`RingEquiv.isJapanese`).
* `TauCeti.Ring.isN1_of_isLocalization`, `TauCeti.Ring.isJapanese_of_isLocalization`: a
  localization of an N-1, respectively Japanese, domain is N-1, respectively Japanese (Stacks,
  Lemma 10.161.3 (032G)).
* `TauCeti.Ring.finite_integralClosure_of_isSeparable`: for a Noetherian domain whose integral
  closure in a finite extension `M` of the fraction field is finite, the integral closure in every
  finite separable extension of `M` is finite (Stacks, Lemma 10.161.8 (032L), applied to the
  normalization); for `M` the fraction field this covers every Noetherian N-1 domain.
* `TauCeti.Ring.isJapanese_iff_isN1`: a Noetherian domain with perfect fraction field is Japanese
  if and only if it is N-1 (Stacks, Lemma 10.161.11 (032M), in characteristic zero).
* `TauCeti.Ring.isJapanese_iff_isPurelyInseparable`: a Noetherian domain is Japanese if and only
  if its integral closure in every finite purely inseparable extension of the fraction field is
  finite (Stacks, Lemma 10.161.12 (032N)); `TauCeti.Ring.IsJapanese.of_isPurelyInseparable` is
  the criterion for an arbitrary model of the fraction field.

## Implementation notes

As in Stacks, the definition of `IsJapanese R` quantifies over the finite extensions `L` of
`FractionRing R` lying in the universe of `R`. Every finite extension of a fraction field of `R`
is isomorphic to one of these, so `IsJapanese.finite_integralClosure` gives the property for
every fraction field and every universe.

## References

* [Stacks Project, Section 10.161 (032E)](https://stacks.math.columbia.edu/tag/032E)
-/

public section

universe u v w

namespace TauCeti.Ring

open Module

/-- A commutative ring `R` is *N-1* if its integral closure in its total ring of fractions
`FractionRing R` is a finite `R`-module. Stacks, Definition 10.161.1 (032F), where `R` is a domain
and `FractionRing R` its fraction field. See `IsN1.finite_integralClosure` for an arbitrary model
of the fraction field. -/
class IsN1 (R : Type u) [CommRing R] : Prop where
  finite_integralClosure_fractionRing : Module.Finite R (integralClosure R (FractionRing R))

/-- A domain `R` is *Japanese* (or *N-2*) if for every finite extension `L` of its fraction field,
the integral closure of `R` in `L` is a finite `R`-module; inseparable extensions are included.
Stacks, Definition 10.161.1 (032F). See `IsJapanese.finite_integralClosure` for an arbitrary model
of the fraction field and an extension in an arbitrary universe. -/
class IsJapanese (R : Type u) [CommRing R] [IsDomain R] : Prop where
  finite_integralClosure_fractionRing (L : Type u) [Field L] [Algebra R L]
    [Algebra (FractionRing R) L] [IsScalarTower R (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L] : Module.Finite R (integralClosure R L)

variable {R : Type u} [CommRing R]

namespace IsN1

/-- The integral closure of an N-1 ring in any model of its total ring of fractions is finite. -/
instance finite_integralClosure [IsN1 R] (K : Type v) [CommRing K] [Algebra R K]
    [IsFractionRing R K] : Module.Finite R (integralClosure R K) :=
  have := finite_integralClosure_fractionRing (R := R)
  .equiv (FractionRing.algEquiv R K).mapIntegralClosure.toLinearEquiv

/-- A ring whose integral closure in some model of its total ring of fractions is finite is
N-1. -/
theorem of_finite_integralClosure (K : Type v) [CommRing K] [Algebra R K] [IsFractionRing R K]
    [Module.Finite R (integralClosure R K)] : IsN1 R :=
  ⟨.equiv (FractionRing.algEquiv R K).symm.mapIntegralClosure.toLinearEquiv⟩

/-- An integrally closed ring is N-1: its integral closure in its total ring of fractions is `R`
itself. -/
instance of_isIntegrallyClosed [IsIntegrallyClosed R] : IsN1 R := by
  refine ⟨?_⟩
  rw [IsIntegrallyClosed.integralClosure_eq_bot R (FractionRing R)]
  infer_instance

end IsN1

namespace IsJapanese

variable [IsDomain R]

/-- The defining property of a Japanese domain `R`, for an arbitrary model `K` of the fraction
field and a finite extension `L` of `K` in an arbitrary universe: the integral closure of `R` in
`L` is a finite `R`-module. -/
theorem finite_integralClosure [IsJapanese R] (K : Type v) (L : Type w) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] : Module.Finite R (integralClosure R L) := by
  -- Replace `L` by an isomorphic copy `L'` in the universe of `R`, viewed as an extension of
  -- `FractionRing R` through the isomorphism `FractionRing R ≃ K`.
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  have : Small.{u} K := small_of_surjective e.surjective
  have : Small.{u} L := Module.Finite.small K L
  let L' := Shrink.{u} L
  let : Algebra (FractionRing R) K := e.toRingHom.toAlgebra
  have : Module.Finite (FractionRing R) K := RingHom.Finite.of_surjective _ e.surjective
  let : Algebra (FractionRing R) L' :=
    ((algebraMap K L').comp (algebraMap (FractionRing R) K)).toAlgebra
  have : IsScalarTower (FractionRing R) K L' := .of_algebraMap_eq' rfl
  -- The `R`- and `K`-algebra isomorphisms `Shrink.algEquiv` have the same underlying map.
  have : IsScalarTower R K L' := .of_algebraMap_eq fun r ↦ (Shrink.algEquiv R L).injective <| by
    rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply R K L]
    exact ((Shrink.algEquiv K L).commutes _).symm
  have : IsScalarTower R (FractionRing R) L' := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R K L']
    exact congrArg (algebraMap K L') (e.commutes r).symm
  have : FiniteDimensional (FractionRing R) L' := Module.Finite.trans K L'
  have := finite_integralClosure_fractionRing (R := R) L'
  exact .equiv (Shrink.algEquiv R L).mapIntegralClosure.toLinearEquiv

/-- A domain `R` is Japanese as soon as its integral closure in every finite extension of some
model `K` of its fraction field, in the universe of `R`, is a finite `R`-module. -/
theorem of_finite_integralClosure (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (h : ∀ (L : Type u) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
      [FiniteDimensional K L], Module.Finite R (integralClosure R L)) : IsJapanese R := by
  refine ⟨fun L _ _ _ _ _ ↦ ?_⟩
  let e : K ≃ₐ[R] FractionRing R := (FractionRing.algEquiv R K).symm
  let : Algebra K L := ((algebraMap (FractionRing R) L).comp e.toRingHom).toAlgebra
  have : IsScalarTower R K L := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (FractionRing R) L]
    exact congrArg (algebraMap (FractionRing R) L) (e.commutes r).symm
  let : Algebra K (FractionRing R) := e.toRingHom.toAlgebra
  have : IsScalarTower K (FractionRing R) L := .of_algebraMap_eq' rfl
  have : Module.Finite K (FractionRing R) := RingHom.Finite.of_surjective _ e.surjective
  have : FiniteDimensional K L := Module.Finite.trans (FractionRing R) L
  exact h L

/-- A Japanese domain is N-1. -/
instance isN1 [IsJapanese R] : IsN1 R :=
  ⟨finite_integralClosure_fractionRing (FractionRing R)⟩

/-- A field is Japanese: its integral closure in a finite extension is the whole extension, which
is finite-dimensional. -/
instance of_field (k : Type u) [Field k] : IsJapanese k := by
  refine ⟨fun L _ _ _ _ _ ↦ ?_⟩
  have : Module.Finite k (FractionRing k) := .equiv (FractionRing.algEquiv k k).symm.toLinearEquiv
  have : Module.Finite k L := .trans (FractionRing k) L
  have : IsNoetherian k L := IsNoetherian.iff_fg.mpr ‹_›
  exact .of_injective (integralClosure k L).val.toLinearMap Subtype.val_injective

/-- A Noetherian integrally closed domain whose fraction field is perfect is Japanese. This covers
every Noetherian integrally closed domain of characteristic zero, for instance `ℤ`, and Dedekind
domains of characteristic zero: over a perfect field every finite extension is separable, and
the integral closure in a finite separable extension is finite by the trace form. -/
instance of_isIntegrallyClosed [IsNoetherianRing R] [IsIntegrallyClosed R]
    [PerfectField (FractionRing R)] : IsJapanese R :=
  ⟨fun L _ _ _ _ _ ↦ IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)⟩

variable (R) in
/-- A domain `S` that is a finite extension of a Japanese domain `R` is Japanese, with no
Noetherian hypothesis. Stacks, Lemma 10.161.5 (032I), for finite extensions. -/
theorem of_finite (S : Type v) [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Module.Finite R S] [IsJapanese R] : IsJapanese S := by
  refine of_finite_integralClosure (FractionRing S) fun L _ _ _ _ _ ↦ ?_
  -- A finite extension `L` of the fraction field of `S` is a finite extension of the fraction
  -- field of `R`, and the integral closure of `S` in `L` is that of `R`, which is finite over `R`
  -- and hence over `S`. First view `L` as an extension of `FractionRing R`.
  let : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R (FractionRing S)
  let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S L := .of_algebraMap_eq' rfl
  let : Algebra (FractionRing R) L :=
    ((algebraMap (FractionRing S) L).comp (algebraMap (FractionRing R) (FractionRing S))).toAlgebra
  have : IsScalarTower (FractionRing R) (FractionRing S) L := .of_algebraMap_eq' rfl
  have : IsScalarTower R (FractionRing S) L := .to₁₃₄ R S _ _
  have : IsScalarTower R (FractionRing R) L := .to₁₂₄ R _ (FractionRing S) _
  have : FiniteDimensional (FractionRing R) L := Module.Finite.trans (FractionRing S) L
  have := finite_integralClosure (R := R) (FractionRing R) L
  -- The integral closure of `S` in `L` is that of `R`, as `S` is integral over `R`.
  have : IsIntegralClosure (integralClosure S L) R L :=
    TauCeti.IsIntegralClosure.tower_bot (A := S)
  have : Module.Finite R (integralClosure S L) :=
    .equiv (IsIntegralClosure.equiv R (integralClosure R L) L (integralClosure S L)).toLinearEquiv
  exact .of_restrictScalars_finite R S _

/-- Being Japanese is invariant under ring isomorphisms. -/
theorem _root_.RingEquiv.isJapanese {S : Type v} [CommRing S] [IsDomain S] [IsJapanese R]
    (e : R ≃+* S) : IsJapanese S :=
  let : Algebra R S := e.toRingHom.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr e.injective
  have : Module.Finite R S := RingHom.Finite.of_surjective _ e.surjective
  of_finite R S

end IsJapanese

/-- **Finiteness of the integral closure in a separable extension.** Let `R` be a Noetherian
domain with fraction field `K`, let `M` be a finite extension of `K` in which the integral closure
of `R` is a finite `R`-module, and let `E` be a finite separable extension of `M`. Then the
integral closure of `R` in `E` is a finite `R`-module. For `M = K` this says that the integral
closure of a Noetherian N-1 domain in a finite separable extension of its fraction field is
finite. Stacks, Lemma 10.161.8 (032L) for normal `R`, applied to the integral closure of `R` in
`M`. -/
theorem finite_integralClosure_of_isSeparable [IsDomain R] [IsNoetherianRing R]
    (K : Type*) (M : Type*) (E : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Field M]
    [Algebra K M] [Algebra R M] [IsScalarTower R K M] [FiniteDimensional K M]
    [Module.Finite R (integralClosure R M)] [Field E] [Algebra M E] [Algebra R E]
    [IsScalarTower R M E] [FiniteDimensional M E] [Algebra.IsSeparable M E] :
    Module.Finite R (integralClosure R E) := by
  -- The integral closure `B` of `R` in `M` is finite over `R`, hence a Noetherian integrally
  -- closed domain with fraction field `M`, and the integral closure of `R` in `E` is that of
  -- `B`, which is finite over `B` since `E / M` is separable.
  let B := integralClosure R M
  have : IsNoetherianRing B := isNoetherian_of_tower R inferInstance
  have : IsFractionRing B M := integralClosure.isFractionRing_of_finite_extension K M
  have : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : Module.Finite B (integralClosure B E) :=
    IsIntegralClosure.finite B M E (integralClosure B E)
  have : Module.Finite R (integralClosure B E) := .trans B _
  have : IsIntegralClosure (integralClosure B E) R E :=
    TauCeti.IsIntegralClosure.tower_bot (A := B)
  exact .equiv (IsIntegralClosure.equiv R (integralClosure B E) E
    (integralClosure R E)).toLinearEquiv

/-- A Noetherian domain whose fraction field is perfect, for instance of characteristic zero, is
Japanese if and only if it is N-1. Stacks, Lemma 10.161.11 (032M), stated there in characteristic
zero. -/
theorem isJapanese_iff_isN1 [IsDomain R] [IsNoetherianRing R] [PerfectField (FractionRing R)] :
    IsJapanese R ↔ IsN1 R :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨fun L _ _ _ _ _ ↦
    finite_integralClosure_of_isSeparable (FractionRing R) (FractionRing R) L⟩⟩

/-- **Testing the Japanese property on purely inseparable extensions.** A Noetherian domain `R`
with fraction field `K` is Japanese as soon as its integral closure in every finite purely
inseparable extension of `K` is a finite `R`-module. Stacks, Lemma 10.161.12 (032N), where `K`
has characteristic `p > 0`; no hypothesis on the characteristic is needed. -/
theorem IsJapanese.of_isPurelyInseparable [IsDomain R] [IsNoetherianRing R] (K : Type v)
    [Field K] [Algebra R K] [IsFractionRing R K]
    (h : ∀ (M : Type u) [Field M] [Algebra K M] [Algebra R M] [IsScalarTower R K M]
      [FiniteDimensional K M] [IsPurelyInseparable K M], Module.Finite R (integralClosure R M)) :
    IsJapanese R := by
  refine IsJapanese.of_finite_integralClosure K fun L _ _ _ _ _ ↦ ?_
  -- Embed `L` into a finite normal extension `E` of `K` and split `E / K` at the fixed field
  -- `M = E ^ Aut(E/K)`: `M / K` is purely inseparable and `E / M` is Galois.
  let E := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let _ : Algebra R E := ((algebraMap K E).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K E := .of_algebraMap_eq' rfl
  let M := IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[K] E))
  have : IsPurelyInseparable K M := IntermediateField.isPurelyInseparable_fixedField_top K E
  have : IsGalois M E := IsGalois.of_fixed_field E (⊤ : Subgroup (E ≃ₐ[K] E))
  -- `R` acts on `M` through `K` (`IntermediateField.algebra'`), so the tower `R → M → E` is the
  -- tower `R → K → E` and holds by definition.
  have : IsScalarTower R M E := .of_algebraMap_eq' rfl
  -- The integral closure of `R` in `M` is finite by hypothesis, and `E / M` is separable.
  have : Module.Finite R (integralClosure R M) := h M
  have : Module.Finite R (integralClosure R E) := finite_integralClosure_of_isSeparable K M E
  -- Finiteness descends from `E` to `L` because `R` is Noetherian.
  exact TauCeti.IsIntegralClosure.finite_of_injective (C' := integralClosure R E)
    ((IsScalarTower.toAlgHom K L E).restrictScalars R) (algebraMap L E).injective

/-- A Noetherian domain is Japanese if and only if its integral closure in every finite purely
inseparable extension of its fraction field is a finite module. Stacks, Lemma 10.161.12 (032N),
with no hypothesis on the characteristic. When the fraction field is perfect its only finite
purely inseparable extension is itself, and the condition reduces to N-1, as in
`isJapanese_iff_isN1`. -/
theorem isJapanese_iff_isPurelyInseparable [IsDomain R] [IsNoetherianRing R] :
    IsJapanese R ↔ ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
      [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
      [IsPurelyInseparable (FractionRing R) L], Module.Finite R (integralClosure R L) :=
  ⟨fun _ L _ _ _ _ _ _ ↦ IsJapanese.finite_integralClosure_fractionRing L,
    fun h ↦ IsJapanese.of_isPurelyInseparable (FractionRing R) fun M _ _ _ _ _ _ ↦ h M⟩

/-- **A localization of an N-1 domain is N-1.** Stacks, Lemma 10.161.3 (032G). -/
theorem isN1_of_isLocalization [IsDomain R] [IsN1 R] (M : Submonoid R) (S : Type*)
    [CommRing S] [IsDomain S] [Algebra R S] [IsLocalization M S] : IsN1 S where
  finite_integralClosure_fractionRing := by
    have : IsFractionRing R (FractionRing S) := IsFractionRing.of_isLocalization_of_isFractionRing
      M S _ (IsLocalization.le_nonZeroDivisors_of_nontrivial M S)
    exact finite_integralClosure_of_isLocalization M S (FractionRing S)

/-- **A localization of a Japanese domain is Japanese.** Stacks, Lemma 10.161.3 (032G). -/
theorem isJapanese_of_isLocalization [IsDomain R] [IsJapanese R] (M : Submonoid R) (S : Type*)
    [CommRing S] [IsDomain S] [Algebra R S] [IsLocalization M S] : IsJapanese S where
  finite_integralClosure_fractionRing L _ _ _ _ _ := by
    let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
    have : IsScalarTower R S L := .of_algebraMap_eq fun _ ↦ rfl
    have : IsScalarTower R (FractionRing S) L := .of_algebraMap_eq fun x ↦
      (IsScalarTower.algebraMap_apply R S L x).trans (IsScalarTower.algebraMap_apply S _ L _)
    have : IsFractionRing R (FractionRing S) := IsFractionRing.of_isLocalization_of_isFractionRing
      M S _ (IsLocalization.le_nonZeroDivisors_of_nontrivial M S)
    have := IsJapanese.finite_integralClosure (R := R) (FractionRing S) L
    exact finite_integralClosure_of_isLocalization M S L

/-- The localization of an N-1 domain at a prime is N-1. -/
instance IsN1.localization_atPrime [IsDomain R] [IsN1 R] (p : Ideal R) [p.IsPrime] :
    IsN1 (Localization.AtPrime p) :=
  isN1_of_isLocalization p.primeCompl _

/-- The localization of a Japanese domain at a prime is Japanese. -/
instance IsJapanese.localization_atPrime [IsDomain R] [IsJapanese R] (p : Ideal R) [p.IsPrime] :
    IsJapanese (Localization.AtPrime p) :=
  isJapanese_of_isLocalization p.primeCompl _

end TauCeti.Ring
