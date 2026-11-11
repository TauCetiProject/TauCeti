/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic

import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.Normal.FixedField
import TauCeti.RingTheory.IntegralClosure.Transfer
import TauCeti.RingTheory.Localization.Away.FractionRing
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
  an arbitrary model `K` of its fraction field and a finitely generated, possibly transcendental,
  field extension `L` of `K` in any universe.
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
* `TauCeti.Ring.IsN1.exists_isIntegrallyClosed_localization_away`: an N-1 domain becomes
  integrally closed after inverting a single nonzero element, so the normal locus of its spectrum
  contains a nonempty open.
* `TauCeti.Ring.isN1_iff_exists_isIntegrallyClosed_localization_away_and_isN1_localization_atPrime`:
  the N-1 local criterion, a Noetherian domain is N-1 if and only if it becomes integrally closed
  after inverting a single nonzero element and its localizations at maximal ideals are N-1
  (Stacks, Lemma 10.161.15 (0333)). The substantive direction is
  `TauCeti.Ring.IsN1.of_isIntegrallyClosed_localization_away_of_isN1_localization_atPrime`.
* `TauCeti.Ring.IsN1.of_span_eq_top`, `TauCeti.Ring.IsJapanese.of_span_eq_top`: being N-1,
  respectively Japanese, is local on `Spec R`: a domain is N-1, respectively Japanese, as soon as
  its localizations `R_{f_i}` are, for elements `f_i` generating the unit ideal (Stacks,
  Lemma 10.161.6 (032J)).
* `TauCeti.Ring.finite_integralClosure_of_isSeparable`: for a Noetherian domain whose integral
  closure in a finite extension `M` of the fraction field is finite, the integral closure in every
  finite separable extension of `M` is finite (Stacks, Lemma 10.161.8 (032L), applied to the
  normalization); for `M` the fraction field this covers every Noetherian N-1 domain.
* `TauCeti.Ring.finite_integralClosure_of_etale`: the integral closure of a Noetherian N-1 domain
  in a finite étale algebra over its fraction field, a finite product of finite separable
  extensions, is finite.
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

* [Stacks Project, Section 10.161 (0BI1)](https://stacks.math.columbia.edu/tag/0BI1)
* The proof of `TauCeti.Ring.finite_integralClosure_of_etale` through the field factors follows
  T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/FiniteNormalModel.lean`, where the base is integrally closed
  (`finiteEtaleAlgebra_integralClosure_finite`).
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

/-- The case of `finite_integralClosure` where `L` is a finite extension of `K`: the integral
closure of the Japanese domain `R` in `L` is a finite `R`-module. -/
private theorem finite_integralClosure_of_finiteDimensional [IsJapanese R] (K : Type v)
    (L : Type w) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] :
    Module.Finite R (integralClosure R L) := by
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

/-- The defining property of a Japanese domain `R`, for an arbitrary model `K` of the fraction
field and a finitely generated field extension `L` of `K`, transcendental or not, in an arbitrary
universe: the integral closure of `R` in `L` is a finite `R`-module. -/
theorem finite_integralClosure [IsJapanese R] (K : Type v) (L : Type w)
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Algebra.EssFiniteType K L] :
    Module.Finite R (integralClosure R L) := by
  -- The elements of `L` integral over `R` are algebraic over `K`, so they lie in the relative
  -- algebraic closure of `K` in `L`, a finite extension of `K`.
  have := finite_integralClosure_of_finiteDimensional (R := R) K (algebraicClosure K L)
  let i : algebraicClosure K L →ₐ[R] L := (algebraicClosure K L).val.restrictScalars R
  refine .of_surjective i.mapIntegralClosure.toLinearMap fun ⟨y, hy⟩ ↦ ?_
  have hyA : y ∈ algebraicClosure K L := mem_algebraicClosure_iff'.mpr (hy.tower_top (A := K))
  exact ⟨⟨⟨y, hyA⟩, (isIntegral_algHom_iff i Subtype.val_injective).mp hy⟩, rfl⟩

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
theorem finite_integralClosure_of_isSeparable [IsNoetherianRing R]
    (K : Type*) (M : Type*) (E : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Field M]
    [Algebra K M] [Algebra R M] [IsScalarTower R K M] [FiniteDimensional K M]
    [Module.Finite R (integralClosure R M)] [Field E] [Algebra M E] [Algebra R E]
    [IsScalarTower R M E] [FiniteDimensional M E] [Algebra.IsSeparable M E] :
    Module.Finite R (integralClosure R E) := by
  have : IsDomain R := (IsFractionRing.isDomain_iff_isField (K := K)).mpr (Field.toIsField K)
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

/-- **Finiteness of the integral closure in a finite étale algebra.** Let `R` be a Noetherian N-1
domain with fraction field `K`, for instance an integrally closed Noetherian domain. Then the
integral closure of `R` in a finite étale `K`-algebra `L`, that is, in a finite product of finite
separable extensions of `K`, is a finite `R`-module. -/
theorem finite_integralClosure_of_etale [IsNoetherianRing R] [IsN1 R]
    (K : Type*) (L : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [CommRing L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra.Etale K L] :
    Module.Finite R (integralClosure R L) := by
  have : IsDomain R := (IsFractionRing.isDomain_iff_isField (K := K)).mpr (Field.toIsField K)
  -- `L` is a finite product of finite separable field extensions `Lᵢ` of `K`.
  obtain ⟨I, _, Li, _, _, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K L).mp inferInstance
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  let (i : I) : Algebra R (Li i) := ((algebraMap K (Li i)).comp (algebraMap R K)).toAlgebra
  have (i : I) : IsScalarTower R K (Li i) := .of_algebraMap_eq' rfl
  have (i : I) : FiniteDimensional K (Li i) :=
    .of_surjective ((LinearMap.proj i).comp e.toLinearEquiv.toLinearMap)
      ((Function.surjective_eval i).comp e.surjective)
  have (i : I) : Module.Finite R (integralClosure R (Li i)) :=
    have := hsep i
    finite_integralClosure_of_isSeparable K K (Li i)
  -- The integral closure in `L` embeds into the product of the integral closures in the `Lᵢ`.
  let φ : integralClosure R L →ₐ[R] ∀ i, integralClosure R (Li i) :=
    AlgHom.pi fun i ↦ ((Pi.evalAlgHom R Li i).comp (e.restrictScalars R).toAlgHom)
      |>.mapIntegralClosure
  refine Module.Finite.of_injective φ.toLinearMap fun x y h ↦ Subtype.ext (e.injective ?_)
  funext i
  exact congrArg Subtype.val (congrFun h i)

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
    (((IsScalarTower.toAlgHom K L E).restrictScalars R).comp (integralClosure R L).val)
    ((algebraMap L E).injective.comp Subtype.val_injective)

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
    [CommRing S] [Algebra R S] [IsLocalization M S] : IsN1 S where
  finite_integralClosure_fractionRing := by
    rcases subsingleton_or_nontrivial S with hS | hS
    · have : Subsingleton (FractionRing S) := inferInstance
      exact Module.Finite.of_finite
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

/-- **Being N-1 is local on `Spec R`.** If the elements of `t` generate the unit ideal of a
domain `R` and the localization `R_f` is N-1 for every nonzero `f ∈ t`, then `R` is N-1. Stacks,
Lemma 10.161.6 (032J). -/
theorem IsN1.of_span_eq_top [IsDomain R] {t : Set R} (ht : Ideal.span t = ⊤)
    (H : ∀ f ∈ t, f ≠ 0 → IsN1 (Localization.Away f)) : IsN1 R := by
  -- Only the nonzero `f ∈ t` matter, and for those `R_f` is a subring of `FractionRing R`.
  let K := FractionRing R
  let (f : ↥(t \ {0})) := Localization.Away.algebraOfIsFractionRing K f.2.2
  have (f : ↥(t \ {0})) := Localization.Away.isScalarTower_of_isFractionRing K f.2.2
  have (f : ↥(t \ {0})) := Localization.Away.isFractionRing K f.2.2
  have (f : ↥(t \ {0})) := H f.1 f.2.1 f.2.2
  exact ⟨finite_integralClosure_of_span_eq_top K (Ideal.span_sdiff_singleton_zero.trans ht)
    fun f ↦ IsN1.finite_integralClosure (R := Localization.Away f.1) K⟩

/-- **Being Japanese is local on `Spec R`.** If the elements of `t` generate the unit ideal of a
domain `R` and the localization `R_f` is Japanese for every `f ∈ t`, then `R` is Japanese. Stacks,
Lemma 10.161.6 (032J). The localization at `f = 0` is the zero ring, which is not a domain, and
the hypothesis asks nothing of it. -/
theorem IsJapanese.of_span_eq_top [IsDomain R] {t : Set R} (ht : Ideal.span t = ⊤)
    (H : ∀ f ∈ t, ∀ [IsDomain (Localization.Away f)], IsJapanese (Localization.Away f)) :
    IsJapanese R := by
  refine of_finite_integralClosure (FractionRing R) fun L _ _ _ _ _ ↦ ?_
  -- Only the nonzero `f ∈ t` matter, and for those `R_f` is a subring of `FractionRing R`, whose
  -- finite extension `L` is a finite extension of the fraction field of `R_f`.
  let K := FractionRing R
  let (f : ↥(t \ {0})) := Localization.Away.algebraOfIsFractionRing K f.2.2
  have (f : ↥(t \ {0})) := Localization.Away.isScalarTower_of_isFractionRing K f.2.2
  have (f : ↥(t \ {0})) := Localization.Away.isFractionRing K f.2.2
  let (f : ↥(t \ {0})) : Algebra (Localization.Away f.1) L :=
    ((algebraMap K L).comp (algebraMap (Localization.Away f.1) K)).toAlgebra
  have (f : ↥(t \ {0})) : IsScalarTower (Localization.Away f.1) K L := .of_algebraMap_eq' rfl
  have (f : ↥(t \ {0})) : IsScalarTower R (Localization.Away f.1) L := .to₁₂₄ _ _ K _
  have (f : ↥(t \ {0})) : IsDomain (Localization.Away f.1) := Localization.Away.isDomain f.2.2
  have (f : ↥(t \ {0})) := H f.1 f.2.1
  exact finite_integralClosure_of_span_eq_top L (Ideal.span_sdiff_singleton_zero.trans ht)
    fun f ↦ IsJapanese.finite_integralClosure (R := Localization.Away f.1) K L

/-- **An N-1 domain is generically integrally closed.** If `R` is an N-1 domain, there is a
nonzero `f : R` such that `R_f` is integrally closed: a common denominator `f` of the finite
`R`-module `R'` of elements of the fraction field integral over `R` satisfies `f • R' ⊆ R`, so
`R_f = R'_f` is integrally closed. -/
theorem IsN1.exists_isIntegrallyClosed_localization_away [IsDomain R] [IsN1 R] :
    ∃ f : R, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f) := by
  let K := FractionRing R
  have hfg : (integralClosure R K).toSubmodule.FG :=
    Module.Finite.iff_fg.mp (IsN1.finite_integralClosure (R := R) K)
  obtain ⟨f, hf, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) hfg
  have hf0 : f ≠ 0 := nonZeroDivisors.ne_zero hf
  refine ⟨f, hf0, ?_⟩
  let := Localization.Away.algebraOfIsFractionRing K hf0
  have := Localization.Away.isScalarTower_of_isFractionRing K hf0
  have := Localization.Away.isFractionRing K hf0
  refine (isIntegrallyClosed_iff K).mpr fun {x} hx ↦ ?_
  -- Some `y = f ^ n` makes `y • x` integral over `R`, and then `f • y • x = z` lies in `R`.
  obtain ⟨⟨y, hy⟩, hyx⟩ := hx.exists_multiple_integral_of_isLocalization (Submonoid.powers f) _
  simp only [Submonoid.smul_def] at hyx
  obtain ⟨z, hz⟩ := hint _ ((mem_integralClosure_iff R K).mpr hyx)
  have hm : f * y ∈ Submonoid.powers f := mul_mem (Submonoid.mem_powers f) hy
  refine ⟨IsLocalization.mk' _ z ⟨f * y, hm⟩, mul_right_cancel₀ (b := algebraMap R K (f * y))
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mul_mem hf (powers_le_nonZeroDivisors_of_noZeroDivisors hf0 hy))) ?_⟩
  calc algebraMap _ K (IsLocalization.mk' _ z ⟨f * y, hm⟩) * algebraMap R K (f * y)
      = algebraMap R K z := by
        rw [IsScalarTower.algebraMap_apply R (Localization.Away f) K (f * y), ← map_mul,
          IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
    _ = x * algebraMap R K (f * y) := by
        rw [hz, Algebra.smul_def, Algebra.smul_def, map_mul]
        ring

/-- The localization of an N-1 domain at a prime is N-1. -/
instance IsN1.localization_atPrime [IsDomain R] [IsN1 R] (p : Ideal R) [p.IsPrime] :
    IsN1 (Localization.AtPrime p) :=
  isN1_of_isLocalization p.primeCompl _

/-- The localization of a Japanese domain at a prime is Japanese. -/
instance IsJapanese.localization_atPrime [IsDomain R] [IsJapanese R] (p : Ideal R) [p.IsPrime] :
    IsJapanese (Localization.AtPrime p) :=
  isJapanese_of_isLocalization p.primeCompl _

section LocalCriterion

/-! ### The N-1 local criterion

Let `R` be a Noetherian domain with fraction field `K` and let `f : R` be nonzero with `R_f`
integrally closed. Every element `x` of `K` integral over `R` then lies in `R_f`, so `f ^ n • x ∈ R`
for some `n`: the integral closure is the increasing union of the finite `R`-modules
`integralPow f n` of integral `x` with `f ^ n • x ∈ R`. Multiplication by `f` embeds each quotient
`integralPow f (n + 2) / integralPow f (n + 1)` into the previous one, so the annihilators
`integralPowColon f n` of these quotients form an ascending chain of ideals, which stabilizes. If
`R_𝔪` is N-1, finitely many generators of its integral closure, after clearing denominators
outside `𝔪`, lie in some `integralPow f n`, so `integralPowColon f n` is not contained in `𝔪`.
When this holds at every maximal ideal the stable value of the chain is `R`, the chain
`integralPow f n` is eventually constant, and the integral closure is finite.
-/

variable {K : Type v} [Field K] [Algebra R K]

/-- The elements of `K` integral over `R` which `f ^ n` carries into `R`. -/
private def integralPow (f : R) (n : ℕ) : Submodule R K :=
  (integralClosure R K).toSubmodule ⊓
    (1 : Submodule R K).comap (f ^ n • LinearMap.id)

private theorem mem_integralPow {f : R} {n : ℕ} {x : K} :
    x ∈ integralPow f n ↔ IsIntegral R x ∧ ∃ r : R, algebraMap R K r = f ^ n • x := by
  simp [integralPow, Submodule.mem_one, mem_integralClosure_iff]

private theorem smul_mem_integralPow {f : R} {n : ℕ} {x : K} (hx : x ∈ integralPow f (n + 1)) :
    f • x ∈ integralPow f n := by
  obtain ⟨hx, r, hr⟩ := mem_integralPow.mp hx
  exact mem_integralPow.mpr ⟨hx.smul f, r, by rw [hr, smul_smul, ← pow_succ]⟩

private theorem integralPow_mono (f : R) : Monotone (integralPow (K := K) f) :=
  monotone_nat_of_le_succ fun n x hx ↦ by
    obtain ⟨hx, r, hr⟩ := mem_integralPow.mp hx
    exact mem_integralPow.mpr ⟨hx, f * r, by rw [pow_succ', mul_smul, ← hr, Algebra.smul_def,
      map_mul]⟩

private theorem fg_integralPow [IsDomain R] [IsNoetherianRing R] [IsFractionRing R K] {f : R}
    (hf : f ≠ 0) (n : ℕ) : (integralPow (K := K) f n).FG := by
  refine (Submodule.fg_span_singleton ((algebraMap R K f ^ n)⁻¹)).of_le fun x hx ↦ ?_
  obtain ⟨-, r, hr⟩ := mem_integralPow.mp hx
  have : algebraMap R K f ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf)
  refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
  rw [Algebra.smul_def, hr, Algebra.smul_def, map_pow]
  field_simp

/-- The ideal of `r : R` with `r • integralPow f (n + 1) ⊆ integralPow f n`. -/
private def integralPowColon (f : R) (n : ℕ) : Ideal R :=
  (integralPow (K := K) f n).colon (integralPow (K := K) f (n + 1))

private theorem integralPowColon_mono (f : R) : Monotone (integralPowColon (K := K) f) :=
  monotone_nat_of_le_succ fun n r hr ↦ Submodule.mem_colon.mpr fun x hx ↦ by
    obtain ⟨hxi, -⟩ := mem_integralPow.mp hx
    obtain ⟨-, s, hs⟩ := mem_integralPow.mp
      (Submodule.mem_colon.mp hr _ (smul_mem_integralPow hx))
    exact mem_integralPow.mpr ⟨hxi.smul r, s, by
      rw [hs, smul_comm r f x, smul_smul, ← pow_succ]⟩

/-- **The local step.** If the integral closure of `R_𝔭` in `K` is finite, then some ideal
`integralPowColon f n` is not contained in `𝔭`, provided every element of `K` integral over `R`
lies in some `integralPow f n`. -/
private theorem exists_not_integralPowColon_le [IsDomain R] [IsNoetherianRing R]
    [IsFractionRing R K] {f : R} (hf : f ≠ 0) (p : Ideal R) [p.IsPrime]
    [Algebra (Localization.AtPrime p) K] [IsScalarTower R (Localization.AtPrime p) K]
    [Module.Finite (Localization.AtPrime p) (integralClosure (Localization.AtPrime p) K)]
    (hfK : ∀ x : K, IsIntegral R x → ∃ n, x ∈ integralPow f n) :
    ∃ n, ¬ integralPowColon (K := K) f n ≤ p := by
  classical
  let Rₚ := Localization.AtPrime p
  -- A finite set `T` of elements integral over `R` whose `Rₚ`-span contains every element
  -- integral over `R`: clear the denominators of finitely many generators over `Rₚ`.
  obtain ⟨Y, hY⟩ := Module.Finite.fg_top (R := Rₚ) (M := integralClosure Rₚ K)
  choose s hs using fun y : integralClosure Rₚ K ↦
    y.2.exists_multiple_integral_of_isLocalization p.primeCompl (y : K)
  let T : Finset K := Y.image fun y ↦ (s y : R) • (y : K)
  have hspan (z : K) (hz : IsIntegral R z) : z ∈ Submodule.span Rₚ (T : Set K) := by
    have hz' : (⟨z, hz.tower_top⟩ : integralClosure Rₚ K) ∈ Submodule.span Rₚ (Y : Set _) :=
      hY ▸ Submodule.mem_top
    have := Submodule.mem_map_of_mem (f := (integralClosure Rₚ K).val.toLinearMap) hz'
    rw [← Submodule.span_image] at this
    refine Submodule.span_le.mpr ?_ this
    rintro _ ⟨y, hy, rfl⟩
    -- `y = (1 / s y) • (s y • y)` with `s y • y ∈ T`.
    have hmem : ((s y : R) • (y : K)) ∈ Submodule.span Rₚ (T : Set K) :=
      Submodule.subset_span (Finset.mem_image_of_mem _ hy)
    have heq : (y : K) = IsLocalization.mk' Rₚ (1 : R) (s y) • ((s y : R) • (y : K)) := by
      rw [← algebraMap_smul Rₚ (s y : R) (y : K), smul_smul, IsLocalization.mk'_spec, map_one,
        one_smul]
    simp only [AlgHom.toLinearMap_apply, Subalgebra.coe_val, SetLike.mem_coe]
    rw [heq]
    exact Submodule.smul_mem _ _ hmem
  -- Some `integralPow f n` contains `T`, hence spans every element integral over `R` over `Rₚ`.
  obtain ⟨n, hn⟩ : ∃ n, (T : Set K) ⊆ (integralPow f n : Submodule R K) := by
    choose! N hN using fun t (ht : t ∈ T) ↦ hfK t <| by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ht
      simpa only [Submonoid.smul_def] using hs y
    exact ⟨T.sup N, fun t ht ↦ integralPow_mono f (Finset.le_sup ht) (hN t ht)⟩
  -- Clearing denominators uniformly, one factor outside `p` carries the finitely generated
  -- `integralPow f (n + 1)` into `integralPow f n`.
  obtain ⟨u, hu, hzu⟩ := (fg_integralPow (K := K) hf (n + 1)).exists_smul_mem_of_le_span
    p.primeCompl fun z hz ↦ Submodule.span_mono hn (hspan z (mem_integralPow.mp hz).1)
  exact ⟨n, fun hle ↦ Ideal.mem_primeCompl_iff.mp hu (hle (Submodule.mem_colon.mpr hzu))⟩

/-- **The N-1 local criterion.** A Noetherian domain `R` is N-1 as soon as `R_f` is integrally
closed for some nonzero `f : R` and the localization `R_𝔪` is N-1 at every maximal ideal `𝔪`.
Stacks, Lemma 10.161.15 (0333); the equivalence is
`isN1_iff_exists_isIntegrallyClosed_localization_away_and_isN1_localization_atPrime`. -/
theorem IsN1.of_isIntegrallyClosed_localization_away_of_isN1_localization_atPrime [IsDomain R]
    [IsNoetherianRing R] {f : R} (hf : f ≠ 0) (hfn : IsIntegrallyClosed (Localization.Away f))
    (H : ∀ (m : Ideal R) [m.IsMaximal], IsN1 (Localization.AtPrime m)) : IsN1 R := by
  let K := FractionRing R
  -- Every element of `K` integral over `R` lies in `R_f`, so a power of `f` carries it into `R`.
  have hfK (x : K) (hx : IsIntegral R x) : ∃ n, x ∈ integralPow f n := by
    let := Localization.Away.algebraOfIsFractionRing K hf
    have := Localization.Away.isScalarTower_of_isFractionRing K hf
    have := Localization.Away.isFractionRing K hf
    obtain ⟨y, rfl⟩ :=
      (IsIntegrallyClosed.isIntegral_iff (R := Localization.Away f) (K := K)).mp hx.tower_top
    obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj (Submonoid.powers f) y
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    refine ⟨n, mem_integralPow.mpr ⟨hx, r, ?_⟩⟩
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization.Away f) K r,
      IsScalarTower.algebraMap_apply R (Localization.Away f) K (f ^ n), ← map_mul, mul_comm, hn,
      hy]
  -- The colon ideals form an ascending chain, which stabilizes at some `N`.
  have hmono := integralPowColon_mono (K := K) f
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R)
    ⟨integralPowColon (K := K) f, hmono⟩
  -- Locally at every maximal ideal the chain eventually leaves it, so its limit is `R`.
  have htop : integralPowColon (K := K) f N = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨n, hn⟩ := exists_not_integralPowColon_le hf m hfK
    exact hn ((hmono (le_max_left n N)).trans ((hN _ (le_max_right n N)).symm.le.trans hle))
  -- Hence the chain `integralPow f n` is constant from `N` on, and it exhausts the closure.
  have hA (n : ℕ) : integralPow (K := K) f n ≤ integralPow f N := by
    rcases le_total n N with h | h
    · exact integralPow_mono f h
    induction n, h using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      intro x hx
      have h1 : (1 : R) ∈ integralPowColon (K := K) f n := by
        have : integralPowColon (K := K) f N = integralPowColon f n := hN n hn
        rw [← this, htop]
        exact Submodule.mem_top
      exact ih (by simpa using Submodule.mem_colon.mp h1 x hx)
  have hfg : (integralClosure R K).toSubmodule.FG := by
    have : (integralClosure R K).toSubmodule = integralPow f N :=
      le_antisymm (fun x hx ↦ (hfK x hx).elim fun n hn ↦ hA n hn) inf_le_left
    rw [this]
    exact fg_integralPow hf N
  have := Module.Finite.iff_fg.mpr hfg
  exact IsN1.of_finite_integralClosure K

end LocalCriterion

/-- **The N-1 local criterion.** A Noetherian domain `R` is N-1 if and only if `R_f` is integrally
closed for some nonzero `f : R` and the localization `R_𝔪` is N-1 at every maximal ideal `𝔪`.
Stacks, Lemma 10.161.15 (0333). -/
@[stacks 0333]
theorem isN1_iff_exists_isIntegrallyClosed_localization_away_and_isN1_localization_atPrime
    [IsDomain R] [IsNoetherianRing R] :
    IsN1 R ↔ (∃ f : R, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f)) ∧
      ∀ (m : Ideal R) [m.IsMaximal], IsN1 (Localization.AtPrime m) :=
  ⟨fun _ ↦ ⟨IsN1.exists_isIntegrallyClosed_localization_away, fun _ _ ↦ inferInstance⟩,
    fun ⟨⟨_, hf, hfn⟩, H⟩ ↦
      .of_isIntegrallyClosed_localization_away_of_isN1_localization_atPrime hf hfn H⟩

end TauCeti.Ring
