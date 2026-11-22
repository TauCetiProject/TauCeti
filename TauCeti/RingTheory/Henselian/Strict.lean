/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic
public import TauCeti.RingTheory.Henselian.Etale
public import TauCeti.RingTheory.Henselian.Integral
public import TauCeti.RingTheory.Henselian.Quotient
public import TauCeti.RingTheory.LocalRing.ResidueField.Instances

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.PurelyInseparable.Basic
import TauCeti.RingTheory.Etale.AdjoinRoot
import TauCeti.RingTheory.LocalRing.Etale
import TauCeti.RingTheory.Unramified.LocalRing

/-!
# Strictly henselian local rings

A local ring `S` is *strictly henselian* (`TauCeti.IsStrictlyHenselianLocalRing`) if it is a
henselian local ring and its residue field `ResidueField S` is separably closed.

The class extends `HenselianLocalRing S` by the field `isSepClosed_residueField`. As with Mathlib's
`IsSepClosure.sep_closed`, that projection is not registered as a global instance because the
converse constructor `TauCeti.IsStrictlyHenselianLocalRing.of_isSepClosed` is an instance and the
two together would form an instance cycle. Consequently, statements taking
`[IsStrictlyHenselianLocalRing S]` apply automatically when `[HenselianLocalRing S]` and
`[IsSepClosed (ResidueField S)]` are in scope, while statements phrased in terms of the pair apply
under `[IsStrictlyHenselianLocalRing S]` by supplying `isSepClosed_residueField` (and at the prime
residue field `(maximalIdeal S).ResidueField` automatically via
`TauCeti.IsStrictlyHenselianLocalRing.isSepClosed_maximalIdeal_residueField`).

Over a strictly henselian local ring `S`, every prime `𝔮` of an étale `S`-algebra `T` lying over
the maximal ideal `𝔪_S` has residue field separable over `κ(𝔪_S)`, hence equal to `κ(𝔪_S)`
(`TauCeti.residueFieldMap_bijective_of_isSepClosed_of_isUnramifiedAt`), so
`HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_of_residueFieldMap_surjective` produces a
unique `S`-algebra retraction `τ : T →ₐ[S] S` with `τ⁻¹(𝔪_S) = 𝔮`
(`TauCeti.IsStrictlyHenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_of_etale`).
Conversely, this étale retraction property implies both `HenselianLocalRing S` (via
`HenselianLocalRing.tfae_etale`) and `IsSepClosed (ResidueField S)` (by retracting the finite étale
local algebra `S[X]/(g)` attached to a monic lift `g` of an irreducible separable polynomial over
`ResidueField S`), yielding the equivalence `TauCeti.IsStrictlyHenselianLocalRing.tfae` (Stacks,
Tag 04GG).

The second half of the file establishes permanence properties (Stacks, Tag 04GH):
* separably closed fields are strictly henselian (`TauCeti.Field.isSepClosed_residueField` together
  with `Field.henselian` and `IsStrictlyHenselianLocalRing.of_isSepClosed`);
* surjective ring homomorphisms onto nontrivial targets and ring isomorphisms preserve strict
  henselianity (`RingHom.isStrictlyHenselianLocalRing_of_surjective`,
  `Ideal.isStrictlyHenselianLocalRing_quotient`, `RingEquiv.isStrictlyHenselianLocalRing`);
* integral (in particular finite) local extensions and integral closures in domains over strictly
  henselian local rings are strictly henselian (`IsStrictlyHenselianLocalRing.of_isIntegral`,
  `integralClosure.isStrictlyHenselianLocalRing`);
* every strictly henselian local ring satisfies `IsFiniteEtaleSplit`
  (`IsStrictlyHenselianLocalRing.isFiniteEtaleSplit`), so finite étale algebras over it split as
  finite products of copies of the base (`Algebra.IsFiniteSplit.of_isFiniteEtaleSplit`).

## Main definitions and results

* `TauCeti.IsStrictlyHenselianLocalRing`: typeclass for strictly henselian local rings.
* `TauCeti.IsStrictlyHenselianLocalRing.of_isSepClosed`: instance from `HenselianLocalRing S` and
  `IsSepClosed (ResidueField S)`.
* `TauCeti.IsStrictlyHenselianLocalRing.isSepClosed_maximalIdeal_residueField`: instance giving
  `IsSepClosed (maximalIdeal S).ResidueField` from `[IsStrictlyHenselianLocalRing S]`.
* `TauCeti.IsStrictlyHenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_of_etale`: unique
  `S`-algebra retraction at any prime of an étale `S`-algebra lying over the maximal ideal.
* `TauCeti.IsStrictlyHenselianLocalRing.tfae`: characterisations of strictly henselian local rings
  (Stacks, Tag 04GG).
* `TauCeti.IsStrictlyHenselianLocalRing.isFiniteEtaleSplit`: strictly henselian local rings have no
  nonsplit finite étale covers.
* `RingHom.isStrictlyHenselianLocalRing_of_surjective`,
  `Ideal.isStrictlyHenselianLocalRing_quotient`,
  `TauCeti.IsStrictlyHenselianLocalRing.of_isIntegral`: permanence under quotients and integral
  local extensions (Stacks, Tag 04GH).

## References

* [Stacks Project, Definition 10.153.1 (Tag 04GF)](https://stacks.math.columbia.edu/tag/04GF)
* [Stacks Project, Lemma 10.153.3 (Tag 04GG)](https://stacks.math.columbia.edu/tag/04GG)
* [Stacks Project, Lemma 10.153.4 (Tag 04GH)](https://stacks.math.columbia.edu/tag/04GH)
* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3, for rings without nonsplit finite étale
  covers.
-/

public section

open _root_.IsLocalRing Polynomial

universe u

namespace TauCeti

/-- A local ring is *strictly henselian* if it is henselian and its residue field is separably
closed. Stacks, Definition 10.153.1 (04GF), (2). -/
@[stacks 04GF "(2)"]
class IsStrictlyHenselianLocalRing (S : Type*) [CommRing S] : Prop
    extends HenselianLocalRing S where
  /-- The residue field is separably closed. It is not an instance, as Mathlib's
  `IsSepClosure.sep_closed` is not: with `of_isSepClosed` it would close a cycle of instances. -/
  isSepClosed_residueField : IsSepClosed (_root_.IsLocalRing.ResidueField S)

namespace IsStrictlyHenselianLocalRing

/-- A henselian local ring with separably closed residue field is strictly henselian, so a
statement taking the class applies under the pair; in the other direction the parent instance
gives `HenselianLocalRing S` and the field `isSepClosed_residueField`, supplied by name, gives
`IsSepClosed (ResidueField S)`. -/
instance of_isSepClosed {S : Type*} [CommRing S] [HenselianLocalRing S]
    [IsSepClosed (_root_.IsLocalRing.ResidueField S)] : IsStrictlyHenselianLocalRing S where
  isSepClosed_residueField := ‹_›

/-- `IsStrictlyHenselianLocalRing S` is equivalent to the conjunction of `HenselianLocalRing S`
and `IsSepClosed (ResidueField S)` once `S` is a local ring. -/
theorem iff_henselianLocalRing_and_isSepClosed (S : Type*) [CommRing S] [_root_.IsLocalRing S] :
    IsStrictlyHenselianLocalRing S ↔
      HenselianLocalRing S ∧ IsSepClosed (_root_.IsLocalRing.ResidueField S) :=
  ⟨fun h ↦ ⟨h.toHenselianLocalRing, h.isSepClosed_residueField⟩,
    fun ⟨_, _⟩ ↦ of_isSepClosed⟩

/-- Over a strictly henselian local ring `S`, the prime residue field
`(maximalIdeal S).ResidueField` at the maximal ideal is separably closed. Unlike
`isSepClosed_residueField`, this can be registered as an instance without cycling with
`of_isSepClosed` because its head is the residue field of `Localization.AtPrime (maximalIdeal S)`.
-/
instance isSepClosed_maximalIdeal_residueField (S : Type*) [CommRing S]
    [IsStrictlyHenselianLocalRing S] :
    IsSepClosed (maximalIdeal S).ResidueField :=
  have := isSepClosed_residueField (S := S)
  inferInstance

section Etale

variable {S T : Type*} [CommRing S] [IsStrictlyHenselianLocalRing S] [CommRing T] [Algebra S T]

/-- Over a strictly henselian local ring `S`, every prime `𝔮` of an étale `S`-algebra `T` lying
over `𝔪_S` is the preimage of `𝔪_S` under a unique `S`-algebra retraction `τ : T →ₐ[S] S`. -/
@[stacks 04GG "(1) ⇒ (8), strictly henselian form"]
theorem existsUnique_algHom_comap_maximalIdeal_of_etale [Algebra.Etale S T] (𝔮 : Ideal T)
    [𝔮.IsPrime] (h𝔮 : 𝔮.comap (algebraMap S T) = maximalIdeal S) :
    ∃! τ : T →ₐ[S] S, (maximalIdeal S).comap τ = 𝔮 :=
  HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_of_residueFieldMap_surjective h𝔮
    (residueFieldMap_bijective_of_isSepClosed_of_isUnramifiedAt h𝔮.symm).surjective

end Etale

/-- **Strictly henselian local rings.** For a local ring `S`, the class, the pair "henselian with
separably closed residue field", and unique retractions of étale neighbourhoods of the closed
point are equivalent: every étale `S`-algebra `T` with a prime `𝔮` over the maximal ideal has a
unique `S`-algebra map `τ : T → S` with `τ⁻¹(𝔪) = 𝔮`. Stacks, Lemma 10.153.3 (04GG), (8), where
`κ(𝔮) = κ` holds because the residue field is separably closed; conversely a retraction of the
finite étale local algebra `S[X]/(g)` of a lifted separable irreducible polynomial gives a root of
it in `κ`. -/
@[stacks 04GG "(1) iff (8), strictly henselian form"]
theorem tfae (S : Type u) [CommRing S] [_root_.IsLocalRing S] :
    List.TFAE
      [IsStrictlyHenselianLocalRing S,
        HenselianLocalRing S ∧ IsSepClosed (_root_.IsLocalRing.ResidueField S),
        ∀ (T : Type u) [CommRing T] [Algebra S T] [Algebra.Etale S T] (𝔮 : Ideal T) [𝔮.IsPrime],
          𝔮.comap (algebraMap S T) = _root_.IsLocalRing.maximalIdeal S →
            ∃! τ : T →ₐ[S] S, (_root_.IsLocalRing.maximalIdeal S).comap τ = 𝔮] := by
  tfae_have 1 ↔ 2 := iff_henselianLocalRing_and_isSepClosed S
  tfae_have 1 → 3 := fun _ _ _ _ _ 𝔮 _ h𝔮 ↦ existsUnique_algHom_comap_maximalIdeal_of_etale 𝔮 h𝔮
  tfae_have 3 → 2 := by
    intro h
    refine ⟨((HenselianLocalRing.tfae_etale S).out 5 1 rfl rfl).mp fun T _ _ _ 𝔮 _ h𝔮 _ ↦
        h T 𝔮 h𝔮,
      IsSepClosed.of_exists_root (ResidueField S) fun p hp_monic hp_irr hp_sep ↦ ?_⟩
    obtain ⟨g, hg_map, -, hg_monic⟩ :=
      lifts_and_degree_eq_and_monic (map_surjective (residue S) residue_surjective p) hp_monic
    have hirr : Irreducible (g.map (residue S)) := hg_map ▸ hp_irr
    have : Algebra.IsStandardEtale S (AdjoinRoot g) :=
      hg_monic.isStandardEtale_adjoinRoot
        (hg_monic.separable_of_separable_map_residue (hg_map ▸ hp_sep))
    let _ : _root_.IsLocalRing (AdjoinRoot g) := hg_monic.isLocalRing_adjoinRoot hirr
    have : IsLocalHom (algebraMap S (AdjoinRoot g)) := AdjoinRoot.isLocalHom_algebraMap hirr
    obtain ⟨τ, -, -⟩ := h (AdjoinRoot g) (maximalIdeal (AdjoinRoot g))
      (maximalIdeal_comap (algebraMap S (AdjoinRoot g)))
    refine ⟨residue S (τ (AdjoinRoot.root g)), ?_⟩
    have hroot : g.eval (τ (AdjoinRoot.root g)) = 0 := by
      rw [← coe_aeval_eq_eval, aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self,
        map_zero]
    rw [← hg_map, eval_map, eval₂_at_apply, hroot, map_zero]
  tfae_finish

/-- A strictly henselian local ring has no nonsplit finite étale covers: a faithfully flat finite
étale algebra has a point over the separably closed residue field, which lifts to a section. -/
instance isFiniteEtaleSplit (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    IsFiniteEtaleSplit R :=
  have := isSepClosed_residueField (S := R)
  isFiniteEtaleSplit_iff_exists_section.mpr fun T _ _ _ _ _ ↦
    have ⟨ψ⟩ := IsFiniteEtaleSplit.nonempty_algHom (ResidueField R) T
    have ⟨φ, _⟩ := (HenselianLocalRing.comp_bijective (R := R) (S := T)).2 ψ
    ⟨φ⟩

/-- **Integral local extensions of strictly henselian local rings.** Any local ring `S` integral
over a strictly henselian local ring `R` is strictly henselian. -/
@[stacks 04GH "(2)"]
theorem of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsStrictlyHenselianLocalRing R] [_root_.IsLocalRing S] [Algebra.IsIntegral R S] :
    IsStrictlyHenselianLocalRing S := by
  have : HenselianLocalRing S := HenselianLocalRing.of_isIntegral R S
  have : IsSepClosed (ResidueField R) := isSepClosed_residueField
  have : Algebra.IsIntegral R (ResidueField S) := Algebra.IsIntegral.trans S
  have : Algebra.IsIntegral (ResidueField R) (ResidueField S) := Algebra.IsIntegral.tower_top R
  have : IsSepClosed (ResidueField S) :=
    Algebra.IsAlgebraic.isSepClosed (F := ResidueField R) (E := ResidueField S)
  exact of_isSepClosed

/-- Any domain integral over a strictly henselian local ring is a strictly henselian local ring. -/
@[stacks 04GH "(2)"]
theorem of_isDomain_of_isIntegral (R S : Type*) [CommRing R] [IsStrictlyHenselianLocalRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] :
    IsStrictlyHenselianLocalRing S :=
  have := isLocalRing_of_isDomain_of_isIntegral_of_henselianRing R S
  of_isIntegral R S

end IsStrictlyHenselianLocalRing

/-- Any model of the integral closure of a strictly henselian local ring in a domain is a strictly
henselian local ring. -/
@[stacks 04GH "(2)"]
theorem IsIntegralClosure.isStrictlyHenselianLocalRing (R S B : Type*) [CommRing R]
    [IsStrictlyHenselianLocalRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [CommRing B] [Algebra R B] [Algebra B S] [IsScalarTower R B S]
    [IsIntegralClosure B R S] : IsStrictlyHenselianLocalRing B := by
  have : IsDomain B := (_root_.IsIntegralClosure.algebraMap_injective B R S).isDomain _
  have := _root_.IsIntegralClosure.isIntegral_algebra R S (A := B)
  exact IsStrictlyHenselianLocalRing.of_isDomain_of_isIntegral R B

/-- The integral closure of a strictly henselian local ring in a domain is strictly henselian. -/
instance integralClosure.isStrictlyHenselianLocalRing (R S : Type*) [CommRing R]
    [IsStrictlyHenselianLocalRing R] [CommRing S] [IsDomain S] [Algebra R S] :
    IsStrictlyHenselianLocalRing (integralClosure R S) :=
  IsIntegralClosure.isStrictlyHenselianLocalRing R S _

end TauCeti

namespace RingHom

/-- A surjective ring homomorphism from a strictly henselian local ring to a nontrivial ring has a
strictly henselian target. -/
@[stacks 04GH "(1)"]
theorem isStrictlyHenselianLocalRing_of_surjective {R S : Type*} [CommRing R]
    [TauCeti.IsStrictlyHenselianLocalRing R] [CommRing S] [Nontrivial S] (φ : R →+* S)
    (hφ : Function.Surjective φ) : TauCeti.IsStrictlyHenselianLocalRing S := by
  have := φ.henselianLocalRing_of_surjective hφ
  have := TauCeti.IsStrictlyHenselianLocalRing.isSepClosed_residueField (S := R)
  have := IsLocalHom.of_surjective φ hφ
  have hsurj : Function.Surjective (ResidueField.map φ) := fun y ↦ by
    obtain ⟨s, rfl⟩ := residue_surjective y
    obtain ⟨r, rfl⟩ := hφ s
    exact ⟨residue R r, ResidueField.map_residue φ r⟩
  have : IsSepClosed (ResidueField S) :=
    .of_ringEquiv
      (RingEquiv.ofBijective (ResidueField.map φ) ⟨(ResidueField.map φ).injective, hsurj⟩)
  exact TauCeti.IsStrictlyHenselianLocalRing.of_isSepClosed

end RingHom

namespace Ideal

/-- Every nontrivial quotient of a strictly henselian local ring is strictly henselian. -/
@[stacks 04GH "(1)"]
instance isStrictlyHenselianLocalRing_quotient {R : Type*} [CommRing R]
    [TauCeti.IsStrictlyHenselianLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)] :
    TauCeti.IsStrictlyHenselianLocalRing (R ⧸ I) :=
  (Ideal.Quotient.mk I).isStrictlyHenselianLocalRing_of_surjective Ideal.Quotient.mk_surjective

end Ideal

namespace RingEquiv

/-- A ring isomorphism transports `TauCeti.IsStrictlyHenselianLocalRing`. -/
protected theorem isStrictlyHenselianLocalRing {R S : Type*} [CommRing R]
    [TauCeti.IsStrictlyHenselianLocalRing R] [CommRing S] (e : R ≃+* S) :
    TauCeti.IsStrictlyHenselianLocalRing S :=
  have := e.symm.toEquiv.nontrivial
  (e : R →+* S).isStrictlyHenselianLocalRing_of_surjective e.surjective

end RingEquiv
