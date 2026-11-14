/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.RingTheory.Henselian.Etale
public import TauCeti.RingTheory.Henselian.Integral
public import TauCeti.RingTheory.Henselian.Quotient

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Unramified.LocalRing
import TauCeti.FieldTheory.IsSepClosed
import TauCeti.RingTheory.AdjoinRoot.Separable

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
under `[IsStrictlyHenselianLocalRing S]` by supplying `isSepClosed_residueField`.

Over a strictly henselian local ring `S`, every prime `𝔮` of an étale `S`-algebra `T` lying over
the maximal ideal `𝔪_S` has residue field separable over `κ(𝔪_S)`, hence equal to `κ(𝔪_S)`, so
`HenselianLocalRing.existsUnique_algHom_of_surjective_residueField_map` produces a unique
`S`-algebra retraction `τ : T →ₐ[S] S` with `τ⁻¹(𝔪_S) = 𝔮`
(`TauCeti.IsStrictlyHenselianLocalRing.existsUnique_algHom_of_etale`). Conversely, this étale
retraction property implies both `HenselianLocalRing S` (via `HenselianLocalRing.tfae_etale`) and
`IsSepClosed (ResidueField S)` (by retracting the standard étale algebra `S[X, 1/g']/(g)` attached
to a monic lift `g` of an irreducible separable polynomial over `ResidueField S`), yielding the
equivalence `TauCeti.IsStrictlyHenselianLocalRing.tfae` (Stacks, Tag 04GG).

The second half of the file establishes permanence properties (Stacks, Tag 04GH):
* separably closed fields are strictly henselian (`Field.isSepClosed_residueField` together with
  `Field.henselian` and `IsStrictlyHenselianLocalRing.of_isSepClosed`);
* surjective ring homomorphisms onto nontrivial targets and ring isomorphisms preserve strict
  henselianity (`RingHom.isStrictlyHenselianLocalRing_of_surjective`,
  `Ideal.isStrictlyHenselianLocalRing_quotient`, `RingEquiv.isStrictlyHenselianLocalRing`);
* integral (in particular finite) local extensions and integral closures in domains over strictly
  henselian local rings are strictly henselian (`IsStrictlyHenselianLocalRing.of_isIntegral`,
  `IsStrictlyHenselianLocalRing.of_finite`, `integralClosure.isStrictlyHenselianLocalRing`);
* every strictly henselian local ring satisfies `IsFiniteEtaleSplit`, so finite étale algebras over
  it split as finite products of copies of the base
  (`IsStrictlyHenselianLocalRing.isFiniteEtaleSplit`,
  `Algebra.IsFiniteSplit.of_isStrictlyHenselianLocalRing`).

## Main definitions and results

* `TauCeti.IsStrictlyHenselianLocalRing`: typeclass for strictly henselian local rings.
* `TauCeti.IsStrictlyHenselianLocalRing.of_isSepClosed`: instance from `HenselianLocalRing S` and
  `IsSepClosed (ResidueField S)`.
* `TauCeti.IsStrictlyHenselianLocalRing.existsUnique_algHom_of_etale`: unique `S`-algebra
  retraction at any prime of an étale `S`-algebra lying over the maximal ideal.
* `TauCeti.IsStrictlyHenselianLocalRing.tfae`: characterisations of strictly henselian local rings
  (Stacks, Tag 04GG).
* `RingHom.isStrictlyHenselianLocalRing_of_surjective`,
  `Ideal.isStrictlyHenselianLocalRing_quotient`,
  `TauCeti.IsStrictlyHenselianLocalRing.of_isIntegral`,
  `TauCeti.IsStrictlyHenselianLocalRing.of_finite`: permanence under quotients and integral local
  extensions (Stacks, Tag 04GH).

## References

* [Stacks Project, Definition 10.153.1 (Tag 04GF)](https://stacks.math.columbia.edu/tag/04GF)
* [Stacks Project, Lemma 10.153.3 (Tag 04GG)](https://stacks.math.columbia.edu/tag/04GG)
* [Stacks Project, Lemma 10.153.4 (Tag 04GH)](https://stacks.math.columbia.edu/tag/04GH)
-/

public section

open IsLocalRing Polynomial

universe u

namespace TauCeti

/-- A local ring is *strictly henselian* if it is henselian and its residue field is separably
closed. Stacks, Definition 10.153.1 (04GF), (2). -/
@[stacks 04GF "(2)"]
class IsStrictlyHenselianLocalRing (S : Type*) [CommRing S] : Prop
    extends HenselianLocalRing S where
  /-- The residue field is separably closed. It is not an instance, as Mathlib's
  `IsSepClosure.sep_closed` is not: with `of_isSepClosed` it would close a cycle of instances. -/
  isSepClosed_residueField : IsSepClosed (IsLocalRing.ResidueField S)

namespace IsStrictlyHenselianLocalRing

/-- A henselian local ring with separably closed residue field is strictly henselian, so a
statement taking the class applies under the pair; in the other direction the parent instance
gives `HenselianLocalRing S` and the field `isSepClosed_residueField`, supplied by name, gives
`IsSepClosed (ResidueField S)`. -/
instance of_isSepClosed {S : Type*} [CommRing S] [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField S)] : IsStrictlyHenselianLocalRing S where
  isSepClosed_residueField := ‹_›

/-- `IsStrictlyHenselianLocalRing S` is equivalent to the conjunction of `HenselianLocalRing S`
and `IsSepClosed (ResidueField S)` once `S` is a local ring. -/
theorem iff_henselianLocalRing_and_isSepClosed (S : Type*) [CommRing S] [IsLocalRing S] :
    IsStrictlyHenselianLocalRing S ↔
      HenselianLocalRing S ∧ IsSepClosed (IsLocalRing.ResidueField S) :=
  ⟨fun h ↦ ⟨h.toHenselianLocalRing, h.isSepClosed_residueField⟩,
    fun ⟨_, _⟩ ↦ of_isSepClosed⟩

section Etale

variable {S T : Type*} [CommRing S] [IsStrictlyHenselianLocalRing S] [CommRing T] [Algebra S T]

/-- Over a strictly henselian local ring `S`, the residue field `(maximalIdeal S).ResidueField`
of the maximal ideal is separably closed. -/
private theorem isSepClosed_maximalIdeal_residueField :
    IsSepClosed (maximalIdeal S).ResidueField := by
  have := isSepClosed_residueField (S := S)
  let g : (maximalIdeal S).ResidueField →+* ResidueField S :=
    Ideal.ResidueField.lift (maximalIdeal S) (residue S) (ker_residue (R := S)).ge fun r hr ↦ by
      rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero, ne_eq,
        residue_eq_zero_iff]
      exact hr
  have hg_surj : Function.Surjective g := fun x ↦ by
    obtain ⟨s, rfl⟩ := residue_surjective x
    exact ⟨algebraMap S (maximalIdeal S).ResidueField s,
      Ideal.ResidueField.lift_algebraMap _ _ _ _ s⟩
  exact .of_ringEquiv (RingEquiv.ofBijective g ⟨g.injective, hg_surj⟩).symm

/-- Over a strictly henselian local ring `S`, any prime `𝔮` of an essentially-finite-type
`S`-algebra `T` at which `T` is unramified and which lies over `𝔪_S` has trivial residue field
extension `κ(𝔪_S) ≅ κ(𝔮)`. -/
@[stacks 04GG "(1) ⇒ (8), residue field isomorphism"]
theorem bijective_residueField_map_of_isUnramifiedAt [Algebra.EssFiniteType S T] {𝔮 : Ideal T}
    [𝔮.IsPrime] [Algebra.IsUnramifiedAt S 𝔮]
    (h𝔮 : 𝔮.comap (algebraMap S T) = maximalIdeal S) :
    Function.Bijective (Ideal.ResidueField.map (maximalIdeal S) 𝔮 (algebraMap S T) h𝔮.symm) := by
  have : IsSepClosed (maximalIdeal S).ResidueField := isSepClosed_maximalIdeal_residueField
  have : 𝔮.LiesOver (maximalIdeal S) := ⟨h𝔮.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal S) 𝔮
  have heq : Ideal.ResidueField.map (maximalIdeal S) 𝔮 (algebraMap S T) h𝔮.symm =
      algebraMap (maximalIdeal S).ResidueField 𝔮.ResidueField := by
    ext s
    rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply S (maximalIdeal S).ResidueField 𝔮.ResidueField,
      IsScalarTower.algebraMap_apply S T 𝔮.ResidueField]
  rw [heq]
  exact IsSepClosed.algebraMap_bijective (maximalIdeal S).ResidueField 𝔮.ResidueField

/-- Over a strictly henselian local ring `S`, every prime `𝔮` of an étale `S`-algebra `T` lying
over `𝔪_S` is the preimage of `𝔪_S` under a unique `S`-algebra retraction `τ : T →ₐ[S] S`. -/
@[stacks 04GG "(1) ⇒ (8), strictly henselian form"]
theorem existsUnique_algHom_of_etale [Algebra.Etale S T] (𝔮 : Ideal T) [𝔮.IsPrime]
    (h𝔮 : 𝔮.comap (algebraMap S T) = maximalIdeal S) :
    ∃! τ : T →ₐ[S] S, (maximalIdeal S).comap τ = 𝔮 :=
  HenselianLocalRing.existsUnique_algHom_of_surjective_residueField_map h𝔮
    (bijective_residueField_map_of_isUnramifiedAt h𝔮).surjective

end Etale

/-- **Strictly henselian local rings.** For a local ring `S`, the class, the pair "henselian with
separably closed residue field", and unique retractions of étale neighbourhoods of the closed
point are equivalent: every étale `S`-algebra `T` with a prime `𝔮` over the maximal ideal has a
unique `S`-algebra map `τ : T → S` with `τ⁻¹(𝔪) = 𝔮`. Stacks, Lemma 10.153.3 (04GG), (8), where
`κ(𝔮) = κ` holds because the residue field is separably closed; conversely a retraction of the
standard étale algebra of a lifted separable irreducible polynomial gives a root of it in `κ`. -/
@[stacks 04GG "(1) iff (8), strictly henselian form"]
theorem tfae (S : Type u) [CommRing S] [IsLocalRing S] :
    List.TFAE
      [IsStrictlyHenselianLocalRing S,
        HenselianLocalRing S ∧ IsSepClosed (IsLocalRing.ResidueField S),
        ∀ (T : Type u) [CommRing T] [Algebra S T] [Algebra.Etale S T] (𝔮 : Ideal T) [𝔮.IsPrime],
          𝔮.comap (algebraMap S T) = IsLocalRing.maximalIdeal S →
            ∃! τ : T →ₐ[S] S, (IsLocalRing.maximalIdeal S).comap τ = 𝔮] := by
  tfae_have 1 ↔ 2 := iff_henselianLocalRing_and_isSepClosed S
  tfae_have 1 → 3 := fun _ _ _ _ _ 𝔮 _ h𝔮 ↦ existsUnique_algHom_of_etale 𝔮 h𝔮
  tfae_have 3 → 2 := by
    intro h
    refine ⟨((HenselianLocalRing.tfae_etale S).out 5 1 rfl rfl).mp fun T _ _ _ 𝔮 _ h𝔮 _ ↦
        h T 𝔮 h𝔮,
      IsSepClosed.of_exists_root (ResidueField S) fun p hp_monic hp_irr hp_sep ↦ ?_⟩
    obtain ⟨g, hg_map, -, hg_monic⟩ :=
      lifts_and_degree_eq_and_monic (Polynomial.mem_lifts _ |>.mpr
        (Polynomial.map_surjective (residue S) residue_surjective p)) hp_monic
    let P : StandardEtalePair S := ⟨g, hg_monic, derivative g, 1, 0, 1, by ring⟩
    have : Fact (Irreducible p) := ⟨hp_irr⟩
    let A := AdjoinRoot p
    let : Algebra S A := RingHom.toAlgebra ((AdjoinRoot.of p).comp (residue S))
    have hA_map : algebraMap S A = (AdjoinRoot.of p).comp (residue S) := rfl
    have hev (q : S[X]) : aeval (AdjoinRoot.root p) q = AdjoinRoot.mk p (q.map (residue S)) := by
      rw [aeval_def, hA_map, ← eval₂_map]
      exact AdjoinRoot.aeval_eq (q.map (residue S))
    have hP : P.HasMap (AdjoinRoot.root p) := by
      refine ⟨?_, ?_⟩
      · change aeval (AdjoinRoot.root p) g = 0
        rw [hev, hg_map, AdjoinRoot.mk_self]
      · change IsUnit (aeval (AdjoinRoot.root p) (derivative g))
        rw [hev, ← derivative_map, hg_map]
        exact Polynomial.separable_iff_isUnit_mk_derivative.mp hp_sep
    let ψ : P.Ring →ₐ[S] A := P.lift (AdjoinRoot.root p) hP
    have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
    have hker : (RingHom.ker ψ).comap (algebraMap S P.Ring) = maximalIdeal S := by
      ext s
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, hA_map, RingHom.comp_apply,
        map_eq_zero_iff (AdjoinRoot.of p) (AdjoinRoot.of p).injective, residue_eq_zero_iff]
    obtain ⟨τ, -, -⟩ := h P.Ring (RingHom.ker ψ) hker
    refine ⟨residue S (τ P.X), ?_⟩
    have hroot : g.eval (τ P.X) = 0 := by simpa [coe_aeval_eq_eval] using (P.hasMap_X.map τ).1
    rw [← hg_map, eval_map, eval₂_at_apply, hroot, map_zero]
  tfae_finish

/-- A strictly henselian local ring has no nonsplit finite étale covers. -/
instance isFiniteEtaleSplit (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    IsFiniteEtaleSplit R :=
  have := isSepClosed_residueField (S := R)
  inferInstance

/-- **Integral local extensions of strictly henselian local rings.** Any local ring `S` integral
over a strictly henselian local ring `R` is strictly henselian. -/
@[stacks 04GH "(2)"]
theorem of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsStrictlyHenselianLocalRing R] [IsLocalRing S] [Algebra.IsIntegral R S] :
    IsStrictlyHenselianLocalRing S := by
  have : HenselianLocalRing S := HenselianLocalRing.of_isIntegral R S
  have : IsSepClosed (ResidueField R) := isSepClosed_residueField
  have : IsLocalHom (algebraMap R S) := ⟨fun r hr ↦ by
    by_contra hnr
    rw [← mem_nonunits_iff, ← mem_maximalIdeal,
      ← Ideal.comap_eq_maximalIdeal_of_isIntegral (maximalIdeal S), Ideal.mem_comap,
      mem_maximalIdeal, mem_nonunits_iff] at hnr
    exact hnr hr⟩
  have : Algebra.IsIntegral R (ResidueField S) :=
    have : Algebra.IsIntegral S (ResidueField S) :=
      Algebra.isIntegral_of_surjective residue_surjective
    Algebra.IsIntegral.trans S
  have : Algebra.IsIntegral (ResidueField R) (ResidueField S) := Algebra.IsIntegral.tower_top R
  have : IsSepClosed (ResidueField S) :=
    Algebra.IsAlgebraic.isSepClosed (F := ResidueField R) (E := ResidueField S)
  exact of_isSepClosed

/-- Any finite local algebra over a strictly henselian local ring is strictly henselian. -/
@[stacks 04GH "(2)"]
theorem of_finite (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsStrictlyHenselianLocalRing R] [IsLocalRing S] [Module.Finite R S] :
    IsStrictlyHenselianLocalRing S :=
  of_isIntegral R S

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

/-- Over a strictly henselian local ring `R`, every finite étale `R`-algebra splits as a finite
product of copies of `R`. -/
theorem Algebra.IsFiniteSplit.of_isStrictlyHenselianLocalRing (R : Type u) [CommRing R]
    [TauCeti.IsStrictlyHenselianLocalRing R] (T : Type*) [CommRing T] [Algebra R T]
    [Algebra.Etale R T] [Module.Finite R T] : Algebra.IsFiniteSplit R T :=
  .of_isFiniteEtaleSplit T

/-- The residue field of a separably closed field is separably closed; together with
`Field.henselian` and `TauCeti.IsStrictlyHenselianLocalRing.of_isSepClosed`, this makes every
separably closed field strictly henselian. -/
instance Field.isSepClosed_residueField (K : Type*) [Field K] [IsSepClosed K] :
    IsSepClosed (ResidueField K) :=
  .of_ringEquiv (RingEquiv.ofBijective (residue K) ⟨(residue K).injective, residue_surjective⟩)

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
