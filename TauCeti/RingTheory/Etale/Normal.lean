/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import TauCeti.RingTheory.Flat.IntegrallyClosed
public import TauCeti.RingTheory.IntegralClosure.ReducedArtinian
public import TauCeti.RingTheory.Localization.LocalizationLocalization
public import TauCeti.RingTheory.Smooth.IntegralClosure
public import TauCeti.RingTheory.Unramified.Field

/-!
# Normality along étale homomorphisms

For an étale homomorphism of local rings `A → B`, that is, `B` is the localization at a prime of an
étale `A`-algebra and `A → B` is local, `A` is a normal domain (a domain that is integrally closed)
if and only if `B` is (Stacks, Proposition 41.19.7 (025P)).

The statements need no Noetherian, depth or dimension hypotheses.

## Main results

* `TauCeti.Algebra.Etale.isDomain_localization_atPrime_of_isIntegrallyClosed` and
  `isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed`: the local rings of an étale
  algebra over an integrally closed domain are integrally closed domains. The algebra is
  integrally closed in its generic fibre, a reduced Artinian ring, so this is a case of
  `IsIntegrallyClosedIn.isDomain_localization_atPrime`.
* `TauCeti.Algebra.Etale.isDomain_localization_atPrime_of_localization_under` and
  `isIntegrallyClosed_localization_atPrime_of_localization_under`: for `A → S` étale and a prime
  `q` of `S` over `p`, if `A_p` is an integrally closed domain then so is `S_q`.
* `TauCeti.Algebra.IsEtaleAt.isDomain_localization_atPrime_of_localization_under` and
  `isIntegrallyClosed_localization_atPrime_of_localization_under`: the same when `S` is only
  finitely presented and étale at `q`, since then some `S_f` with `f ∉ q` is étale.
* `TauCeti.Algebra.Etale.isIntegrallyClosed`: an étale domain over an integrally closed domain is
  integrally closed.
* `TauCeti.Algebra.isNormalDomain_iff_of_etale`: Stacks 025P; normality is expressed by
  `IsDomain` and `IsIntegrallyClosed` since Mathlib has no predicate "normal domain".

## References

* [Stacks Project, Proposition 41.19.7](https://stacks.math.columbia.edu/tag/025P) and
  [Lemma 10.163.9](https://stacks.math.columbia.edu/tag/033C).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Stacks/Common/EtaleNormal.lean`, which proves the ascent:
  `Algebra.Etale.isDomain_localization_atPrime_of_isIntegrallyClosed` and
  `isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed` are
  its `Pcf.Stacks.isDomain_isIntegrallyClosed_atPrime_of_etale_of_isDomain` (whose private
  steps `eq_of_comap_le_of_etale` and `isField_localization_tensor_fractionRing_of_etale` are
  generalized in `TauCeti.RingTheory.IntegralClosure.ReducedArtinian`);
  `Algebra.Etale.isDomain_localization_atPrime_of_localization_under` and
  `isIntegrallyClosed_localization_atPrime_of_localization_under` are
  its `Pcf.Stacks.isDomain_isIntegrallyClosed_atPrime_of_etale`; and
  `Algebra.Etale.isIntegrallyClosed` is its `Pcf.Stacks.isIntegrallyClosed_of_etale`, which the
  source states through its own normal-ring predicate. The descent direction and
  `isNormalDomain_iff_of_etale` are new.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Algebra

namespace Etale

section Core

variable {R S : Type*} [CommRing R] [CommRing S] [_root_.Algebra R S] [IsDomain R]
  [IsIntegrallyClosed R] [_root_.Algebra.Etale R S]

variable (R) in
include R in
/-- **The local rings of an étale algebra over an integrally closed domain are domains.** The étale
case of Stacks, Lemma 10.163.9 (033C), at one prime. -/
@[stacks 033C "étale case, over an integrally closed domain, at one prime"]
theorem isDomain_localization_atPrime_of_isIntegrallyClosed (Q : Ideal S) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) :=
  -- `S` is integrally closed in its generic fibre, a reduced Artinian ring.
  IsIntegrallyClosedIn.isDomain_localization_atPrime (S ⊗[R] FractionRing R) Q

variable (R) in
include R in
/-- **The local rings of an étale algebra over an integrally closed domain are integrally
closed.** The étale case of Stacks, Lemma 10.163.9 (033C), at one prime. -/
@[stacks 033C "étale case, over an integrally closed domain, at one prime"]
theorem isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed (Q : Ideal S) [Q.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime Q) :=
  IsIntegrallyClosedIn.isIntegrallyClosed_localization_atPrime (S ⊗[R] FractionRing R) Q

end Core

section Pointwise

variable {A S : Type*} [CommRing A] [CommRing S] [_root_.Algebra A S] [_root_.Algebra.Etale A S]

variable (A) in
/-- Let `A → S` be étale and `q` a prime of `S` over `p`. If `A_p` is an integrally closed domain,
then so is `S_q`, as a conjunction. -/
private theorem isDomain_and_isIntegrallyClosed_localization_atPrime (q : Ideal S) [q.IsPrime]
    [IsDomain (Localization.AtPrime (q.under A))]
    [IsIntegrallyClosed (Localization.AtPrime (q.under A))] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let p := q.under A
  let Ap := Localization.AtPrime p
  let C := Ap ⊗[A] S
  let : _root_.Algebra S C := _root_.Algebra.TensorProduct.rightAlgebra
  let M := _root_.Algebra.algebraMapSubmonoid S p.primeCompl
  have : IsLocalization M C := IsLocalization.tensorRight (S := S) Ap p.primeCompl
  have hd : Disjoint (M : Set S) (q : Set S) :=
    (Ideal.disjoint_map_primeCompl_iff_comap_le (f := algebraMap A S) (p := p) (I := q)).mpr
      le_rfl |>.symm
  obtain ⟨P, _, -, ⟨f⟩⟩ := IsLocalization.exists_ringEquiv_localization_atPrime M C q hd
  have := isDomain_localization_atPrime_of_isIntegrallyClosed Ap P
  have := isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed Ap P
  exact ⟨f.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv (R := Localization.AtPrime P) f.symm⟩

variable (A) in
/-- **Local rings of an étale algebra over integrally closed local rings of the base are
domains.** Let `A → S` be
étale and `q` a prime of `S` over `p`. If `A_p` is an integrally closed domain, then `S_q` is a
domain. The étale case of Stacks, Lemma 10.163.9 (033C), in local form. -/
@[stacks 033C "étale case, local form"]
theorem isDomain_localization_atPrime_of_localization_under (q : Ideal S) [q.IsPrime]
    [IsDomain (Localization.AtPrime (q.under A))]
    [IsIntegrallyClosed (Localization.AtPrime (q.under A))] :
    IsDomain (Localization.AtPrime q) :=
  (isDomain_and_isIntegrallyClosed_localization_atPrime A q).1

variable (A) in
/-- **Integrally closed local rings ascend along étale maps.** Let `A → S` be étale and `q` a prime
of `S` over `p`. If `A_p` is an integrally closed domain, then `S_q` is integrally closed. The
étale case of Stacks, Lemma 10.163.9 (033C), in local form. -/
@[stacks 033C "étale case, local form"]
theorem isIntegrallyClosed_localization_atPrime_of_localization_under (q : Ideal S) [q.IsPrime]
    [IsDomain (Localization.AtPrime (q.under A))]
    [IsIntegrallyClosed (Localization.AtPrime (q.under A))] :
    IsIntegrallyClosed (Localization.AtPrime q) :=
  (isDomain_and_isIntegrallyClosed_localization_atPrime A q).2

variable (A S) in
/-- **An étale domain over an integrally closed domain is integrally closed.** The étale case of
Stacks, Lemma 10.163.9 (033C), for domains. -/
@[stacks 033C "étale case, both rings domains"]
theorem isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A] [IsDomain S] :
    IsIntegrallyClosed S := by
  refine IsIntegrallyClosed.of_localization_maximal fun q _ hq ↦ ?_
  have := hq.isPrime
  exact isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed A q

end Pointwise

end Etale

namespace IsEtaleAt

variable {A S : Type*} [CommRing A] [CommRing S] [_root_.Algebra A S]
  [_root_.Algebra.FinitePresentation A S]

variable (A) in
/-- Let `S` be finitely presented over `A` and étale at a prime `q` over `p`. If `A_p` is an
integrally closed domain, then so is `S_q`, as a conjunction. -/
private theorem isDomain_and_isIntegrallyClosed_localization_atPrime (q : Ideal S) [q.IsPrime]
    [_root_.Algebra.IsEtaleAt A q] [IsDomain (Localization.AtPrime (q.under A))]
    [IsIntegrallyClosed (Localization.AtPrime (q.under A))] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  -- Some `S_f` with `f ∉ q` is étale over `A`, and `S_q` is a localization of it at a prime `P`.
  obtain ⟨f, hfq, _⟩ := _root_.Algebra.exists_etale_of_isEtaleAt (R := A) q
  obtain ⟨P, _, hP, ⟨e⟩⟩ := IsLocalization.exists_ringEquiv_localization_atPrime
    (Submonoid.powers f) (Localization.Away f) q
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfq)
  subst hP
  -- The prime `(P.under S).under A` is `P.under A`, as `A → S_f` factors through `S`.
  have : IsDomain (Localization.AtPrime (P.under A)) := by
    convert (inferInstance : IsDomain (Localization.AtPrime ((P.under S).under A))) using 3 <;>
      exact (Ideal.under_under P).symm
  have : IsIntegrallyClosed (Localization.AtPrime (P.under A)) := by
    convert (inferInstance : IsIntegrallyClosed (Localization.AtPrime ((P.under S).under A)))
      using 3 <;> exact (Ideal.under_under P).symm
  have := Etale.isDomain_localization_atPrime_of_localization_under A P
  have := Etale.isIntegrallyClosed_localization_atPrime_of_localization_under A P
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

variable (A) in
/-- **Local rings at étale points are domains.** Let `S` be finitely presented over `A` and étale
at a prime `q` over `p`. If `A_p` is an integrally closed domain, then `S_q` is a domain. The
pointwise étale case of Stacks, Lemma 10.163.9 (033C), in local form. -/
@[stacks 033C "pointwise étale case, local form"]
theorem isDomain_localization_atPrime_of_localization_under (q : Ideal S) [q.IsPrime]
    [_root_.Algebra.IsEtaleAt A q] [IsDomain (Localization.AtPrime (q.under A))]
    [IsIntegrallyClosed (Localization.AtPrime (q.under A))] :
    IsDomain (Localization.AtPrime q) :=
  (isDomain_and_isIntegrallyClosed_localization_atPrime A q).1

variable (A) in
/-- **Local rings at étale points are integrally closed.** Let `S` be finitely presented over `A`
and étale at a prime `q` over `p`. If `A_p` is an integrally closed domain, then `S_q` is
integrally closed. The pointwise étale case of Stacks, Lemma 10.163.9 (033C), in local form. -/
@[stacks 033C "pointwise étale case, local form"]
theorem isIntegrallyClosed_localization_atPrime_of_localization_under (q : Ideal S) [q.IsPrime]
    [_root_.Algebra.IsEtaleAt A q] [IsDomain (Localization.AtPrime (q.under A))]
    [IsIntegrallyClosed (Localization.AtPrime (q.under A))] :
    IsIntegrallyClosed (Localization.AtPrime q) :=
  (isDomain_and_isIntegrallyClosed_localization_atPrime A q).2

end IsEtaleAt

/-- **Normality along étale homomorphisms of local rings.** Let `A` be a local ring, `C` an étale
`A`-algebra, `q` a prime of `C`, and `B` an `A`-algebra isomorphic to `C_q` with `A → B` local
(an étale homomorphism of local rings, Stacks, Definition 41.11.1 (0258)). Then `A` is an
integrally closed domain iff `B` is. Stacks, Proposition 41.19.7 (025P); Stacks assumes `A` and
`B` Noetherian, and no Noetherian hypothesis is assumed here. -/
@[stacks 025P]
theorem isNormalDomain_iff_of_etale {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [IsLocalRing A] [_root_.Algebra A B] [IsLocalHom (algebraMap A B)]
    [_root_.Algebra A C] [_root_.Algebra.Etale A C] (q : Ideal C) [q.IsPrime]
    (e : B ≃ₐ[A] Localization.AtPrime q) :
    (IsDomain A ∧ IsIntegrallyClosed A) ↔ (IsDomain B ∧ IsIntegrallyClosed B) := by
  constructor
  · rintro ⟨hA, hAc⟩
    have := Etale.isDomain_localization_atPrime_of_isIntegrallyClosed A q
    have := Etale.isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed A q
    exact ⟨e.toMulEquiv.isDomain _,
      IsIntegrallyClosed.of_equiv (R := Localization.AtPrime q) e.symm.toRingEquiv⟩
  · rintro ⟨hB, hBc⟩
    have : IsLocalRing B := e.toRingEquiv.symm.isLocalRing
    have : Module.Flat A B := Module.Flat.of_linearEquiv e.toLinearEquiv
    have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact ⟨IsDomain.of_faithfulSMul A B, IsIntegrallyClosed.of_faithfullyFlat A B⟩

end Algebra

end TauCeti
