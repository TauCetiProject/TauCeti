/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.Reduced
public import TauCeti.RingTheory.Flat.IntegrallyClosed
public import TauCeti.RingTheory.Localization.Integral
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
  algebra over an integrally closed domain are integrally closed domains.
* `TauCeti.Algebra.Etale.isDomain_localization_atPrime_of_localization_under` and
  `isIntegrallyClosed_localization_atPrime_of_localization_under`: for `A → S` étale and a prime
  `q` of `S` over `p`, if `A_p` is an integrally closed domain then so is `S_q`.
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
  its `Pcf.Stacks.isDomain_isIntegrallyClosed_atPrime_of_etale_of_isDomain` (with the private
  steps `eq_of_comap_le_of_etale` and `isField_localization_tensor_fractionRing_of_etale`);
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

/-- Two primes of the generic fibre of an étale algebra over an integrally closed domain whose
contractions lie in a common prime `Q` coincide. -/
private theorem eq_of_comap_le (Q : Ideal S) [Q.IsPrime]
    (P₁ P₂ : Ideal (S ⊗[R] FractionRing R)) [P₁.IsPrime] [P₂.IsPrime]
    (h₁ : P₁.comap (algebraMap S _) ≤ Q) (h₂ : P₂.comap (algebraMap S _) ≤ Q) : P₁ = P₂ := by
  -- A separating idempotent of the Artinian generic fibre is integral over `S`, hence comes from
  -- an idempotent `s` of `S`; both `s` and `1 - s` would lie in `Q`.
  by_contra hne
  obtain ⟨e, he₂, hidem, hall⟩ := IsArtinianRing.exists_notMem_forall_mem_of_ne P₂
  have he₁ : e ∈ P₁ := hall P₁ inferInstance hne
  have : Nontrivial S := nontrivial_of_ne 0 1 fun h ↦
    ‹Q.IsPrime›.ne_top ((Ideal.eq_top_iff_one Q).mpr (h ▸ Q.zero_mem))
  have hint : IsIntegral S e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; decide)
    · simp [pow_two, hidem.eq]
  obtain ⟨s, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  have hs₁ : s ∈ Q := h₁ he₁
  have hzero : algebraMap S (S ⊗[R] FractionRing R) s *
      algebraMap S (S ⊗[R] FractionRing R) (1 - s) = 0 := by
    rw [map_sub, map_one, mul_sub, mul_one, hidem.eq, sub_self]
  have hcompl : algebraMap S (S ⊗[R] FractionRing R) (1 - s) ∈ P₂ :=
    (‹P₂.IsPrime›.mem_or_mem (hzero ▸ P₂.zero_mem)).resolve_left he₂
  have hs₂ : 1 - s ∈ Q := h₂ hcompl
  exact ‹Q.IsPrime›.ne_top ((Ideal.eq_top_iff_one Q).mpr (by simpa using Q.add_mem hs₁ hs₂))

variable (R) in
include R in
/-- The localization at `S \ Q` of the generic fibre of an étale algebra over an integrally closed
domain is a field as soon as it is nonzero. -/
private theorem isField_localization_tensorProduct (Q : Ideal S) [Q.IsPrime]
    (Lq : Type*) [CommRing Lq] [_root_.Algebra (S ⊗[R] FractionRing R) Lq]
    [IsLocalization (_root_.Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq]
    [Nontrivial Lq] : IsField Lq := by
  have : IsArtinianRing Lq := IsArtinianRing.localization_artinian
    (_root_.Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq
  -- `isReduced_localizationPreserves` requires `Lq` in the universe of the ring it localizes, so
  -- transport Mathlib's instance for `Localization` along the canonical isomorphism instead.
  have : IsReduced Lq := by
    let e := IsLocalization.algEquiv
      (_root_.Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq
      (Localization (_root_.Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl))
    exact isReduced_of_injective e.toRingHom e.injective
  have hcomap : ∀ m : Ideal Lq, m.IsMaximal →
      (m.under (S ⊗[R] FractionRing R)).under S ≤ Q := by
    intro m hm s hs
    by_contra hsQ
    have hunit : IsUnit (algebraMap (S ⊗[R] FractionRing R) Lq
        (algebraMap S (S ⊗[R] FractionRing R) s)) :=
      IsLocalization.map_units Lq (⟨algebraMap S (S ⊗[R] FractionRing R) s,
        _root_.Algebra.mem_algebraMapSubmonoid_of_mem (⟨s, hsQ⟩ : Q.primeCompl)⟩ :
          _root_.Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl)
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hs hunit)
  have : IsLocalRing Lq := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal Lq
    refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun m' hm' ↦ ?_⟩
    have := hm.isPrime
    have := hm'.isPrime
    have heq : m'.under (S ⊗[R] FractionRing R) = m.under (S ⊗[R] FractionRing R) :=
      eq_of_comap_le Q _ _ (hcomap m' hm') (hcomap m hm)
    rw [← IsLocalization.map_under
        (_root_.Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq m', heq,
      IsLocalization.map_under
        (_root_.Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq m]
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing Lq

variable (R) in
include R in
/-- The local rings of an étale algebra over an integrally closed domain are integrally closed
domains, as a conjunction. -/
private theorem isDomain_and_isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed
    (Q : Ideal S) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  let M := _root_.Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl
  have hclq : IsIntegrallyClosedIn (Localization.AtPrime Q) (Localization M) :=
    IsLocalization.isIntegrallyClosedIn (R := S) (S := S ⊗[R] FractionRing R) Q.primeCompl
  have hinj := (isIntegrallyClosedIn_iff.mp hclq).1
  have : Nontrivial (Localization M) := hinj.nontrivial
  let : Field (Localization M) := (isField_localization_tensorProduct R Q _).toField
  have : FaithfulSMul (Localization.AtPrime Q) (Localization M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact ⟨hinj.isDomain _, IsIntegrallyClosed.of_isIntegrallyClosedIn _ (Localization M)⟩

variable (R) in
include R in
/-- **The local rings of an étale algebra over an integrally closed domain are domains.** The étale
case of Stacks, Lemma 10.163.9 (033C), at one prime. -/
@[stacks 033C "étale case, over an integrally closed domain, at one prime"]
theorem isDomain_localization_atPrime_of_isIntegrallyClosed (Q : Ideal S) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) :=
  (isDomain_and_isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed R Q).1

variable (R) in
include R in
/-- **The local rings of an étale algebra over an integrally closed domain are integrally
closed.** The étale case of Stacks, Lemma 10.163.9 (033C), at one prime. -/
@[stacks 033C "étale case, over an integrally closed domain, at one prime"]
theorem isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed (Q : Ideal S) [Q.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime Q) :=
  (isDomain_and_isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed R Q).2

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
  obtain ⟨hdom, hic⟩ :=
    isDomain_and_isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed Ap P
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
    obtain ⟨hdom, hic⟩ :=
      Etale.isDomain_and_isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed A q
    exact ⟨e.toMulEquiv.isDomain _,
      IsIntegrallyClosed.of_equiv (R := Localization.AtPrime q) e.symm.toRingEquiv⟩
  · rintro ⟨hB, hBc⟩
    have : IsLocalRing B := e.toRingEquiv.symm.isLocalRing
    have : Module.Flat A B := Module.Flat.of_linearEquiv e.toLinearEquiv
    have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact ⟨IsDomain.of_faithfulSMul A B, IsIntegrallyClosed.of_faithfullyFlat A B⟩

end Algebra

end TauCeti
