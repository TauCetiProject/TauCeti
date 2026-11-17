/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import TauCeti.RingTheory.Etale.Normal
public import TauCeti.RingTheory.Localization.LocalizationLocalization
public import TauCeti.RingTheory.MvPolynomial.IntegrallyClosed

/-!
# Normal rings: localization, polynomial rings and étale base change

A ring `R` is *normal* when its localization at every prime is an integrally closed domain
(Stacks, Definition 10.37.11 (00GV)); this is the condition
`∀ p [p.IsPrime], IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`,
which `TauCeti.AlgebraicGeometry.isNormalScheme_Spec_iff_forall_localization` identifies with the
normality of `Spec R`. This file shows that normality is preserved by isomorphisms, by
localization, by polynomial rings in any set of variables and by étale algebras, and deduces that
for a finite separable field extension `K / k` and a normal `k`-algebra `B`, the ring `K ⊗[k] B` is
normal. No Noetherian hypothesis is made anywhere.

The last statement is the case of a finite separable extension in the proof that `K ⊗[k] B` is
normal for every separable extension `K / k` (Stacks, Lemma 10.165.5 (06DF) with `A = K`); the
polynomial and localization statements are the other two steps of that proof, which writes a
finitely generated separable extension as a finite separable extension of a rational function
field `k(t_1, …, t_n)`, and `k(t_1, …, t_n) ⊗[k] B` as a localization of `B[t_1, …, t_n]`.

## Main results

* `TauCeti.forall_isDomain_and_isIntegrallyClosed_of_ringEquiv`: normality is invariant under
  ring isomorphisms.
* `TauCeti.forall_isDomain_and_isIntegrallyClosed_of_isLocalization`: a localization of a normal
  ring is normal (Stacks, Lemma 10.37.13 (030B)).
* `TauCeti.MvPolynomial.forall_isDomain_and_isIntegrallyClosed`: a polynomial ring in any set of
  variables over a normal ring is normal (Stacks, Lemma 10.37.8 (030A)).
* `TauCeti.Algebra.Etale.forall_isDomain_and_isIntegrallyClosed`: an étale algebra over a normal
  ring is normal (Stacks, Lemma 10.163.9 (033C)).
* `TauCeti.forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_etale`: for an étale
  `A`-algebra `S` and an `A`-algebra `B` that is a normal ring, `S ⊗[A] B` is normal.
* `TauCeti.forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_isSeparable`: for a
  finite separable field extension `K / k` and a `k`-algebra `B` that is a normal ring,
  `K ⊗[k] B` is normal (the finite case of Stacks, Lemma 10.165.5 (06DF)).

## References

* [Stacks Project, Definition 10.37.11](https://stacks.math.columbia.edu/tag/00GV),
  [Lemma 10.37.8](https://stacks.math.columbia.edu/tag/030A),
  [Lemma 10.37.13](https://stacks.math.columbia.edu/tag/030B),
  [Lemma 10.163.9](https://stacks.math.columbia.edu/tag/033C) and
  [Lemma 10.165.5](https://stacks.math.columbia.edu/tag/06DF).
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- **Normality is invariant under ring isomorphisms.** If every localization of `R` at a prime is
an integrally closed domain and `R ≃+* S`, then so is every localization of `S` at a prime. -/
theorem forall_isDomain_and_isIntegrallyClosed_of_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] (e : R ≃+* S)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let := e.toRingHom.toAlgebra
  have : _root_.Algebra.Etale R S :=
    _root_.Algebra.Etale.of_equiv (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl)
  obtain ⟨_, _⟩ := hR (q.under R)
  exact ⟨Algebra.Etale.isDomain_localization_atPrime_of_localization_under R q,
    Algebra.Etale.isIntegrallyClosed_localization_atPrime_of_localization_under R q⟩

/-- **A localization of a normal ring is normal.** If every localization of `R` at a prime is an
integrally closed domain, then so is every localization at a prime of a localization `S` of `R`:
it is a localization of `R` at a prime. Stacks, Lemma 10.37.13 (030B). -/
@[stacks 030B]
theorem forall_isDomain_and_isIntegrallyClosed_of_isLocalization {R : Type*} [CommRing R]
    (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime q) q
  let e : Localization.AtPrime (q.under R) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv (q.under R).primeCompl _ (Localization.AtPrime q)).toRingEquiv
  obtain ⟨_, _⟩ := hR (q.under R)
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

namespace MvPolynomial

open _root_.MvPolynomial

attribute [local instance] algebraMvPolynomial in
/-- **A polynomial ring over a normal ring is normal.** If every localization of `R` at a prime is
an integrally closed domain, then so is every localization at a prime of the polynomial ring
`MvPolynomial σ R`, in any set of variables. For a prime `Q` over `q`, the local ring at `Q` is a
localization at a prime of `MvPolynomial σ R_q`, an integrally closed domain. Stacks, Lemma 10.37.8
(030A), for any number of variables. -/
@[stacks 030A "any number of variables"]
theorem forall_isDomain_and_isIntegrallyClosed {σ R : Type*} [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (Q : Ideal (MvPolynomial σ R)) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  let q := Q.under R
  obtain ⟨_, _⟩ := hR q
  let M := q.primeCompl.map (C : R →+* MvPolynomial σ R)
  -- `MvPolynomial σ R_q` is the localization of `MvPolynomial σ R` at `M`, which misses `Q`.
  have hM : Disjoint (M : Set (MvPolynomial σ R)) Q := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ haQ
    exact ha haQ
  obtain ⟨P, _, -, ⟨e⟩⟩ := IsLocalization.exists_ringEquiv_localization_atPrime M
    (MvPolynomial σ (Localization.AtPrime q)) Q hM
  have : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  have : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ _ P.primeCompl_le_nonZeroDivisors
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv (R := Localization.AtPrime P) e.symm⟩

end MvPolynomial

namespace Algebra

namespace Etale

/-- **An étale algebra over a normal ring is normal.** If `A → S` is étale and every localization
of `A` at a prime is an integrally closed domain, then so is every localization of `S` at a prime.
Stacks, Lemma 10.163.9 (033C), étale case. -/
@[stacks 033C "étale case"]
theorem forall_isDomain_and_isIntegrallyClosed {A S : Type*} [CommRing A] [CommRing S]
    [_root_.Algebra A S] [_root_.Algebra.Etale A S]
    (hA : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨_, _⟩ := hA (q.under A)
  exact ⟨isDomain_localization_atPrime_of_localization_under A q,
    isIntegrallyClosed_localization_atPrime_of_localization_under A q⟩

end Etale

end Algebra

/-- **Étale base change preserves normality.** If `S` is an étale `A`-algebra and `B` is an
`A`-algebra whose localizations at primes are integrally closed domains, then so are the
localizations at primes of `S ⊗[A] B`, which is étale over `B`. -/
theorem forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_etale {A S B : Type*} [CommRing A]
    [CommRing S] [CommRing B] [_root_.Algebra A S] [_root_.Algebra A B]
    [_root_.Algebra.Etale A S]
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal (S ⊗[A] B)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  forall_isDomain_and_isIntegrallyClosed_of_ringEquiv
    (_root_.Algebra.TensorProduct.comm A B S).toRingEquiv
    (Algebra.Etale.forall_isDomain_and_isIntegrallyClosed (A := B) hB) q

/-- **Finite separable base change of the ground field preserves normality.** For a finite
separable field extension `K / k` and a `k`-algebra `B` whose localizations at primes are
integrally closed domains, the localizations at primes of `K ⊗[k] B` are integrally closed
domains. `K` is étale over `k`, so this is a case of
`TauCeti.forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_etale`. Stacks,
Lemma 10.165.5 (06DF), for `A = K` finite separable over `k`. -/
@[stacks 06DF "`A` a finite separable field extension"]
theorem forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_isSeparable {k K B : Type*}
    [Field k] [Field K] [CommRing B] [_root_.Algebra k K] [_root_.Algebra k B]
    [FiniteDimensional k K] [_root_.Algebra.IsSeparable k K]
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal (K ⊗[k] B)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  have : _root_.Algebra.Etale k K :=
    { formallyEtale := .of_isSeparable k K
      finitePresentation := (_root_.Algebra.FinitePresentation.of_finiteType).mp inferInstance }
  forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_etale hB q

end TauCeti
