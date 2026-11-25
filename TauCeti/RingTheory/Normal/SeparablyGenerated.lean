/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import TauCeti.RingTheory.AlgebraicIndependent.BaseChange
import TauCeti.RingTheory.Etale.Normal
import TauCeti.RingTheory.Localization.Normal
import TauCeti.RingTheory.MvPolynomial.IntegrallyClosed

/-!
# Normality under a finitely generated separable extension of the ground field

A ring is *normal* when its localization at every prime is an integrally closed domain (Stacks,
Definition 10.37.11 (00GV)). Let `k` be a field, `K / k` a finitely generated separably
generated field extension, and `B` a `k`-algebra that is a normal ring. Then `K ⊗[k] B` is a
normal ring.

Choose a transcendence basis `s` of `K / k` such that `K` is separable over `E = k(s)`. The ring
`k[s] ⊗[k] B` is the polynomial ring `B[s]`, which is normal; `E ⊗[k] B` is its localization at
the nonzero polynomials of `k[s]`, so it is normal; and `K` is finite separable, hence étale,
over `E`, so `K ⊗[k] B ≅ K ⊗[E] (E ⊗[k] B)` is étale over `E ⊗[k] B` and normal.

## Main results

* `TauCeti.forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_isSeparablyGenerated`: for a
  finitely generated separably generated field extension `K / k` and a `k`-algebra `B` that is a
  normal ring, `K ⊗[k] B` is a normal ring. This is Stacks, Lemma 10.165.5 (06DF), for `A = K`
  finitely generated over `k`.

## References

* [Stacks Project, Definition 10.37.11](https://stacks.math.columbia.edu/tag/00GV) and
  [Lemma 10.165.5](https://stacks.math.columbia.edu/tag/06DF).
-/

public section

open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin

namespace TauCeti

/-- **Separably generated base change of the ground field preserves normality.** Let `K / k` be
a finitely generated field extension that is separably generated, and `B` a `k`-algebra whose
localizations at primes are integrally closed domains. Then the localizations at primes of
`K ⊗[k] B` are integrally closed domains. Stacks, Lemma 10.165.5 (06DF), for `A = K` finitely
generated over `k`. -/
@[stacks 06DF "`A` a finitely generated separably generated field extension"]
theorem forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_isSeparablyGenerated
    {k K B : Type*} [Field k] [Field K] [CommRing B] [Algebra k K] [Algebra k B]
    [Algebra.EssFiniteType k K] [Algebra.IsSeparablyGenerated k K]
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal (K ⊗[k] B)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨s, hs, hsep⟩ := Algebra.IsSeparablyGenerated.isSeparable (k := k) (K := K)
  set R := Algebra.adjoin k s
  set E := IntermediateField.adjoin k s
  -- `R ⊗[k] B` is the polynomial ring `B[s]`, a normal ring.
  have hRB := (hs.1.adjoinTensorAlgEquiv B).symm.toRingEquiv.forall_isDomain_and_isIntegrallyClosed
    (TauCeti.MvPolynomial.forall_isDomain_and_isIntegrallyClosed hB)
  -- `E ⊗[k] B` is a localization of `R ⊗[k] B`, so it is normal.
  have hEB := forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalization
    (nonZeroDivisors R) E hRB
  -- `K` is finite separable, hence étale, over `E`.
  have : Algebra.EssFiniteType E K := .of_comp k E K
  have : Module.Finite E K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : Algebra.Etale E K := Algebra.Etale.of_isSeparable E K
  -- `K ⊗[k] B ≅ K ⊗[E] (E ⊗[k] B)` is étale over the normal ring `E ⊗[k] B`.
  exact RingEquiv.forall_isDomain_and_isIntegrallyClosed
    (Algebra.TensorProduct.cancelBaseChange k E K K B).toRingEquiv
    (forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_etale hEB) q

end TauCeti
