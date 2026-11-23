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
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
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

* `TauCeti.forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalization`: if `C` is a
  localization of the `k`-algebra `A` and `A ⊗[k] B` is a normal ring, then so is `C ⊗[k] B`.
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

/-- **Localization of the first factor preserves normality of a tensor product.** Let `C` be a
localization of the `k`-algebra `A` at `M`. If the localizations at primes of `A ⊗[k] B` are
integrally closed domains, then so are those of `C ⊗[k] B`, which is the localization of
`A ⊗[k] B` at the image of `M`. -/
theorem forall_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalization {k A B : Type*}
    [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] (M : Submonoid A)
    (C : Type*) [CommRing C] [Algebra k C] [Algebra A C] [IsScalarTower k A C]
    [IsLocalization M C]
    (h : ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal (C ⊗[k] B)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let φ : A ⊗[k] B →ₐ[k] C ⊗[k] B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A C) (AlgHom.id k B)
  algebraize [φ.toRingHom]
  have : IsScalarTower A (A ⊗[k] B) (C ⊗[k] B) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, φ]
  have := IsLocalization.tensorProduct_tensorProduct k B M C
    (by ext; simp [RingHom.algebraMap_toAlgebra, φ])
  exact IsLocalization.forall_isDomain_and_isIntegrallyClosed
    (Algebra.algebraMapSubmonoid (A ⊗[k] B) M) (C ⊗[k] B) h q

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
  let eR : MvPolynomial s k ≃ₐ[k] R :=
    hs.1.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (congrArg (Algebra.adjoin k) Subtype.range_coe))
  let eRB : MvPolynomial s B ≃+* R ⊗[k] B :=
    ((MvPolynomial.algebraTensorAlgEquiv k B).toRingEquiv.symm.trans
      (Algebra.TensorProduct.comm k B (MvPolynomial s k)).toRingEquiv).trans
      (Algebra.TensorProduct.congr eR (AlgEquiv.refl : B ≃ₐ[k] B)).toRingEquiv
  have hRB := eRB.forall_isDomain_and_isIntegrallyClosed
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
