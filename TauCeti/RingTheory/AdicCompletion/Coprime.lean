/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.AlgHom

import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Adic completion along pairwise coprime ideals

For a finite family `I : ι → Ideal R` of pairwise coprime ideals in a commutative ring `R`, the
powers `I i ^ n` remain pairwise coprime and satisfy `(⨅ i, I i) ^ n = ⨅ i, I i ^ n`. Applying the
Chinese remainder theorem (`Ideal.quotientInfRingEquivPiQuotient`) at each level `n` and passing to
the inverse limit identifies `AdicCompletion (⨅ i, I i) R` as an `R`-algebra with the product
`∀ i, AdicCompletion (I i) R`, whose `i`-th coordinate is the functorial map induced by the
inclusion `(⨅ j, I j) ≤ I i`.

Neither Noetherianity nor finite generation of the ideals is required; the empty index type and unit
ideals are included. Compare `TauCeti.Henselization.coprimeEquiv` for the analogous decomposition
of henselizations.

## Main definitions and results

* `AdicCompletion.coprimeEquiv`: the canonical `R`-algebra isomorphism
  `AdicCompletion (⨅ i, I i) R ≃ₐ[R] ∀ i, AdicCompletion (I i) R`.
* `AdicCompletion.coprimeEquiv_apply` and `AdicCompletion.coprimeEquiv_of`: coordinate and
  compatibility lemmas for `AdicCompletion.coprimeEquiv`.
* `AdicCompletion.bijective_pi_mapₐ`: bijectivity of the product map into
  `∀ i, AdicCompletion (I i) R`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, no. 13, Proposition 18.
* H. Matsumura, *Commutative Ring Theory*, Theorem 8.15.
-/

public section

open Function

namespace AdicCompletion

variable {R : Type*} [CommRing R] {ι : Type*} (I : ι → Ideal R)

private theorem iInf_pow_eq_iInf [Finite ι] (hI : Pairwise (IsCoprime on I)) (n : ℕ) :
    (⨅ i, I i) ^ n = ⨅ i, I i ^ n := by
  cases nonempty_fintype ι
  have huniv : (⨅ i, I i) = ∏ i : ι, I i := by
    simpa using (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      fun i _ j _ hij ↦ hI hij).symm
  have hpow : (⨅ i, I i ^ n) = ∏ i : ι, I i ^ n := by
    simpa using (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      fun i _ j _ hij ↦ (hI hij).pow).symm
  rw [huniv, hpow, Finset.prod_pow]

private noncomputable def coprimeQuotEquiv [Finite ι] (hI : Pairwise (IsCoprime on I)) (n : ℕ) :
    (R ⧸ (⨅ i, I i) ^ n) ≃+* ∀ i, R ⧸ I i ^ n :=
  (Ideal.quotientEquivAlgOfEq R (iInf_pow_eq_iInf I hI n)).toRingEquiv.trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i ↦ I i ^ n) fun _ _ hij ↦ (hI hij).pow)

private theorem coprimeQuotEquiv_mk_apply [Finite ι] (hI : Pairwise (IsCoprime on I)) (n : ℕ)
    (r : R) (i : ι) :
    coprimeQuotEquiv I hI n (Ideal.Quotient.mk ((⨅ j, I j) ^ n) r) i =
      Ideal.Quotient.mk (I i ^ n) r :=
  rfl

private noncomputable def piEvalRingHom (n : ℕ) :
    (∀ i, AdicCompletion (I i) R) →+* ∀ i, R ⧸ I i ^ n :=
  RingHom.pi fun i ↦ (evalₐ (I i) n).toRingHom.comp (Pi.evalRingHom _ i)

private theorem piEvalRingHom_apply (n : ℕ) (z : ∀ i, AdicCompletion (I i) R) (i : ι) :
    piEvalRingHom I n z i = evalₐ (I i) n (z i) :=
  rfl

private theorem coprimeInv_aux [Finite ι] (hI : Pairwise (IsCoprime on I)) {m n : ℕ}
    (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (⨅ i, I i) hmn).comp
        ((coprimeQuotEquiv I hI n).symm.toRingHom.comp (piEvalRingHom I n)) =
      (coprimeQuotEquiv I hI m).symm.toRingHom.comp (piEvalRingHom I m) := by
  ext z
  apply (coprimeQuotEquiv I hI m).injective
  funext i
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply, piEvalRingHom_apply]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    ((coprimeQuotEquiv I hI n).symm (piEvalRingHom I n z))
  have hri : Ideal.Quotient.mk (I i ^ n) r = evalₐ (I i) n (z i) := by
    have h := congrFun (congrArg (coprimeQuotEquiv I hI n) hr) i
    simpa only [RingEquiv.apply_symm_apply, coprimeQuotEquiv_mk_apply, piEvalRingHom_apply] using h
  rw [← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, coprimeQuotEquiv_mk_apply,
    ← factor_evalₐ hmn (z i), ← hri, Ideal.Quotient.factor_mk]

private noncomputable def coprimeInv [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    (∀ i, AdicCompletion (I i) R) →ₐ[R] AdicCompletion (⨅ i, I i) R :=
  let g := liftRingHom (⨅ i, I i)
    (fun n ↦ (coprimeQuotEquiv I hI n).symm.toRingHom.comp (piEvalRingHom I n))
    (coprimeInv_aux I hI)
  { g with
    toFun := g
    commutes' := fun r ↦ ext_evalₐ fun n ↦ by
      have heval : evalₐ (⨅ i, I i) n (g (algebraMap R (∀ i, AdicCompletion (I i) R) r)) =
          (coprimeQuotEquiv I hI n).symm
            (piEvalRingHom I n (algebraMap R (∀ i, AdicCompletion (I i) R) r)) :=
        evalₐ_liftRingHom (⨅ i, I i) _ (coprimeInv_aux I hI) n _
      rw [heval, algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalₐ_of]
      apply (coprimeQuotEquiv I hI n).injective
      funext i
      simp [coprimeQuotEquiv_mk_apply, piEvalRingHom_apply, algebraMap_apply] }

private theorem evalₐ_coprimeInv [Finite ι] (hI : Pairwise (IsCoprime on I)) (n : ℕ)
    (z : ∀ i, AdicCompletion (I i) R) :
    evalₐ (⨅ i, I i) n (coprimeInv I hI z) =
      (coprimeQuotEquiv I hI n).symm (piEvalRingHom I n z) :=
  evalₐ_liftRingHom (⨅ i, I i) _ (coprimeInv_aux I hI) n z

private theorem coprimeFwd_comp_coprimeInv [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    (AlgHom.pi fun i ↦
      mapₐ (AlgHom.id R R) (fun _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx))).comp
      (coprimeInv I hI) = AlgHom.id R (∀ i, AdicCompletion (I i) R) := by
  refine AlgHom.ext fun z ↦ funext fun i ↦ ext_evalₐ fun n ↦ ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.pi_apply, evalₐ_mapₐ, evalₐ_coprimeInv]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    ((coprimeQuotEquiv I hI n).symm (piEvalRingHom I n z))
  have hri : Ideal.Quotient.mk (I i ^ n) r = evalₐ (I i) n (z i) := by
    have h := congrFun (congrArg (coprimeQuotEquiv I hI n) hr) i
    simpa only [RingEquiv.apply_symm_apply, coprimeQuotEquiv_mk_apply, piEvalRingHom_apply] using h
  rw [← hr, Ideal.quotientMap_mk, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom,
    RingHom.id_apply, hri]

private theorem coprimeInv_comp_coprimeFwd [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    (coprimeInv I hI).comp
      (AlgHom.pi fun i ↦
        mapₐ (AlgHom.id R R) (fun _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx))) =
      AlgHom.id R (AdicCompletion (⨅ i, I i) R) := by
  refine AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply, evalₐ_coprimeInv]
  apply (coprimeQuotEquiv I hI n).injective
  funext i
  rw [RingEquiv.apply_symm_apply, piEvalRingHom_apply, AlgHom.pi_apply, evalₐ_mapₐ]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ (⨅ j, I j) n x)
  rw [← hr, coprimeQuotEquiv_mk_apply, Ideal.quotientMap_mk, AlgHom.toRingHom_eq_coe,
    AlgHom.id_toRingHom, RingHom.id_apply]

/-- Completing a commutative ring along the intersection of finitely many pairwise coprime ideals
gives the product of the individual completions as an `R`-algebra. Neither Noetherianity nor finite
generation is required; the empty family and unit ideals are allowed. -/
noncomputable def coprimeEquiv [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    AdicCompletion (⨅ i, I i) R ≃ₐ[R] ∀ i, AdicCompletion (I i) R :=
  AlgEquiv.ofAlgHom
    (AlgHom.pi fun i ↦
      mapₐ (AlgHom.id R R) (fun _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx)))
    (coprimeInv I hI)
    (coprimeFwd_comp_coprimeInv I hI)
    (coprimeInv_comp_coprimeFwd I hI)

/-- Each coordinate of `coprimeEquiv` is the functorial map induced by `(⨅ j, I j) ≤ I i`. -/
@[simp]
theorem coprimeEquiv_apply [Finite ι] (hI : Pairwise (IsCoprime on I))
    (x : AdicCompletion (⨅ i, I i) R) (i : ι) :
    coprimeEquiv I hI x i =
      mapₐ (AlgHom.id R R) (fun _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx)) x := by
  rw [coprimeEquiv, AlgEquiv.ofAlgHom_apply, AlgHom.pi_apply]

/-- `coprimeEquiv` sends `of _ R r` to the constant tuple `fun i ↦ of (I i) R r`. -/
theorem coprimeEquiv_of [Finite ι] (hI : Pairwise (IsCoprime on I)) (r : R) (i : ι) :
    coprimeEquiv I hI (of (⨅ j, I j) R r) i = of (I i) R r := by
  simp

/-- The product of the natural projections
`AdicCompletion (⨅ j, I j) R →ₐ[A] AdicCompletion (I i) R` is bijective for any scalar ring `A`
when `I` is a finite pairwise coprime family of ideals. -/
theorem bijective_pi_mapₐ {A : Type*} [CommRing A] [Algebra A R] [Finite ι]
    (hI : Pairwise (IsCoprime on I))
    (hle : ∀ i, (⨅ j, I j) ≤ (I i).comap (AlgHom.id A R) :=
      fun i _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx)) :
    Function.Bijective (AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (hle i)) := by
  have hcoe : ⇑(AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (hle i)) = ⇑(coprimeEquiv I hI) := by
    funext x i
    rw [AlgHom.pi_apply, coprimeEquiv_apply]
    refine ext_evalₐ fun n ↦ ?_
    rw [evalₐ_mapₐ, evalₐ_mapₐ]
    rfl
  exact hcoe ▸ (coprimeEquiv I hI).bijective

end AdicCompletion
