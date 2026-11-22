/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.AlgHom

import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Ideal.Operations

/-!
# Adic completion along pairwise coprime ideals

For a finite pairwise coprime family `I : ι → Ideal R` in a commutative ring `R`,
`(⨅ i, I i) ^ n = ⨅ i, I i ^ n` (`Ideal.iInf_pow_eq_iInf_of_pairwise_isCoprime`). Applying the
Chinese remainder theorem (`Ideal.quotientInfRingEquivPiQuotient`) at each level `n` identifies
`AdicCompletion (⨅ i, I i) R` as an `R`-algebra with `∀ i, AdicCompletion (I i) R` without
Noetherian or finite-generation hypotheses (including empty index types and unit ideals).

## Main definitions and results

* `AdicCompletion.coprimeEquiv`: `AdicCompletion (⨅ i, I i) R ≃ₐ[R] ∀ i, AdicCompletion (I i) R`,
  with `AdicCompletion.coprimeEquiv_apply` and `AdicCompletion.coprimeEquiv_of`.
* `AdicCompletion.pi_mapₐ_id_bijective_of_pairwise_isCoprime`: bijectivity of the product map into
  `∀ i, AdicCompletion (I i) R`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, no. 13, Proposition 18.
* H. Matsumura, *Commutative Ring Theory*, Theorem 8.15.
-/

public section

open Function

namespace AdicCompletion

variable {R : Type*} [CommRing R] {ι : Type*} (I : ι → Ideal R)

private noncomputable def coprimeQuotEquiv [Finite ι] (hI : Pairwise (IsCoprime on I)) (n : ℕ) :
    (R ⧸ (⨅ i, I i) ^ n) ≃+* ∀ i, R ⧸ I i ^ n :=
  (Ideal.quotientEquivAlgOfEq R
      (Ideal.iInf_pow_eq_iInf_of_pairwise_isCoprime I hI n)).toRingEquiv.trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i ↦ I i ^ n) fun _ _ hij ↦ (hI hij).pow)

private theorem coprimeQuotEquiv_mk_apply [Finite ι] (hI : Pairwise (IsCoprime on I)) (n : ℕ)
    (r : R) (i : ι) :
    coprimeQuotEquiv I hI n (Ideal.Quotient.mk ((⨅ j, I j) ^ n) r) i =
      Ideal.Quotient.mk (I i ^ n) r := by
  simp only [coprimeQuotEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
    Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientInfRingEquivPiQuotient_mk_apply _ r i

private noncomputable def piEvalRingHom (n : ℕ) :
    (∀ i, AdicCompletion (I i) R) →+* ∀ i, R ⧸ I i ^ n :=
  RingHom.pi fun i ↦ (evalₐ (I i) n).toRingHom.comp (Pi.evalRingHom _ i)

private theorem piEvalRingHom_apply (n : ℕ) (z : ∀ i, AdicCompletion (I i) R) (i : ι) :
    piEvalRingHom I n z i = evalₐ (I i) n (z i) := rfl

private theorem exists_mk_coprimeQuotEquiv_symm [Finite ι] (hI : Pairwise (IsCoprime on I)) (n : ℕ)
    (z : ∀ i, AdicCompletion (I i) R) :
    ∃ r : R, Ideal.Quotient.mk ((⨅ j, I j) ^ n) r =
        (coprimeQuotEquiv I hI n).symm (piEvalRingHom I n z) ∧
      ∀ i, Ideal.Quotient.mk (I i ^ n) r = evalₐ (I i) n (z i) := by
  obtain ⟨r, hr⟩ :=
    Ideal.Quotient.mk_surjective ((coprimeQuotEquiv I hI n).symm (piEvalRingHom I n z))
  refine ⟨r, hr, fun i ↦ ?_⟩
  simpa [coprimeQuotEquiv_mk_apply, piEvalRingHom_apply] using
    congr_fun (congrArg (⇑(coprimeQuotEquiv I hI n)) hr) i

private theorem coprimeInv_aux [Finite ι] (hI : Pairwise (IsCoprime on I)) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (⨅ i, I i) hmn).comp
        ((coprimeQuotEquiv I hI n).symm.toRingHom.comp (piEvalRingHom I n)) =
      (coprimeQuotEquiv I hI m).symm.toRingHom.comp (piEvalRingHom I m) := by
  ext z; refine (coprimeQuotEquiv I hI m).injective <| funext fun i ↦ ?_
  obtain ⟨r, hr, hri⟩ := exists_mk_coprimeQuotEquiv_symm I hI n z
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply, piEvalRingHom_apply, ← hr, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, coprimeQuotEquiv_mk_apply, ← factor_evalₐ hmn (z i), ← hri]

private noncomputable def coprimeInv [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    (∀ i, AdicCompletion (I i) R) →ₐ[R] AdicCompletion (⨅ i, I i) R :=
  let g := liftRingHom (⨅ i, I i)
    (fun n ↦ (coprimeQuotEquiv I hI n).symm.toRingHom.comp (piEvalRingHom I n))
    (coprimeInv_aux I hI)
  { g with
    toFun := g
    commutes' := fun r ↦ ext_evalₐ fun n ↦ (coprimeQuotEquiv I hI n).injective <| funext fun i ↦ by
      rw [evalₐ_liftRingHom (⨅ i, I i) _ (coprimeInv_aux I hI) n]
      simp [coprimeQuotEquiv_mk_apply, piEvalRingHom_apply, algebraMap_apply] }

private theorem evalₐ_coprimeInv [Finite ι] (hI : Pairwise (IsCoprime on I)) (n : ℕ)
    (z : ∀ i, AdicCompletion (I i) R) :
    evalₐ (⨅ i, I i) n (coprimeInv I hI z) = (coprimeQuotEquiv I hI n).symm (piEvalRingHom I n z) :=
  evalₐ_liftRingHom (⨅ i, I i) _ (coprimeInv_aux I hI) n z

private theorem coprimeFwd_comp_coprimeInv [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    (AlgHom.pi fun i ↦ mapₐ (AlgHom.id R R)
      (fun _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx))).comp (coprimeInv I hI) =
      AlgHom.id R (∀ i, AdicCompletion (I i) R) :=
  AlgHom.ext fun z ↦ funext fun i ↦ ext_evalₐ fun n ↦ by
    obtain ⟨r, hr, hri⟩ := exists_mk_coprimeQuotEquiv_symm I hI n z
    simp [evalₐ_coprimeInv, ← hr, hri]

private theorem coprimeInv_comp_coprimeFwd [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    (coprimeInv I hI).comp
      (AlgHom.pi fun i ↦ mapₐ (AlgHom.id R R) (fun _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx))) =
      AlgHom.id R (AdicCompletion (⨅ i, I i) R) :=
  AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ (coprimeQuotEquiv I hI n).injective <| funext fun i ↦ by
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ (⨅ j, I j) n x)
    simp [evalₐ_coprimeInv, piEvalRingHom_apply, ← hr, coprimeQuotEquiv_mk_apply]

/-- Completing a commutative ring along the intersection of finitely many pairwise coprime ideals
gives the product of the individual completions as an `R`-algebra. -/
noncomputable def coprimeEquiv [Finite ι] (hI : Pairwise (IsCoprime on I)) :
    AdicCompletion (⨅ i, I i) R ≃ₐ[R] ∀ i, AdicCompletion (I i) R :=
  AlgEquiv.ofAlgHom
    (AlgHom.pi fun i ↦ mapₐ (AlgHom.id R R) (fun _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx)))
    (coprimeInv I hI) (coprimeFwd_comp_coprimeInv I hI) (coprimeInv_comp_coprimeFwd I hI)

/-- Each coordinate of `coprimeEquiv` is the functorial map induced by `(⨅ j, I j) ≤ I i`. -/
@[simp] theorem coprimeEquiv_apply [Finite ι] (hI : Pairwise (IsCoprime on I))
    (x : AdicCompletion (⨅ i, I i) R) (i : ι) :
    coprimeEquiv I hI x i =
      mapₐ (AlgHom.id R R) (fun _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx)) x := by
  rw [coprimeEquiv, AlgEquiv.ofAlgHom_apply, AlgHom.pi_apply]

/-- `coprimeEquiv` sends `of _ R r` to the constant tuple `fun i ↦ of (I i) R r`. -/
theorem coprimeEquiv_of [Finite ι] (hI : Pairwise (IsCoprime on I)) (r : R) (i : ι) :
    coprimeEquiv I hI (of (⨅ j, I j) R r) i = of (I i) R r := by simp

/-- The product of the natural projections
`AdicCompletion (⨅ j, I j) R →ₐ[A] AdicCompletion (I i) R` is bijective for any scalar ring `A`
when `I` is a finite pairwise coprime family of ideals. -/
theorem pi_mapₐ_id_bijective_of_pairwise_isCoprime {A : Type*} [CommRing A] [Algebra A R]
    [Finite ι] (hI : Pairwise (IsCoprime on I))
    (hle : ∀ i, (⨅ j, I j) ≤ (I i).comap (AlgHom.id A R) :=
      fun i _ hx ↦ Ideal.mem_comap.mpr (iInf_le I i hx)) :
    Function.Bijective (AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (hle i)) := by
  have hcoe : ⇑(AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (hle i)) = ⇑(coprimeEquiv I hI) :=
    funext fun x ↦ funext fun i ↦ by
      rw [AlgHom.pi_apply, coprimeEquiv_apply]; apply mapₐ_congr; intro; rfl
  exact hcoe ▸ (coprimeEquiv I hI).bijective

end AdicCompletion
