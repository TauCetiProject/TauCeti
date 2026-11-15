/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import TauCeti.RingTheory.TensorProduct.Reduced
import Mathlib.RingTheory.LocalProperties.Reduced
import TauCeti.RingTheory.LocalRing.Localization

/-!
# Ramification index under localization and field pushouts

This file relates `Ideal.ramificationIdx` at a prime to the local ring at that prime, proves that
primes of a pushout `L ⊗[k] A` along an arbitrary field extension `L / k` have ramification index
`1` over `A` whenever the contracted prime of `A` has separable residue field over `k`, and compares
horizontal ramification indices in a commutative square of local rings whose vertical ramification
indices are `1`.

Let `A` be an algebra over a field `k`, `L / k` an arbitrary field extension (not necessarily
algebraic or separable), and `B = L ⊗[k] A` a pushout algebra. Let `q` be a prime ideal of `B`
lying over `p = q ∩ A`.

If the residue field `κ(p)` of `p` is separable (hence algebraic) over `k`, then the fibre ring
`p.Fiber B = κ(p) ⊗[A] B ≃ κ(p) ⊗[k] L` is reduced
(`TauCeti.isReduced_tensorProduct_of_isSeparable`) and integral over the field `L`, so every prime
ideal of `p.Fiber B` is maximal and its localization at the prime `Q` corresponding to `q` is a
field. Since `Localization.AtPrime Q ≃ B_q ⧸ p B_q` (`Ideal.Fiber.localizationAlgEquivQuotient`),
the extended ideal `p B_q` is the maximal ideal of `B_q`, and therefore `q.ramificationIdx A = 1`.

Neither Noetherianity nor finite generation is assumed on `A` or `L`. Over a perfect field `k`
(in particular in characteristic zero), this applies at every prime `q` of `L ⊗[k] A` whose
contraction `q ∩ A` has residue field algebraic over `k`, such as closed points of finite-type
`k`-schemes.

## Main results

* `IsLocalRing.ramificationIdx_maximalIdeal`,
  `IsLocalRing.ramificationIdx_maximalIdeal_eq_one_iff`: for a local `R`-algebra `S`, the
  ramification index of `maximalIdeal S` over `R` is the `S`-length of
  `S ⧸ ((maximalIdeal S).under R) S`, and equals `1` iff `((maximalIdeal S).under R) S` is
  `maximalIdeal S`.
* `Ideal.ramificationIdx_maximalIdeal_localization`,
  `Ideal.ramificationIdx_maximalIdeal_localization_of_liesOver`: `q.ramificationIdx R` agrees with
  the ramification index of `maximalIdeal (Localization.AtPrime q)` over `R` or over
  `Localization.AtPrime (q.under R)`.
* `Ideal.ramificationIdx_eq_of_isLocalHom_square`: in a commutative square `R → S → B` and
  `R → A → B` with `S, A, B` local, `S → B` and `A → B` local homomorphisms, `A → B` flat, and
  vertical ramification indices `1`, `(maximalIdeal B).ramificationIdx S =
  (maximalIdeal A).ramificationIdx R` (with no flatness assumption on `R → A` or `S → B`).
* `Ideal.ramificationIdx_eq_one_of_isPushout_of_isSeparable`: if `κ(q ∩ A)` is separable over `k`,
  then `q.ramificationIdx A = 1` in any pushout `B = L ⊗[k] A` along a field extension `L / k`.
* `Ideal.ramificationIdx_eq_one_of_isPushout_of_isAlgebraic`: over a perfect field `k`, the same
  conclusion holds whenever `κ(q ∩ A)` is algebraic over `k`.
-/

public section

open scoped TensorProduct

namespace IsLocalRing

/-- For a local `R`-algebra `S`, the ramification index of `maximalIdeal S` over `R` is the
`S`-length of `S ⧸ ((maximalIdeal S).under R) S`, avoiding a second localization at
`maximalIdeal S`. -/
theorem ramificationIdx_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] :
    (maximalIdeal S).ramificationIdx R =
      (Module.length S (S ⧸ ((maximalIdeal S).under R).map (algebraMap R S))).toNat := by
  let Sm := Localization.AtPrime (maximalIdeal S)
  let e : S ≃ₐ[S] Sm := algEquivLocalizationAtMaximalIdeal S S
  have he : (e : S →+* Sm) = algebraMap S Sm :=
    RingHom.ext (algEquivLocalizationAtMaximalIdeal_apply S S)
  let I := ((maximalIdeal S).under R).map (algebraMap R S)
  let J := ((maximalIdeal S).under R).map (algebraMap R Sm)
  have hIJ : I.map e = J := by
    dsimp only [I, J]
    rw [IsScalarTower.algebraMap_eq R S Sm, ← Ideal.map_map, ← he]
    rfl
  have hsurj : Function.Surjective (algebraMap S Sm) := by
    rw [← he]
    exact e.surjective
  let q : (S ⧸ I) ≃ₐ[S] Sm ⧸ J := Ideal.quotientEquivAlg I J e hIJ.symm
  rw [Ideal.ramificationIdx_def, ← Module.length_eq_of_surjective hsurj,
    ← q.toLinearEquiv.length_eq]

/-- For a local homomorphism `R → S` of local rings, the ramification index of `maximalIdeal S`
over `R` is the `S`-length of `S ⧸ (maximalIdeal R) S`. -/
theorem ramificationIdx_maximalIdeal_of_isLocalHom {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] :
    (maximalIdeal S).ramificationIdx R =
      (Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S))).toNat := by
  rw [ramificationIdx_maximalIdeal, Ideal.under, maximalIdeal_comap]

/-- For a local `R`-algebra `S`, `(maximalIdeal S).ramificationIdx R = 1` iff the extended ideal
`((maximalIdeal S).under R) S` is `maximalIdeal S`. -/
theorem ramificationIdx_maximalIdeal_eq_one_iff {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] :
    (maximalIdeal S).ramificationIdx R = 1 ↔
      ((maximalIdeal S).under R).map (algebraMap R S) = maximalIdeal S := by
  rw [ramificationIdx_maximalIdeal, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff]

end IsLocalRing

namespace Ideal

section LocalComparison

/-- The ramification index of `maximalIdeal (Localization.AtPrime q)` over `R` equals
`q.ramificationIdx R`. -/
@[simp]
theorem ramificationIdx_maximalIdeal_localization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)).ramificationIdx R =
      q.ramificationIdx R := by
  rw [IsLocalRing.ramificationIdx_maximalIdeal, ramificationIdx_def,
    ← Ideal.under_under (B := S), Localization.AtPrime.under_maximalIdeal]

/-- The ramification index of `maximalIdeal (Localization.AtPrime q)` over
`Localization.AtPrime p` equals `q.ramificationIdx R` whenever `q` lies over `p`. -/
theorem ramificationIdx_maximalIdeal_localization_of_liesOver {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)).ramificationIdx
        (Localization.AtPrime p) = q.ramificationIdx R := by
  rw [IsLocalRing.ramificationIdx_maximalIdeal_of_isLocalHom, ramificationIdx_eq p q,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **Comparison of ramification indices in a square of local rings.** Suppose `R → S → B` and
`R → A → B` commute, `S, A, B` are local rings, `S → B` and `A → B` are local homomorphisms, `A → B`
is flat, `(maximalIdeal B).ramificationIdx A = 1`, and `(maximalIdeal S).ramificationIdx R = 1`.
Then `(maximalIdeal B).ramificationIdx S = (maximalIdeal A).ramificationIdx R`, with no flatness
assumption on `R → A` or `S → B`. -/
theorem ramificationIdx_eq_of_isLocalHom_square {R S A B : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [IsLocalRing S] [IsLocalRing A] [IsLocalRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B]
    [IsLocalHom (algebraMap S B)] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hAB : (IsLocalRing.maximalIdeal B).ramificationIdx A = 1)
    (hRS : (IsLocalRing.maximalIdeal S).ramificationIdx R = 1) :
    (IsLocalRing.maximalIdeal B).ramificationIdx S =
      (IsLocalRing.maximalIdeal A).ramificationIdx R := by
  have hunderS : (IsLocalRing.maximalIdeal B).under S = IsLocalRing.maximalIdeal S :=
    IsLocalRing.maximalIdeal_comap (algebraMap S B)
  have hunderA : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have hmapS : ((IsLocalRing.maximalIdeal S).under R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S :=
    IsLocalRing.ramificationIdx_maximalIdeal_eq_one_iff.mp hRS
  have hBS : (IsLocalRing.maximalIdeal B).ramificationIdx S =
      (IsLocalRing.maximalIdeal B).ramificationIdx R := by
    rw [IsLocalRing.ramificationIdx_maximalIdeal_of_isLocalHom,
      IsLocalRing.ramificationIdx_maximalIdeal, ← Ideal.under_under (B := S), hunderS,
      IsScalarTower.algebraMap_eq R S B, ← Ideal.map_map, hmapS]
  rw [hBS, ramificationIdx_tower (R := R) (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal B), hAB, mul_one]

end LocalComparison

/-- In a reduced commutative ring all of whose prime ideals are maximal, the localization at any
prime ideal is a field. -/
private theorem isField_localizationAtPrime_of_isReduced_of_forall_isMaximal
    {C : Type*} [CommRing C] [IsReduced C] (hmax : ∀ P : Ideal C, P.IsPrime → P.IsMaximal)
    (Q : Ideal C) [Q.IsPrime] : IsField (Localization.AtPrime Q) := by
  refine IsLocalRing.isField_iff_maximalIdeal_eq.mpr ?_
  have hnil : nilradical (Localization.AtPrime Q) = ⊥ :=
    nilradical_eq_zero (R := Localization.AtPrime Q)
  rw [← hnil, nilradical, Ideal.radical_eq_sInf, eq_comm]
  refine le_antisymm (sInf_le ⟨bot_le, (IsLocalRing.maximalIdeal.isMaximal _).isPrime⟩) ?_
  refine le_sInf fun J ⟨_, hJ⟩ ↦ ?_
  have hJQ : J.under C ≤ Q := fun c hc ↦ by
    by_contra hcQ
    exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hc
      (IsLocalization.map_units (Localization.AtPrime Q) (⟨c, hcQ⟩ : Q.primeCompl)))
  have hJeq : J.comap (algebraMap C (Localization.AtPrime Q)) = Q :=
    (hmax (J.under C) (hJ.under C)).eq_of_le ‹Q.IsPrime›.ne_top hJQ
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
  exact hJeq.ge

section FieldPushout

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- In a pushout `B = L ⊗[k] A` along an arbitrary field extension `L / k`, every prime `q` of `B`
whose contraction `q ∩ A` has residue field separable over `k` has ramification index `1` over `A`.
No finite-type or Noetherian assumption is needed on `A` or `L`. -/
theorem ramificationIdx_eq_one_of_isPushout_of_isSeparable (k L : Type*) [Field k] [Field L]
    [Algebra k L] [Algebra k A] [Algebra k B] [Algebra L B]
    [IsScalarTower k L B] [IsScalarTower k A B] [Algebra.IsPushout k L A B]
    (q : Ideal B) [q.IsPrime] (hsep : Algebra.IsSeparable k (q.under A).ResidueField) :
    q.ramificationIdx A = 1 := by
  let p := q.under A
  have : Algebra.IsSeparable k p.ResidueField := hsep
  have : Algebra.IsAlgebraic k p.ResidueField := Algebra.IsSeparable.isAlgebraic k p.ResidueField
  have : Algebra.IsPushout k A L B := .symm inferInstance
  -- Identify `p.Fiber B = κ(p) ⊗[A] B` with `L ⊗[k] κ(p)`, which is reduced and integral over `L`.
  let eFiber : (L ⊗[k] p.ResidueField) ≃ₐ[k] p.Fiber B :=
    (Algebra.TensorProduct.comm k L p.ResidueField).trans <|
      ((Algebra.TensorProduct.cancelBaseChange k A p.ResidueField p.ResidueField L).symm.trans
        (Algebra.TensorProduct.congr AlgEquiv.refl
          (Algebra.IsPushout.equiv k A L B))).restrictScalars k
  have : IsReduced (p.Fiber B) :=
    isReduced_of_injective eFiber.symm eFiber.symm.injective
  have hmax : ∀ P : Ideal (p.Fiber B), P.IsPrime → P.IsMaximal := fun P hP ↦ by
    let P' : Ideal (L ⊗[k] p.ResidueField) := P.comap eFiber.toRingHom
    have : P'.IsPrime := hP.comap _
    have : P'.IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := L) P' ?_
      rw [Ideal.eq_bot_of_prime (P'.under L)]
      exact Ideal.bot_isMaximal
    have hcomp : eFiber.toRingHom.comp eFiber.symm.toRingHom = RingHom.id _ :=
      RingHom.ext fun z ↦ eFiber.apply_symm_apply z
    rw [← Ideal.comap_id P, ← hcomp, ← Ideal.comap_comap]
    exact Ideal.comap_isMaximal_of_surjective
      eFiber.symm.toRingHom eFiber.symm.surjective (K := P')
  let Q : PrimeSpectrum (p.Fiber B) :=
    PrimeSpectrum.primesOverOrderIsoFiber A B p ⟨q, ⟨inferInstance, ⟨rfl⟩⟩⟩
  have hQunder : Q.asIdeal.comap Algebra.TensorProduct.includeRight = q :=
    congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber A B p).symm_apply_apply
      ⟨q, ⟨inferInstance, ⟨rfl⟩⟩⟩)
  have hFieldQ : IsField (Localization.AtPrime Q.asIdeal) :=
    isField_localizationAtPrime_of_isReduced_of_forall_isMaximal hmax Q.asIdeal
  -- Transport `Localization.AtPrime Q` to `B_q ⧸ p B_q`.
  have key : ∀ (q' : Ideal B) [q'.IsPrime],
      Q.asIdeal.comap Algebra.TensorProduct.includeRight = q' →
      IsField (Localization.AtPrime q' ⧸ p.map (algebraMap A (Localization.AtPrime q'))) := by
    rintro q' _ rfl
    let := Localization.AtPrime.algebraOfLiesOver p
      (Q.asIdeal.comap
        (Algebra.TensorProduct.includeRight (R := A) (A := p.ResidueField) (B := B)))
    exact MulEquiv.isField hFieldQ
      (Ideal.Fiber.localizationAlgEquivQuotient p Q.asIdeal).symm.toMulEquiv
  rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr (key q hQunder)

/-- Over a perfect field `k` (in particular in characteristic zero), every prime `q` of a pushout
`B = L ⊗[k] A` along a field extension `L / k` whose contraction `q ∩ A` has residue field
algebraic over `k` satisfies `q.ramificationIdx A = 1`. -/
theorem ramificationIdx_eq_one_of_isPushout_of_isAlgebraic (k L : Type*) [Field k] [PerfectField k]
    [Field L] [Algebra k L] [Algebra k A] [Algebra k B] [Algebra L B]
    [IsScalarTower k L B] [IsScalarTower k A B] [Algebra.IsPushout k L A B]
    (q : Ideal B) [q.IsPrime] (halg : Algebra.IsAlgebraic k (q.under A).ResidueField) :
    q.ramificationIdx A = 1 := by
  have : Algebra.IsAlgebraic k (q.under A).ResidueField := halg
  exact ramificationIdx_eq_one_of_isPushout_of_isSeparable k L q inferInstance

end FieldPushout

end Ideal
