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

This file relates `Ideal.ramificationIdx` at a prime to local rings, compares horizontal
ramification indices in a local-ring square with vertical ramification indices `1`, and proves that
primes of a pushout `B = L ⊗[k] A` along any field extension `L / k` have ramification index `1`
over `A` when `κ(q ∩ A)` is separable over `k`.

* `IsLocalRing.ramificationIdx_maximalIdeal`,
  `IsLocalRing.ramificationIdx_maximalIdeal_of_isLocalHom`,
  `IsLocalRing.ramificationIdx_maximalIdeal_eq_one_iff`: length characterization of
  `(maximalIdeal S).ramificationIdx R`.
* `Ideal.ramificationIdx_maximalIdeal_localization`,
  `Ideal.ramificationIdx_maximalIdeal_localization_of_liesOver`: localization invariance.
* `Ideal.ramificationIdx_eq_of_isLocalHom_square`: horizontal invariance in a local-ring square
  with vertical ramification indices `1` (flatness only on `A → B`).
* `Ideal.ramificationIdx_eq_one_of_isPushout_of_isSeparable`,
  `Ideal.ramificationIdx_eq_one_of_isPushout_of_isAlgebraic`: `q.ramificationIdx A = 1` in any
  field pushout `B = L ⊗[k] A` when `κ(q ∩ A)` is separable (or algebraic over perfect `k`).
-/

public section

open scoped TensorProduct

namespace IsLocalRing

/-- For a local `R`-algebra `S`, the ramification index of `maximalIdeal S` over `R` is the
`S`-length of `S ⧸ ((maximalIdeal S).under R) S`. -/
theorem ramificationIdx_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] :
    (maximalIdeal S).ramificationIdx R =
      (Module.length S (S ⧸ ((maximalIdeal S).under R).map (algebraMap R S))).toNat := by
  let Sm := Localization.AtPrime (maximalIdeal S)
  let e : S ≃ₐ[S] Sm := algEquivLocalizationAtMaximalIdeal S S
  have he : (e : S →+* Sm) = algebraMap S Sm :=
    RingHom.ext (algEquivLocalizationAtMaximalIdeal_apply S S)
  have hIJ : (((maximalIdeal S).under R).map (algebraMap R S)).map e =
      ((maximalIdeal S).under R).map (algebraMap R Sm) := by
    rw [IsScalarTower.algebraMap_eq R S Sm, ← Ideal.map_map, ← he]; rfl
  have hsurj : Function.Surjective (algebraMap S Sm) := he ▸ e.surjective
  rw [Ideal.ramificationIdx_def, ← Module.length_eq_of_surjective hsurj,
    ← (Ideal.quotientEquivAlg _ _ e hIJ.symm).toLinearEquiv.length_eq]

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
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have hBS : (IsLocalRing.maximalIdeal B).ramificationIdx S =
      (IsLocalRing.maximalIdeal B).ramificationIdx R := by
    rw [IsLocalRing.ramificationIdx_maximalIdeal_of_isLocalHom,
      IsLocalRing.ramificationIdx_maximalIdeal, ← Ideal.under_under (B := S),
      show (IsLocalRing.maximalIdeal B).under S = IsLocalRing.maximalIdeal S from
        IsLocalRing.maximalIdeal_comap (algebraMap S B),
      IsScalarTower.algebraMap_eq R S B, ← Ideal.map_map,
      IsLocalRing.ramificationIdx_maximalIdeal_eq_one_iff.mp hRS]
  rw [hBS, ramificationIdx_tower (R := R) (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal B), hAB, mul_one]

end LocalComparison

/-- In a reduced commutative ring all of whose prime ideals are maximal, the localization at any
prime ideal is a field. -/
private theorem isField_localizationAtPrime_of_isReduced_of_forall_isMaximal
    {C : Type*} [CommRing C] [IsReduced C] (hmax : ∀ P : Ideal C, P.IsPrime → P.IsMaximal)
    (Q : Ideal C) [Q.IsPrime] : IsField (Localization.AtPrime Q) := by
  refine IsLocalRing.isField_iff_maximalIdeal_eq.mpr ?_
  rw [← Ideal.zero_eq_bot, ← nilradical_eq_zero (R := Localization.AtPrime Q), nilradical,
    Ideal.radical_eq_sInf, eq_comm]
  refine le_antisymm (sInf_le ⟨bot_le, (IsLocalRing.maximalIdeal.isMaximal _).isPrime⟩)
    (le_sInf fun J ⟨_, hJ⟩ ↦ ?_)
  have hJQ : J.under C ≤ Q := fun c hc ↦ by_contra fun hcQ ↦
    hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hc
      (IsLocalization.map_units (Localization.AtPrime Q) (⟨c, hcQ⟩ : Q.primeCompl)))
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
  exact ((hmax (J.under C) (hJ.under C)).eq_of_le ‹Q.IsPrime›.ne_top hJQ).ge

section FieldPushout

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (k L : Type*) [Field k] [hL : Field L] [Algebra k L] [Algebra k A] [Algebra k B] [Algebra L B]
  [IsScalarTower k L B] [IsScalarTower k A B] [hP : Algebra.IsPushout k L A B]

include hL hP in
/-- In a pushout `B = L ⊗[k] A` along an arbitrary field extension `L / k`, every prime `q` of `B`
whose contraction `q ∩ A` has residue field separable over `k` has ramification index `1` over `A`.
No finite-type or Noetherian assumption is needed on `A` or `L`. -/
theorem ramificationIdx_eq_one_of_isPushout_of_isSeparable (q : Ideal B) [q.IsPrime]
    (hsep : Algebra.IsSeparable k (q.under A).ResidueField) :
    q.ramificationIdx A = 1 := by
  let p := q.under A
  have : Algebra.IsSeparable k p.ResidueField := hsep
  have : Algebra.IsAlgebraic k p.ResidueField := Algebra.IsSeparable.isAlgebraic k p.ResidueField
  have : Algebra.IsPushout k A L B := .symm inferInstance
  let eFiber : (L ⊗[k] p.ResidueField) ≃ₐ[k] p.Fiber B :=
    (Algebra.TensorProduct.comm k L p.ResidueField).trans <|
      ((Algebra.TensorProduct.cancelBaseChange k A p.ResidueField p.ResidueField L).symm.trans
        (Algebra.TensorProduct.congr AlgEquiv.refl
          (Algebra.IsPushout.equiv k A L B))).restrictScalars k
  have : IsReduced (p.Fiber B) := isReduced_of_injective eFiber.symm eFiber.symm.injective
  have hmax : ∀ P : Ideal (p.Fiber B), P.IsPrime → P.IsMaximal := fun P hP ↦ by
    let P' := P.comap eFiber.toRingHom
    have : P'.IsPrime := hP.comap _
    have : P'.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := L) P'
      (by rw [Ideal.eq_bot_of_prime (P'.under L)]; exact Ideal.bot_isMaximal)
    have hcomp : eFiber.toRingHom.comp eFiber.symm.toRingHom = RingHom.id _ :=
      RingHom.ext eFiber.apply_symm_apply
    rw [← Ideal.comap_id P, ← hcomp, ← Ideal.comap_comap]
    exact Ideal.comap_isMaximal_of_surjective eFiber.symm.toRingHom eFiber.symm.surjective (K := P')
  let Q : PrimeSpectrum (p.Fiber B) :=
    PrimeSpectrum.primesOverOrderIsoFiber A B p ⟨q, ⟨inferInstance, ⟨rfl⟩⟩⟩
  have hQunder : Q.asIdeal.comap Algebra.TensorProduct.includeRight = q :=
    congrArg Subtype.val ((PrimeSpectrum.primesOverOrderIsoFiber A B p).symm_apply_apply
      ⟨q, ⟨inferInstance, ⟨rfl⟩⟩⟩)
  have hFieldQ : IsField (Localization.AtPrime Q.asIdeal) :=
    isField_localizationAtPrime_of_isReduced_of_forall_isMaximal hmax Q.asIdeal
  have key : ∀ (q' : Ideal B) [q'.IsPrime],
      Q.asIdeal.comap Algebra.TensorProduct.includeRight = q' →
      IsField (Localization.AtPrime q' ⧸ p.map (algebraMap A (Localization.AtPrime q'))) := by
    rintro q' _ rfl
    let := Localization.AtPrime.algebraOfLiesOver p
      (Q.asIdeal.comap (Algebra.TensorProduct.includeRight (R := A) (A := p.ResidueField) (B := B)))
    exact MulEquiv.isField hFieldQ
      (Ideal.Fiber.localizationAlgEquivQuotient p Q.asIdeal).symm.toMulEquiv
  rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr (key q hQunder)

include hL hP in
/-- Over a perfect field `k` (in particular in characteristic zero), every prime `q` of a pushout
`B = L ⊗[k] A` along a field extension `L / k` whose contraction `q ∩ A` has residue field
algebraic over `k` satisfies `q.ramificationIdx A = 1`. -/
theorem ramificationIdx_eq_one_of_isPushout_of_isAlgebraic [PerfectField k] (q : Ideal B)
    [q.IsPrime] (halg : Algebra.IsAlgebraic k (q.under A).ResidueField) :
    q.ramificationIdx A = 1 :=
  have : Algebra.IsAlgebraic k (q.under A).ResidueField := halg
  ramificationIdx_eq_one_of_isPushout_of_isSeparable k L q inferInstance

end FieldPushout

end Ideal
