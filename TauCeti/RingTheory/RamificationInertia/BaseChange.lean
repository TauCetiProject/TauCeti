/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import TauCeti.RingTheory.RamificationInertia.Localization
public import TauCeti.RingTheory.TensorProduct.Reduced
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Ramification index under field pushouts

This file proves that primes of a pushout `B = L ⊗[k] A` along any field extension `L / k` have
ramification index `1` over `A` when `κ(q ∩ A)` is separable over `k` (or algebraic over perfect
`k`), with no finite-type or Noetherian assumptions:

* `Ideal.ramificationIdx_eq_one_of_isPushout_of_isSeparable`,
  `Ideal.ramificationIdx_eq_one_of_isPushout_of_isAlgebraic`: `q.ramificationIdx A = 1` in any
  field pushout `B = L ⊗[k] A` when `κ(q ∩ A)` is separable (or algebraic over perfect `k`).
-/

public section

open scoped TensorProduct

namespace Ideal

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
  have : Ring.KrullDimLE 0 (p.Fiber B) := Ring.krullDimLE_zero_iff.mpr hmax
  have hQmin : Q.asIdeal ∈ minimalPrimes (p.Fiber B) :=
    Ideal.mem_minimalPrimes_iff_isPrime.mpr Q.isPrime
  have : Ring.KrullDimLE 0 (Localization.AtPrime Q.asIdeal) :=
    Ring.KrullDimLE.of_isLocalization Q.asIdeal hQmin (Localization.AtPrime Q.asIdeal)
  have hFieldQ : IsField (Localization.AtPrime Q.asIdeal) := Ring.KrullDimLE.isField_of_isReduced
  have key : ∀ (q' : Ideal B) [q'.IsPrime],
      Q.asIdeal.comap Algebra.TensorProduct.includeRight = q' →
      IsField (Localization.AtPrime q' ⧸ p.map (algebraMap A (Localization.AtPrime q'))) := by
    rintro q' _ rfl
    let := Localization.AtPrime.algebraOfLiesOver p
      (Q.asIdeal.comap (Algebra.TensorProduct.includeRight (R := A) (A := p.ResidueField) (B := B)))
    exact MulEquiv.isField hFieldQ
      (Ideal.Fiber.localizationAlgEquivQuotient p Q.asIdeal).symm.toMulEquiv
  rw [← Ideal.ramificationIdx_maximalIdeal_localization,
    IsLocalRing.ramificationIdx_maximalIdeal_eq_one_iff,
    ← Ideal.under_under (B := B), Localization.AtPrime.under_maximalIdeal]
  exact IsLocalRing.eq_maximalIdeal
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr (key q hQunder))

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
