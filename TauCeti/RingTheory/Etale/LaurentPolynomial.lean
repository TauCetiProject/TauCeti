/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.Algebra.Polynomial.Laurent.PrincipalIdealRing
import TauCeti.Algebra.Polynomial.Laurent.RatFunc
import TauCeti.FieldTheory.FunctionField.AffineModel.Extension
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.XPowSubCX
import TauCeti.FieldTheory.FunctionField.Radical.TwoPlaces
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.Etale.Connected
import TauCeti.RingTheory.Etale.Idempotent
import TauCeti.RingTheory.Idempotents.Connected.Components
import TauCeti.RingTheory.RamificationInertia.Unramified
import TauCeti.RingTheory.Smooth.IntegralClosure
import TauCeti.Topology.NoetherianSpace.ConnectedComponents

/-!
# Finite étale algebras over Laurent polynomial rings

Let `K` be a field. The Laurent polynomial ring `K[T;T⁻¹]` is a principal ideal domain
(`LaurentPolynomial.instIsPrincipalIdealRing`) with fraction field `RatFunc K`
(`TauCeti.isFractionRing_ratFunc_of_laurent`). For every `n ≠ 0`, the polynomial `Y ^ n - T` is
irreducible over `RatFunc K` (`TauCeti.irreducible_X_pow_sub_C_X`), so the Kummer coordinate ring
`standardTameCover K[T;T⁻¹] (T 1) n = K[T;T⁻¹][Y] / (Y ^ n - T)` embeds into the field
`RatFunc K[Y] / (Y ^ n - X)` and is an integral domain; in particular its prime spectrum is
connected.

When `K` is algebraically closed of characteristic zero, these Kummer algebras exhaust the
connected finite étale `K[T;T⁻¹]`-algebras (`TauCeti.exists_algEquiv_standardTameCover_of_etale`),
and decomposing by connected components shows that every finite étale `K[T;T⁻¹]`-algebra is a
finite product of Kummer algebras (`TauCeti.isFiniteProductOfStandardTameCovers_of_etale`). This is
the algebraic classification of finite étale covers of the multiplicative group `𝔾_{m, K}` (SGA 1,
Exposé XIII, §2).

## Proof of the classification

Let `A` be a connected finite étale `K[T;T⁻¹]`-algebra with `K` algebraically closed of
characteristic zero. By `TauCeti.Algebra.Etale.isDomain_of_connectedSpace`,
`TauCeti.Algebra.Etale.isIntegrallyClosed_of_connectedSpace`, and
`TauCeti.Algebra.Etale.isFractionRing_tensorProduct_of_connectedSpace`, `A` is an integrally closed
domain whose generic fibre `L = RatFunc K ⊗[K[T;T⁻¹]] A` is a finite extension field of
`F = RatFunc K` of degree `n ≥ 1`, with `A` integrally closed in `L` (hence a Dedekind domain with
fraction field `L`).

Every place of `F / K` other than `0` (`X = 0`) and `∞` is finite on `K[T;T⁻¹]`, since `X` and
`X⁻¹` have order zero there; a place `P'` of `L / K` above it is therefore finite on `A`, and
étaleness of `A` over `K[T;T⁻¹]` gives `e(P' ∣ P) = 1`. In characteristic zero every place is tame,
so `TauCeti.exists_pow_eq_X_of_unramified_outside_zero_infty` (which combines Hurwitz's genus
formula and Riemann–Roch for tame extensions unramified outside two rational places; see
`TauCeti/FieldTheory/FunctionField/Radical/TwoPlaces.lean`) produces `y ∈ L` with `y ^ n = T`.
Integrality places `y` in `A`, giving a `K[T;T⁻¹]`-algebra map `K[T;T⁻¹][Y] / (Y ^ n - T) → A`
that induces an isomorphism on generic fibres and, by smooth base-change descent
(`AlgHom.bijective_of_bijective_tensorProduct`), is bijective on `A`.

## Main declarations

* `TauCeti.isDomain_standardTameCover_laurentPolynomial_T`: for `n ≠ 0`,
  `K[T;T⁻¹][Y] / (Y ^ n - T)` is an integral domain.
* `TauCeti.exists_algEquiv_standardTameCover_of_etale`: over an algebraically closed field `K` of
  characteristic zero, every connected finite étale `K[T;T⁻¹]`-algebra is isomorphic to
  `K[T;T⁻¹][Y] / (Y ^ n - T)` for some `n ≠ 0`.
* `TauCeti.isFiniteProductOfStandardTameCovers_of_etale`: every finite étale `K[T;T⁻¹]`-algebra is
  a finite product of such Kummer algebras.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental (SGA 1)*, Exposé XIII, §2.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Example 4.6.12 (2).
-/

public section

open Polynomial
open scoped LaurentPolynomial TensorProduct

namespace TauCeti

section RatFuncModel

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Kummer algebras over `K[T;T⁻¹]` are integral domains.** For any field `K` and `n ≠ 0`,
`K[T;T⁻¹][Y] / (Y ^ n - T)` is free over `K[T;T⁻¹]` and its generic fibre over `RatFunc K` is the
field `RatFunc K[Y] / (Y ^ n - X)` (`TauCeti.irreducible_X_pow_sub_C_X`). -/
theorem isDomain_standardTameCover_laurentPolynomial_T (K : Type*) [Field K] {n : ℕ}
    (hn : n ≠ 0) :
    IsDomain (standardTameCover K[T;T⁻¹] (LaurentPolynomial.T 1) n) := by
  have : NeZero n := ⟨hn⟩
  let _ : Algebra K[T;T⁻¹] (RatFunc K) := (laurentToRatFunc K).toRingHom.toAlgebra
  have hmonic : (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹])).Monic := monic_X_pow_sub_C _ hn
  have : Module.Free K[T;T⁻¹] (standardTameCover K[T;T⁻¹] (LaurentPolynomial.T 1) n) :=
    hmonic.free_adjoinRoot
  have hmap :
      (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹])).map (algebraMap K[T;T⁻¹] (RatFunc K)) =
        X ^ n - C (RatFunc.X : RatFunc K) := by
    simp [RingHom.algebraMap_toAlgebra, laurentToRatFunc_T]
  let e : RatFunc K ⊗[K[T;T⁻¹]] standardTameCover K[T;T⁻¹] (LaurentPolynomial.T 1) n ≃ₐ[RatFunc K]
      AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc K)) :=
    (AdjoinRoot.algebraTensorAlgEquiv (RatFunc K)
      (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹]))).trans
      (AdjoinRoot.mapAlgEquiv (AlgEquiv.refl : RatFunc K ≃ₐ[RatFunc K] RatFunc K) _ _
        (.of_eq (by simpa using hmap)))
  exact (e.injective.comp (Algebra.TensorProduct.includeRight_injective
    (laurentToRatFunc_injective K))).isDomain
    (e.toRingHom.comp (Algebra.TensorProduct.includeRight :
      standardTameCover K[T;T⁻¹] (LaurentPolynomial.T 1) n →ₐ[K[T;T⁻¹]] _).toRingHom)

section Classification

/-- Every place of `RatFunc K` other than `X = 0` and `∞` is finite on `K[T;T⁻¹]`. -/
private theorem laurentToRatFunc_mem_integers_of_ne {K : Type*} [Field K]
    {P : Place K (RatFunc K)}
    (hP0 : P ≠ Place.adicOfIrreducible (irreducible_X (R := K))) (hPinf : P ≠ Place.infty K)
    (r : K[T;T⁻¹]) :
    laurentToRatFunc K r ∈ P.integers := by
  have hXord : P.ord (RatFunc.X : RatFunc K) = 0 := Place.ord_X_eq_zero_of_ne hP0 hPinf
  have hXpow : ∀ m : ℤ, (RatFunc.X : RatFunc K) ^ m ∈ P.integers := fun m ↦ by
    rw [P.mem_integers_iff_ord_nonneg, P.ord_zpow, hXord, mul_zero]
  induction r using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | C_mul_T m c =>
    rw [map_mul, AlgHom.apply_laurentPolynomial_C, laurentToRatFunc_T]
    exact mul_mem (P.algebraMap_mem_integers c) (hXpow m)

/-- Over an algebraically closed field `K` of characteristic zero, the function field
`L = RatFunc K ⊗[K[T;T⁻¹]] A` of a connected finite étale `K[T;T⁻¹]`-algebra `A` contains an `n`-th
root of `RatFunc.X`, where `n = [L : RatFunc K]`. -/
private theorem exists_pow_eq_X_of_etale_laurentPolynomial (K A : Type*) [Field K] [IsAlgClosed K]
    [CharZero K] [CommRing A] [Algebra K[T;T⁻¹] A] [Module.Finite K[T;T⁻¹] A]
    [Algebra.Etale K[T;T⁻¹] A] [ConnectedSpace (PrimeSpectrum A)] :
    letI : Algebra K[T;T⁻¹] (RatFunc K) := (laurentToRatFunc K).toRingHom.toAlgebra
    letI : Field (RatFunc K ⊗[K[T;T⁻¹]] A) :=
      (haveI := isFractionRing_ratFunc_of_laurent K
      Algebra.Etale.isField_tensorProduct_of_connectedSpace K[T;T⁻¹] (RatFunc K) A).toField
    ∃ y : RatFunc K ⊗[K[T;T⁻¹]] A,
      y ^ Module.finrank (RatFunc K) (RatFunc K ⊗[K[T;T⁻¹]] A) =
        algebraMap (RatFunc K) (RatFunc K ⊗[K[T;T⁻¹]] A) RatFunc.X := by
  let F := RatFunc K
  let _ : Algebra K[T;T⁻¹] F := (laurentToRatFunc K).toRingHom.toAlgebra
  have : IsScalarTower K K[T;T⁻¹] F :=
    .of_algebraMap_eq fun c ↦ ((laurentToRatFunc K).commutes c).symm
  have : IsFractionRing K[T;T⁻¹] F := isFractionRing_ratFunc_of_laurent K
  have : IsDomain A := Algebra.Etale.isDomain_of_connectedSpace K[T;T⁻¹] A
  have : IsIntegrallyClosed A := Algebra.Etale.isIntegrallyClosed_of_connectedSpace K[T;T⁻¹] A
  let L := F ⊗[K[T;T⁻¹]] A
  let _ : Field L := (Algebra.Etale.isField_tensorProduct_of_connectedSpace K[T;T⁻¹] F A).toField
  let _ : Algebra K A := RingHom.toAlgebra ((algebraMap K[T;T⁻¹] A).comp (algebraMap K K[T;T⁻¹]))
  have : IsScalarTower K K[T;T⁻¹] A := .of_algebraMap_eq' rfl
  have : IsScalarTower K A L := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K F L, IsScalarTower.algebraMap_apply K K[T;T⁻¹] F,
      ← IsScalarTower.algebraMap_apply K[T;T⁻¹] F L, IsScalarTower.algebraMap_apply K[T;T⁻¹] A L,
      ← IsScalarTower.algebraMap_apply K K[T;T⁻¹] A]
  have : IsFractionRing A L :=
    Algebra.Etale.isFractionRing_tensorProduct_of_connectedSpace K[T;T⁻¹] F A
  have : Algebra.IsIntegral K[T;T⁻¹] A := Algebra.IsIntegral.of_finite K[T;T⁻¹] A
  have : IsIntegralClosure A K[T;T⁻¹] L := IsIntegralClosure.of_isIntegrallyClosed A K[T;T⁻¹] L
  have : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain K[T;T⁻¹] F L A
  have hunram : ∀ P' : Place K L,
      P'.restrict K F ≠ Place.adicOfIrreducible (irreducible_X (R := K)) →
      P'.restrict K F ≠ Place.infty K → Place.ramificationIdx F P' = 1 := fun P' h0 hinf ↦ by
    have hR : ∀ r : K[T;T⁻¹], algebraMap K[T;T⁻¹] F r ∈ (P'.restrict K F).integers :=
      laurentToRatFunc_mem_integers_of_ne h0 hinf
    have hA : ∀ a : A, algebraMap A L a ∈ P'.integers :=
      Place.algebraMap_mem_integers_of_restrict_eq_ofPrime K F ((P'.restrict K F).center hR)
        ((P'.restrict K F).ofPrime_center K F hR).symm
    rw [Place.ramificationIdx_eq_ramificationIdx_center (R := K[T;T⁻¹]) K F P' hA]
    exact (Ideal.isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_residueField
      (R := K[T;T⁻¹]) (P'.center hA).asIdeal |>.mp inferInstance).1
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  exact exists_pow_eq_X_of_unramified_outside_zero_infty
    (fun P' ↦ Place.isTame_of_charZero K F P') hunram

/-- **Classification of connected finite étale algebras over `K[T;T⁻¹]`.** Over an algebraically
closed field `K` of characteristic zero, every connected finite étale `K[T;T⁻¹]`-algebra `A` is
isomorphic to a Kummer algebra `K[T;T⁻¹][Y] / (Y ^ n - T)` for some `n ≠ 0`. -/
theorem exists_algEquiv_standardTameCover_of_etale (K A : Type*) [Field K] [IsAlgClosed K]
    [CharZero K] [CommRing A] [Algebra K[T;T⁻¹] A] [Module.Finite K[T;T⁻¹] A]
    [Algebra.Etale K[T;T⁻¹] A] [ConnectedSpace (PrimeSpectrum A)] :
    ∃ n : ℕ, n ≠ 0 ∧
      Nonempty (standardTameCover K[T;T⁻¹] (LaurentPolynomial.T 1) n ≃ₐ[K[T;T⁻¹]] A) := by
  let F := RatFunc K
  let _ : Algebra K[T;T⁻¹] F := (laurentToRatFunc K).toRingHom.toAlgebra
  have : IsFractionRing K[T;T⁻¹] F := isFractionRing_ratFunc_of_laurent K
  have : IsDomain A := Algebra.Etale.isDomain_of_connectedSpace K[T;T⁻¹] A
  have : IsIntegrallyClosed A := Algebra.Etale.isIntegrallyClosed_of_connectedSpace K[T;T⁻¹] A
  let L := F ⊗[K[T;T⁻¹]] A
  let _ : Field L := (Algebra.Etale.isField_tensorProduct_of_connectedSpace K[T;T⁻¹] F A).toField
  set n : ℕ := Module.finrank F L
  have hn_pos : 0 < n := Module.finrank_pos
  have hn : n ≠ 0 := hn_pos.ne'
  have : NeZero n := ⟨hn⟩
  obtain ⟨y, hy⟩ := exists_pow_eq_X_of_etale_laurentPolynomial K A
  have hT : algebraMap K[T;T⁻¹] F (LaurentPolynomial.T 1) = RatFunc.X := by
    rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      laurentToRatFunc_T, zpow_one]
  have hyT : y ^ n = algebraMap K[T;T⁻¹] L (LaurentPolynomial.T 1) := by
    rw [hy, IsScalarTower.algebraMap_apply K[T;T⁻¹] F L, hT]
  -- `A` is integrally closed in `L`, so `y` comes from an `n`-th root `a ∈ A` of `T 1`.
  have hinjAL : Function.Injective (algebraMap A L) :=
    Algebra.TensorProduct.includeRight_injective (laurentToRatFunc_injective K)
  have : Algebra.IsIntegral K[T;T⁻¹] A := Algebra.IsIntegral.of_finite K[T;T⁻¹] A
  have : IsFractionRing A L :=
    Algebra.Etale.isFractionRing_tensorProduct_of_connectedSpace K[T;T⁻¹] F A
  have : IsIntegralClosure A K[T;T⁻¹] L := IsIntegralClosure.of_isIntegrallyClosed A K[T;T⁻¹] L
  have : IsIntegrallyClosedIn A L := IsIntegrallyClosedIn.of_isIntegralClosure K[T;T⁻¹]
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow hn_pos
    (by rw [hyT, IsScalarTower.algebraMap_apply K[T;T⁻¹] A L]; exact isIntegral_algebraMap)
  have ha_pow : a ^ n = algebraMap K[T;T⁻¹] A (LaurentPolynomial.T 1) :=
    hinjAL (by rw [map_pow, ha, hyT, IsScalarTower.algebraMap_apply K[T;T⁻¹] A L])
  let B := standardTameCover K[T;T⁻¹] (LaurentPolynomial.T 1) n
  let ψ : B →ₐ[K[T;T⁻¹]] A :=
    (AdjoinRoot.algHomEquiv A (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹]))).symm ⟨a, by
      rw [map_sub, map_pow, aeval_X, aeval_C, ha_pow, sub_self]⟩
  -- On generic fibres, `ψ` induces an `F`-algebra map between fields of the same dimension `n`.
  let ψF : F ⊗[K[T;T⁻¹]] B →ₐ[F] L := Algebra.TensorProduct.map (AlgHom.id F F) ψ
  have hmap : (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹])).map (algebraMap K[T;T⁻¹] F) =
      X ^ n - C (RatFunc.X : F) := by
    simp [RingHom.algebraMap_toAlgebra, laurentToRatFunc_T]
  let eB : AdjoinRoot (X ^ n - C (RatFunc.X : F)) ≃ₐ[F] F ⊗[K[T;T⁻¹]] B :=
    (AdjoinRoot.mapAlgEquiv (AlgEquiv.refl : F ≃ₐ[F] F) _ _
      (.of_eq (by simpa using hmap.symm))).trans
      (AdjoinRoot.algebraTensorAlgEquiv F (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹]))).symm
  have hψF_bij : Function.Bijective ψF :=
    (Function.Bijective.of_comp_iff ψF eB.bijective).mp
      ((ψF.comp eB.toAlgHom).toLinearMap.linearEquivOfInjective
        (ψF.comp eB.toAlgHom).toRingHom.injective
        (finrank_adjoinRoot_X_pow_sub_C_X K n)).bijective
  have hn_unit : IsUnit (n : K[T;T⁻¹]) := by
    simpa using
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn) : IsUnit (n : K)).map
        (algebraMap K K[T;T⁻¹])
  have : Algebra.Etale K[T;T⁻¹] B :=
    standardTameCover_etale (LaurentPolynomial.isUnit_T 1) hn_unit
  exact ⟨n, hn, ⟨AlgEquiv.ofBijective ψ (ψ.bijective_of_bijective_tensorProduct hinjAL hψF_bij)⟩⟩

/-- **Classification of finite étale algebras over `K[T;T⁻¹]`.** Over an algebraically closed field
`K` of characteristic zero, every finite étale `K[T;T⁻¹]`-algebra is a finite product of Kummer
algebras `K[T;T⁻¹][Y] / (Y ^ (e i) - T)` with `e i ≥ 1` invertible in `K[T;T⁻¹]`. -/
theorem isFiniteProductOfStandardTameCovers_of_etale (K A : Type*) [Field K] [IsAlgClosed K]
    [CharZero K] [CommRing A] [Algebra K[T;T⁻¹] A] [Module.Finite K[T;T⁻¹] A]
    [Algebra.Etale K[T;T⁻¹] A] :
    IsFiniteProductOfStandardTameCovers K[T;T⁻¹] A (LaurentPolynomial.T 1) := by
  classical
  have : IsNoetherianRing A := IsNoetherianRing.of_finite K[T;T⁻¹] A
  have : Finite (ConnectedComponents (PrimeSpectrum A)) :=
    finite_connectedComponents_of_noetherianSpace
  let _ : Fintype (ConnectedComponents (PrimeSpectrum A)) := Fintype.ofFinite _
  let eAlg : A ≃ₐ[K[T;T⁻¹]]
      ∀ C : ConnectedComponents (PrimeSpectrum A),
        A ⧸ PrimeSpectrum.connectedComponentsIdeal C :=
    AlgEquiv.ofRingEquiv (f := PrimeSpectrum.ringEquivPiQuotientConnectedComponentsIdeal (R := A))
      fun r ↦ funext fun C ↦ by
        rw [PrimeSpectrum.ringEquivPiQuotientConnectedComponentsIdeal_apply, Pi.algebraMap_apply,
          IsScalarTower.algebraMap_apply K[T;T⁻¹] A (A ⧸ PrimeSpectrum.connectedComponentsIdeal C),
          Ideal.Quotient.algebraMap_eq]
  have hcomp (C : ConnectedComponents (PrimeSpectrum A)) :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        (standardTameCover K[T;T⁻¹] (LaurentPolynomial.T 1) n ≃ₐ[K[T;T⁻¹]]
          A ⧸ PrimeSpectrum.connectedComponentsIdeal C) := by
    have : Module.Finite K[T;T⁻¹] (A ⧸ PrimeSpectrum.connectedComponentsIdeal C) :=
      Module.Finite.of_surjective
        (Ideal.Quotient.mkₐ K[T;T⁻¹] (PrimeSpectrum.connectedComponentsIdeal C)).toLinearMap
        Ideal.Quotient.mk_surjective
    have : Algebra.Etale K[T;T⁻¹] (A ⧸ PrimeSpectrum.connectedComponentsIdeal C) := by
      obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe C
      have heq := (PrimeSpectrum.connectedComponentsIdeal_mk p).trans
        (PrimeSpectrum.connectedComponentIdeal_eq_span p)
      have := Algebra.Etale.quotient_span_singleton (R := K[T;T⁻¹])
        (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent p).one_sub
      exact Algebra.Etale.of_equiv (Ideal.quotientEquivAlgOfEq K[T;T⁻¹] heq.symm)
    exact exists_algEquiv_standardTameCover_of_etale K
      (A ⧸ PrimeSpectrum.connectedComponentsIdeal C)
  choose e he_ne hφ using hcomp
  let σ : Fin (Fintype.card (ConnectedComponents (PrimeSpectrum A))) ≃
      ConnectedComponents (PrimeSpectrum A) := (Fintype.equivFin _).symm
  refine (isFiniteProductOfStandardTameCovers_iff (LaurentPolynomial.T 1)).mpr
    ⟨_, inferInstance, fun i ↦ e (σ i), fun i ↦ Nat.one_le_iff_ne_zero.mpr (he_ne (σ i)),
      fun i ↦ by
        simpa [LaurentPolynomial.C_eq_algebraMap] using
          (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (he_ne (σ i))) : IsUnit (e (σ i) : K)).map
            (LaurentPolynomial.C : K →+* K[T;T⁻¹]),
      ⟨eAlg.trans <|
        (AlgEquiv.piCongrLeft' K[T;T⁻¹]
          (fun C ↦ A ⧸ PrimeSpectrum.connectedComponentsIdeal C) (Fintype.equivFin _)).trans <|
          AlgEquiv.piCongrRight fun i ↦ (Classical.choice (hφ (σ i))).symm⟩⟩

end Classification

end RatFuncModel

end TauCeti
