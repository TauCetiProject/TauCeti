/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.Algebra.Polynomial.Laurent.Basic
import TauCeti.Algebra.Polynomial.Laurent.Polynomial
import TauCeti.FieldTheory.FunctionField.AffineModel.Extension
import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
import TauCeti.FieldTheory.FunctionField.Place.ConstantField
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.XPowSubCX
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.Etale.Connected
import TauCeti.RingTheory.Etale.Idempotent
import TauCeti.RingTheory.Idempotents.Connected.Components
import TauCeti.RingTheory.Localization.PrincipalIdealRing
import TauCeti.RingTheory.RamificationInertia.Unramified
import TauCeti.RingTheory.Smooth.IntegralClosure
import TauCeti.Topology.NoetherianSpace.ConnectedComponents

/-!
# Finite étale algebras over Laurent polynomial rings

Let `K` be a field. The Laurent polynomial ring `K[T;T⁻¹]`, being the localization of `K[X]` away
from `X`, is a principal ideal domain (hence a Dedekind domain and an integrally closed domain) with
fraction field `RatFunc K`. For every `n ≠ 0`, the polynomial `Y ^ n - T` is irreducible over
`RatFunc K` (`TauCeti.irreducible_X_pow_sub_C_X`), so the Kummer coordinate ring
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
characteristic zero. By `TauCeti.Algebra.Etale.isDomain_of_connectedSpace` and
`TauCeti.Algebra.Etale.isIntegrallyClosed_of_connectedSpace`, `A` is an integrally closed domain
whose generic fibre `L = RatFunc K ⊗[K[T;T⁻¹]] A` is a finite extension field of `F = RatFunc K`
of degree `n ≥ 1`, with `A` integrally closed in `L` (hence a Dedekind domain with fraction field
`L`).

Every place of `F / K` other than `0` (`X = 0`) and `∞` is finite on `K[T;T⁻¹]`, since `X` and
`X⁻¹` have order zero there; a place `P'` of `L / K` above it is therefore finite on `A`, and
étaleness of `A` over `K[T;T⁻¹]` gives `e(P' ∣ P) = 1`. In characteristic zero every place is tame,
so the Hurwitz genus formula (`TauCeti.hurwitz_genus_formula_ratFunc`) reads
`2g(L) - 2 = -2n + ∑_{P' ∣ 0}(e - 1) + ∑_{P' ∣ ∞}(e - 1)`. Because `0` and `∞` each have at least
one extension to `L` and the ramification indices in each fibre add up to at most `n`, both sums
are at most `n - 1`; hence `g(L) = 0`, and there are unique places `Q₀ ∣ 0` and `Q_∞ ∣ ∞`, both of
ramification index `n`.

By Riemann–Roch in genus zero, the degree-zero divisor `Q_∞ - Q₀` has a nonzero section `z`, whose
principal divisor is `Q₀ - Q_∞`. Then `z ^ n / X` has order zero at every place of `L`, hence lies
in `Kˣ`; rescaling `z` by an `n`-th root in `K` produces `y ∈ L` with `y ^ n = T`. Integrality
places `y` in `A`, giving a `K[T;T⁻¹]`-algebra map `K[T;T⁻¹][Y] / (Y ^ n - T) → A` that induces an
isomorphism on generic fibres and, because smooth base change commutes with integral closure, is
bijective on `A`.

## Main declarations

* `LaurentPolynomial.instIsPrincipalIdealRing`: `K[T;T⁻¹]` is a principal ideal domain over a
  field `K`.
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
open scoped LaurentPolynomial TensorProduct IntermediateField

namespace LaurentPolynomial

/-- Over a field `K`, the Laurent polynomial ring `K[T;T⁻¹]` is a principal ideal domain, being the
localization of `K[X]` away from `X`. -/
instance instIsPrincipalIdealRing (K : Type*) [Field K] : IsPrincipalIdealRing K[T;T⁻¹] :=
  IsLocalization.isPrincipalIdealRing (Submonoid.powers (X : K[X])) K[T;T⁻¹]

end LaurentPolynomial

namespace TauCeti

section RatFuncModel

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The `K`-algebra map `K[T;T⁻¹] → RatFunc K` sending `T` to `RatFunc.X`. -/
private noncomputable def laurentToRatFunc (K : Type*) [Field K] : K[T;T⁻¹] →ₐ[K] RatFunc K :=
  laurentEval (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

private theorem laurentToRatFunc_T_one (K : Type*) [Field K] :
    laurentToRatFunc K (LaurentPolynomial.T 1) = RatFunc.X := by
  simp [laurentToRatFunc]

private theorem laurentToRatFunc_toLaurent (K : Type*) [Field K] (p : K[X]) :
    laurentToRatFunc K (algebraMap K[X] K[T;T⁻¹] p) = algebraMap K[X] (RatFunc K) p := by
  have hhom : (laurentToRatFunc K).toRingHom.comp (algebraMap K[X] K[T;T⁻¹]) =
      algebraMap K[X] (RatFunc K) := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · ext c
      change laurentToRatFunc K (algebraMap K[X] K[T;T⁻¹] (C c)) =
        algebraMap K[X] (RatFunc K) (C c)
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K K[X] K[T;T⁻¹],
        (laurentToRatFunc K).commutes, IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
    · change laurentToRatFunc K (Polynomial.toLaurent X) = _
      rw [Polynomial.toLaurent_X, laurentToRatFunc_T_one, RatFunc.algebraMap_X]
  exact RingHom.congr_fun hhom p

private theorem laurentToRatFunc_injective (K : Type*) [Field K] :
    Function.Injective (laurentToRatFunc K) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro r hr
  obtain ⟨⟨p, s⟩, hps⟩ := IsLocalization.surj (Submonoid.powers (X : K[X])) r
  have hp0 : algebraMap K[X] (RatFunc K) p = 0 := by
    rw [← laurentToRatFunc_toLaurent, ← hps, map_mul, hr, zero_mul]
  have hp : p = 0 := (map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp hp0
  rw [hp, map_zero] at hps
  exact (IsLocalization.map_units K[T;T⁻¹] s).mul_left_eq_zero.mp hps

/-- Equipped with `laurentToRatFunc K`, `RatFunc K` is a fraction field of `K[T;T⁻¹]`. -/
private theorem isFractionRing_ratFunc_of_laurent (K : Type*) [Field K] :
    letI : Algebra K[T;T⁻¹] (RatFunc K) := (laurentToRatFunc K).toRingHom.toAlgebra
    IsFractionRing K[T;T⁻¹] (RatFunc K) := by
  let _ : Algebra K[T;T⁻¹] (RatFunc K) := (laurentToRatFunc K).toRingHom.toAlgebra
  have hinj : Function.Injective (algebraMap K[T;T⁻¹] (RatFunc K)) := laurentToRatFunc_injective K
  refine ⟨fun y ↦ isUnit_iff_ne_zero.mpr (map_ne_zero_of_mem_nonZeroDivisors _ hinj y.2),
    fun z ↦ ?_, fun {a b} hab ↦ ⟨1, by simp [hinj hab]⟩⟩
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors K[X]) z
  have hq : algebraMap K[X] K[T;T⁻¹] q ∈ nonZeroDivisors K[T;T⁻¹] := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    have hinjX : Function.Injective (algebraMap K[X] K[T;T⁻¹]) :=
      IsLocalization.injective K[T;T⁻¹] (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr X_ne_zero))
    exact map_ne_zero_of_mem_nonZeroDivisors _ hinjX q.2
  refine ⟨⟨algebraMap K[X] K[T;T⁻¹] p, ⟨algebraMap K[X] K[T;T⁻¹] q, hq⟩⟩, ?_⟩
  change z * laurentToRatFunc K (algebraMap K[X] K[T;T⁻¹] q) =
    laurentToRatFunc K (algebraMap K[X] K[T;T⁻¹] p)
  rwa [laurentToRatFunc_toLaurent, laurentToRatFunc_toLaurent]

/-- When `A` is a connected étale `K[T;T⁻¹]`-algebra, `RatFunc K ⊗[K[T;T⁻¹]] A` is a fraction field
of `A`. -/
private theorem isFractionRing_ratFuncTensor (K A : Type*) [Field K] [CommRing A]
    [Algebra K[T;T⁻¹] A] [Algebra.Etale K[T;T⁻¹] A] [ConnectedSpace (PrimeSpectrum A)] :
    letI : Algebra K[T;T⁻¹] (RatFunc K) := (laurentToRatFunc K).toRingHom.toAlgebra
    haveI : IsDomain A := Algebra.Etale.isDomain_of_connectedSpace K[T;T⁻¹] A
    IsFractionRing A (RatFunc K ⊗[K[T;T⁻¹]] A) := by
  let F := RatFunc K
  let _ : Algebra K[T;T⁻¹] F := (laurentToRatFunc K).toRingHom.toAlgebra
  have : IsFractionRing K[T;T⁻¹] F := isFractionRing_ratFunc_of_laurent K
  have : IsDomain A := Algebra.Etale.isDomain_of_connectedSpace K[T;T⁻¹] A
  let L := F ⊗[K[T;T⁻¹]] A
  let _ : Field L := (Algebra.Etale.isField_tensorProduct_of_connectedSpace K[T;T⁻¹] F A).toField
  have hinjAL : Function.Injective (algebraMap A L) :=
    Algebra.TensorProduct.includeRight_injective (laurentToRatFunc_injective K)
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors K[T;T⁻¹])) L :=
    IsLocalization.tensorRight (S := A) F (nonZeroDivisors K[T;T⁻¹])
  refine ⟨fun y ↦ isUnit_iff_ne_zero.mpr (map_ne_zero_of_mem_nonZeroDivisors _ hinjAL y.2),
    fun z ↦ ?_, fun {a b} hab ↦ ⟨1, by simp [hinjAL hab]⟩⟩
  obtain ⟨⟨a, s, hs⟩, h⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors K[T;T⁻¹])) z
  obtain ⟨r, hr, rfl⟩ := hs
  have hinjRA : Function.Injective (algebraMap K[T;T⁻¹] A) := by
    intro x₁ x₂ hxy
    apply laurentToRatFunc_injective K
    apply (algebraMap F L).injective
    change algebraMap F L (algebraMap K[T;T⁻¹] F x₁) = algebraMap F L (algebraMap K[T;T⁻¹] F x₂)
    rw [← IsScalarTower.algebraMap_apply K[T;T⁻¹] F L,
      ← IsScalarTower.algebraMap_apply K[T;T⁻¹] F L,
      IsScalarTower.algebraMap_apply K[T;T⁻¹] A L,
      IsScalarTower.algebraMap_apply K[T;T⁻¹] A L, hxy]
  exact ⟨⟨a, ⟨algebraMap K[T;T⁻¹] A r, map_mem_nonZeroDivisors _ hinjRA hr⟩⟩, h⟩

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
    change (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹])).map (laurentToRatFunc K).toRingHom = _
    simp [laurentToRatFunc_T_one]
  let e : RatFunc K ⊗[K[T;T⁻¹]] standardTameCover K[T;T⁻¹] (LaurentPolynomial.T 1) n ≃ₐ[RatFunc K]
      AdjoinRoot (X ^ n - C (RatFunc.X : RatFunc K)) :=
    (AdjoinRoot.algebraTensorAlgEquiv (RatFunc K)
      (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹]))).trans
      (AdjoinRoot.mapAlgEquiv (AlgEquiv.refl : RatFunc K ≃ₐ[RatFunc K] RatFunc K) _ _
        (.of_eq (by simpa using hmap)))
  exact Algebra.Etale.isDomain_of_isField_tensorProduct (laurentToRatFunc_injective K)
    (MulEquiv.isField (Field.toIsField _) e.toMulEquiv)

section Classification

open AlgebraicGeometry

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
    rw [map_mul, AlgHom.apply_laurentPolynomial_C, laurentToRatFunc, laurentEval_T,
      Units.val_zpow_eq_zpow_val, Units.val_mk0]
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
  classical
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
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : IsFractionRing A L := isFractionRing_ratFuncTensor K A
  have : Algebra.IsIntegral K[T;T⁻¹] A := Algebra.IsIntegral.of_finite K[T;T⁻¹] A
  have : IsIntegralClosure A K[T;T⁻¹] L := IsIntegralClosure.of_isIntegrallyClosed A K[T;T⁻¹] L
  have : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain K[T;T⁻¹] F L A
  have hL : IsFunctionField K L := isFunctionField_iff_functionField.mpr inferInstance
  -- Every place of `L` not over `0` or `∞` is unramified over `F`.
  let P₀ : Place K F := Place.adicOfIrreducible (irreducible_X (R := K))
  let Pinf : Place K F := Place.infty K
  have hP0_ord : P₀.ord (RatFunc.X : F) = 1 := Place.ord_adicOfIrreducible_X_self
  have hPinf_ord : Pinf.ord (RatFunc.X : F) = -1 := by
    change (Place.infty K).ord (RatFunc.X : RatFunc K) = -1
    rw [Place.ord_infty, RatFunc.intDegree_X]
  have hP0_ne_inf : P₀ ≠ Pinf := by
    intro h
    have h1 := hP0_ord
    rw [h, hPinf_ord] at h1
    omega
  obtain ⟨Q₀₀, hQ₀₀⟩ := Place.restrict_surjective_of_finiteDimensional
    (IsFunctionField.ratFunc K) hL P₀
  obtain ⟨Qinf₀, hQinf₀⟩ := Place.restrict_surjective_of_finiteDimensional
    (IsFunctionField.ratFunc K) hL Pinf
  have hexL : IsIntegrallyClosedIn K L :=
    Q₀₀.isIntegrallyClosedIn_of_degree_eq_one
      (Q₀₀.degree_eq_one_of_isAlgClosed_of_isFunctionField hL)
  have hunram : ∀ P' : Place K L, P'.restrict K F ≠ P₀ → P'.restrict K F ≠ Pinf →
      Place.ramificationIdx F P' = 1 := by
    intro P' h0 hinf
    have hR : ∀ r : K[T;T⁻¹], algebraMap K[T;T⁻¹] F r ∈ (P'.restrict K F).integers :=
      laurentToRatFunc_mem_integers_of_ne h0 hinf
    have hA : ∀ a : A, algebraMap A L a ∈ P'.integers :=
      Place.algebraMap_mem_integers_of_restrict_eq_ofPrime K F ((P'.restrict K F).center hR)
        ((P'.restrict K F).ofPrime_center K F hR).symm
    rw [Place.ramificationIdx_eq_ramificationIdx_center (R := K[T;T⁻¹]) K F P' hA]
    exact (Ideal.isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_residueField
      (R := K[T;T⁻¹]) (P'.center hA).asIdeal |>.mp inferInstance).1
  -- Hurwitz + fundamental inequality force `genus K L = 0` and unique `Q₀ ∣ P₀`, `Qinf ∣ Pinf`.
  set n : ℕ := Module.finrank F L
  have hn_pos : 0 < n := Module.finrank_pos
  let S₀ : Finset (Place K L) := (Place.finite_setOf_restrict_eq K F P₀).toFinset
  let Sinf : Finset (Place K L) := (Place.finite_setOf_restrict_eq K F Pinf).toFinset
  have hmemS₀ : ∀ P', P' ∈ S₀ ↔ P'.restrict K F = P₀ := fun _ ↦ Set.Finite.mem_toFinset _
  have hmemSinf : ∀ P', P' ∈ Sinf ↔ P'.restrict K F = Pinf := fun _ ↦ Set.Finite.mem_toFinset _
  have hdisj : Disjoint S₀ Sinf := Finset.disjoint_left.mpr fun P' h1 h2 ↦
    hP0_ne_inf (((hmemS₀ P').mp h1).symm.trans ((hmemSinf P').mp h2))
  have hcard₀ : 1 ≤ S₀.card := Finset.card_pos.mpr ⟨Q₀₀, (hmemS₀ Q₀₀).mpr hQ₀₀⟩
  have hcardinf : 1 ≤ Sinf.card := Finset.card_pos.mpr ⟨Qinf₀, (hmemSinf Qinf₀).mpr hQinf₀⟩
  have hsum₀ : ∑ P' ∈ S₀, Place.ramificationIdx F P' ≤ n := by
    refine le_trans (Finset.sum_le_sum fun P' _ ↦
      Nat.le_mul_of_pos_right _ (Place.one_le_relativeDegree K F P')) ?_
    exact Place.sum_ramificationIdx_mul_relativeDegree_le_finrank K F P₀ S₀
      fun P' hP' ↦ (hmemS₀ P').mp hP'
  have hsuminf : ∑ P' ∈ Sinf, Place.ramificationIdx F P' ≤ n := by
    refine le_trans (Finset.sum_le_sum fun P' _ ↦
      Nat.le_mul_of_pos_right _ (Place.one_le_relativeDegree K F P')) ?_
    exact Place.sum_ramificationIdx_mul_relativeDegree_le_finrank K F Pinf Sinf
      fun P' hP' ↦ (hmemSinf P').mp hP'
  let Ddiff := Divisor.tameDifferent K L (IsFunctionField.ratFunc K)
  have hsupp : Ddiff.support ⊆ S₀ ∪ Sinf := by
    intro P' hP'
    rw [Finset.mem_union, hmemS₀, hmemSinf]
    by_contra! hne
    have he1 : Place.ramificationIdx (RatFunc K) P' = 1 := hunram P' hne.1 hne.2
    have hcoeff : Ddiff.coeff P' = 0 := by simp [Ddiff, he1]
    exact Finsupp.mem_support_iff.mp hP' hcoeff
  have hdeg_diff : Divisor.degree Ddiff =
      ((∑ P' ∈ S₀, Place.ramificationIdx F P' : ℕ) : ℤ) - S₀.card +
        (((∑ P' ∈ Sinf, Place.ramificationIdx F P' : ℕ) : ℤ) - Sinf.card) := by
    rw [Divisor.degree_apply_of_isAlgClosed hL Ddiff,
      Finset.sum_subset hsupp (fun P' _ hnot ↦ Finsupp.notMem_support_iff.mp hnot)]
    change ∑ P' ∈ S₀ ∪ Sinf, Ddiff.coeff P' = _
    simp only [Ddiff, Divisor.coeff_tameDifferent, Finset.sum_union hdisj, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_sum]
    rfl
  have hhurwitz : 2 * (genus K L : ℤ) - 2 = -2 * (n : ℤ) + Divisor.degree Ddiff := by
    have htame : Ddiff = Divisor.different K L (IsFunctionField.ratFunc K) :=
      (Divisor.tameDifferent_eq_different_iff K L (IsFunctionField.ratFunc K)).mpr
        (fun P' ↦ Place.isTame_of_charZero K F P')
    rw [htame]
    exact hurwitz_genus_formula_ratFunc hexL
  have hgenus : genus K L = 0 := by omega
  have hcard₀_eq : S₀.card = 1 := by omega
  have hcardinf_eq : Sinf.card = 1 := by omega
  have hsum₀_eq : ∑ P' ∈ S₀, Place.ramificationIdx F P' = n := by omega
  have hsuminf_eq : ∑ P' ∈ Sinf, Place.ramificationIdx F P' = n := by omega
  obtain ⟨Q₀, hS₀_eq⟩ := Finset.card_eq_one.mp hcard₀_eq
  obtain ⟨Qinf, hSinf_eq⟩ := Finset.card_eq_one.mp hcardinf_eq
  have hQ₀_res : Q₀.restrict K F = P₀ := (hmemS₀ Q₀).mp (hS₀_eq ▸ Finset.mem_singleton_self Q₀)
  have hQinf_res : Qinf.restrict K F = Pinf :=
    (hmemSinf Qinf).mp (hSinf_eq ▸ Finset.mem_singleton_self Qinf)
  have hQ₀_ram : Place.ramificationIdx F Q₀ = n := by simpa [hS₀_eq] using hsum₀_eq
  have hQinf_ram : Place.ramificationIdx F Qinf = n := by simpa [hSinf_eq] using hsuminf_eq
  have hQ_ne : Q₀ ≠ Qinf := fun h ↦ hP0_ne_inf (hQ₀_res ▸ h ▸ hQinf_res)
  -- Riemann–Roch on `Qinf - Q₀` produces `z ∈ Lˣ` with `(z) = Q₀ - Qinf`.
  let D : Divisor K L := WeilDivisor.ofPoint Qinf - WeilDivisor.ofPoint Q₀
  have hdegD : Divisor.degree D = 0 := by
    rw [Divisor.degree_sub, Divisor.degree_ofPoint, Divisor.degree_ofPoint,
      Qinf.degree_eq_one_of_isAlgClosed_of_isFunctionField hL,
      Q₀.degree_eq_one_of_isAlgClosed_of_isFunctionField hL, sub_self]
  have hdimD : (Divisor.dim D : ℤ) = 1 := by
    have := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hL hexL
      (D := D) (by rw [hgenus, hdegD]; norm_num)
    omega
  obtain ⟨z, hzD, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hL D).mp (by omega))
  let E : Divisor K L := Divisor.principal hL (Units.mk0 z hz0) + D
  have hE_nonneg : 0 ≤ E := (mem_riemannRochSpace_units_iff hL).mp hzD
  have hE_zero : E = 0 :=
    (Divisor.eq_of_le_of_degree_eq hL hE_nonneg (by simp [E, hdegD])).symm
  have hprin_z : Divisor.principal hL (Units.mk0 z hz0) =
      WeilDivisor.ofPoint Q₀ - WeilDivisor.ofPoint Qinf := by
    have := eq_neg_of_add_eq_zero_left hE_zero
    simpa [D, sub_eq_add_neg, add_comm] using this
  -- Compare `z ^ n` with `RatFunc.X`: their quotient `u` has no poles, hence lies in `K`.
  let uX : Lˣ := Units.map (algebraMap F L).toMonoidHom (Units.mk0 RatFunc.X RatFunc.X_ne_zero)
  let u : Lˣ := Units.mk0 z hz0 ^ n * uX⁻¹
  have hu_ord : ∀ Q : Place K L, Q.ord (u : L) = 0 := by
    intro Q
    have hzn : Q.ord ((Units.mk0 z hz0 ^ n : Lˣ) : L) =
        (n : ℤ) * (Divisor.principal hL (Units.mk0 z hz0)).coeff Q := by
      rw [Units.val_pow_eq_pow_val, Q.ord_pow, ← Divisor.coeff_principal]
    have huX : Q.ord ((uX : Lˣ) : L) =
        (Place.ramificationIdx F Q : ℤ) * (Q.restrict K F).ord RatFunc.X := by
      change Q.ord (algebraMap F L RatFunc.X) = _
      exact Place.ord_algebraMap_restrict K F Q RatFunc.X
    rw [Units.val_mul, Q.ord_mul (Units.ne_zero _) (Units.ne_zero _), Units.val_inv_eq_inv_val,
      Q.ord_inv, hzn, huX, hprin_z]
    by_cases hQ0 : Q = Q₀
    · subst hQ0
      rw [hQ₀_res, hP0_ord]
      simp [hQ_ne, hQ₀_ram]
    · by_cases hQi : Q = Qinf
      · subst hQi
        rw [hQinf_res, hPinf_ord]
        simp [Ne.symm hQ_ne, hQinf_ram]
      · have hnot0 : Q.restrict K F ≠ P₀ := fun h ↦ hQ0 <|
          Finset.mem_singleton.mp (hS₀_eq ▸ (hmemS₀ Q).mpr h)
        have hnoti : Q.restrict K F ≠ Pinf := fun h ↦ hQi <|
          Finset.mem_singleton.mp (hSinf_eq ▸ (hmemSinf Q).mpr h)
        simp [hQ0, hQi, Place.ord_X_eq_zero_of_ne hnot0 hnoti]
  have hu_poles : Divisor.poles hL u = 0 := by
    apply WeilDivisor.ext
    intro Q
    rw [Divisor.coeff_poles, hu_ord Q, WeilDivisor.coeff_zero]
    norm_num
  have hu_alg : IsAlgebraic K (u : L) := by
    by_contra htr
    have htr' : Transcendental K (u : L) := htr
    have : FiniteDimensional K⟮(u : L)⟯ L := hL.finiteDimensional_adjoin htr'
    have hdeg := Divisor.degree_poles hL u htr'
    rw [hu_poles, Divisor.degree_zero] at hdeg
    have hpos : 0 < Module.finrank K⟮(u : L)⟯ L := Module.finrank_pos
    omega
  obtain ⟨c, hc⟩ := isIntegrallyClosedIn_iff_forall_isAlgebraic.mp hexL (u : L) hu_alg
  have hc0 : c ≠ 0 := fun h ↦ u.ne_zero (hc ▸ h ▸ map_zero _)
  -- Extract an `n`-th root `d` of `c` in the algebraically closed field `K`.
  obtain ⟨d, hd⟩ : ∃ d : K, d ^ n = c := by
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_root (X ^ n - C c)
      (by rw [degree_X_pow_sub_C hn_pos]; exact_mod_cast hn_pos.ne')
    exact ⟨d, sub_eq_zero.mp (by simpa using hd)⟩
  refine ⟨algebraMap K L d⁻¹ * z, ?_⟩
  have hzu : z ^ n = (u : L) * algebraMap F L RatFunc.X := by
    change z ^ n = ((Units.mk0 z hz0 ^ n * uX⁻¹ : Lˣ) : L) * (uX : L)
    rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one, Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [mul_pow, ← map_pow, inv_pow, hd, hzu, ← hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0,
    map_one, one_mul]

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
  have hyT : y ^ n = algebraMap K[T;T⁻¹] L (LaurentPolynomial.T 1) := by
    rw [hy, IsScalarTower.algebraMap_apply K[T;T⁻¹] F L]
    exact congrArg (algebraMap F L) (laurentToRatFunc_T_one K).symm
  -- `A` is integrally closed in `L`, so `y` comes from an `n`-th root `a ∈ A` of `T 1`.
  have hinjAL : Function.Injective (algebraMap A L) :=
    Algebra.TensorProduct.includeRight_injective (laurentToRatFunc_injective K)
  have : Algebra.IsIntegral K[T;T⁻¹] A := Algebra.IsIntegral.of_finite K[T;T⁻¹] A
  have : IsFractionRing A L := isFractionRing_ratFuncTensor K A
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
    change (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹])).map (laurentToRatFunc K).toRingHom = _
    simp [laurentToRatFunc_T_one]
  let eB : AdjoinRoot (X ^ n - C (RatFunc.X : F)) ≃ₐ[F] F ⊗[K[T;T⁻¹]] B :=
    (AdjoinRoot.mapAlgEquiv (AlgEquiv.refl : F ≃ₐ[F] F) _ _
      (.of_eq (by simpa using hmap.symm))).trans
      (AdjoinRoot.algebraTensorAlgEquiv F (X ^ n - C (LaurentPolynomial.T 1 : K[T;T⁻¹]))).symm
  have hψF_bij : Function.Bijective ψF := by
    have hcomp_bij : Function.Bijective (ψF.comp eB.toAlgHom) :=
      ((ψF.comp eB.toAlgHom).toLinearMap.linearEquivOfInjective
        (ψF.comp eB.toAlgHom).toRingHom.injective
        (finrank_adjoinRoot_X_pow_sub_C_X K n)).bijective
    exact (Function.Bijective.of_comp_iff ψF eB.bijective).mp hcomp_bij
  -- Smooth base change commutes with integral closure, making `ψ` bijective on `A`.
  have : Algebra.Etale K[T;T⁻¹] B := by
    have hu : IsUnit ((n : K)) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
    exact standardTameCover_etale (LaurentPolynomial.isUnit_T 1)
      (by simpa [LaurentPolynomial.C_eq_algebraMap] using
        hu.map (LaurentPolynomial.C : K →+* K[T;T⁻¹]))
  have hinjBL : Function.Injective
      (Algebra.TensorProduct.includeRight : B →ₐ[K[T;T⁻¹]] F ⊗[K[T;T⁻¹]] B) :=
    Algebra.TensorProduct.includeRight_injective (laurentToRatFunc_injective K)
  refine ⟨n, hn, ⟨AlgEquiv.ofBijective ψ ⟨fun b₁ b₂ hb ↦ hinjBL ?_, fun x ↦ ?_⟩⟩⟩
  · refine hψF_bij.1 ?_
    change ψF (1 ⊗ₜ b₁) = ψF (1 ⊗ₜ b₂)
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hb]
  · let eFL : F ⊗[K[T;T⁻¹]] B ≃ₐ[F] L := AlgEquiv.ofBijective ψF hψF_bij
    have hxint : IsIntegral K[T;T⁻¹] (eFL.symm (1 ⊗ₜ x)) :=
      ((Algebra.IsIntegral.isIntegral (R := K[T;T⁻¹]) x).map
        (Algebra.TensorProduct.includeRight : A →ₐ[K[T;T⁻¹]] L)).map
          (eFL.symm.toAlgHom.restrictScalars K[T;T⁻¹])
    obtain ⟨b, hb⟩ := hxint.exists_includeRight_eq
    refine ⟨b, hinjAL ?_⟩
    change (1 : F) ⊗ₜ[K[T;T⁻¹]] ψ b = 1 ⊗ₜ x
    have h1 : ψF (1 ⊗ₜ b) = 1 ⊗ₜ ψ b := by rw [Algebra.TensorProduct.map_tmul]; rfl
    rw [← h1, ← Algebra.TensorProduct.includeRight_apply, hb]
    exact eFL.apply_symm_apply (1 ⊗ₜ x)

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
  let eRing := PrimeSpectrum.ringEquivPiQuotientConnectedComponentsIdeal (R := A)
  let eAlg : A ≃ₐ[K[T;T⁻¹]]
      ∀ C : ConnectedComponents (PrimeSpectrum A),
        A ⧸ PrimeSpectrum.connectedComponentsIdeal C :=
    { eRing with
      commutes' r := funext fun C ↦ by
        change eRing (algebraMap K[T;T⁻¹] A r) C = _
        rw [PrimeSpectrum.ringEquivPiQuotientConnectedComponentsIdeal_apply]
        rfl }
  have hcomp : ∀ C : ConnectedComponents (PrimeSpectrum A),
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        (standardTameCover K[T;T⁻¹] (LaurentPolynomial.T 1) n ≃ₐ[K[T;T⁻¹]]
          A ⧸ PrimeSpectrum.connectedComponentsIdeal C) := by
    intro C
    have : Module.Finite K[T;T⁻¹] (A ⧸ PrimeSpectrum.connectedComponentsIdeal C) :=
      Module.Finite.of_surjective
        (Ideal.Quotient.mkₐ K[T;T⁻¹] (PrimeSpectrum.connectedComponentsIdeal C)).toLinearMap
        Ideal.Quotient.mk_surjective
    have : Algebra.Etale K[T;T⁻¹] (A ⧸ PrimeSpectrum.connectedComponentsIdeal C) := by
      obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe C
      have heq :
          PrimeSpectrum.connectedComponentsIdeal (p : ConnectedComponents (PrimeSpectrum A)) =
            Ideal.span {1 - PrimeSpectrum.connectedComponentIdempotent p} :=
        (PrimeSpectrum.connectedComponentsIdeal_mk p).trans
          (PrimeSpectrum.connectedComponentIdeal_eq_span p)
      have : Algebra.Etale K[T;T⁻¹]
          (A ⧸ Ideal.span {1 - PrimeSpectrum.connectedComponentIdempotent p}) :=
        Algebra.Etale.quotient_span_singleton
          (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent p).one_sub
      exact Algebra.Etale.of_equiv (Ideal.quotientEquivAlgOfEq K[T;T⁻¹] heq.symm)
    exact exists_algEquiv_standardTameCover_of_etale K
      (A ⧸ PrimeSpectrum.connectedComponentsIdeal C)
  choose e he_ne hφ using hcomp
  let m := Fintype.card (ConnectedComponents (PrimeSpectrum A))
  let σ : Fin m ≃ ConnectedComponents (PrimeSpectrum A) := (Fintype.equivFin _).symm
  refine (isFiniteProductOfStandardTameCovers_iff (LaurentPolynomial.T 1)).mpr
    ⟨Fin m, inferInstance, fun i ↦ e (σ i),
      fun i ↦ Nat.one_le_iff_ne_zero.mpr (he_ne (σ i)),
      fun i ↦ ?_, ⟨?_⟩⟩
  · have hu : IsUnit ((e (σ i) : K)) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (he_ne (σ i)))
    simpa [LaurentPolynomial.C_eq_algebraMap] using
      hu.map (LaurentPolynomial.C : K →+* K[T;T⁻¹])
  · exact eAlg.trans <|
      (AlgEquiv.piCongrLeft' K[T;T⁻¹]
        (fun C ↦ A ⧸ PrimeSpectrum.connectedComponentsIdeal C) (Fintype.equivFin _)).trans <|
        AlgEquiv.piCongrRight fun i ↦ (Classical.choice (hφ (σ i))).symm

end Classification

end RatFuncModel

end TauCeti
