/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Localization of Kähler differentials

Let `A` be an `R`-algebra and `F` a commutative `A`-algebra. For a localization `B` of `A`
receiving a compatible map to `F`, the image of `Ω[B⁄R]` in `Ω[F⁄R]` is the localization of
the image of `Ω[A⁄R]`. Consequently, a differential in `Ω[F⁄R]` comes from `Ω[A⁄R]` if and
only if it comes from the differentials of `A` localized at every maximal ideal. No
domain, fraction-field, perfectness, finite type, or Noetherian hypothesis is needed.

The main application is to a domain `A` with fraction field `F`: there the criterion says that
regularity of a rational differential can be checked in the local rings of `A`. When
`Ω[A⁄R]` is torsion-free, for instance when `A` is formally smooth over `R`, the map
`Ω[A⁄R] → Ω[F⁄R]` is injective, so regular differentials can be treated as rational
differentials. This injectivity is not restated here: it follows from Mathlib's
`IsLocalizedModule.injective_iff_isRegular`, applied to the instance
`KaehlerDifferential.isLocalizedModule_map`, together with
`Module.Flat.isSMulRegular_of_nonZeroDivisors` in the formally smooth case.

In a pushout `B = S ⊗[R] A` of commutative rings and a prime `q` of `B` over `p = q ∩ A`, Kähler
differentials commute with base change and localization:
`B_q ⊗[A_p] Ω[A_p ⁄ R] ≃ₗ[B_q] Ω[B_q ⁄ S]`.

## Main results

* `TauCeti.KaehlerDifferential.range_map_eq_localized₀_range`: localization of differentials
  localizes their image in the target differential module.
* `TauCeti.KaehlerDifferential.mem_range_map_iff_forall_isMaximal`: membership in the global
  image can be checked using any family of maximal localizations.
* `TauCeti.KaehlerDifferential.atPrimePushoutEquiv`: base change and localization of Kähler
  differentials at a prime in a pushout `B = S ⊗[R] A`, with pure-tensor formula
  `TauCeti.KaehlerDifferential.atPrimePushoutEquiv_tmul_D`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 8.
* The Stacks Project, Tag 00RM (localization of differentials) and Tag 031J
  (projectivity of differentials of a formally smooth algebra).
-/

public section

noncomputable section

namespace TauCeti

open KaehlerDifferential TensorProduct
open scoped nonZeroDivisors

namespace KaehlerDifferential

section Localization

variable (R A B F : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing F]
  [Algebra R A] [Algebra R B] [Algebra R F] [Algebra A B] [Algebra A F]
  [Algebra B F] [IsScalarTower R A B] [IsScalarTower R A F]
  [IsScalarTower R B F] [IsScalarTower A B F]

/-- The image of the differentials of `S⁻¹A` in `Ω[F⁄R]` is the localization at `S` of the
image of the differentials of `A`. Here `F` is any commutative algebra receiving `B`, and
the equality is in `A`-submodules of `Ω[F⁄R]`. -/
theorem range_map_eq_localized₀_range (S : Submonoid A) [IsLocalization S B] :
    haveI := isLocalizedModule_id S Ω[F⁄R] B
    ((map R R B F).restrictScalars A).range =
      (map R R A F).range.localized₀ S (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R]) := by
  have : IsLocalizedModule S (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R]) :=
    isLocalizedModule_id S Ω[F⁄R] B
  have hmap : IsLocalizedModule.map S (map R R A B)
      (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R]) (map R R A F) =
        (map R R B F).restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext S (map R R A B)
      (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R])
    rw [IsLocalizedModule.map_comp]
    apply LinearMap.ext_on (span_range_derivation R A)
    rintro _ ⟨a, rfl⟩
    simp [map_D, ← IsScalarTower.algebraMap_apply A B F]
  rw [← hmap]
  exact LinearMap.range_localizedMap_eq_localized₀_range _ _ _ _

section Maximal

variable (Aₚ : ∀ (P : Ideal A) [P.IsMaximal], Type*)
  [∀ (P : Ideal A) [P.IsMaximal], CommRing (Aₚ P)]
  [∀ (P : Ideal A) [P.IsMaximal], Algebra A (Aₚ P)]
  [∀ (P : Ideal A) [P.IsMaximal], IsLocalization.AtPrime (Aₚ P) P]
  [∀ (P : Ideal A) [P.IsMaximal], Algebra R (Aₚ P)]
  [∀ (P : Ideal A) [P.IsMaximal], Algebra (Aₚ P) F]
  [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R A (Aₚ P)]
  [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R (Aₚ P) F]
  [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower A (Aₚ P) F]

/-- A differential in `Ω[F⁄R]` comes from `Ω[A⁄R]` exactly when it comes from the
differentials of every maximal localization, using any family of localization models
mapping compatibly to `F`. -/
theorem mem_range_map_iff_forall_isMaximal (ω : Ω[F⁄R]) :
    ω ∈ (map R R A F).range ↔
      ∀ (P : Ideal A) [P.IsMaximal],
        ω ∈ ((map R R (Aₚ P) F).restrictScalars A).range := by
  have hlocal (P : Ideal A) [P.IsMaximal] :
      IsLocalizedModule P.primeCompl (LinearMap.id : Ω[F⁄R] →ₗ[A] Ω[F⁄R]) :=
    isLocalizedModule_id P.primeCompl Ω[F⁄R] (Aₚ P)
  refine ⟨fun h P _ ↦ ?_, fun h ↦ ?_⟩
  · rw [range_map_eq_localized₀_range R A (Aₚ P) F P.primeCompl]
    exact ⟨ω, h, 1, by simp⟩
  · -- Pass the localization family explicitly: instance synthesis does not recover this
    -- higher-order family from `hlocal`. Name the module and map families to fix their roles.
    refine @Submodule.mem_of_localization_maximal (R := A) (M := Ω[F⁄R])
      (Mₚ := fun _ _ ↦ Ω[F⁄R]) (f := fun _ _ ↦ LinearMap.id) _ _ _ _ _ hlocal ω _
      fun P _ ↦ ?_
    rw [← range_map_eq_localized₀_range R A (Aₚ P) F P.primeCompl]
    exact h P

end Maximal

end Localization

section Pushout

variable (R S A : Type*) {B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

/-- In a pushout `B = S ⊗[R] A`, `B_q ⊗[A_{q ∩ A}] Ω[A_{q ∩ A} ⁄ R] ≃ₗ[B_q] Ω[B_q ⁄ S]`. -/
def atPrimePushoutEquiv (q : Ideal B) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    (Localization.AtPrime q ⊗[Localization.AtPrime (q.under A)]
      Ω[Localization.AtPrime (q.under A)⁄R]) ≃ₗ[Localization.AtPrime q]
      Ω[Localization.AtPrime q⁄S] :=
  let p := q.under A
  let Ap := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.FormallyEtale A Ap := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have : Algebra.FormallyEtale B Bq := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  AlgebraTensorModule.congr (LinearEquiv.refl Bq Bq)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A Ap).symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A Ap Bq Bq Ω[A⁄R] ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A B Bq Bq Ω[A⁄R]).symm ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl Bq Bq)
      (KaehlerDifferential.tensorKaehlerEquiv R S A B) ≪≫ₗ
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale S B Bq

/-- Evaluating `atPrimePushoutEquiv` on a pure tensor `b ⊗ₜ D R A_p a`. -/
@[simp]
theorem atPrimePushoutEquiv_tmul_D (q : Ideal B) [q.IsPrime]
    (b : Localization.AtPrime q) (a : Localization.AtPrime (q.under A)) :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    atPrimePushoutEquiv R S A q (b ⊗ₜ D R (Localization.AtPrime (q.under A)) a) =
      b • D S (Localization.AtPrime q)
        (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q) a) := by
  let p := q.under A
  let Ap := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.FormallyEtale A Ap := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have : Algebra.FormallyEtale B Bq := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have hAlg (x : A) :
      atPrimePushoutEquiv R S A q (1 ⊗ₜ D R Ap (algebraMap A Ap x)) =
        D S Bq (algebraMap Ap Bq (algebraMap A Ap x)) := by
    dsimp only [atPrimePushoutEquiv, Ap, Bq, p]
    simp only [LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
      AlgebraTensorModule.cancelBaseChange_tmul,
      AlgebraTensorModule.cancelBaseChange_symm_tmul,
      KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
    congr 1
    rw [← IsScalarTower.algebraMap_apply A B Bq, ← IsScalarTower.algebraMap_apply A Ap Bq]
  have hOne : atPrimePushoutEquiv R S A q (1 ⊗ₜ D R Ap a) =
      D S Bq (algebraMap Ap Bq a) := by
    obtain ⟨⟨a', s⟩, ha⟩ := IsLocalization.surj p.primeCompl a
    have hD : (algebraMap A Ap (s : A)) • D R Ap a =
        D R Ap (algebraMap A Ap a') - a • D R Ap (algebraMap A Ap (s : A)) := by
      have hmul := congrArg (D R Ap) ha
      rw [Derivation.leibniz, add_comm] at hmul
      exact eq_sub_of_add_eq hmul
    have hEq : (algebraMap Ap Bq (algebraMap A Ap (s : A))) •
        atPrimePushoutEquiv R S A q (1 ⊗ₜ D R Ap a) =
        (algebraMap Ap Bq (algebraMap A Ap (s : A))) • D S Bq (algebraMap Ap Bq a) := by
      calc (algebraMap Ap Bq (algebraMap A Ap (s : A))) •
            atPrimePushoutEquiv R S A q (1 ⊗ₜ D R Ap a)
          = atPrimePushoutEquiv R S A q
              (((algebraMap A Ap (s : A)) • (1 : Bq)) ⊗ₜ[Ap] D R Ap a) := by
            rw [← (atPrimePushoutEquiv R S A q).map_smul, TensorProduct.smul_tmul',
              algebraMap_smul Bq]
        _ = atPrimePushoutEquiv R S A q
              (1 ⊗ₜ[Ap] ((algebraMap A Ap (s : A)) • D R Ap a)) := by
            rw [TensorProduct.smul_tmul]
        _ = D S Bq (algebraMap Ap Bq (algebraMap A Ap a')) -
              (algebraMap Ap Bq a) • D S Bq (algebraMap Ap Bq (algebraMap A Ap (s : A))) := by
            rw [hD, TensorProduct.tmul_sub, map_sub, hAlg,
              ← TensorProduct.smul_tmul, ← algebraMap_smul Bq a (1 : Bq),
              ← TensorProduct.smul_tmul', (atPrimePushoutEquiv R S A q).map_smul, hAlg]
        _ = (algebraMap Ap Bq (algebraMap A Ap (s : A))) • D S Bq (algebraMap Ap Bq a) := by
            have hmulB : algebraMap Ap Bq (algebraMap A Ap a') =
                algebraMap Ap Bq a * algebraMap Ap Bq (algebraMap A Ap (s : A)) := by
              rw [← ha, map_mul]
            rw [hmulB, Derivation.leibniz, add_sub_cancel_left]
    have hu : IsUnit (algebraMap Ap Bq (algebraMap A Ap (s : A))) :=
      (IsLocalization.map_units Ap s).map (algebraMap Ap Bq)
    exact (IsUnit.smul_left_cancel hu).mp hEq
  rw [show (b ⊗ₜ[Ap] D R Ap a) = b • (1 ⊗ₜ[Ap] D R Ap a) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    (atPrimePushoutEquiv R S A q).map_smul, hOne]

end Pushout

end KaehlerDifferential

end TauCeti
