/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalProperties.Submodule
import TauCeti.RingTheory.Finiteness.Nakayama
import TauCeti.RingTheory.Localization.Module

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

Differentials forming a basis along a closed subscheme `V(J)` form a basis on a neighbourhood
of it: if `Ω[A⁄R]` is finite projective and the classes of `D xᵢ` form a basis of
`Ω[A⁄R] ⧸ J • Ω[A⁄R]` over `A ⧸ J`, then the `D xᵢ` form a basis of `Ω[A[1/g]⁄R]` for some
`g ≡ 1 (mod J)`. This is Nakayama's lemma for the map `Aⁿ → Ω[A⁄R]` they define.

## Main results

* `TauCeti.KaehlerDifferential.range_map_eq_localized₀_range`: localization of differentials
  localizes their image in the target differential module.
* `TauCeti.KaehlerDifferential.mem_range_map_iff_forall_isMaximal`: membership in the global
  image can be checked using any family of maximal localizations.
* `TauCeti.KaehlerDifferential.linearMap_eq_of_D_algebraMap`: `Aₘ`-linear maps out of
  `Ω[Aₘ⁄R]` agree once they agree on `D R Aₘ (algebraMap A Aₘ x)`.
* `TauCeti.KaehlerDifferential.atPrimePushoutEquiv`: base change and localization of Kähler
  differentials at a prime in a pushout `B = S ⊗[R] A`, with pure-tensor formula
  `TauCeti.KaehlerDifferential.atPrimePushoutEquiv_tmul_D`.
* `TauCeti.KaehlerDifferential.exists_sub_one_mem_and_basis_localizationAway`: if `Ω[A⁄R]` is
  finite projective and differentials `D xᵢ` reduce to a basis of `Ω[A⁄R] ⧸ J • Ω[A⁄R]`, they
  form a basis of `Ω[A[1/g]⁄R]` for some `g ≡ 1 (mod J)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 8.
* The Stacks Project, Tag 00RM (localization of differentials) and Tag 031J
  (projectivity of differentials of a formally smooth algebra).
* The Stacks Project, Lemma 15.9.14 (Tag 07M7): the proof of its free case contains the step
  where a lifted basis of `Ω[A⁄R] ⧸ J • Ω[A⁄R]` becomes a basis after inverting some
  `g ≡ 1 (mod J)`.
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

/-- Two `Aₘ`-linear maps out of `Ω[Aₘ⁄R]` agree everywhere once they agree on
`D R Aₘ (algebraMap A Aₘ x)` for all `x : A`. -/
theorem linearMap_eq_of_D_algebraMap {R A Aₘ N : Type*}
    [CommRing R] [CommRing A] [CommRing Aₘ] [Algebra R A] [Algebra A Aₘ] [Algebra R Aₘ]
    [IsScalarTower R A Aₘ] (M : Submonoid A) [IsLocalization M Aₘ]
    [AddCommGroup N] [Module Aₘ N] {f g : Ω[Aₘ⁄R] →ₗ[Aₘ] N}
    (h : ∀ x : A, f (D R Aₘ (algebraMap A Aₘ x)) = g (D R Aₘ (algebraMap A Aₘ x))) :
    f = g := by
  let : Module A N := Module.compHom N (algebraMap A Aₘ)
  have : IsScalarTower A Aₘ N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsLocalizedModule M (LinearMap.id : N →ₗ[A] N) := isLocalizedModule_id M N Aₘ
  have hfg : f.restrictScalars A = g.restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext M (map R R A Aₘ) (LinearMap.id : N →ₗ[A] N)
    apply LinearMap.ext_on (span_range_derivation R A)
    rintro _ ⟨x, rfl⟩
    simpa [map_D] using h x
  exact LinearMap.ext fun ω ↦ LinearMap.congr_fun hfg ω

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
  let lhs : Ω[Ap⁄R] →ₗ[Ap] Ω[Bq⁄S] :=
    ((atPrimePushoutEquiv R S A q).toLinearMap.restrictScalars Ap).comp
      (TensorProduct.mk Ap Bq Ω[Ap⁄R] 1)
  let rhs : Ω[Ap⁄R] →ₗ[Ap] Ω[Bq⁄S] := KaehlerDifferential.map R S Ap Bq
  have hAlg (x : A) : lhs (D R Ap (algebraMap A Ap x)) = rhs (D R Ap (algebraMap A Ap x)) := by
    dsimp only [lhs, rhs, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_toLinearMap, TensorProduct.mk_apply, atPrimePushoutEquiv, Ap, Bq, p]
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
    simpa [lhs, rhs] using LinearMap.congr_fun
      (linearMap_eq_of_D_algebraMap p.primeCompl hAlg) (D R Ap a)
  calc
    atPrimePushoutEquiv R S A q (b ⊗ₜ D R Ap a)
      = atPrimePushoutEquiv R S A q (b • (1 ⊗ₜ[Ap] D R Ap a)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = b • atPrimePushoutEquiv R S A q (1 ⊗ₜ D R Ap a) :=
        (atPrimePushoutEquiv R S A q).map_smul b _
    _ = b • D S Bq (algebraMap Ap Bq a) := by rw [hOne]

end Pushout

section Basis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Differentials forming a basis along `V(J)` form a basis nearby.** Let `Ω[A⁄R]` be finite
projective, as when `A` is smooth over `R`, and let `D xᵢ` be differentials whose classes form a
basis of `Ω[A⁄R] ⧸ J • Ω[A⁄R]` over `A ⧸ J`. Then for some `g ≡ 1 (mod J)` the `D xᵢ` form a basis
of `Ω[A[1/g]⁄R]`.

This is a step of the proof of Stacks Lemma 15.9.14 (Tag 07M7). The proof is adapted from the end
of Mathlib's `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`, with the prime replaced by the
condition `g ≡ 1 (mod J)`. -/
theorem exists_sub_one_mem_and_basis_localizationAway [Module.Finite A Ω[A⁄R]]
    [Module.Projective A Ω[A⁄R]] (J : Ideal A) {ι : Type*} [Finite ι] {x : ι → A}
    (b : Module.Basis ι (A ⧸ J) (Ω[A⁄R] ⧸ J • (⊤ : Submodule A Ω[A⁄R])))
    (hb : ∀ i, b i = Submodule.Quotient.mk (D R A (x i))) :
    ∃ g : A, g - 1 ∈ J ∧ ∃ b' : Module.Basis ι (Localization.Away g) Ω[Localization.Away g⁄R],
      ∀ i, b' i = D R _ (algebraMap A _ (x i)) := by
  classical
  have := Fintype.ofFinite ι
  let mkQ := (J • (⊤ : Submodule A Ω[A⁄R])).mkQ
  let φ : (ι →₀ A) →ₗ[A] Ω[A⁄R] := Finsupp.linearCombination A fun i ↦ D R A (x i)
  have hφ (v : ι →₀ A) : mkQ (φ v) = ∑ i, Ideal.Quotient.mk J (v i) • b i := by
    simp [mkQ, φ, Finsupp.linearCombination_apply, Finsupp.sum_fintype, hb, map_sum]
  -- `φ` is surjective modulo `J`, and its kernel lies in `J • Aⁿ` as `b` is linearly independent.
  have hrange : LinearMap.range φ ⊔ J • ⊤ = ⊤ := by
    refine eq_top_iff.mpr fun ω _ ↦ ?_
    choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (b.repr (mkQ ω) i)
    let v : ι →₀ A := Finsupp.equivFunOnFinite.symm c
    have hv : mkQ (ω - φ v) = 0 := by
      rw [map_sub, hφ, sub_eq_zero]
      simp [v, hc]
    rw [← sub_add_cancel ω (φ v)]
    exact add_mem (Submodule.mem_sup_right ((Submodule.Quotient.mk_eq_zero _).mp hv))
      (Submodule.mem_sup_left ⟨v, rfl⟩)
  have hker : LinearMap.ker φ ≤ J • ⊤ := fun v hv ↦ by
    have hvi (i : ι) : v i ∈ J := by
      have := hφ v
      rw [LinearMap.mem_ker.mp hv, map_zero, eq_comm] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        (Fintype.linearIndependent_iff.mp b.linearIndependent _ this i)
    rw [← Finsupp.sum_single v, Finsupp.sum]
    exact sum_mem fun i _ ↦ by
      simpa using
        Submodule.smul_mem_smul (hvi i) (Submodule.mem_top (x := Finsupp.single i (1 : A)))
  -- Nakayama's lemma gives `g ≡ 1 (mod J)` such that `φ` is bijective after inverting `g`.
  obtain ⟨g, hgJ, hgr, hgk⟩ :=
    φ.exists_sub_one_mem_and_smul_mem_range_and_smul_eq_zero J hrange hker
  let W := Localization.Away g
  let l₁ : (ι →₀ A) →ₗ[A] (ι →₀ W) := Finsupp.mapRange.linearMap (Algebra.linearMap A W)
  let l₂ : Ω[A⁄R] →ₗ[A] Ω[W⁄R] := map R R A W
  let φW : (ι →₀ W) →ₗ[W] Ω[W⁄R] := IsLocalizedModule.mapExtendScalars (.powers g) l₁ l₂ W φ
  have hφW : Function.Bijective φW :=
    (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ l₂).mpr
      (LocalizedModule.bijective_map_of_smul_mem_range (Submonoid.mem_powers g) hgr hgk)
  refine ⟨g, hgJ, .ofRepr (LinearEquiv.ofBijective φW hφW).symm, fun i ↦ ?_⟩
  simp [W, φW, l₁, l₂, IsLocalizedModule.map_linearCombination, φ]

end Basis

end KaehlerDifferential

end TauCeti
