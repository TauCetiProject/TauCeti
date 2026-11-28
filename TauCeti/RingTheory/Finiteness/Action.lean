/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import TauCeti.RingTheory.KrullDimension.Basic
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Algebras acting on a module finite over the base

Let an `R`-algebra `S` act on an `R`-module `M` compatibly with scalars. The image of
`Algebra.lsmul R R M` is the quotient of `S` by the annihilator of `M`. If `M` is Noetherian
over `R`, this action image is Noetherian over `R`. Already for finitely generated `M`,
the image is integral. Lying over then identifies the base support with the image of the
support over `S`, and the two supports have the same dimension.

For a finite base module, if `S` is a domain of finite Krull dimension and the base support
has dimension at least `dim S`, the action is faithful. If the base module is Noetherian,
then `S` itself is finite over `R`.
This is the dimension argument in M. Kisin, *Moduli of finite flat group schemes, and modularity*,
Lemma 3.3.4.
-/

public section

namespace Module

section Action

variable (R S M : Type*) [CommSemiring R] [Ring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The action identifies the quotient by the annihilator with its image in the algebra
of base-linear endomorphisms. -/
noncomputable def quotientAnnihilatorEquivRangeLsmul :
    (S ⧸ annihilator S M) ≃ₐ[R] (Algebra.lsmul R R M (A := S)).range := by
  let f := Algebra.lsmul R R M (A := S)
  have h : annihilator S M = RingHom.ker f := by
    ext s
    exact mem_annihilator.trans (LinearMap.ext_iff (f := f s) (g := 0)).symm
  exact (Ideal.quotientEquivAlgOfEq R h).trans (Ideal.quotientKerEquivRange f)

/-- The class of a scalar acts by multiplication by that scalar. -/
@[simp]
theorem quotientAnnihilatorEquivRangeLsmul_mk (s : S) :
    quotientAnnihilatorEquivRangeLsmul R S M (Ideal.Quotient.mk _ s) =
      (Algebra.lsmul R R M).rangeRestrict s := by
  simp [quotientAnnihilatorEquivRangeLsmul, Ideal.quotientKerEquivRange]

/-- The inverse sends a scalar action to the class of any representative. -/
@[simp]
theorem quotientAnnihilatorEquivRangeLsmul_symm_rangeRestrict (s : S) :
    (quotientAnnihilatorEquivRangeLsmul R S M).symm ((Algebra.lsmul R R M).rangeRestrict s) =
      Ideal.Quotient.mk _ s := by
  rw [AlgEquiv.symm_apply_eq, quotientAnnihilatorEquivRangeLsmul_mk]

end Action

section Finiteness

variable (R S M : Type*) [CommRing R] [Ring S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The effective action algebra on a finitely generated module is integral over the base. -/
theorem isIntegral_quotient_annihilator [Module.Finite R M] :
    Algebra.IsIntegral R (S ⧸ annihilator S M) :=
  (quotientAnnihilatorEquivRangeLsmul R S M).isIntegral_iff.mpr inferInstance

/-- The effective action algebra of a Noetherian base module is Noetherian as a base module. -/
theorem isNoetherian_quotient_annihilator [IsNoetherian R M] :
    IsNoetherian R (S ⧸ annihilator S M) := by
  let e := quotientAnnihilatorEquivRangeLsmul R S M
  exact isNoetherian_of_injective ((Algebra.lsmul R R M (A := S)).range.val.toLinearMap ∘ₗ
    e.toLinearMap) (Subtype.val_injective.comp e.injective)

end Finiteness

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

open PrimeSpectrum

/-- For a module finite over the base, the image of its support under contraction is exactly
its support over the base, even when the algebra acting on it is not finite. -/
theorem image_comap_support_of_finite [Module.Finite R M] :
    comap (algebraMap R S) '' support S M = support R M := by
  let A := R ⧸ annihilator R M
  let B := S ⧸ annihilator S M
  have : Module.Finite S M := .of_restrictScalars_finite R S M
  have : (annihilator S M).LiesOver (annihilator R M) := ⟨comap_annihilator.symm⟩
  have : Algebra.IsIntegral R B := isIntegral_quotient_annihilator R S M
  have : Algebra.IsIntegral A B := .tower_top R
  have hsurj := Algebra.IsIntegral.comap_surjective A B
  calc
    _ = Set.range (comap (algebraMap R B)) := by
      rw [support_eq_zeroLocus, ← range_comap_quotientMk_eq_zeroLocus, ← Set.range_comp,
        IsScalarTower.algebraMap_eq R S B, comap_comp]
      rfl
    _ = Set.range (comap (algebraMap R A)) := by
      rw [IsScalarTower.algebraMap_eq R A B, comap_comp, hsurj.range_comp]
    _ = _ := (range_comap_quotientMk_eq_zeroLocus _).trans support_eq_zeroLocus.symm

/-- Restricting scalars preserves support dimension when the module is finite over the base. -/
theorem supportDim_eq_of_restrictScalars_finite [Module.Finite R M] :
    supportDim S M = supportDim R M := by
  have : Module.Finite S M := .of_restrictScalars_finite R S M
  have : (annihilator S M).LiesOver (annihilator R M) := ⟨comap_annihilator.symm⟩
  have := isIntegral_quotient_annihilator R S M
  have : Algebra.IsIntegral (R ⧸ annihilator R M) (S ⧸ annihilator S M) := .tower_top R
  rw [supportDim_eq_ringKrullDim_quotient_annihilator,
    supportDim_eq_ringKrullDim_quotient_annihilator]
  exact TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul

/-- A finite-dimensional domain acting on a finite base module acts faithfully if the base
support has dimension at least that of the domain. -/
theorem faithfulSMul_of_ringKrullDim_le_supportDim
    [Module.Finite R M] [IsDomain S] [FiniteRingKrullDim S]
    (hdim : ringKrullDim S ≤ supportDim R M) : FaithfulSMul S M := by
  have : Module.Finite S M := .of_restrictScalars_finite R S M
  rw [← supportDim_eq_of_restrictScalars_finite R S M,
    supportDim_eq_ringKrullDim_quotient_annihilator] at hdim
  have hinj := (RingHom.injective_iff_ringKrullDim_le_of_surjective
    (Ideal.Quotient.mk (annihilator S M)) Ideal.Quotient.mk_surjective).2 hdim
  apply annihilator_eq_bot.mp
  simpa only [Ideal.mk_ker] using (RingHom.injective_iff_ker_eq_bot _).1 hinj

/-- If the base module is Noetherian and its support has dimension at least that of the
finite-dimensional acting domain, the domain is finite over the base and acts faithfully. -/
theorem finite_and_faithfulSMul_of_ringKrullDim_le_supportDim
    [IsNoetherian R M] [IsDomain S] [FiniteRingKrullDim S]
    (hdim : ringKrullDim S ≤ supportDim R M) : Module.Finite R S ∧ FaithfulSMul S M := by
  have hfaith := faithfulSMul_of_ringKrullDim_le_supportDim R S M hdim
  have hann := annihilator_eq_bot.mpr hfaith
  have : IsNoetherian R (S ⧸ annihilator S M) := isNoetherian_quotient_annihilator R S M
  have hfin := IsNoetherian.finite R (S ⧸ annihilator S M)
  rw [hann] at hfin
  exact ⟨Module.Finite.equiv (AlgEquiv.quotientBot R S).toLinearEquiv, hfaith⟩

/-- A finite-dimensional domain acting on a Noetherian module faithful over the base
is finite over the base and acts faithfully if its dimension is at most that of the base. -/
theorem finite_and_faithfulSMul_of_ringKrullDim_le
    [IsDomain S] [FiniteRingKrullDim S] [IsNoetherian R M] [FaithfulSMul R M]
    (hdim : ringKrullDim S ≤ ringKrullDim R) : Module.Finite R S ∧ FaithfulSMul S M := by
  have hs : supportDim R M = ringKrullDim R := by
    rw [supportDim_eq_ringKrullDim_quotient_annihilator,
      annihilator_eq_bot.mpr (inferInstance : FaithfulSMul R M)]
    exact (RingEquiv.quotientBot R).ringKrullDim
  exact finite_and_faithfulSMul_of_ringKrullDim_le_supportDim R S M (hdim.trans_eq hs.symm)

end Module
