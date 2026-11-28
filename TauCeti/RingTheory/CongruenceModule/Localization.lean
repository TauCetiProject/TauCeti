/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CongruenceModule.Basic
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.Algebra.Module.Torsion.Localization
import TauCeti.RingTheory.Localization.Ideal

/-!
# Localization of congruence modules

Let `φ : A →ₐ[O] O` be an augmentation. Localizing `A` at elements whose images under
`φ` are units in `O` preserves the congruence module and ideal when `ker φ` is finitely
generated. The quotient by the action of `ker φ` and the submodule killed by `ker φ`
are already local for these denominators, as their scalar actions factor through `O`.
This lets one pass to the local Hecke factor at the residual eigensystem over a local
coefficient ring while keeping the same coefficient ring and congruence module.
The extended augmentation is supplied by `IsLocalization.liftAlgHom` whenever the
denominators map to units.

The congruence module here is the codimension-zero construction of
Iyengar, Khare and Manning, *Congruence modules and the Wiles–Lenstra–Diamond numerical
criterion in higher codimensions*, §2.2, <https://doi.org/10.1007/s00222-024-01292-y>.
-/

public section

open Submodule

namespace AlgHom

variable {O A B : Type*} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
  [Algebra O B] [Algebra A B] [IsScalarTower O A B]
  (φ : A →ₐ[O] O) (S : Submonoid A) [IsLocalization S B]
  (ψ : B →ₐ[O] O) (hψ : ψ.comp (IsScalarTower.toAlgHom O A B) = φ)

variable {φ ψ} in
include hψ in
private theorem isUnit_augmentation_of_mem (s : S) : IsUnit (φ s) := by
  rw [← hψ]
  exact IsLocalization.isUnit_comp S ψ.toRingHom s

variable {φ ψ} in
include S hψ in
private theorem ker_eq_map_of_localized_augmentation :
    RingHom.ker ψ = (RingHom.ker φ).map (algebraMap A B) := by
  simpa only [RingHom.ker_coe_toRingHom] using
    (ψ : B →+* O).ker_eq_map_of_isLocalization S (φ := (φ : A →+* O))
      (congrArg AlgHom.toRingHom hψ)

variable {M N : Type*} [AddCommGroup M] [Module O M] [Module A M] [IsScalarTower O A M]
  [AddCommGroup N] [Module O N] [Module A N] [Module B N] [IsScalarTower O A N]
  [IsScalarTower O B N] [IsScalarTower A B N]
  (f : M →ₗ[A] N) [IsLocalizedModule S f]

/-- The localization map carries the submodule killed by `ker φ` isomorphically onto the
submodule killed by `ker ψ`, provided `ker φ` is finitely generated. -/
noncomputable def torsionByKerLocalizationEquiv (hfin : (RingHom.ker φ).FG) :
    torsionBySet A M (RingHom.ker φ) ≃ₗ[O] torsionBySet B N (RingHom.ker ψ) :=
  letI := φ.isLocalizedModule_id_of_isTorsionBySet_ker S (isUnit_augmentation_of_mem S hψ)
    (torsionBySet_isTorsionBySet (R := A) (M := M) (RingHom.ker φ))
  ((IsLocalizedModule.linearEquiv S LinearMap.id
      ((torsionBySet A M (RingHom.ker φ)).toLocalized' B S f)).restrictScalars O).trans
    ((LinearEquiv.ofEq _ _ (by
      rw [ker_eq_map_of_localized_augmentation S hψ,
        localized'_torsionBySet_ideal S f _ hfin])).restrictScalars O)

/-- On the submodule killed by the augmentation kernel, the comparison is the original
localization map. -/
@[simp]
theorem coe_torsionByKerLocalizationEquiv_apply (hfin : (RingHom.ker φ).FG)
    (x : torsionBySet A M (RingHom.ker φ)) :
    ↑(φ.torsionByKerLocalizationEquiv S ψ hψ f hfin x) = f (x : M) := by
  let := φ.isLocalizedModule_id_of_isTorsionBySet_ker S (isUnit_augmentation_of_mem S hψ)
    (torsionBySet_isTorsionBySet (R := A) (M := M) (RingHom.ker φ))
  have hx := IsLocalizedModule.linearEquiv_apply S LinearMap.id
    ((torsionBySet A M (RingHom.ker φ)).toLocalized' B S f) x
  simpa [torsionByKerLocalizationEquiv] using congrArg Subtype.val hx

/-- The localization map induces an equivalence of the quotients by the augmentation
kernels acting on the two modules. -/
noncomputable def quotientKerSMulLocalizationEquiv :
    (M ⧸ (RingHom.ker φ • ⊤ : Submodule A M)) ≃ₗ[O]
      (N ⧸ (RingHom.ker ψ • ⊤ : Submodule B N)) :=
  letI := φ.isLocalizedModule_id_of_isTorsionBySet_ker S (isUnit_augmentation_of_mem S hψ)
    (Module.isTorsionBySet_quotient_ideal_smul M (RingHom.ker φ))
  ((IsLocalizedModule.linearEquiv S LinearMap.id
      ((RingHom.ker φ • ⊤ : Submodule A M).toLocalizedQuotient' B S f)).restrictScalars O).trans
    ((Submodule.quotEquivOfEq _ _ (by
      rw [ker_eq_map_of_localized_augmentation S hψ,
        localized'_smul, localized'_top, Ideal.localized'_eq_map])).restrictScalars O)

/-- The comparison of quotients by the kernel actions sends the class of `x` to that of
`f x`. -/
@[simp]
theorem quotientKerSMulLocalizationEquiv_mk (x : M) :
    φ.quotientKerSMulLocalizationEquiv S ψ hψ f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := by
  let := φ.isLocalizedModule_id_of_isTorsionBySet_ker S (isUnit_augmentation_of_mem S hψ)
    (Module.isTorsionBySet_quotient_ideal_smul M (RingHom.ker φ))
  have hx := IsLocalizedModule.linearEquiv_apply S LinearMap.id
    ((RingHom.ker φ • ⊤ : Submodule A M).toLocalizedQuotient' B S f) (Submodule.Quotient.mk x)
  simp only [LinearMap.id_apply] at hx
  simp [quotientKerSMulLocalizationEquiv, hx]

/-- The comparison of quotients by the kernel actions identifies their quotients by
`O`-torsion. -/
noncomputable def quotientKerSMulTorsionLocalizationEquiv :
    ((M ⧸ (RingHom.ker φ • ⊤ : Submodule A M)) ⧸
      torsion O (M ⧸ (RingHom.ker φ • ⊤ : Submodule A M))) ≃ₗ[O]
      ((N ⧸ (RingHom.ker ψ • ⊤ : Submodule B N)) ⧸
        torsion O (N ⧸ (RingHom.ker ψ • ⊤ : Submodule B N))) :=
  let e := φ.quotientKerSMulLocalizationEquiv S ψ hψ f
  Submodule.Quotient.equiv _ _ e (by
    rw [Submodule.map_equiv_eq_comap_symm]
    exact TauCeti.Submodule.comap_torsion_of_comp_eq_smul
      (f := e.symm.toLinearMap) (g := e.toLinearMap) (a := 1) (by simp) (fun x => by simp))

/-- The comparison of the torsion-free quotients is induced by `f` on representatives. -/
@[simp]
theorem quotientKerSMulTorsionLocalizationEquiv_mk (x : M) :
    φ.quotientKerSMulTorsionLocalizationEquiv S ψ hψ f
        (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (Submodule.Quotient.mk (f x)) := by
  simp [quotientKerSMulTorsionLocalizationEquiv]

/-- Localization intertwines the two maps that define the congruence modules. -/
theorem congruenceMap_localization (hfin : (RingHom.ker φ).FG) :
    (φ.quotientKerSMulTorsionLocalizationEquiv S ψ hψ f).toLinearMap ∘ₗ φ.congruenceMap M =
      ψ.congruenceMap N ∘ₗ (φ.torsionByKerLocalizationEquiv S ψ hψ f hfin).toLinearMap := by
  ext x
  simp

/-- Localizing at denominators sent to units by an augmentation preserves the associated
congruence module over `O` when the augmentation kernel is finitely generated. -/
noncomputable def congruenceModuleLocalizationEquiv (hfin : (RingHom.ker φ).FG) :
    φ.congruenceModule M ≃ₗ[O] ψ.congruenceModule N :=
  Submodule.Quotient.equiv _ _ (φ.quotientKerSMulTorsionLocalizationEquiv S ψ hψ f) (by
    rw [← LinearMap.range_comp, φ.congruenceMap_localization S ψ hψ f hfin,
      LinearEquiv.range_comp])

/-- The congruence-module comparison is induced by the localization map on representatives. -/
@[simp]
theorem congruenceModuleLocalizationEquiv_congruenceModuleMk
    (hfin : (RingHom.ker φ).FG) (x : M) :
    φ.congruenceModuleLocalizationEquiv S ψ hψ f hfin (φ.congruenceModuleMk M x) =
      ψ.congruenceModuleMk N (f x) := by
  simp [congruenceModuleLocalizationEquiv, congruenceModuleMk_apply]

include S hψ in
/-- The congruence ideal is unchanged under localization at denominators sent to units
by the augmentation, provided its kernel is finitely generated. -/
theorem congruenceIdeal_eq_of_localization (hfin : (RingHom.ker φ).FG) :
    φ.congruenceIdeal = ψ.congruenceIdeal := by
  let f := Algebra.linearMap A B
  let e := φ.congruenceModuleLocalizationEquiv S ψ hψ f hfin
  ext x
  have hx := e.map_eq_zero_iff (x := φ.congruenceModuleMk A (algebraMap O A x))
  simpa [e, f, congruenceModuleMk_self_eq_zero_iff, ← IsScalarTower.algebraMap_apply O A B]
    using hx.symm

end AlgHom
