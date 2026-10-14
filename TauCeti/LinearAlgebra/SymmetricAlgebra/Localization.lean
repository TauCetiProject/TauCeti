/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.BaseChange
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Symmetric powers of localized modules

Symmetric powers commute with extension of scalars and hence with localization. Here the
comparison applies to an arbitrary map exhibiting scalar extension, rather than only to the
tensor-product model. Its characteristic equation identifies it with the map induced by the
original module map on homogeneous symmetric-algebra elements. Consequently the induced
semilinear map on each homogeneous piece is a localization map.
-/

public section

open scoped TensorProduct
open TauCeti.SymmetricAlgebra

noncomputable section

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module A N]
  [IsScalarTower R A N] {f : M →ₗ[R] N}

namespace IsBaseChange

-- The scalar-extension comparison, pure-tensor formula, and localization proof follow the
-- proof pattern in `TauCeti/LinearAlgebra/ExteriorPower/Localization.lean`. The comparison uses
-- `TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange` and `SymmetricAlgebra.map`.
/-- Scalar extension of a symmetric power along any map exhibiting scalar extension.
No flatness or finite-generation assumption is required. -/
def symmetricPowerEquiv (h : IsBaseChange A f) (n : ℕ) :
    A ⊗[R] homogeneousSubmodule R M n ≃ₗ[A] homogeneousSubmodule A N n :=
  (homogeneousSubmoduleEquivBaseChange n).symm.trans
    ((SymmetricAlgebra.mapEquiv A h.equiv).toLinearEquiv.ofSubmodules _ _ (by
      apply le_antisymm
      · rintro y ⟨x, hx, rfl⟩
        simpa only [LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
          SymmetricAlgebra.mapEquiv_apply, SetLike.mem_coe] using
          map_mem_homogeneousSubmodule h.equiv.toLinearMap hx
      · intro y hy
        refine ⟨(SymmetricAlgebra.mapEquiv A h.equiv).symm y, ?_, ?_⟩
        · simpa only [SymmetricAlgebra.mapEquiv_symm, SymmetricAlgebra.mapEquiv_apply,
            SetLike.mem_coe] using
            map_mem_homogeneousSubmodule h.equiv.symm.toLinearMap hy
        · exact (SymmetricAlgebra.mapEquiv A h.equiv).apply_symm_apply y))

/-- The symmetric-power comparison is the ambient scalar-extension comparison followed by
the symmetric-algebra map of the scalar-extension equivalence. -/
@[simp]
theorem coe_symmetricPowerEquiv_apply (h : IsBaseChange A f) (n : ℕ)
    (x : A ⊗[R] homogeneousSubmodule R M n) :
    (h.symmetricPowerEquiv n x : SymmetricAlgebra A N) =
      SymmetricAlgebra.map A h.equiv.toLinearMap
        (scalarTensorBialgEquiv (k := R) (K := A)
          ((homogeneousSubmodule R M n).subtype.baseChange A x)) := by
  simp only [symmetricPowerEquiv, LinearEquiv.trans_apply, LinearEquiv.ofSubmodules_apply,
    AlgEquiv.toLinearEquiv_apply, SymmetricAlgebra.mapEquiv_apply]
  exact congrArg (SymmetricAlgebra.map A h.equiv.toLinearMap)
    (coe_homogeneousSubmoduleEquivBaseChange_symm_apply n x)

/-- On pure tensors the comparison is the scaled map of symmetric algebras induced by
the original module map. The semilinear presentation and its agreement with the linear map
are explicit arguments; the equation also applies to degree zero. -/
theorem coe_symmetricPowerEquiv_tmul (h : IsBaseChange A f) (n : ℕ)
    (f' : M →ₛₗ[algebraMap R A] N) (hf : ∀ m, f' m = f m)
    (a : A) (x : homogeneousSubmodule R M n) :
    (h.symmetricPowerEquiv n (a ⊗ₜ[R] x) : SymmetricAlgebra A N) =
      a • SymmetricAlgebra.mapₛₗ f' x.1 := by
  have he : (SymmetricAlgebra.map A h.equiv.toLinearMap : _ →+* _).comp
      ((scalarTensorBialgEquiv (k := R) (K := A)).toAlgEquiv.toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom) = SymmetricAlgebra.mapₛₗ f' := by
    apply SymmetricAlgebra.ringHom_ext
    · ext r
      calc
        _ = SymmetricAlgebra.map A h.equiv.toLinearMap
            (scalarTensorBialgEquiv (k := R) (K := A)
              (algebraMap R (A ⊗[R] SymmetricAlgebra R M) r)) :=
          congrArg (fun z ↦ SymmetricAlgebra.map A h.equiv.toLinearMap
            (scalarTensorBialgEquiv (k := R) (K := A) z))
              (Algebra.TensorProduct.includeRight.commutes r)
        _ = SymmetricAlgebra.map A h.equiv.toLinearMap
            (algebraMap A _ (algebraMap R A r)) := by
          rw [IsScalarTower.algebraMap_apply R A (A ⊗[R] SymmetricAlgebra R M)]
          exact congrArg (SymmetricAlgebra.map A h.equiv.toLinearMap)
            ((scalarTensorBialgEquiv (k := R) (K := A)).toAlgEquiv.commutes _)
        _ = _ := (AlgHom.commutes _ _).trans (SymmetricAlgebra.mapₛₗ_algebraMap f' r).symm
    · intro m
      simp [Algebra.TensorProduct.includeRight_apply, hf, h.equiv_tmul]
  have ht : a ⊗ₜ[R] x.1 = a • (1 ⊗ₜ[R] x.1) := by simp [TensorProduct.smul_tmul']
  rw [coe_symmetricPowerEquiv_apply, LinearMap.baseChange_tmul]
  simp only [Submodule.subtype_apply]
  rw [ht, map_smul, map_smul]
  exact congrArg (a • ·) (RingHom.congr_fun he x.1)

variable {M' N' : Type*} [AddCommMonoid M'] [Module R M'] [AddCommMonoid N']
  [Module R N'] [Module A N'] [IsScalarTower R A N'] {f' : M' →ₗ[R] N'}

/-- The symmetric-power scalar-extension comparison is natural in commuting maps of the
original and extended modules. -/
theorem symmetricPowerEquiv_naturality (h : IsBaseChange A f) (h' : IsBaseChange A f')
    (n : ℕ) (g : M →ₗ[R] M') (g' : N →ₗ[A] N')
    (comm : (g'.restrictScalars R) ∘ₗ f = f' ∘ₗ g) :
    (homogeneousSubmoduleMapₛₗ g' n) ∘ₗ (h.symmetricPowerEquiv n).toLinearMap =
      (h'.symmetricPowerEquiv n).toLinearMap ∘ₗ
        (homogeneousSubmoduleMapₛₗ g n).baseChange A := by
  have hc : g' ∘ₗ h.equiv.toLinearMap = h'.equiv.toLinearMap ∘ₗ g.baseChange A := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, IsBaseChange.equiv_tmul,
      LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply, map_smul] using
      congrArg (a • ·) (LinearMap.congr_fun comm m)
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      coe_homogeneousSubmoduleMapₛₗ_apply, coe_symmetricPowerEquiv_apply,
      LinearMap.baseChange_tmul, Submodule.subtype_apply, SymmetricAlgebra.mapₛₗ_eq_map,
      RingHom.coe_coe]
    rw [← AlgHom.comp_apply, SymmetricAlgebra.map_comp_map, hc,
      ← SymmetricAlgebra.map_comp_map, AlgHom.comp_apply]
    apply congrArg (SymmetricAlgebra.map A h'.equiv.toLinearMap)
    simpa only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgEquiv.toAlgHom_apply, BialgEquiv.coe_toAlgEquiv] using
      (AlgHom.congr_fun (g.scalarTensorBialgEquiv_comp_map (S := A)) (a ⊗ₜ[R] x.1)).symm

end IsBaseChange

namespace LinearMap

variable {S : Submonoid R} [IsLocalization S A] (f) [IsLocalizedModule S f]

/-- A map on homogeneous symmetric-algebra pieces agreeing with the map induced by a
localization of modules is itself a localization. The target scalar action is retained
explicitly so that this applies to restriction-of-scalars module presentations. -/
theorem isLocalizedModule_symmetricPower (n : ℕ)
    [symR : Module R (homogeneousSubmodule A N n)]
    [symTower : @IsScalarTower R A (homogeneousSubmodule A N n) _
      (homogeneousSubmodule A N n).module.toSMul symR.toSMul]
    (f' : M →ₛₗ[algebraMap R A] N) (hf : ∀ m, f' m = f m)
    (g : homogeneousSubmodule R M n →ₗ[R] homogeneousSubmodule A N n)
    (hg : ∀ x, (g x : SymmetricAlgebra A N) = SymmetricAlgebra.mapₛₗ f' x.1) :
    IsLocalizedModule S g := by
  -- Use Mathlib's scalar-extension characterization `isLocalizedModule_iff_isBaseChange`.
  rw [@isLocalizedModule_iff_isBaseChange R _ S A _ _ _
    (homogeneousSubmodule R M n) _ _ (homogeneousSubmodule A N n) _ symR _ symTower g]
  refine @IsBaseChange.of_equiv R (homogeneousSubmodule R M n)
    (homogeneousSubmodule A N n) A _ _ _ _ _ _ symR _ symTower g
    ((IsLocalizedModule.isBaseChange S A f).symmetricPowerEquiv n) ?_
  intro x
  apply Subtype.ext
  simpa only [IsBaseChange.coe_symmetricPowerEquiv_tmul _ n f' hf, one_smul] using (hg x).symm

end LinearMap
