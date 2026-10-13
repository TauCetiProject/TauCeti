/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BaseChange

/-!
# Extension of scalars and symmetric powers

Symmetric powers commute with extension of scalars along arbitrary homomorphisms of
commutative rings. The natural comparison constructed here is induced by the unit of the
extension--restriction adjunction on homogeneous symmetric-algebra elements. It is the module
calculation used for pullback of symmetric powers of quasicoherent sheaves on affine schemes.

The comparison uses `TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange`;
its categorical packaging follows `TauCeti.extendScalarsExteriorPowerNatIso`. The identity law
uses Mathlib's canonical `ModuleCat.extendScalarsId`. No flatness or finiteness assumption is
needed.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Exercise 5.16.
-/

public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingHom

universe u₁ u₂ v

noncomputable section

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

/-- Symmetric powers commute with extension of scalars along any ring homomorphism. -/
def extendScalarsSymmetricPowerIso (n : ℕ) (M : ModuleCat.{max u₁ v} R) :
    (ModuleCat.extendScalars f).obj (M.symmetricPower n) ≅
      ((ModuleCat.extendScalars f).obj M).symmetricPower n := by
  let _ := f.toAlgebra
  exact (TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange (R := R)
    (S := S) (M := M) n).symm.toModuleIso

/-- After inclusion in the symmetric algebra, the comparison is the ambient
scalar-extension equivalence on the extended homogeneous piece. -/
theorem coe_extendScalarsSymmetricPowerIso_hom_apply (n : ℕ)
    (M : ModuleCat.{max u₁ v} R)
    (x : (ModuleCat.extendScalars f).obj (M.symmetricPower n)) :
    ((f.extendScalarsSymmetricPowerIso n M).hom.hom x :
        SymmetricAlgebra S ((ModuleCat.extendScalars f).obj M)) =
      (letI := f.toAlgebra
       TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv (k := R) (K := S)
         ((TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n).subtype.baseChange S x)) := by
  let _ := f.toAlgebra
  -- Unwrap the categorical isomorphism to identify the degreewise linear equivalence.
  change ((TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange
    (R := R) (S := S) (M := M) n).symm x : SymmetricAlgebra S (S ⊗[R] M)) = _
  exact TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleEquivBaseChange_symm_apply
    (R := R) (S := S) (M := M) n x

/-- On pure tensors the comparison is the ambient symmetric-algebra comparison. -/
@[simp]
theorem coe_extendScalarsSymmetricPowerIso_hom_tmul (n : ℕ)
    (M : ModuleCat.{max u₁ v} R) (s : S) (x : M.symmetricPower n) :
    ((f.extendScalarsSymmetricPowerIso n M).hom.hom (s ⊗ₜ[R,f] x) :
        SymmetricAlgebra S ((ModuleCat.extendScalars f).obj M)) =
      (letI := f.toAlgebra
       TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv (k := R) (K := S) (s ⊗ₜ[R] x.1)) := by
  let _ := f.toAlgebra
  -- Compute through the degreewise linear equivalence, avoiding the categorical scalar wrappers.
  change ((TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange
    (R := R) (S := S) (M := M) n).symm (s ⊗ₜ[R] x) : SymmetricAlgebra S (S ⊗[R] M)) = _
  simpa only [LinearMap.baseChange_tmul, Submodule.subtype_apply] using
    TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleEquivBaseChange_symm_apply
      (R := R) (S := S) (M := M) n (s ⊗ₜ[R] x)

/-- The inverse comparison is the inverse ambient scalar-extension equivalence,
after inclusion of the extended homogeneous piece. -/
theorem subtype_baseChange_extendScalarsSymmetricPowerIso_inv_apply (n : ℕ)
    (M : ModuleCat.{max u₁ v} R)
    (x : ((ModuleCat.extendScalars f).obj M).symmetricPower n) :
    letI := f.toAlgebra
    (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n).subtype.baseChange S
        ((f.extendScalarsSymmetricPowerIso n M).inv.hom x) =
      (TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv (k := R) (K := S)).symm x.1 := by
  let _ := f.toAlgebra
  -- Unwrap the inverse categorical comparison to use the degreewise inclusion formula.
  change (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n).subtype.baseChange S
    (TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange
      (R := R) (S := S) (M := M) n x) = _
  exact TauCeti.SymmetricAlgebra.subtype_baseChange_homogeneousSubmoduleEquivBaseChange
    (R := R) (S := S) (M := M) n x

/-- The comparison is natural in the original module. -/
@[reassoc]
theorem extendScalarsSymmetricPowerIso_hom_naturality (n : ℕ)
    {M N : ModuleCat.{max u₁ v} R} (g : M ⟶ N) :
    (ModuleCat.extendScalars f).map (ModuleCat.symmetricPower.map g n) ≫
        (f.extendScalarsSymmetricPowerIso n N).hom =
      (f.extendScalarsSymmetricPowerIso n M).hom ≫
        ModuleCat.symmetricPower.map ((ModuleCat.extendScalars f).map g) n := by
  let _ := f.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  apply Subtype.ext
  -- `erw` crosses the categorical scalar wrappers before computing the module maps.
  erw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul,
    ModuleCat.symmetricPower.coe_map_apply]
  erw [coe_extendScalarsSymmetricPowerIso_hom_tmul.{u₁, u₂, v},
    coe_extendScalarsSymmetricPowerIso_hom_tmul.{u₁, u₂, v},
    ModuleCat.symmetricPower.coe_map_apply]
  have h := AlgHom.congr_fun (g.hom.scalarTensorBialgEquiv_comp_map (S := S))
    ((1 : S) ⊗ₜ[R] x.1)
  -- Identify the underlying map by the named pure-tensor formulas, rather than
  -- unfolding the restriction-of-scalars module structure used by the functor.
  have hg : ((ModuleCat.extendScalars f).map g).hom = g.hom.baseChange S := by
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul s m =>
      exact (ModuleCat.ExtendScalars.map_tmul f g s m).trans
        (LinearMap.baseChange_tmul (A := S) g.hom s m).symm
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  erw [hg]
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    AlgEquiv.toAlgHom_apply, BialgEquiv.coe_toAlgEquiv] at h
  exact h

/-- The natural scalar-extension comparison for symmetric powers of arbitrary modules. -/
def extendScalarsSymmetricPowerNatIso (n : ℕ) :
    ModuleCat.symmetricPower.functor.{max u₁ v} R n ⋙
        ModuleCat.extendScalars.{u₁, u₂, max u₁ v} f ≅
      ModuleCat.extendScalars.{u₁, u₂, max u₁ v} f ⋙
        ModuleCat.symmetricPower.functor.{max u₁ u₂ v} S n :=
  NatIso.ofComponents (extendScalarsSymmetricPowerIso.{u₁, u₂, v} f n)
    (fun g ↦ extendScalarsSymmetricPowerIso_hom_naturality.{u₁, u₂, v} f n g)

/-- The forward components of the natural comparison. -/
@[simp]
theorem extendScalarsSymmetricPowerNatIso_hom_app (n : ℕ)
    (M : ModuleCat.{max u₁ v} R) :
    (extendScalarsSymmetricPowerNatIso.{u₁, u₂, v} f n).hom.app M =
      (f.extendScalarsSymmetricPowerIso n M).hom :=
  (rfl)

/-- The inverse components of the natural comparison. -/
@[simp]
theorem extendScalarsSymmetricPowerNatIso_inv_app (n : ℕ)
    (M : ModuleCat.{max u₁ v} R) :
    (extendScalarsSymmetricPowerNatIso.{u₁, u₂, v} f n).inv.app M =
      (f.extendScalarsSymmetricPowerIso n M).inv :=
  (rfl)

end

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- The symmetric-power comparison respects Mathlib's identity comparison for
extension of scalars. -/
theorem extendScalarsSymmetricPowerNatIso_id (n : ℕ) :
    (extendScalarsSymmetricPowerNatIso.{u, u, v} (RingHom.id R) n).hom ≫
        Functor.whiskerRight (ModuleCat.extendScalarsId.{u, max u v} R).hom
          (ModuleCat.symmetricPower.functor R n) ≫
        (ModuleCat.symmetricPower.functor R n).leftUnitor.hom =
      Functor.whiskerLeft (ModuleCat.symmetricPower.functor R n)
          (ModuleCat.extendScalarsId.{u, max u v} R).hom ≫
        (ModuleCat.symmetricPower.functor R n).rightUnitor.hom := by
  let _ := (RingHom.id R).toAlgebra
  apply NatTrans.ext
  funext M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app]
  -- Reduce the composite functor objects so extension-of-scalars extensionality applies.
  dsimp only [Functor.comp_obj, ModuleCat.symmetricPower.functor_obj]
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  let a : (ModuleCat.extendScalars (RingHom.id R)).obj M →ₗ[R] M :=
    ((ModuleCat.extendScalarsId R).hom.app M).hom
  let e := TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv (k := R) (K := R) (M := M)
  have h : (SymmetricAlgebra.map R a).toRingHom.comp
      (e.toAlgEquiv.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) =
        RingHom.id (SymmetricAlgebra R M) := by
    apply SymmetricAlgebra.ringHom_ext
    · ext r
      -- The ring-homomorphism composites have the same underlying algebra maps.
      change (SymmetricAlgebra.map R a)
        (e (Algebra.TensorProduct.includeRight (algebraMap R _ r))) = algebraMap R _ r
      rw [Algebra.TensorProduct.includeRight_apply,
        ← Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra,
        RingHom.id_apply]
      simp only [e]
      erw [TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv_tmul_one, AlgHom.commutes]
    · intro m
      -- Evaluate the ambient comparison on a generator.
      change (SymmetricAlgebra.map R a) (e ((1 : R) ⊗ₜ[R] SymmetricAlgebra.ι R M m)) =
        SymmetricAlgebra.ι R M m
      simp only [e, TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv_tmul_ι]
      erw [SymmetricAlgebra.map_apply_ι]
      exact congrArg (SymmetricAlgebra.ι R M)
        (ModuleCat.extendScalarsId_hom_app_one_tmul M m)
  apply Subtype.ext
  -- `erw` crosses the categorical scalar wrappers before computing components.
  erw [ModuleCat.comp_apply]
  simp only [extendScalarsSymmetricPowerNatIso_hom_app]
  erw [ModuleCat.symmetricPower.coe_map_apply,
    coe_extendScalarsSymmetricPowerIso_hom_tmul.{u, u, v}]
  have hx : (SymmetricAlgebra.map R a) (e ((1 : R) ⊗ₜ[R] x.1)) = x.1 :=
    RingHom.congr_fun h x.1
  erw [ModuleCat.comp_apply, ModuleCat.id_apply,
    ModuleCat.extendScalarsId_hom_app_one_tmul]
  exact hx

end

end RingHom
