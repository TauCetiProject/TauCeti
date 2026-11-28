/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.BaseChange
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
public import TauCeti.CategoryTheory.Monoidal.Internal.Module
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Monoidal comparison for base change of commutative algebras

Extension of scalars of commutative `R`-algebras `CommAlgCat.extendScalars R S` is naturally
isomorphic to the functor induced on commutative monoid objects in `ModuleCat` by
`ModuleCat.extendScalars (algebraMap R S)` (`CommAlgCat.extendScalarsIsoMapCommMon`).
-/

public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings MonObj

universe u

namespace CommAlgCat

/-- Component isomorphism identifying `S ⊗[R] A` with the commutative algebra attached to
`(ModuleCat.extendScalars (algebraMap R S)).mapCommMon`. -/
private noncomputable def extendScalarsObjIsoMapCommMonObj (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : CommAlgCat.{u} R) :
    (extendScalars.{u, u, u} R S).obj A ≅
      ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.obj
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapCommMon.obj
          (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj A)) :=
  let φ := algebraMap R S
  let G := ModuleCat.extendScalars.{u, u, u} φ
  let A₀ := ModuleCat.of R A
  let A' := ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj A
  let B := ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.obj (G.mapCommMon.obj A')
  let eLin : (S ⊗[R] A) ≃ₗ[S] B :=
    (ModuleCat.extendScalarsAlgebraMapIso (S := S) A₀).symm.toLinearEquiv
  let he (s : S) (a : A) :
      eLin (s ⊗ₜ[R] a) = (s ⊗ₜ[R, φ] (a : A'.X) : ↑(G.obj A'.X)) :=
    ModuleCat.extendScalarsAlgebraMapIso_inv_tmul A₀ s a
  let eAlg : (S ⊗[R] A) ≃ₐ[S] B :=
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct eLin
      (fun s₁ s₂ a₁ a₂ ↦ by
        symm
        rw [ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor_obj_mapCommMon_mul,
          he s₁ a₁, he s₂ a₂]
        erw [ModuleCat.extendScalars_μ_tmul φ A'.X A'.X s₁ s₂ a₁ a₂,
          ModuleCat.ExtendScalars.map_tmul]
        dsimp only [A']
        rw [ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse_obj_mul]
        erw [ConcreteCategory.hom_ofHom, LinearMap.mul'_apply, ← he])
      (by
        symm
        rw [ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor_obj_mapCommMon_one]
        erw [ModuleCat.extendScalars_ε_apply φ 1, ModuleCat.ExtendScalars.map_tmul]
        dsimp only [A']
        rw [ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse_obj_one]
        erw [ConcreteCategory.hom_ofHom, Algebra.linearMap_apply, map_one, ← he])
  isoMk eAlg

private theorem extendScalarsObjIsoMapCommMonObj_hom_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : CommAlgCat.{u} R) (s : S) (a : A) :
    dsimp% only (extendScalarsObjIsoMapCommMonObj R S A).hom (s ⊗ₜ[R] a) =
      s ⊗ₜ[R, algebraMap R S] a :=
  (Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply
    (C := ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.obj
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapCommMon.obj
        (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj A))) _ _ _ _).trans
    (ModuleCat.extendScalarsAlgebraMapIso_inv_tmul (ModuleCat.of R A) s a)

/-- Extension of scalars of commutative `R`-algebras along `algebraMap R S` is naturally
isomorphic to the functor induced by `ModuleCat.extendScalars (algebraMap R S)` on commutative
monoid objects. -/
noncomputable def extendScalarsIsoMapCommMon (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] :
    extendScalars.{u, u, u} R S ≅
      ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙
        (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapCommMon ⋙
          ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor :=
  NatIso.ofComponents (extendScalarsObjIsoMapCommMonObj R S) fun {A B} f ↦ by
    have htmul (s : S) (a : A) :
        (extendScalarsObjIsoMapCommMonObj R S B).hom.hom
            (Algebra.TensorProduct.map (AlgHom.id S S) f.hom (s ⊗ₜ[R] a)) =
          ((ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙
              (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapCommMon ⋙
                ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor).map f).hom
            ((extendScalarsObjIsoMapCommMonObj R S A).hom.hom (s ⊗ₜ[R] a)) := by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        extendScalarsObjIsoMapCommMonObj_hom_tmul, extendScalarsObjIsoMapCommMonObj_hom_tmul]
      symm
      refine (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor_map_apply _ _).trans ?_
      exact ModuleCat.ExtendScalars.map_tmul (algebraMap R S)
        (ModuleCat.ofHom f.hom.toLinearMap) s a
    apply hom_ext
    apply AlgHom.toRingHom_injective
    apply Algebra.TensorProduct.ringHom_ext
    · ext s
      simpa [hom_comp, Algebra.TensorProduct.includeLeftRingHom_apply] using htmul s 1
    · ext a
      simpa [hom_comp] using htmul 1 a

-- Normalize `CommAlgCat.of` carrier projections so `@[simp]` matches after projection reduction.
/-- `extendScalarsIsoMapCommMon` sends `s ⊗ a` to `s ⊗ a`. -/
@[simp]
theorem extendScalarsIsoMapCommMon_hom_app_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : CommAlgCat.{u} R) (s : S) (a : A) :
    dsimp% only [Functor.comp_obj] ((extendScalarsIsoMapCommMon R S).hom.app A) (s ⊗ₜ[R] a) =
      s ⊗ₜ[R, algebraMap R S] a :=
  extendScalarsObjIsoMapCommMonObj_hom_tmul R S A s a

/-- The inverse of `extendScalarsIsoMapCommMon` sends `s ⊗ a` to `s ⊗ a`. -/
@[simp]
theorem extendScalarsIsoMapCommMon_inv_app_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : CommAlgCat.{u} R) (s : S) (a : A) :
    dsimp% only [Functor.comp_obj]
        ((extendScalarsIsoMapCommMon R S).inv.app A) (s ⊗ₜ[R, algebraMap R S] a) =
      s ⊗ₜ[R] a :=
  (congrArg ((extendScalarsIsoMapCommMon R S).inv.app A)
    (extendScalarsIsoMapCommMon_hom_app_tmul R S A s a).symm).trans
    (ConcreteCategory.congr_hom ((extendScalarsIsoMapCommMon R S).hom_inv_id_app A) (s ⊗ₜ[R] a))

end CommAlgCat
