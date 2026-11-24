/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Finite
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Preadditive
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Functoriality

/-!
# Modules over a finite algebra are comodules over its dual coalgebra

The linear dual `A^∨ = ConvolutionDual R A` of a finite projective `R`-algebra `A` is a
coalgebra, with comultiplication transposed from the multiplication of `A`. This file shows that
left `A`-modules are the same as right `A^∨`-comodules. An algebra action `ρ : A → End_R M`
gives the coaction
`m ↦ ∑ᵢ ρ(eᵢ) m ⊗ eᵢ^∨`
for any finite family `eᵢ ∈ A`, `eᵢ^∨ ∈ A^∨` reconstructing each element of `A`, in
particular for a basis and its dual basis. Conversely, contracting a coaction against evaluation
at `a ∈ A` gives the action of `a`. No finiteness condition is imposed on the module. An algebra
morphism `f : A → B` dualizes to a coalgebra morphism `B^∨ → A^∨`, and restricting an action
along `f` corresponds to corestricting the coaction along it; `f` need not be injective or
surjective.

This is the finite-dimensional step of reconstructing an abelian category with a fibre functor
as comodules over a coalgebra: a finite piece of such a category is a category of modules over a
finite algebra of fibre endomorphisms, and the coalgebra is assembled from the duals of these
algebras.

## Main definitions

* `TauCeti.Comodule.ofAlgebraAction`: the right `A^∨`-comodule of an algebra action of `A`.
* `TauCeti.Comodule.algebraAction`: the algebra action of `A` defined by an `A^∨`-coaction.
* `TauCeti.Comodule.algebraActionEquiv`: these constructions are inverse bijections.
* `TauCeti.ComoduleCat.equivalenceModuleCat`: the equivalence between left `A`-modules and right
  `A^∨`-comodules, over the restriction of scalars to `R`.
* `TauCeti.FGComoduleCat.equivalenceFGModuleCat`: its restriction to finite modules.
* `TauCeti.ComoduleCat.ofModuleCatCompForget₂Iso` and
  `TauCeti.FGComoduleCat.equivalenceFGModuleCatCompForget₂Iso`: the underlying `R`-modules are
  the restrictions of scalars.
* `TauCeti.ComoduleCat.restrictScalarsCompOfModuleCatIso`: restriction of scalars along an
  algebra morphism is corestriction along its dual coalgebra morphism.

## Main statements

* `TauCeti.Comodule.coact_ofAlgebraAction_eq_sum`: the coaction formula in a finite family.
* `TauCeti.Comodule.map_coact_ofAlgebraAction_iff`: a linear map is a comodule morphism exactly
  when it intertwines the algebra actions.
* `TauCeti.Comodule.corestrict_ofAlgebraAction`: corestriction along a dual coalgebra morphism
  is restriction of the action.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
* A. Huber and S. Müller-Stach, *Periods and Nori Motives*, §7.1.
* P. Deligne and J. S. Milne, *Tannakian categories*, proof of Proposition 2.14.
-/

public noncomputable section

open CategoryTheory
open scoped TensorProduct
open TensorProduct WithConv

namespace TauCeti

namespace Comodule

section Semiring

variable {R A M N : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The right comodule over the dual coalgebra `A^∨` of a finite projective algebra `A`
defined by an algebra action of `A`. Its coaction is `m ↦ ∑ᵢ ρ(eᵢ) m ⊗ eᵢ^∨`, see
`TauCeti.Comodule.coact_ofAlgebraAction_eq_sum`. -/
@[implicit_reducible]
def ofAlgebraAction (ρ : A →ₐ[R] Module.End R M) : Comodule R (ConvolutionDual R A) M :=
  ofConvolutionAction (ρ.comp (ConvolutionDual.evalAlgEquiv R A).symm.toAlgHom)

/-- Contracting the coaction defined by an algebra action against evaluation at `a` applies
the action of `a`. -/
theorem tensorComponent_ofAlgebraAction (ρ : A →ₐ[R] Module.End R M) (a : A) (m : M) :
    LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A a).ofConv
      ((ofAlgebraAction ρ).coact m) = ρ a m := by
  rw [ofAlgebraAction, tensorComponent_ofConvolutionAction, toConv_ofConv]
  simp

/-- **The coaction of the dual coalgebra in a finite family.** If `eᵢ ∈ A` and
`eᵢ^∨ ∈ A^∨` satisfy `∑ᵢ eᵢ^∨(a) eᵢ = a`, then the coaction defined by an algebra action `ρ`
is `m ↦ ∑ᵢ ρ(eᵢ) m ⊗ eᵢ^∨`. For a finite basis `b`, take `e := b` and
`e' := fun i => toConv (b.coord i)`. -/
theorem coact_ofAlgebraAction_eq_sum {ι : Type*} [Fintype ι] (e : ι → A)
    (e' : ι → ConvolutionDual R A) (he : ∀ a : A, ∑ i, (e' i).ofConv a • e i = a)
    (ρ : A →ₐ[R] Module.End R M) (m : M) :
    (ofAlgebraAction ρ).coact m = ∑ i, ρ (e i) m ⊗ₜ[R] e' i := by
  apply ConvolutionDual.tensor_eq_of_forall_tensorComponent_evalAlgEquiv_eq
  intro a
  rw [tensorComponent_ofAlgebraAction, map_sum]
  simp only [LinearMap.tensorComponent_tmul, ConvolutionDual.evalAlgEquiv_apply_apply]
  conv_lhs => rw [← he a]
  simp [map_sum, map_smul]

/-- The algebra action of a finite projective algebra `A` defined by a right coaction of its
dual coalgebra: `a` acts by contracting the coaction against evaluation at `a`. -/
def algebraAction [Comodule R (ConvolutionDual R A) M] : A →ₐ[R] Module.End R M :=
  (convolutionAction (R := R) (C := ConvolutionDual R A) (M := M)).comp
    (ConvolutionDual.evalAlgEquiv R A).toAlgHom

/-- The algebra action defined by a coaction contracts it against evaluation. -/
@[simp]
theorem algebraAction_apply [Comodule R (ConvolutionDual R A) M] (a : A) (m : M) :
    algebraAction (R := R) (A := A) (M := M) a m =
      LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A a).ofConv
        (coact (R := R) (C := ConvolutionDual R A) m) := by
  simp [algebraAction]

/-- Comodule morphisms intertwine the algebra actions defined by the coactions. -/
@[simp↓]
theorem Hom.map_algebraAction [Comodule R (ConvolutionDual R A) M]
    [Comodule R (ConvolutionDual R A) N] (f : Hom R (ConvolutionDual R A) M N) (a : A) (m : M) :
    f (algebraAction (R := R) (A := A) (M := M) a m) =
      algebraAction (R := R) (A := A) (M := N) a (f m) := by
  simp only [algebraAction, AlgHom.comp_apply]
  exact Hom.map_convolutionAction f _ m

/-- The algebra action of the comodule defined by an algebra action is the original action. -/
@[simp]
theorem algebraAction_ofAlgebraAction (ρ : A →ₐ[R] Module.End R M) :
    (letI := ofAlgebraAction ρ; algebraAction (R := R) (A := A) (M := M)) = ρ := by
  let := ofAlgebraAction ρ
  ext a m
  rw [algebraAction_apply, tensorComponent_ofAlgebraAction]

/-- The comodule defined by the algebra action of a coaction is the original comodule. -/
@[simp]
theorem ofAlgebraAction_algebraAction [σ : Comodule R (ConvolutionDual R A) M] :
    ofAlgebraAction (algebraAction (R := R) (A := A) (M := M)) = σ := by
  apply Comodule.ext
  ext m
  apply ConvolutionDual.tensor_eq_of_forall_tensorComponent_evalAlgEquiv_eq
  intro a
  rw [tensorComponent_ofAlgebraAction, algebraAction_apply]

variable (R A M) in
/-- **Modules over a finite algebra are comodules over its dual coalgebra.** Right coactions of
the dual coalgebra `A^∨` of a finite projective algebra `A` correspond bijectively to algebra
actions of `A`. -/
def algebraActionEquiv :
    Comodule R (ConvolutionDual R A) M ≃ (A →ₐ[R] Module.End R M) where
  toFun σ := letI := σ; algebraAction
  invFun := ofAlgebraAction
  left_inv σ := ofAlgebraAction_algebraAction (σ := σ)
  right_inv := algebraAction_ofAlgebraAction

/-- The forward bijection takes the algebra action of a coaction. -/
@[simp]
theorem algebraActionEquiv_apply (σ : Comodule R (ConvolutionDual R A) M) :
    algebraActionEquiv R A M σ = (letI := σ; algebraAction) := (rfl)

/-- The inverse bijection is the comodule of an algebra action. -/
@[simp]
theorem algebraActionEquiv_symm_apply (ρ : A →ₐ[R] Module.End R M) :
    (algebraActionEquiv R A M).symm ρ = ofAlgebraAction ρ := (rfl)

/-- **Morphisms of modules are morphisms of comodules.** A linear map between modules over a
finite projective algebra commutes with the coactions of the dual coalgebra exactly when it
intertwines the actions of the algebra. -/
theorem map_coact_ofAlgebraAction_iff (ρ : A →ₐ[R] Module.End R M)
    (τ : A →ₐ[R] Module.End R N) (f : M →ₗ[R] N) :
    TensorProduct.map f LinearMap.id ∘ₗ (ofAlgebraAction ρ).coact =
        (ofAlgebraAction τ).coact ∘ₗ f ↔
      ∀ a, f ∘ₗ ρ a = τ a ∘ₗ f := by
  have key : ∀ (a : A) (m : M),
      LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A a).ofConv
        (TensorProduct.map f LinearMap.id ((ofAlgebraAction ρ).coact m)) = f (ρ a m) := by
    intro a m
    rw [LinearMap.tensorComponent_map, LinearMap.comp_id, tensorComponent_ofAlgebraAction]
  constructor
  · intro h a
    ext m
    have hm := congr(LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A a).ofConv
      ($h m))
    simp only [LinearMap.comp_apply] at hm
    rwa [key, tensorComponent_ofAlgebraAction] at hm
  · intro h
    ext m
    apply ConvolutionDual.tensor_eq_of_forall_tensorComponent_evalAlgEquiv_eq
    intro a
    simp only [LinearMap.comp_apply]
    rw [key, tensorComponent_ofAlgebraAction, ← LinearMap.comp_apply, h a,
      LinearMap.comp_apply]

section Transition

variable {B : Type*} [Semiring B] [Algebra R B] [Module.Finite R B] [Module.Projective R B]

omit [AddCommMonoid N] [Module R N] in
/-- **Transition maps.** Corestricting the comodule of an action of `B` along the dual
coalgebra morphism `B^∨ → A^∨` of an algebra morphism `f : A → B` gives the comodule of the
restricted action of `A`. The morphism `f` need not be injective or surjective. -/
theorem corestrict_ofAlgebraAction (f : A →ₐ[R] B) (τ : B →ₐ[R] Module.End R M) :
    (letI := ofAlgebraAction τ; Corestrict (ConvolutionDual.coalgMap R f)) =
      ofAlgebraAction (τ.comp f) := by
  let := ofAlgebraAction τ
  apply Comodule.ext
  ext m
  apply ConvolutionDual.tensor_eq_of_forall_tensorComponent_evalAlgEquiv_eq
  intro a
  rw [tensorComponent_ofAlgebraAction, corestrict_coact_apply, LinearMap.tensorComponent_map,
    ConvolutionDual.ofConv_evalAlgEquiv_comp_coalgMap, tensorComponent_ofAlgebraAction,
    LinearMap.id_apply, AlgHom.comp_apply]

end Transition

end Semiring

end Comodule

namespace ComoduleCat

universe u v w

variable (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]

/-- **Modules as comodules over the dual coalgebra.** A left `A`-module, regarded as an
`R`-module by restriction of scalars, with the right coaction of the dual coalgebra `A^∨`
defined by its action. -/
@[expose] def ofModuleCat :
    ModuleCat.{w} A ⥤ ComoduleCat.{u, max u v, w} R (ConvolutionDual R A) where
  obj M :=
    letI : IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
      .of_algebraMap_smul fun _ _ => rfl
    letI := Comodule.ofAlgebraAction (Algebra.lsmul (A := A) R R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj M))
    of R (ConvolutionDual R A) ((ModuleCat.restrictScalars (algebraMap R A)).obj M)
  map {M N} f :=
    letI : IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
      .of_algebraMap_smul fun _ _ => rfl
    letI : IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj N) :=
      .of_algebraMap_smul fun _ _ => rfl
    letI := Comodule.ofAlgebraAction (Algebra.lsmul (A := A) R R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj M))
    letI := Comodule.ofAlgebraAction (Algebra.lsmul (A := A) R R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj N))
    ofHom R (ConvolutionDual R A)
      { toLinearMap := ((ModuleCat.restrictScalars (algebraMap R A)).map f).hom
        map_coact := (Comodule.map_coact_ofAlgebraAction_iff (Algebra.lsmul R R _)
          (Algebra.lsmul R R _) _).mpr fun a =>
          LinearMap.ext fun m => f.hom.map_smul a m }

/-- The scalars of `R` act on the comodule of an `A`-module through `algebraMap R A`. -/
theorem ofModuleCat_obj_smul (M : ModuleCat.{w} A) (r : R) (m : (ofModuleCat R A).obj M) :
    r • m = algebraMap R A r • (show M from m) :=
  (rfl)

/-- The functor `ofModuleCat` does not change the underlying function of a morphism. -/
@[simp]
theorem ofModuleCat_map_apply {M N : ModuleCat.{w} A} (f : M ⟶ N) (m : (ofModuleCat R A).obj M) :
    dsimp% (ofModuleCat R A).map f m = f (show M from m) :=
  (rfl)

/-- The coaction of `ofModuleCat` contracts against evaluation at `a` to the action of `a`. -/
@[simp]
theorem tensorComponent_coact_ofModuleCat_obj (M : ModuleCat.{w} A) (a : A)
    (m : (ofModuleCat R A).obj M) :
    LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A a).ofConv
      (Comodule.coact (R := R) (C := ConvolutionDual R A) m) = a • (show M from m) :=
  Comodule.tensorComponent_ofAlgebraAction _ a m

/-- The left `A`-module underlying a right comodule over the dual coalgebra `A^∨`. -/
@[expose, implicit_reducible]
def algebraActionModule (M : ComoduleCat.{u, max u v, w} R (ConvolutionDual R A)) : Module A M :=
  Module.compHom M (Comodule.algebraAction (R := R) (A := A) (M := M)).toRingHom

/-- **Comodules over the dual coalgebra as modules.** A right comodule over the dual coalgebra
`A^∨`, regarded as a left `A`-module through `TauCeti.Comodule.algebraAction`. -/
@[expose] def toModuleCat :
    ComoduleCat.{u, max u v, w} R (ConvolutionDual R A) ⥤ ModuleCat.{w} A where
  obj M :=
    letI := Module.addCommMonoidToAddCommGroup R (M := M)
    letI := algebraActionModule R A M
    ModuleCat.of A M
  map {M N} f :=
    letI := Module.addCommMonoidToAddCommGroup R (M := M)
    letI := Module.addCommMonoidToAddCommGroup R (M := N)
    letI := algebraActionModule R A M
    letI := algebraActionModule R A N
    ModuleCat.ofHom
      { toFun := f
        map_add' := map_add f
        map_smul' a m := Comodule.Hom.map_algebraAction f a m }

/-- The algebra acts on the module of a comodule through `TauCeti.Comodule.algebraAction`. -/
theorem toModuleCat_obj_smul (M : ComoduleCat.{u, max u v, w} R (ConvolutionDual R A)) (a : A)
    (m : (toModuleCat R A).obj M) :
    a • m = Comodule.algebraAction (R := R) (A := A) (M := M) a (show M from m) :=
  (rfl)

/-- The identification of an `A`-module with the module underlying its comodule over the dual
coalgebra, the unit of `TauCeti.ComoduleCat.equivalenceModuleCat`. It is the identity on
elements. -/
def ofModuleCatUnitLinearEquiv (M : ModuleCat.{w} A) :
    M ≃ₗ[A] (toModuleCat R A).obj ((ofModuleCat R A).obj M) where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' a m := by
    rw [RingHom.id_apply]
    refine Eq.trans ?_ (toModuleCat_obj_smul R A ((ofModuleCat R A).obj M) a m).symm
    rw [Comodule.algebraAction_apply, tensorComponent_coact_ofModuleCat_obj]
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unit linear equivalence is the identity on elements. -/
@[simp]
theorem ofModuleCatUnitLinearEquiv_apply (M : ModuleCat.{w} A) (m : M) :
    ofModuleCatUnitLinearEquiv R A M m = m :=
  (rfl)

/-- The underlying linear equivalence of `TauCeti.ComoduleCat.ofModuleCatCounitIso`. -/
def ofModuleCatCounitLinearEquiv (M : ComoduleCat.{u, max u v, w} R (ConvolutionDual R A)) :
    (ofModuleCat R A).obj ((toModuleCat R A).obj M) ≃ₗ[R] M where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' r m := by
    rw [RingHom.id_apply, ofModuleCat_obj_smul, toModuleCat_obj_smul, AlgHom.commutes,
      Module.algebraMap_end_apply]
  left_inv _ := rfl
  right_inv _ := rfl

/-- The counit linear equivalence is the identity on elements. -/
@[simp]
theorem ofModuleCatCounitLinearEquiv_apply
    (M : ComoduleCat.{u, max u v, w} R (ConvolutionDual R A))
    (m : (ofModuleCat R A).obj ((toModuleCat R A).obj M)) :
    ofModuleCatCounitLinearEquiv R A M m = m :=
  (rfl)

/-- The comodule of the `A`-module underlying a comodule over the dual coalgebra is the original
comodule, the counit of `TauCeti.ComoduleCat.equivalenceModuleCat`. It is the identity on
elements. -/
def ofModuleCatCounitIso (M : ComoduleCat.{u, max u v, w} R (ConvolutionDual R A)) :
    (ofModuleCat R A).obj ((toModuleCat R A).obj M) ≅ M :=
  isoOfLinearEquiv R (ConvolutionDual R A) (ofModuleCatCounitLinearEquiv R A M) (by
    ext m
    apply ConvolutionDual.tensor_eq_of_forall_tensorComponent_evalAlgEquiv_eq
    intro a
    simp only [LinearMap.comp_apply, LinearMap.tensorComponent_map, LinearMap.comp_id,
      tensorComponent_coact_ofModuleCat_obj]
    -- Both sides are the action of `a` on `m` defined by the coaction of `M`; the linear
    -- equivalence is the identity on elements.
    rw [← Comodule.algebraAction_apply]
    exact toModuleCat_obj_smul R A M a m)

/-- **Modules over a finite algebra are comodules over its dual coalgebra.** For a finite
projective algebra `A` over a commutative ring `R`, left `A`-modules are equivalent to right
comodules over the dual coalgebra `A^∨`. The coaction is `m ↦ ∑ᵢ eᵢ m ⊗ eᵢ^∨`, and the
underlying `R`-module is obtained by restriction of scalars, see
`TauCeti.ComoduleCat.ofModuleCatCompForget₂Iso`. The unit and counit are the identity on
elements. -/
@[expose] def equivalenceModuleCat :
    ModuleCat.{w} A ≌ ComoduleCat.{u, max u v, w} R (ConvolutionDual R A) where
  functor := ofModuleCat R A
  inverse := toModuleCat R A
  unitIso := NatIso.ofComponents (fun M => (ofModuleCatUnitLinearEquiv R A M).toModuleIso)
    fun f => by
      ext m
      rfl
  counitIso := NatIso.ofComponents (ofModuleCatCounitIso R A) fun f => by
    ext m
    rfl
  functor_unitIso_comp M := by
    ext m
    rfl

/-- The functor of `equivalenceModuleCat` is `ofModuleCat`. -/
@[simp]
theorem equivalenceModuleCat_functor : (equivalenceModuleCat.{u, v, w} R A).functor =
    ofModuleCat R A :=
  rfl

/-- The inverse of `equivalenceModuleCat` is `toModuleCat`. -/
@[simp]
theorem equivalenceModuleCat_inverse : (equivalenceModuleCat.{u, v, w} R A).inverse =
    toModuleCat R A :=
  rfl

/-- The unit of `equivalenceModuleCat` is the identity on elements. -/
@[simp]
theorem equivalenceModuleCat_unitIso_hom_app_apply (M : ModuleCat.{w} A) (m : M) :
    dsimp% ((equivalenceModuleCat R A).unitIso.hom.app M).hom m = m :=
  (rfl)

/-- The inverse of the unit of `equivalenceModuleCat` is the identity on elements. -/
@[simp]
theorem equivalenceModuleCat_unitIso_inv_app_apply (M : ModuleCat.{w} A)
    (m : (toModuleCat R A).obj ((ofModuleCat R A).obj M)) :
    dsimp% ((equivalenceModuleCat R A).unitIso.inv.app M).hom m = m :=
  (rfl)

/-- The counit of `equivalenceModuleCat` is the identity on elements. -/
@[simp]
theorem equivalenceModuleCat_counitIso_hom_app_apply
    (M : ComoduleCat.{u, max u v, w} R (ConvolutionDual R A))
    (m : (ofModuleCat R A).obj ((toModuleCat R A).obj M)) :
    dsimp% (equivalenceModuleCat R A).counitIso.hom.app M m = m :=
  (rfl)

/-- The inverse of the counit of `equivalenceModuleCat` is the identity on elements. -/
@[simp]
theorem equivalenceModuleCat_counitIso_inv_app_apply
    (M : ComoduleCat.{u, max u v, w} R (ConvolutionDual R A)) (m : M) :
    dsimp% (equivalenceModuleCat R A).counitIso.inv.app M m = m :=
  (rfl)

/-- The `R`-module underlying the comodule of an `A`-module is its restriction of scalars. The
components are the identity on elements. -/
def ofModuleCatCompForget₂Iso :
    ofModuleCat R A ⋙ forget₂ (ComoduleCat.{u, max u v, w} R (ConvolutionDual R A))
        (ModuleCat.{w} R) ≅
      ModuleCat.restrictScalars.{w} (algebraMap R A) :=
  NatIso.ofComponents (fun _ =>
    { hom := ModuleCat.homEquiv.symm LinearMap.id
      inv := ModuleCat.homEquiv.symm LinearMap.id })
    fun f => by
      ext m
      rfl

/-- The components of `ofModuleCatCompForget₂Iso` are the identity on elements. -/
@[simp]
theorem ofModuleCatCompForget₂Iso_hom_app_apply (M : ModuleCat.{w} A)
    (m : (ofModuleCat R A ⋙ forget₂ (ComoduleCat.{u, max u v, w} R (ConvolutionDual R A))
      (ModuleCat.{w} R)).obj M) :
    dsimp% ((ofModuleCatCompForget₂Iso R A).hom.app M).hom m = m :=
  (rfl)

/-- The inverse components of `ofModuleCatCompForget₂Iso` are the identity on elements. -/
@[simp]
theorem ofModuleCatCompForget₂Iso_inv_app_apply (M : ModuleCat.{w} A)
    (m : (ModuleCat.restrictScalars.{w} (algebraMap R A)).obj M) :
    dsimp% ((ofModuleCatCompForget₂Iso R A).inv.app M).hom m = m :=
  (rfl)

section Transition

variable {A} {B : Type*} [Ring B] [Algebra R B] [Module.Finite R B] [Module.Projective R B]

/-- The identification of the comodule of a module restricted along `f : A → B` with the
corestriction of its comodule along the dual coalgebra morphism `B^∨ → A^∨`. It is the identity
on elements. -/
private def restrictScalarsLinearEquiv (f : A →ₐ[R] B) (M : ModuleCat.{w} B) :
    (ofModuleCat R A).obj ((ModuleCat.restrictScalars f.toRingHom).obj M) ≃ₗ[R]
      (corestrict (ConvolutionDual.coalgMap R f)).obj ((ofModuleCat R B).obj M) where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' r m := by
    rw [RingHom.id_apply, ofModuleCat_obj_smul]
    refine Eq.trans ?_ (ofModuleCat_obj_smul R B M r m).symm
    rw [ModuleCat.restrictScalars.smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Transition maps.** Restricting scalars along an algebra morphism `f : A → B` corresponds to
corestricting comodules along the dual coalgebra morphism `B^∨ → A^∨`. -/
def restrictScalarsCompOfModuleCatIso (f : A →ₐ[R] B) :
    ModuleCat.restrictScalars.{w} f.toRingHom ⋙ ofModuleCat R A ≅
      ofModuleCat R B ⋙ corestrict (ConvolutionDual.coalgMap R f) :=
  NatIso.ofComponents
    (fun M => isoOfLinearEquiv R (ConvolutionDual R A) (restrictScalarsLinearEquiv R f M) (by
      ext m
      apply ConvolutionDual.tensor_eq_of_forall_tensorComponent_evalAlgEquiv_eq
      intro a
      simp only [LinearMap.comp_apply, LinearMap.tensorComponent_map, LinearMap.comp_id]
      -- Both contractions are the action of `f a` on `m`.
      refine (tensorComponent_coact_ofModuleCat_obj R A
        ((ModuleCat.restrictScalars f.toRingHom).obj M) a m).trans ?_
      refine Eq.trans ?_ (LinearMap.tensorComponent_map _ LinearMap.id
        (ConvolutionDual.coalgMap R f).toLinearMap
        (Comodule.coact (R := R) (C := ConvolutionDual R B) (M := (ofModuleCat R B).obj M)
          m)).symm
      rw [ConvolutionDual.ofConv_evalAlgEquiv_comp_coalgMap, LinearMap.id_apply]
      -- The restricted action of `a` is the action of `f a`.
      exact (tensorComponent_coact_ofModuleCat_obj R B M (f a) m).symm))
    fun g => by
      ext m
      rfl

/-- The components of `restrictScalarsCompOfModuleCatIso` are the identity on elements. -/
@[simp]
theorem restrictScalarsCompOfModuleCatIso_hom_app_apply (f : A →ₐ[R] B) (M : ModuleCat.{w} B)
    (m : (ModuleCat.restrictScalars.{w} f.toRingHom ⋙ ofModuleCat R A).obj M) :
    dsimp% (restrictScalarsCompOfModuleCatIso R f).hom.app M m = m :=
  (rfl)

/-- The inverse components of `restrictScalarsCompOfModuleCatIso` are the identity on elements. -/
@[simp]
theorem restrictScalarsCompOfModuleCatIso_inv_app_apply (f : A →ₐ[R] B) (M : ModuleCat.{w} B)
    (m : (ofModuleCat R B ⋙ corestrict (ConvolutionDual.coalgMap R f)).obj M) :
    dsimp% (restrictScalarsCompOfModuleCatIso R f).inv.app M m = m :=
  (rfl)

end Transition

end ComoduleCat

namespace FGComoduleCat

universe u v w

variable (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]

/-- The comodule of an `A`-module over the dual coalgebra is finite over `R` exactly when the
module is finite over `A`. -/
theorem isFG_inverseImage_ofModuleCat :
    (ComoduleCat.isFG.{u, max u v, w} R (ConvolutionDual R A)).inverseImage
        (ComoduleCat.ofModuleCat R A) = ModuleCat.isFG.{w} A := by
  ext M
  have : IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
    .of_algebraMap_smul fun _ _ => rfl
  -- The `R`-module underlying `(ofModuleCat R A).obj M` is the restriction of scalars of `M`.
  change Module.Finite R ((ModuleCat.restrictScalars (algebraMap R A)).obj M) ↔ Module.Finite A M
  exact ⟨fun _ => Module.Finite.of_restrictScalars_finite R A
      ((ModuleCat.restrictScalars (algebraMap R A)).obj M),
    fun h => by
      have : Module.Finite A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) := h
      exact Module.Finite.trans A ((ModuleCat.restrictScalars (algebraMap R A)).obj M)⟩

/-- **Finite modules over a finite algebra are finite comodules over its dual coalgebra.** The
restriction of `TauCeti.ComoduleCat.equivalenceModuleCat` to finitely generated objects. -/
def equivalenceFGModuleCat :
    FGModuleCat.{w} A ≌ FGComoduleCat.{u, max u v, w} R (ConvolutionDual R A) :=
  (ComoduleCat.equivalenceModuleCat R A).congrFullSubcategory
    (isFG_inverseImage_ofModuleCat R A)

/-- The `R`-module underlying the finite comodule of a finite `A`-module is its restriction of
scalars. The components are the identity on elements. -/
def equivalenceFGModuleCatCompForget₂Iso :
    (equivalenceFGModuleCat R A).functor ⋙
        forget₂ (FGComoduleCat.{u, max u v, w} R (ConvolutionDual R A)) (ModuleCat.{w} R) ≅
      (ModuleCat.isFG.{w} A).ι ⋙ ModuleCat.restrictScalars.{w} (algebraMap R A) :=
  (ModuleCat.isFG.{w} A).ι.isoWhiskerLeft (ComoduleCat.ofModuleCatCompForget₂Iso R A)

end FGComoduleCat

end TauCeti
