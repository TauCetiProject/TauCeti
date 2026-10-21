/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Monoidal
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.ScalarExtension.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Functor

/-!
# Scalar extension and its point automorphisms

Let `H` be a Hopf algebra over a commutative semiring `R`, and let `A` be a commutative
`R`-algebra. Scalar extension of the underlying-module functor is constructed for all comodules
in `TauCeti.Algebra.Coalgebra.Comodule.ScalarExtension` and restricted to finitely generated
comodules in `TauCeti.Algebra.Coalgebra.Comodule.Finite.ScalarExtension.Basic`:

```text
FGComoduleCat R H ⥤ SemimoduleCat A,    M ↦ A ⊗[R] M.
```

Every `A`-valued point of `H` acts naturally and invertibly on the all-comodule functor: its
component at `M` is the usual point action on `A ⊗[R] M`. These automorphisms form a group
homomorphism, which restricts by precomposition to the finite-comodule functor.

This is the base change of the neutral underlying-module functor, without a faithfulness claim:
scalar extension along an arbitrary `R → A` need not be faithful.

The finite natural point-representation category also has a scalar-extension lax monoidal
functor, transported from finite comodules along their monoidal equivalence. Its underlying
modules are `A ⊗[R] V`, and its morphisms are base changes of the underlying linear maps.
Together, these constructions supply categorical infrastructure for Tannakian reconstruction.

## Main declarations

* `TauCeti.FGPointRepresentationCat.scalarExtensionMonoidalFunctor`: scalar extension on
  finite natural point representations, with its tensor and unit comparisons.
* `TauCeti.Tannaka.pointNatIso`: the point action as a natural automorphism of the functor.
* `TauCeti.Tannaka.pointNatIsoHom`: points acting on all comodules, as a group homomorphism.
* `TauCeti.Tannaka.fgPointNatIsoHom`: the induced action on finitely generated comodules.

## References

This is the scalar-extended underlying-module functor and point action used in Tannakian
reconstruction; see
J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 9.4. The construction reuses Mathlib's
linear-map base change and Tau Ceti's finite-comodule category and point action.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v w x

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type x) [CommSemiring A] [Algebra R A]

/-- An `A`-valued point of `H` acts by an automorphism on the scalar extension of each
comodule. -/
private noncomputable def pointIso (g : WithConv (H →ₐ[R] A))
    (M : ComoduleCat.{u, v, w} R H) :
    (ComoduleCat.scalarExtensionFunctor R H A).obj M ≅
      (ComoduleCat.scalarExtensionFunctor R H A).obj M :=
  (eqToIso (ComoduleCat.scalarExtensionFunctor_obj R H A M)).trans
    ((Comodule.pointsAction M g).toModuleIsoₛ.trans
      (eqToIso (ComoduleCat.scalarExtensionFunctor_obj R H A M).symm))

/-- Every algebra-valued point acts as a natural automorphism of the scalar-extension functor.
Naturality is precisely the fact that scalar extension of a comodule morphism
intertwines point actions. -/
noncomputable def pointNatIso (g : WithConv (H →ₐ[R] A)) :
    ComoduleCat.scalarExtensionFunctor R H A ≅
      ComoduleCat.scalarExtensionFunctor R H A :=
  NatIso.ofComponents (pointIso R H A g) (fun {M N} f ↦ by
    -- Reduce the private component constructor directly so its formulas are stated only by the
    -- public component theorems below.
    change
      (ComoduleCat.scalarExtensionFunctor R H A).map f ≫
          eqToHom (ComoduleCat.scalarExtensionFunctor_obj R H A N) ≫
            (Comodule.pointsAction N g).toModuleIsoₛ.hom ≫
              eqToHom (ComoduleCat.scalarExtensionFunctor_obj R H A N).symm =
        eqToHom (ComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
            (Comodule.pointsAction M g).toModuleIsoₛ.hom ≫
              eqToHom (ComoduleCat.scalarExtensionFunctor_obj R H A M).symm ≫
                (ComoduleCat.scalarExtensionFunctor R H A).map f
    rw [ComoduleCat.scalarExtensionFunctor_map]
    simp only [Category.assoc]
    rw [cancel_epi]
    simp only [← Category.assoc]
    rw [cancel_mono]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      LinearEquiv.toModuleIsoₛ_hom, Comodule.pointsAction_toLinearMap]
    apply SemimoduleCat.hom_ext
    simpa only [SemimoduleCat.hom_comp, LinearEquiv.toModuleIsoₛ_hom,
      SemimoduleCat.hom_ofHom, Comodule.pointsAction_toLinearMap] using
      (Comodule.baseChange_comp_endOfPoint f g.ofConv).symm)

/-- The component of the point natural automorphism is the transported point action. -/
@[simp]
theorem pointNatIso_hom_app (g : WithConv (H →ₐ[R] A))
    (M : ComoduleCat.{u, v, w} R H) :
    (pointNatIso R H A g).hom.app M =
      eqToHom (ComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
        (Comodule.pointsAction M g).toModuleIsoₛ.hom ≫
          eqToHom (ComoduleCat.scalarExtensionFunctor_obj R H A M).symm :=
  (rfl)

/-- The inverse component of the point natural automorphism is the transported inverse point
action. -/
@[simp]
theorem pointNatIso_inv_app (g : WithConv (H →ₐ[R] A))
    (M : ComoduleCat.{u, v, w} R H) :
    (pointNatIso R H A g).inv.app M =
      eqToHom (ComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
        (Comodule.pointsAction M g).toModuleIsoₛ.inv ≫
          eqToHom (ComoduleCat.scalarExtensionFunctor_obj R H A M).symm :=
  (rfl)

/-- Algebra-valued points act on the scalar-extension functor by natural automorphisms. -/
noncomputable def pointNatIsoHom :
    WithConv (H →ₐ[R] A) →* Aut (ComoduleCat.scalarExtensionFunctor R H A) where
  toFun g := .of (pointNatIso R H A g)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext M
    -- Extensionality exposes a component of `Aut`; reduction identifies that component
    -- with the natural isomorphism supplied as `pointNatIsoHom.toFun`.
    change (pointNatIso R H A 1).hom.app M = 𝟙 _
    rw [pointNatIso_hom_app]
    simp
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext M
    -- Multiplication in `Aut` is reverse isomorphism composition, so reducing the bundled
    -- homomorphism turns this component into the following explicitly ordered composite.
    change (pointNatIso R H A (g * h)).hom.app M =
      (pointNatIso R H A h).hom.app M ≫ (pointNatIso R H A g).hom.app M
    rw [pointNatIso_hom_app, pointNatIso_hom_app, pointNatIso_hom_app]
    simp only [Category.assoc]
    rw [cancel_epi]
    simp only [← Category.assoc]
    rw [cancel_mono]
    simp only [map_mul, LinearEquiv.toModuleIsoₛ_hom, LinearEquiv.coe_toLinearMap_mul,
      Comodule.pointsAction_toLinearMap, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
    apply SemimoduleCat.hom_ext
    rfl

/-- Evaluating the points action homomorphism gives the corresponding natural automorphism. -/
@[simp]
theorem pointNatIsoHom_apply (g : WithConv (H →ₐ[R] A)) :
    (pointNatIsoHom R H A g).asIso = pointNatIso R H A g :=
  (rfl)

/-- Restricting the point action to finitely generated comodules gives automorphisms of the
finite scalar-extension functor used in Tannakian reconstruction. -/
noncomputable def fgPointNatIsoHom :
    WithConv (H →ₐ[R] A) →* Aut (FGComoduleCat.scalarExtensionFunctor R H A) :=
  (Aut.autMulEquivOfIso
      (eqToIso (FGComoduleCat.scalarExtensionFunctor_def R H A)).symm).toMonoidHom.comp
    ((((Functor.whiskeringLeft _ _ _).obj
      (FGComoduleCat.incl (R := R) (C := H))).mapAut
        (ComoduleCat.scalarExtensionFunctor R H A)).comp (pointNatIsoHom R H A))

/-- The finite-comodule point action is obtained from the all-comodule action by precomposition
and transport across the defining equality of the finite scalar-extension functor. -/
private theorem fgPointNatIsoHom_apply (g : WithConv (H →ₐ[R] A)) :
    fgPointNatIsoHom R H A g =
      (Aut.autMulEquivOfIso
        (eqToIso (FGComoduleCat.scalarExtensionFunctor_def R H A)).symm)
          (.of (((Functor.whiskeringLeft _ _ _).obj
            (FGComoduleCat.incl (R := R) (C := H))).mapIso
              (pointNatIsoHom R H A g).asIso)) :=
  (rfl)

/-- The component of the finite-comodule point automorphism is the transported point action. -/
@[simp]
theorem fgPointNatIsoHom_hom_app (g : WithConv (H →ₐ[R] A))
    (M : FGComoduleCat.{u, v, w} R H) :
    (fgPointNatIsoHom R H A g).asIso.hom.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
        (Comodule.pointsAction M g).toModuleIsoₛ.hom ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm := by
  rw [fgPointNatIsoHom_apply]
  -- Rewriting unfolds the outer monoid homomorphism application but does not expose the
  -- hom component assembled by `autMulEquivOfIso` and whiskering, so reduce that component.
  change
    (eqToIso (FGComoduleCat.scalarExtensionFunctor_def R H A).symm).inv.app M ≫
          (pointNatIso R H A g).hom.app
            ((FGComoduleCat.incl (R := R) (C := H)).obj M) ≫
        (eqToIso (FGComoduleCat.scalarExtensionFunctor_def R H A).symm).hom.app M = _
  rw [pointNatIso_hom_app]
  simp

/-- The inverse component of the finite-comodule point automorphism is the transported inverse
point action. -/
@[simp]
theorem fgPointNatIsoHom_inv_app (g : WithConv (H →ₐ[R] A))
    (M : FGComoduleCat.{u, v, w} R H) :
    (fgPointNatIsoHom R H A g).asIso.inv.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
        (Comodule.pointsAction M g).toModuleIsoₛ.inv ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm := by
  rw [fgPointNatIsoHom_apply]
  -- Rewriting unfolds the outer monoid homomorphism application but does not expose the
  -- inverse component assembled by `autMulEquivOfIso` and whiskering, so reduce that component.
  change
    (eqToIso (FGComoduleCat.scalarExtensionFunctor_def R H A).symm).inv.app M ≫
          (pointNatIso R H A g).inv.app
            ((FGComoduleCat.incl (R := R) (C := H)).obj M) ≫
        (eqToIso (FGComoduleCat.scalarExtensionFunctor_def R H A).symm).hom.app M = _
  rw [pointNatIso_inv_app]
  simp

end TauCeti.Tannaka

namespace TauCeti

universe u v

namespace FGPointRepresentationCat

variable (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
variable (A : Type u) [CommRing A] [Algebra R A]

/-- Scalar extension of finite natural point representations, with its tensor structure
inherited from the representation--comodule equivalence. -/
noncomputable abbrev scalarExtensionMonoidalFunctor :
    LaxMonoidalFunctor (FGPointRepresentationCat.{u, v, u} R H) (SemimoduleCat.{u} A) :=
  (fgPointRepresentationCategoryEquivalence R H).functor.precomposeLaxMonoidal.obj
    (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)

/-- On underlying modules, scalar extension is the tensor product with the value algebra. -/
theorem scalarExtensionMonoidalFunctor_obj (V : FGPointRepresentationCat.{u, v, u} R H) :
    (scalarExtensionMonoidalFunctor R H A).toFunctor.obj V = SemimoduleCat.of A (A ⊗[R] V) := by
  rw [scalarExtensionMonoidalFunctor, Functor.precomposeLaxMonoidal_obj_toFunctor,
    Functor.comp_obj,
    FGComoduleCat.scalarExtensionMonoidalFunctor_toFunctor,
    FGComoduleCat.scalarExtensionFunctor_obj]
  have hM := congrArg ComoduleCat.toSemimoduleCat
    (FGPointRepresentationCat.toComodule_obj_obj R H V)
  rw [PointRepresentationCat.toComodule_obj_toSemimoduleCat] at hM
  exact congrArg (fun M : SemimoduleCat.{u} R ↦ SemimoduleCat.of A (A ⊗[R] M)) hM

/-- The underlying functor is scalar extension after recovering the finite comodule. -/
theorem scalarExtensionMonoidalFunctor_toFunctor :
    (scalarExtensionMonoidalFunctor R H A).toFunctor =
      toComodule R H ⋙ FGComoduleCat.scalarExtensionFunctor R H A := by
  rw [scalarExtensionMonoidalFunctor, Functor.precomposeLaxMonoidal_obj_toFunctor,
    FGComoduleCat.scalarExtensionMonoidalFunctor_toFunctor]

/-- Scalar extension acts on representation morphisms by base change of the underlying
linear map. The object equalities identify its source and target with tensor products. -/
theorem scalarExtensionMonoidalFunctor_map
    {V W : FGPointRepresentationCat.{u, v, u} R H} (f : V ⟶ W) :
    (scalarExtensionMonoidalFunctor R H A).map f =
      eqToHom (scalarExtensionMonoidalFunctor_obj R H A V) ≫
        SemimoduleCat.ofHom (f.hom.toLinearMap.baseChange A) ≫
          eqToHom (scalarExtensionMonoidalFunctor_obj R H A W).symm := by
  apply (conj_eqToHom_iff_heq _ _ (scalarExtensionMonoidalFunctor_obj R H A V)
    (scalarExtensionMonoidalFunctor_obj R H A W)).2
  rw [scalarExtensionMonoidalFunctor, Functor.precomposeLaxMonoidal_obj_toFunctor,
    FGComoduleCat.scalarExtensionMonoidalFunctor_toFunctor, Functor.comp_map,
    FGComoduleCat.scalarExtensionFunctor_map]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  have hV := congrArg ComoduleCat.toSemimoduleCat (toComodule_obj_obj R H V)
  have hW := congrArg ComoduleCat.toSemimoduleCat (toComodule_obj_obj R H W)
  rw [PointRepresentationCat.toComodule_obj_toSemimoduleCat] at hV hW
  have hf := toComodule_map_toLinearMap R H f
  -- Eliminate bundled-module equalities before changing scalars in heterogeneous maps.
  have hbase : ∀ {M N M' N' : SemimoduleCat.{u} R}
      (g : M →ₗ[R] N) (g' : M' →ₗ[R] N'), M = M' → N = N' → HEq g g' →
        HEq (SemimoduleCat.ofHom (g.baseChange A))
          (SemimoduleCat.ofHom (g'.baseChange A)) := by
    intro M N M' N' g g' hM hN hg
    cases hM
    cases hN
    cases hg
    rfl
  exact hbase _ _ hV hW hf

open MonoidalCategory Functor.LaxMonoidal

/-- The tensorator is comodule scalar extension's tensorator followed by base change of
the representation--comodule tensor comparison, with the composite's object transports. -/
theorem scalarExtensionMonoidalFunctor_μ
    (V W : FGPointRepresentationCat.{u, v, u} R H) :
    let h (X : FGPointRepresentationCat.{u, v, u} R H) :
        (scalarExtensionMonoidalFunctor R H A).obj X =
          (FGComoduleCat.scalarExtensionFunctor R H A).obj ((toComodule R H).obj X) :=
      (congrArg (fun F ↦ F.obj X) (scalarExtensionMonoidalFunctor_toFunctor R H A)).trans
        (Functor.comp_obj (toComodule R H) (FGComoduleCat.scalarExtensionFunctor R H A) X)
    μ (scalarExtensionMonoidalFunctor R H A).toFunctor V W =
      eqToHom (congrArg₂ (fun M N : SemimoduleCat.{u} A ↦ M ⊗ N) (h V) (h W)) ≫
        (μ (FGComoduleCat.scalarExtensionFunctor R H A)
          ((toComodule R H).obj V) ((toComodule R H).obj W) ≫
          (FGComoduleCat.scalarExtensionFunctor R H A).map (μ (toComodule R H) V W)) ≫
        eqToHom (h (V ⊗ W)).symm := by
  apply (conj_eqToHom_iff_heq _ _ _
    ((congrArg (fun F ↦ F.obj (V ⊗ W))
      (scalarExtensionMonoidalFunctor_toFunctor R H A)).trans (Functor.comp_obj (toComodule R H)
        (FGComoduleCat.scalarExtensionFunctor R H A) (V ⊗ W)))).2
  exact Functor.precomposeLaxMonoidal_obj_μ
    (toComodule R H) (FGComoduleCat.scalarExtensionMonoidalFunctor R H A) V W

/-- The unit comparison is comodule scalar extension's unit comparison followed by base
change of the representation--comodule unit comparison, with the composite's object transport. -/
theorem scalarExtensionMonoidalFunctor_ε :
    ε (scalarExtensionMonoidalFunctor R H A).toFunctor =
      (ε (FGComoduleCat.scalarExtensionFunctor R H A) ≫
        (FGComoduleCat.scalarExtensionFunctor R H A).map (ε (toComodule R H))) ≫
        eqToHom ((congrArg (fun F ↦ F.obj (𝟙_ (FGPointRepresentationCat.{u, v, u} R H)))
          (scalarExtensionMonoidalFunctor_toFunctor R H A)).trans
            (Functor.comp_obj (toComodule R H) (FGComoduleCat.scalarExtensionFunctor R H A)
              (𝟙_ (FGPointRepresentationCat.{u, v, u} R H)))).symm := by
  apply eq_of_heq
  rw [heq_comp_eqToHom_iff]
  exact Functor.precomposeLaxMonoidal_obj_ε
    (toComodule R H) (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)

end FGPointRepresentationCat

end TauCeti
