/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import TauCeti.AlgebraicGeometry.AffineSpace.Ring
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Group

/-!
# Scalar multiplication on `Spec_X (Sym F)`

For a quasicoherent sheaf `F` on a scheme `X`, the points of `𝕍(F) = Spec_X (Sym F)` over a scheme
`q : T ⟶ X` are the module maps `F ⟶ q_* 𝒪_T` (`relativeSpecSymmetricAlgebraHomEquiv`), and these
form a module over the ring `Γ(T, ⊤)` of global functions on `T`: a function `c` acts by composing
with the pushforward of multiplication by `c` on `𝒪_T`. Pulling back along a morphism over `X` is
semilinear for the pullback of functions, and the points of the affine line
`𝔸¹_X = 𝔸(PUnit; X)` over `T` are exactly the global functions on `T`
(`AlgebraicGeometry.AffineSpace.homAsOverRingEquiv`). By the Yoneda lemma this gives the scalar
multiplication `𝔸¹_X ×_X 𝕍(F) ⟶ 𝕍(F)` (Stacks Project, Tag 01M1, and EGA II, 1.7).

Together with the additive group structure of `𝕍(F)`
(`TauCeti.AlgebraicGeometry.addGrpObjRelativeSpecSymmetricAlgebra`), this makes `𝕍(F)` a module
scheme over the ring scheme `𝔸¹_X`: the action is unital and associative (Mathlib's `ModObj` for
the multiplicative monoid object `𝔸¹_X`), it distributes over the addition of `𝔸¹_X` and over the
addition of `𝕍(F)`, and the morphism `𝕍(F) ⟶ 𝕍(F')` induced by a map `F' ⟶ F` is `𝔸¹_X`-linear.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraSMul` and
  `TauCeti.AlgebraicGeometry.modObjRelativeSpecSymmetricAlgebra`: the scalar multiplication
  `𝔸¹_X ×_X Spec_X (Sym F) ⟶ Spec_X (Sym F)`, an action of the monoid object `𝔸¹_X`;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraHomEquiv_lift_comp_smul`: the module map
  of a scalar multiple `a • t` is the module map of `t` multiplied by the function `a`, and
  `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraPullbackHomEquiv_lift_comp_smul`: the
  same for linear functionals `q^* F ⟶ 𝒪_T`;
* `TauCeti.AlgebraicGeometry.lift_add_right_comp_relativeSpecSymmetricAlgebraSMul` and
  `TauCeti.AlgebraicGeometry.lift_add_left_comp_relativeSpecSymmetricAlgebraSMul`: distributivity
  over the addition of points and of scalars;
* `TauCeti.AlgebraicGeometry.isModHom_relativeSpec_map`: the morphism induced by `F' ⟶ F` is
  `𝔸¹_X`-linear.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (F : QuasicoherentSheaf X)

/-- The scalar multiplication `𝔸¹_X ×_X Spec_X (Sym F) ⟶ Spec_X (Sym F)`: the point of
`Spec_X (Sym F)` whose module map is the module map of the second projection multiplied by the
function given by the first projection. -/
def relativeSpecSymmetricAlgebraSMul :
    𝔸(PUnit.{u + 1}; X).asOver X ⊗ (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F))) ⟶
      (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F))) :=
  (relativeSpecSymmetricAlgebraHomEquiv F _).symm
    (relativeSpecSymmetricAlgebraHomEquiv F _ (snd _ _) ≫
      (Scheme.Modules.pushforward _).map (Scheme.Modules.globalSectionsSmul _
        (AffineSpace.homAsOverEquiv _ (fst _ _) .unit)))

/-- The module map of a morphism `f` into `𝔸¹_X ×_X Spec_X (Sym F)` followed by the scalar
multiplication is the module map of its second component multiplied by its first component. -/
lemma relativeSpecSymmetricAlgebraHomEquiv_comp_smul {T : Over X}
    (f : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X ⊗ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraHomEquiv F T (f ≫ relativeSpecSymmetricAlgebraSMul F) =
      relativeSpecSymmetricAlgebraHomEquiv F T (f ≫ snd _ _) ≫
        (Scheme.Modules.pushforward T.hom).map (Scheme.Modules.globalSectionsSmul _
          (AffineSpace.homAsOverEquiv T (f ≫ fst _ _) .unit)) := by
  rw [relativeSpecSymmetricAlgebraHomEquiv_comp, relativeSpecSymmetricAlgebraSMul,
    Equiv.apply_symm_apply, relativeSpecSymmetricAlgebraHomEquiv_comp,
    AffineSpace.homAsOverEquiv_comp]
  -- pulling back along `f` commutes with multiplication by the scalar component; associativity
  -- is applied by hand since these composites mix the `X.Modules` and `SheafOfModules` category
  -- instances, on which `rw [Category.assoc]` cannot build its motive
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (Scheme.Hom.globalSectionsSmul_pushforwardStructureAlgebraMap f.left (Over.w f) _)).trans
      (Category.assoc _ _ _).symm)

/-- **Scalar multiples of points of `Spec_X (Sym F)`.** For a scheme `q : T ⟶ X` over `X`, a
function `a : T ⟶ 𝔸¹_X` and a point `t : T ⟶ Spec_X (Sym F)`, the module map `F ⟶ q_* 𝒪_T` of the
scalar multiple `a • t` is that of `t` composed with the pushforward of multiplication by `a` on
`𝒪_T`. -/
lemma relativeSpecSymmetricAlgebraHomEquiv_lift_comp_smul {T : Over X}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraHomEquiv F T (lift a t ≫ relativeSpecSymmetricAlgebraSMul F) =
      relativeSpecSymmetricAlgebraHomEquiv F T t ≫
        (Scheme.Modules.pushforward T.hom).map (Scheme.Modules.globalSectionsSmul _
          (AffineSpace.homAsOverEquiv T a .unit)) := by
  rw [relativeSpecSymmetricAlgebraHomEquiv_comp_smul, lift_fst, lift_snd]

/-- **Scalar multiples of points of `Spec_X (Sym F)` as linear functionals.** The linear
functional `q^* F ⟶ 𝒪_T` of the scalar multiple `a • t` is that of `t` followed by multiplication
by `a` on `𝒪_T`. -/
lemma relativeSpecSymmetricAlgebraPullbackHomEquiv_lift_comp_smul {T : Over X}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraPullbackHomEquiv F T
        (lift a t ≫ relativeSpecSymmetricAlgebraSMul F) =
      relativeSpecSymmetricAlgebraPullbackHomEquiv F T t ≫
        Scheme.Modules.globalSectionsSmul _ (AffineSpace.homAsOverEquiv T a .unit) := by
  rw [relativeSpecSymmetricAlgebraPullbackHomEquiv_apply,
    relativeSpecSymmetricAlgebraPullbackHomEquiv_apply,
    relativeSpecSymmetricAlgebraHomEquiv_lift_comp_smul]
  exact Adjunction.homEquiv_naturality_right_symm _ _ _

open scoped CommRingObj

/-- **`Spec_X (Sym F)` is a module over the affine line.** The scalar multiplication
`relativeSpecSymmetricAlgebraSMul` is an action of the multiplicative monoid object `𝔸¹_X` of
`Over X`. -/
instance modObjRelativeSpecSymmetricAlgebra :
    ModObj (𝔸(PUnit.{u + 1}; X).asOver X) ((MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) where
  smul := relativeSpecSymmetricAlgebraSMul F
  one_smul := by
    dsimp only [selfLeftAction_actionHomLeft, selfLeftAction_actionObj,
      selfLeftAction_actionUnitIso]
    apply (relativeSpecSymmetricAlgebraHomEquiv F _).injective
    -- the scalar component of `η ▷ 𝕍(F)` is the function `1`
    have h : fst (𝟙_ (Over X)) ((MorphismProperty.Over.forget _ _ X).obj
          ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) ≫
        η[𝔸(PUnit.{u + 1}; X).asOver X] = 1 := by
      rw [Hom.one_def, toUnit_unique (fst _ _) (toUnit _)]
    rw [relativeSpecSymmetricAlgebraHomEquiv_comp_smul, whiskerRight_fst, whiskerRight_snd, h,
      AffineSpace.homAsOverEquiv_one, Pi.one_apply,
      Scheme.Modules.globalSectionsSmul_one, CategoryTheory.Functor.map_id, leftUnitor_hom]
    exact Category.comp_id _
  mul_smul := by
    dsimp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionObj, selfLeftAction_actionAssocIso]
    apply (relativeSpecSymmetricAlgebraHomEquiv F _).injective
    -- the scalar component of `μ ▷ 𝕍(F)` is the product of the two scalar components
    have h : fst (𝔸(PUnit.{u + 1}; X).asOver X ⊗ 𝔸(PUnit.{u + 1}; X).asOver X)
          ((MorphismProperty.Over.forget _ _ X).obj
            ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) ≫
        μ[𝔸(PUnit.{u + 1}; X).asOver X] =
          fst _ _ ≫ fst _ _ * fst _ _ ≫ snd _ _ := by
      rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
    simp only [← Category.assoc, relativeSpecSymmetricAlgebraHomEquiv_comp_smul]
    simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd, whiskerLeft_snd]
    simp only [← Category.assoc, relativeSpecSymmetricAlgebraHomEquiv_comp_smul]
    simp only [Category.assoc, whiskerLeft_fst, associator_hom_fst, associator_hom_snd_fst,
      associator_hom_snd_snd, h, AffineSpace.homAsOverEquiv_mul, Pi.mul_apply,
      Scheme.Modules.globalSectionsSmul_mul, CategoryTheory.Functor.map_comp]
    -- `simp only [Category.assoc]` does not apply across the mixed category instances
    exact (Category.assoc _ _ _).symm

/-- The action of `𝔸¹_X` on `Spec_X (Sym F)` is `relativeSpecSymmetricAlgebraSMul`. -/
@[simp]
lemma smul_relativeSpecSymmetricAlgebra :
    γ[𝔸(PUnit.{u + 1}; X).asOver X, (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))] =
      relativeSpecSymmetricAlgebraSMul F :=
  (rfl)

open scoped AddMonObj

/-- The scalar multiplication of `Spec_X (Sym F)` distributes over the addition of points:
`a • (t₁ + t₂) = a • t₁ + a • t₂`. -/
lemma lift_add_right_comp_relativeSpecSymmetricAlgebraSMul {T : Over X}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X)
    (t₁ t₂ : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    lift a (t₁ + t₂) ≫ relativeSpecSymmetricAlgebraSMul F =
      lift a t₁ ≫ relativeSpecSymmetricAlgebraSMul F +
        lift a t₂ ≫ relativeSpecSymmetricAlgebraSMul F := by
  apply (relativeSpecSymmetricAlgebraHomEquiv F T).injective
  simp only [relativeSpecSymmetricAlgebraHomEquiv_add,
    relativeSpecSymmetricAlgebraHomEquiv_lift_comp_smul]
  exact Preadditive.add_comp (C := X.Modules) _ _ _ _ _ _

/-- The scalar multiplication of `Spec_X (Sym F)` distributes over the addition of scalars:
`(a₁ + a₂) • t = a₁ • t + a₂ • t`. -/
lemma lift_add_left_comp_relativeSpecSymmetricAlgebraSMul {T : Over X}
    (a₁ a₂ : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    lift (a₁ + a₂) t ≫ relativeSpecSymmetricAlgebraSMul F =
      lift a₁ t ≫ relativeSpecSymmetricAlgebraSMul F +
        lift a₂ t ≫ relativeSpecSymmetricAlgebraSMul F := by
  apply (relativeSpecSymmetricAlgebraHomEquiv F T).injective
  simp only [relativeSpecSymmetricAlgebraHomEquiv_add,
    relativeSpecSymmetricAlgebraHomEquiv_lift_comp_smul, AffineSpace.homAsOverEquiv_add,
    Pi.add_apply, Scheme.Modules.globalSectionsSmul_add, (Scheme.Modules.pushforward T.hom).map_add]
  exact Preadditive.comp_add (C := X.Modules) _ _ _ _ _ _

/-- **Morphisms of linear schemes are linear.** For a map `a : F' ⟶ F` of quasicoherent sheaves,
the induced morphism `Spec_X (Sym F) ⟶ Spec_X (Sym F')` commutes with the scalar multiplications
by `𝔸¹_X`. -/
instance isModHom_relativeSpec_map {F' F : QuasicoherentSheaf X} (a : F' ⟶ F) :
    IsModHom (𝔸(PUnit.{u + 1}; X).asOver X) ((MorphismProperty.Over.forget _ _ X).map
      ((relativeSpec X).map ((symmetricAlgebra X).map a).op)) where
  smul_hom := by
    dsimp only [selfLeftAction_actionHomRight, selfLeftAction_actionObj]
    rw [smul_relativeSpecSymmetricAlgebra, smul_relativeSpecSymmetricAlgebra]
    apply (relativeSpecSymmetricAlgebraHomEquiv F' _).injective
    -- both module maps are `a` followed by the module map of the scalar multiplication on `F`
    rw [relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map,
      relativeSpecSymmetricAlgebraHomEquiv_comp_smul, whiskerLeft_fst, whiskerLeft_snd,
      relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map, relativeSpecSymmetricAlgebraSMul,
      Equiv.apply_symm_apply]
    exact (Category.assoc _ _ _).symm

end

end TauCeti.AlgebraicGeometry
