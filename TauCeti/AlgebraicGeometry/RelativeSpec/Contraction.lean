/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import TauCeti.AlgebraicGeometry.AffineSpace.Ring
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Scaling
public import TauCeti.AlgebraicGeometry.RelativeSpec.UniversalProperty

/-!
# The contraction action on the relative spectrum of a graded algebra

Let `A = (Aₙ)ₙ` be a graded quasicoherent algebra on a scheme `X`. The relative spectrum
`C = Spec_X (⨁ₙ Aₙ)` carries an action of the multiplicative monoid of the affine line
`𝔸¹_X = 𝔸(PUnit; X)`, the *contraction*: a point `t : T ⟶ C` over `X` pulls back regular
functions along an algebra map `⨁ₙ Aₙ ⟶ q_* 𝒪_T` (`relativeSpecHomIso`), and for a function
`c : T ⟶ 𝔸¹_X` the point `c • t` is the one whose algebra map is multiplied by `cⁿ` on the
summand `Aₙ` (`GradedQuasicoherentAlgebra.scaleHom`). On an affine open `Spec R` of `X` this is the
coaction `⨁ₙ Aₙ → R[t] ⊗_R ⨁ₙ Aₙ`, `a ↦ tⁿ ⊗ a` for `a` of degree `n`. When `A` is a cone algebra,
`C` is a cone in the sense of Fulton and of Behrend–Fantechi, and this is its `𝔸¹`-action.

By the Yoneda lemma the contraction is a morphism `𝔸¹_X ×_X C ⟶ C` over `X`
(`gradedRelativeSpecSMul`), an action of the monoid object `𝔸¹_X` of `Over X` (Mathlib's
`ModObj`). Morphisms of graded algebras induce equivariant morphisms of relative spectra.

When the unit `𝒪_X ⟶ A₀` is an isomorphism, for instance for a cone algebra, `C` has a *vertex*
`X ⟶ C` over `X` (`gradedRelativeSpecVertex`), the relative spectrum of the augmentation
`⨁ₙ Aₙ ⟶ A₀ = 𝒪_X`. Contracting any point by `0` lands on the vertex, the vertex is fixed by the
action, and morphisms of graded algebras preserve vertices. For `A = Sym F` the contraction is the
scalar multiplication of the linear scheme `Spec_X (Sym F)` and the vertex is its zero section
(`gradedRelativeSpecSMul_gradedSymmetricAlgebra` and
`gradedRelativeSpecVertex_gradedSymmetricAlgebra`, proved where the linear structure is
available).

## Main declarations

* `TauCeti.AlgebraicGeometry.gradedRelativeSpecSMul`: the contraction
  `𝔸¹_X ×_X Spec_X (⨁ₙ Aₙ) ⟶ Spec_X (⨁ₙ Aₙ)`, characterized on points by
  `relativeSpecHomIso_hom_app_app_lift_comp_gradedRelativeSpecSMul`;
* `TauCeti.AlgebraicGeometry.modObjGradedRelativeSpec`: it is an action of the monoid object
  `𝔸¹_X`;
* `TauCeti.AlgebraicGeometry.isModHom_relativeSpec_map_toQuasicoherentAlgebra_map`: morphisms of
  graded algebras induce equivariant morphisms;
* `TauCeti.AlgebraicGeometry.gradedRelativeSpecVertex`: the vertex, characterized on points by
  `relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecVertex`;
* `TauCeti.AlgebraicGeometry.lift_zero_comp_gradedRelativeSpecSMul`: `0 • t` is the vertex;
* `TauCeti.AlgebraicGeometry.lift_toUnit_comp_gradedRelativeSpecVertex_comp_gradedRelativeSpecSMul`:
  the vertex is fixed by the action;
* `TauCeti.AlgebraicGeometry.gradedRelativeSpecVertex_comp_relativeSpec_map`: morphisms of
  graded algebras preserve vertices.

## References

* W. Fulton, *Intersection Theory*, 2nd ed., Appendix B.5 (cones).
* K. Behrend and B. Fantechi, *The intrinsic normal cone*, Invent. Math. 128 (1997), §1.
* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1), for the linear case.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry GradedQuasicoherentAlgebra

universe u

noncomputable section

variable {X : Scheme.{u}} (A : GradedQuasicoherentAlgebra X)

/-- **The contraction action.** The morphism `𝔸¹_X ×_X Spec_X (⨁ₙ Aₙ) ⟶ Spec_X (⨁ₙ Aₙ)` over
`X` whose algebra map is that of the second projection multiplied by `cⁿ` on the summand `Aₙ`,
where `c` is the function given by the first projection. -/
def gradedRelativeSpecSMul :
    𝔸(PUnit.{u + 1}; X).asOver X ⊗ (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A))) ⟶
      (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A))) :=
  ((relativeSpecHomIso X).inv.app _).app _
    (scaleHom A _ (((relativeSpecHomIso X).hom.app _).app _ (snd _ _))
      (AffineSpace.homAsOverEquiv _ (fst _ _) .unit))

/-- The algebra map of the contraction is the scaled algebra map of the second projection. -/
theorem relativeSpecHomIso_hom_app_app_gradedRelativeSpecSMul :
    ((relativeSpecHomIso X).hom.app _).app _ (gradedRelativeSpecSMul A) =
      scaleHom A _ (((relativeSpecHomIso X).hom.app _).app _ (snd _ _))
        (AffineSpace.homAsOverEquiv _ (fst _ _) .unit) :=
  relativeSpecHomIso_hom_app_app_inv_app_app _ _ _

/-- The algebra map of a morphism `f` into `𝔸¹_X ×_X Spec_X (⨁ₙ Aₙ)` followed by the contraction
is the algebra map of its second component scaled by its first component. -/
theorem relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecSMul {T : Over X}
    (f : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X ⊗ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A)))) :
    ((relativeSpecHomIso X).hom.app _).app (op T) (f ≫ gradedRelativeSpecSMul A) =
      scaleHom A T.hom (((relativeSpecHomIso X).hom.app _).app (op T) (f ≫ snd _ _))
        (AffineSpace.homAsOverEquiv T (f ≫ fst _ _) .unit) := by
  rw [relativeSpecHomIso_hom_app_app_comp, relativeSpecHomIso_hom_app_app_gradedRelativeSpecSMul]
  refine (scaleHom_comp_pushforwardStructureAlgebraMap A _ _ _ f.left (Over.w f)).trans ?_
  exact congrArg₂ (scaleHom A T.hom) (relativeSpecHomIso_hom_app_app_comp _ f (snd _ _)).symm
    (AffineSpace.homAsOverEquiv_comp f (fst _ _) .unit).symm

open scoped CommRingObj in
/-- **`Spec_X (⨁ₙ Aₙ)` is acted on by the affine line.** The contraction
`gradedRelativeSpecSMul` is an action of the multiplicative monoid object `𝔸¹_X` of `Over X`. -/
instance modObjGradedRelativeSpec :
    ModObj (𝔸(PUnit.{u + 1}; X).asOver X) ((MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A)))) where
  smul := gradedRelativeSpecSMul A
  one_smul := by
    dsimp only [selfLeftAction_actionHomLeft, selfLeftAction_actionObj,
      selfLeftAction_actionUnitIso]
    apply relativeSpecHomIso_hom_app_app_injective
    -- the scalar component of `η ▷ Spec_X (⨁ₙ Aₙ)` is the function `1`
    have h : fst (𝟙_ (Over X)) ((MorphismProperty.Over.forget _ _ X).obj
          ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A)))) ≫
        η[𝔸(PUnit.{u + 1}; X).asOver X] = 1 := by
      rw [Hom.one_def, toUnit_unique (fst _ _) (toUnit _)]
    rw [relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecSMul, whiskerRight_fst,
      whiskerRight_snd, h, AffineSpace.homAsOverEquiv_one, Pi.one_apply, leftUnitor_hom]
    exact scaleHom_one A _ _
  mul_smul := by
    dsimp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionObj, selfLeftAction_actionAssocIso]
    apply relativeSpecHomIso_hom_app_app_injective
    -- the scalar component of `μ ▷ Spec_X (⨁ₙ Aₙ)` is the product of the two scalar components
    have h : fst (𝔸(PUnit.{u + 1}; X).asOver X ⊗ 𝔸(PUnit.{u + 1}; X).asOver X)
          ((MorphismProperty.Over.forget _ _ X).obj
            ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A)))) ≫
        μ[𝔸(PUnit.{u + 1}; X).asOver X] =
          fst _ _ ≫ fst _ _ * fst _ _ ≫ snd _ _ := by
      rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
    simp only [← Category.assoc, relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecSMul]
    simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd, whiskerLeft_snd]
    simp only [← Category.assoc, relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecSMul]
    simp only [Category.assoc, whiskerLeft_fst, associator_hom_fst, associator_hom_snd_fst,
      associator_hom_snd_snd, h, AffineSpace.homAsOverEquiv_mul, Pi.mul_apply]
    exact (scaleHom_scaleHom A _ _ _ _).symm

/-- The action of `𝔸¹_X` on `Spec_X (⨁ₙ Aₙ)` is `gradedRelativeSpecSMul`. -/
lemma smul_gradedRelativeSpec :
    γ[𝔸(PUnit.{u + 1}; X).asOver X, (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A)))] =
      gradedRelativeSpecSMul A :=
  (rfl)

/-- **Contracting points.** For a scheme `q : T ⟶ X` over `X`, a function `a : T ⟶ 𝔸¹_X` and a
point `t : T ⟶ Spec_X (⨁ₙ Aₙ)`, the algebra map of `a • t` is that of `t` multiplied by `aⁿ` on
the summand `Aₙ`. -/
theorem relativeSpecHomIso_hom_app_app_lift_comp_gradedRelativeSpecSMul {T : Over X}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A)))) :
    ((relativeSpecHomIso X).hom.app _).app (op T) (lift a t ≫ gradedRelativeSpecSMul A) =
      scaleHom A T.hom (((relativeSpecHomIso X).hom.app _).app (op T) t)
        (AffineSpace.homAsOverEquiv T a .unit) := by
  rw [relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecSMul, lift_fst, lift_snd]

/-- **Morphisms of graded algebras are equivariant.** For a morphism `f : A ⟶ A'` of graded
quasicoherent algebras, the induced morphism `Spec_X (⨁ₙ A'ₙ) ⟶ Spec_X (⨁ₙ Aₙ)` commutes with
the contractions. -/
instance isModHom_relativeSpec_map_toQuasicoherentAlgebra_map {A' : GradedQuasicoherentAlgebra X}
    (f : A ⟶ A') :
    IsModHom (𝔸(PUnit.{u + 1}; X).asOver X) ((MorphismProperty.Over.forget _ _ X).map
      ((relativeSpec X).map (toQuasicoherentAlgebra.map f).op)) where
  smul_hom := by
    dsimp only [selfLeftAction_actionHomRight, selfLeftAction_actionObj]
    rw [smul_gradedRelativeSpec, smul_gradedRelativeSpec]
    apply relativeSpecHomIso_hom_app_app_injective
    rw [relativeSpecHomIso_hom_app_app_comp_relativeSpec_map,
      relativeSpecHomIso_hom_app_app_gradedRelativeSpecSMul,
      relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecSMul, whiskerLeft_fst,
      whiskerLeft_snd, relativeSpecHomIso_hom_app_app_comp_relativeSpec_map]
    exact toQuasicoherentAlgebra_map_comp_scaleHom A _ _ f _

section Vertex

variable [IsIso A.obj.toMon.one]

/-- **The vertex.** If the unit `𝒪_X ⟶ A₀` is an isomorphism, the section `X ⟶ Spec_X (⨁ₙ Aₙ)`
over `X` given by the augmentation `⨁ₙ Aₙ ⟶ A₀ = 𝒪_X`, which kills every summand of positive
degree. -/
def gradedRelativeSpecVertex : 𝟙_ (Over X) ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A))) :=
  ((relativeSpecHomIso X).inv.app _).app _
    (augmentation A (𝟙_ (Over X)).hom.pushforwardStructureAlgebra)

/-- The algebra map of the vertex is the augmentation. -/
theorem relativeSpecHomIso_hom_app_app_gradedRelativeSpecVertex :
    ((relativeSpecHomIso X).hom.app _).app _ (gradedRelativeSpecVertex A) =
      augmentation A (𝟙_ (Over X)).hom.pushforwardStructureAlgebra :=
  relativeSpecHomIso_hom_app_app_inv_app_app _ _ _

/-- For a scheme `q : T ⟶ X` over `X`, the algebra map of the point `T ⟶ X ⟶ Spec_X (⨁ₙ Aₙ)`
through the vertex is the augmentation `⨁ₙ Aₙ ⟶ q_* 𝒪_T`. -/
theorem relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecVertex {T : Over X}
    (g : T ⟶ 𝟙_ (Over X)) :
    ((relativeSpecHomIso X).hom.app _).app (op T) (g ≫ gradedRelativeSpecVertex A) =
      augmentation A T.hom.pushforwardStructureAlgebra := by
  rw [relativeSpecHomIso_hom_app_app_comp]
  exact (congrArg (· ≫ _) (relativeSpecHomIso_hom_app_app_gradedRelativeSpecVertex A)).trans
    (augmentation_comp A _)

open scoped CommRingObj in
/-- **Contracting by zero gives the vertex.** For every point `t : T ⟶ Spec_X (⨁ₙ Aₙ)`, the
point `0 • t` factors through the vertex. -/
theorem lift_zero_comp_gradedRelativeSpecSMul {T : Over X}
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op (toQuasicoherentAlgebra.obj A)))) :
    lift 0 t ≫ gradedRelativeSpecSMul A = toUnit T ≫ gradedRelativeSpecVertex A := by
  apply relativeSpecHomIso_hom_app_app_injective
  have h : AffineSpace.homAsOverEquiv T (0 : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X) .unit = 0 := by
    rw [← AffineSpace.homAsOverRingEquiv_apply, map_zero, Pi.zero_apply]
  rw [relativeSpecHomIso_hom_app_app_lift_comp_gradedRelativeSpecSMul, h,
    relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecVertex]
  exact scaleHom_zero A _ _

/-- **The vertex is fixed by the contraction.** -/
theorem lift_toUnit_comp_gradedRelativeSpecVertex_comp_gradedRelativeSpecSMul {T : Over X}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X) :
    lift a (toUnit T ≫ gradedRelativeSpecVertex A) ≫ gradedRelativeSpecSMul A =
      toUnit T ≫ gradedRelativeSpecVertex A := by
  apply relativeSpecHomIso_hom_app_app_injective
  rw [relativeSpecHomIso_hom_app_app_lift_comp_gradedRelativeSpecSMul,
    relativeSpecHomIso_hom_app_app_comp_gradedRelativeSpecVertex]
  exact scaleHom_augmentation A _ _

/-- **Morphisms of graded algebras preserve vertices.** -/
@[reassoc (attr := simp)]
theorem gradedRelativeSpecVertex_comp_relativeSpec_map {A' : GradedQuasicoherentAlgebra X}
    [IsIso A'.obj.toMon.one] (f : A ⟶ A') :
    gradedRelativeSpecVertex A' ≫ (MorphismProperty.Over.forget _ _ X).map
      ((relativeSpec X).map (toQuasicoherentAlgebra.map f).op) = gradedRelativeSpecVertex A := by
  apply relativeSpecHomIso_hom_app_app_injective
  rw [relativeSpecHomIso_hom_app_app_comp_relativeSpec_map,
    relativeSpecHomIso_hom_app_app_gradedRelativeSpecVertex,
    relativeSpecHomIso_hom_app_app_gradedRelativeSpecVertex]
  exact toQuasicoherentAlgebra_map_comp_augmentation A f

end Vertex

end

end TauCeti.AlgebraicGeometry
