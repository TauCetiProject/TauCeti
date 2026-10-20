/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Functor
public import TauCeti.CategoryTheory.Monoidal.Rigid.MixedDualFunctor

/-!
# The double duals are inverse monoidal autoequivalences

In a rigid monoidal category `C`, the right dual functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ`, `X ↦ Xᘁ`, and the left
dual functor, `X ↦ ᘁX`, are both monoidal equivalences. A quasi-inverse of the right dual functor
takes left duals, and one of the left dual functor takes right duals: the units are the monoidal
trivializations `X ≅ ᘁ(Xᘁ)` and `X ≅ (ᘁX)ᘁ` of the mixed double duals, and the counits are
the trivializations exchanged and read in `(Cᵒᵖ)ᴹᵒᵖ`: the counit of each equivalence is the
unit of the other.

Composing the first equivalence with the inverse of the second gives a monoidal autoequivalence
of `C` whose functor is the double right dual functor `X ↦ Xᘁᘁ` and whose inverse is the double
left dual functor `X ↦ ᘁ(ᘁX)`. So the two double duals are mutually inverse monoidal
autoequivalences, and their composites in either order are trivialized by monoidal natural
isomorphisms

```text
doubleRightDualFunctor C ⋙ doubleLeftDualFunctor C ≅ 𝟭 C,
doubleLeftDualFunctor C ⋙ doubleRightDualFunctor C ≅ 𝟭 C.
```

There is no natural isomorphism between the double right dual and the double left dual functors
in general: it would make the fourfold dual isomorphic to the identity. The monoidality of the
units comes from `TauCeti.leftDualRightDualIso_isMonoidal` and
`TauCeti.rightDualLeftDualIso_isMonoidal`; that of the composite isomorphisms is then a general
property of monoidal equivalences (`CategoryTheory.Equivalence.isMonoidal_of_isMonoidal_unit`).

## Main declarations

* `TauCeti.rightDualEquivalence` and `TauCeti.leftDualEquivalence`: the right and left dual
  functors as monoidal equivalences `C ≌ (Cᵒᵖ)ᴹᵒᵖ`;
* `TauCeti.doubleRightDualEquivalence`: the monoidal autoequivalence of `C` with functor
  `doubleRightDualFunctor C` and inverse `doubleLeftDualFunctor C`;
* `TauCeti.doubleRightDualCompDoubleLeftDual` and `TauCeti.doubleLeftDualCompDoubleRightDual`: the
  monoidal natural isomorphisms trivializing the two composites, with components computed by
  `TauCeti.doubleRightDualCompDoubleLeftDual_hom_app` and
  `TauCeti.doubleLeftDualCompDoubleRightDual_hom_app`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite ExactPairing

universe v u

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The right dual functor of a rigid monoidal category, as an equivalence `C ≌ (Cᵒᵖ)ᴹᵒᵖ`. Its
inverse takes left duals; its unit is the trivialization `X ≅ ᘁ(Xᘁ)` and its counit is the
trivialization `(ᘁX)ᘁ ≅ X` read in `(Cᵒᵖ)ᴹᵒᵖ`. -/
-- Exposed: the statements of the unit and counit lemmas below only typecheck once the functor
-- and inverse unfold.
@[expose]
noncomputable def rightDualEquivalence : C ≌ Cᵒᵖᴹᵒᵖ where
  functor := rightDualFunctor C
  inverse := (leftDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor
  unitIso := (leftDualRightDualIso C).symm
  counitIso := NatIso.ofComponents
    (fun X => (mopFunctor Cᵒᵖ).mapIso
      (rightDualIso (RightRigidCategory.rightDual (ᘁX.unmop.unop)).exact
        HasLeftDual.exact).symm.op)
    fun {X Y} f => by
      apply Quiver.Hom.unmop_inj
      apply Quiver.Hom.unop_inj
      have h := (rightDualLeftDualIso C).inv.naturality f.unmop.unop
      rw [rightDualLeftDualFunctor_map, rightDualLeftDualIso_inv_app,
        rightDualLeftDualIso_inv_app,
        ← @rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual _)
          (RightRigidCategory.rightDual _)] at h
      -- Removing the wrappers is the identity on morphisms, and the composite sends `f` to
      -- the right adjoint mate of its left adjoint mate, by definition.
      exact h.symm
  functor_unitIso_comp X := by
    rw [Iso.symm_hom, leftDualRightDualIso_inv_app]
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    -- With `A` the chosen left dual of `Xᘁ`, the right mate of the comparison `X ≅ A` of left
    -- duals of `Xᘁ` is the comparison of the two right duals `Aᘁ` and `Xᘁ` of `A`.
    have key {A A' : C} (q : ExactPairing A Xᘁ) (p : ExactPairing A A') :
        (rightDualIso p q).inv ≫
          rightMate HasRightDual.exact p (leftDualIso q HasRightDual.exact).inv = 𝟙 Xᘁ := by
      rw [leftDualIso_inv, ← leftDualIso_hom, rightMate_leftDualIso_hom, ← rightDualIso_hom,
        Iso.inv_hom_id]
    have h := key (LeftRigidCategory.leftDual Xᘁ).exact (RightRigidCategory.rightDual _).exact
    rw [← @rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual _)
      (RightRigidCategory.rightDual _)] at h
    -- Removing the wrappers is the identity on morphisms, and the right dual functor sends a
    -- morphism to its right adjoint mate, by definition.
    exact h

/-- The left dual functor of a rigid monoidal category, as an equivalence `C ≌ (Cᵒᵖ)ᴹᵒᵖ`. Its
inverse takes right duals; its unit is the trivialization `X ≅ (ᘁX)ᘁ` and its counit is the
trivialization `ᘁ(Xᘁ) ≅ X` read in `(Cᵒᵖ)ᴹᵒᵖ`. -/
-- Exposed: the statements of the unit and counit lemmas below only typecheck once the functor
-- and inverse unfold.
@[expose]
noncomputable def leftDualEquivalence : C ≌ Cᵒᵖᴹᵒᵖ where
  functor := leftDualFunctor C
  inverse := (rightDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor
  unitIso := (rightDualLeftDualIso C).symm
  counitIso := NatIso.ofComponents
    (fun X => (mopFunctor Cᵒᵖ).mapIso
      (leftDualIso (LeftRigidCategory.leftDual (X.unmop.unop)ᘁ).exact
        HasRightDual.exact).symm.op)
    fun {X Y} f => by
      apply Quiver.Hom.unmop_inj
      apply Quiver.Hom.unop_inj
      have h := (leftDualRightDualIso C).inv.naturality f.unmop.unop
      rw [leftDualRightDualFunctor_map, leftDualRightDualIso_inv_app,
        leftDualRightDualIso_inv_app,
        ← @leftAdjointMate_eq_leftMate C _ _ _ _ (LeftRigidCategory.leftDual _)
          (LeftRigidCategory.leftDual _)] at h
      -- Removing the wrappers is the identity on morphisms, and the composite sends `f` to
      -- the left adjoint mate of its right adjoint mate, by definition.
      exact h.symm
  functor_unitIso_comp X := by
    rw [Iso.symm_hom, rightDualLeftDualIso_inv_app]
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    -- With `A` the chosen right dual of `ᘁX`, the left mate of the comparison `X ≅ A` of right
    -- duals of `ᘁX` is the comparison of the two left duals `ᘁA` and `ᘁX` of `A`.
    have key {A A' : C} (q : ExactPairing (ᘁX) A) (p : ExactPairing A' A) :
        (leftDualIso p q).inv ≫
          leftMate HasLeftDual.exact p (rightDualIso q HasLeftDual.exact).inv = 𝟙 (ᘁX) := by
      rw [rightDualIso_inv, ← rightDualIso_hom, leftMate_rightDualIso_hom, ← leftDualIso_hom,
        Iso.inv_hom_id]
    have h := key (RightRigidCategory.rightDual (ᘁX)).exact (LeftRigidCategory.leftDual _).exact
    rw [← @leftAdjointMate_eq_leftMate C _ _ _ _ (LeftRigidCategory.leftDual _)
      (LeftRigidCategory.leftDual _)] at h
    -- Removing the wrappers is the identity on morphisms, and the left dual functor sends a
    -- morphism to its left adjoint mate, by definition.
    exact h

variable {C} in
/-- The counit of `rightDualEquivalence C` at `X` is the inverse of the trivialization
`(ᘁX)ᘁ ≅ X`, read in `(Cᵒᵖ)ᴹᵒᵖ`. -/
@[simp]
theorem rightDualEquivalence_counitIso_hom_app (X : Cᵒᵖᴹᵒᵖ) :
    (rightDualEquivalence C).counitIso.hom.app X =
      ((rightDualLeftDualIso C).inv.app X.unmop.unop).op.mop := by
  rw [rightDualLeftDualIso_inv_app]
  -- The counit is defined by these components, through `mopFunctor`.
  rfl

variable {C} in
/-- The counit of `leftDualEquivalence C` at `X` is the inverse of the trivialization
`ᘁ(Xᘁ) ≅ X`, read in `(Cᵒᵖ)ᴹᵒᵖ`. -/
@[simp]
theorem leftDualEquivalence_counitIso_hom_app (X : Cᵒᵖᴹᵒᵖ) :
    (leftDualEquivalence C).counitIso.hom.app X =
      ((leftDualRightDualIso C).inv.app X.unmop.unop).op.mop := by
  rw [leftDualRightDualIso_inv_app]
  -- The counit is defined by these components, through `mopFunctor`.
  rfl

/-- The functor of `rightDualEquivalence C` is the right dual functor. -/
@[simp]
theorem rightDualEquivalence_functor : (rightDualEquivalence C).functor = rightDualFunctor C :=
  (rfl)

/-- The inverse of `rightDualEquivalence C` takes left duals. -/
@[simp]
theorem rightDualEquivalence_inverse : (rightDualEquivalence C).inverse =
    (leftDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor :=
  rfl

/-- The unit of `rightDualEquivalence C` is the inverse of the trivialization `ᘁ(Xᘁ) ≅ X`. -/
@[simp]
theorem rightDualEquivalence_unitIso :
    (rightDualEquivalence C).unitIso = (leftDualRightDualIso C).symm :=
  (rfl)

/-- The functor of `leftDualEquivalence C` is the left dual functor. -/
@[simp]
theorem leftDualEquivalence_functor : (leftDualEquivalence C).functor = leftDualFunctor C :=
  (rfl)

/-- The inverse of `leftDualEquivalence C` takes right duals. -/
@[simp]
theorem leftDualEquivalence_inverse : (leftDualEquivalence C).inverse =
    (rightDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor :=
  rfl

/-- The unit of `leftDualEquivalence C` is the inverse of the trivialization `(ᘁX)ᘁ ≅ X`. -/
@[simp]
theorem leftDualEquivalence_unitIso :
    (leftDualEquivalence C).unitIso = (rightDualLeftDualIso C).symm :=
  (rfl)

/-- The functor of `rightDualEquivalence C` is strong monoidal: it is the right dual functor. -/
noncomputable instance rightDualEquivalenceFunctorMonoidal :
    (rightDualEquivalence C).functor.Monoidal :=
  inferInstanceAs (rightDualFunctor C).Monoidal

/-- The inverse of `rightDualEquivalence C` is strong monoidal, as a composite of strong monoidal
functors. -/
noncomputable instance rightDualEquivalenceInverseMonoidal :
    (rightDualEquivalence C).inverse.Monoidal :=
  inferInstanceAs ((leftDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor).Monoidal

/-- The right dual functor is a monoidal equivalence: the unit of `rightDualEquivalence C` is the
monoidal trivialization of `X ↦ ᘁ(Xᘁ)`. -/
instance rightDualEquivalence_isMonoidal : (rightDualEquivalence C).IsMonoidal :=
  have : NatTrans.IsMonoidal (rightDualEquivalence C).unit :=
    inferInstanceAs (NatTrans.IsMonoidal (leftDualRightDualIso C).inv)
  (rightDualEquivalence C).isMonoidal_of_isMonoidal_unit

/-- The functor of `leftDualEquivalence C` is strong monoidal: it is the left dual functor. -/
noncomputable instance leftDualEquivalenceFunctorMonoidal :
    (leftDualEquivalence C).functor.Monoidal :=
  inferInstanceAs (leftDualFunctor C).Monoidal

/-- The inverse of `leftDualEquivalence C` is strong monoidal, as a composite of strong monoidal
functors. -/
noncomputable instance leftDualEquivalenceInverseMonoidal :
    (leftDualEquivalence C).inverse.Monoidal :=
  inferInstanceAs ((rightDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor).Monoidal

/-- The left dual functor is a monoidal equivalence: the unit of `leftDualEquivalence C` is the
monoidal trivialization of `X ↦ (ᘁX)ᘁ`. -/
instance leftDualEquivalence_isMonoidal : (leftDualEquivalence C).IsMonoidal :=
  have : NatTrans.IsMonoidal (leftDualEquivalence C).unit :=
    inferInstanceAs (NatTrans.IsMonoidal (rightDualLeftDualIso C).inv)
  (leftDualEquivalence C).isMonoidal_of_isMonoidal_unit

/-- The double right dual functor of a rigid monoidal category, as an autoequivalence of `C` whose
inverse is the double left dual functor: the right dual equivalence followed by the inverse of
the left dual equivalence. -/
noncomputable def doubleRightDualEquivalence : C ≌ C :=
  (rightDualEquivalence C).trans (leftDualEquivalence C).symm

/-- The functor of `doubleRightDualEquivalence C` is the double right dual functor. -/
@[simp]
theorem doubleRightDualEquivalence_functor :
    (doubleRightDualEquivalence C).functor = doubleRightDualFunctor C :=
  (rfl)

/-- The inverse of `doubleRightDualEquivalence C` is the double left dual functor. -/
@[simp]
theorem doubleRightDualEquivalence_inverse :
    (doubleRightDualEquivalence C).inverse = doubleLeftDualFunctor C :=
  (rfl)

/-- The functor of `doubleRightDualEquivalence C` carries the monoidal structure of the double
right dual functor. -/
noncomputable instance doubleRightDualEquivalenceFunctorMonoidal :
    (doubleRightDualEquivalence C).functor.Monoidal :=
  inferInstanceAs (doubleRightDualFunctor C).Monoidal

/-- The inverse of `doubleRightDualEquivalence C` carries the monoidal structure of the double
left dual functor. -/
noncomputable instance doubleRightDualEquivalenceInverseMonoidal :
    (doubleRightDualEquivalence C).inverse.Monoidal :=
  inferInstanceAs (doubleLeftDualFunctor C).Monoidal

/-- The double right and double left dual functors form a monoidal equivalence, as a composite of
monoidal equivalences. -/
instance doubleRightDualEquivalence_isMonoidal : (doubleRightDualEquivalence C).IsMonoidal :=
  inferInstanceAs ((rightDualEquivalence C).trans (leftDualEquivalence C).symm).IsMonoidal

/-- Applying the double right dual functor and then the double left dual functor is naturally
isomorphic to the identity: the inverse unit of `doubleRightDualEquivalence C`. It is monoidal by
`TauCeti.doubleRightDualCompDoubleLeftDual_isMonoidal`. -/
noncomputable def doubleRightDualCompDoubleLeftDual :
    doubleRightDualFunctor C ⋙ doubleLeftDualFunctor C ≅ 𝟭 C :=
  (doubleRightDualEquivalence C).unitIso.symm

/-- The isomorphism `ᘁ(ᘁ(Xᘁᘁ)) ≅ X` is monoidal, so the double left dual functor is inverse to the
double right dual functor as a monoidal functor. -/
instance doubleRightDualCompDoubleLeftDual_isMonoidal :
    NatTrans.IsMonoidal (doubleRightDualCompDoubleLeftDual C).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    ((rightDualEquivalence C).trans (leftDualEquivalence C).symm).unitIso.inv)

/-- Applying the double left dual functor and then the double right dual functor is naturally
isomorphic to the identity: the counit of `doubleRightDualEquivalence C`. It is monoidal by
`TauCeti.doubleLeftDualCompDoubleRightDual_isMonoidal`. -/
noncomputable def doubleLeftDualCompDoubleRightDual :
    doubleLeftDualFunctor C ⋙ doubleRightDualFunctor C ≅ 𝟭 C :=
  (doubleRightDualEquivalence C).counitIso

/-- The isomorphism `(ᘁ(ᘁX))ᘁᘁ ≅ X` is monoidal, so the double right dual functor is inverse to
the double left dual functor as a monoidal functor. -/
instance doubleLeftDualCompDoubleRightDual_isMonoidal :
    NatTrans.IsMonoidal (doubleLeftDualCompDoubleRightDual C).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    ((rightDualEquivalence C).trans (leftDualEquivalence C).symm).counitIso.hom)

variable {C}

/-- The component of `doubleRightDualCompDoubleLeftDual C` at `X`: the left dual of the inverse
of the trivialization `ᘁ(Xᘁᘁ) ≅ Xᘁ`, followed by the trivialization `ᘁ(Xᘁ) ≅ X`. -/
@[simp]
theorem doubleRightDualCompDoubleLeftDual_hom_app (X : C) :
    (doubleRightDualCompDoubleLeftDual C).hom.app X =
      ((leftDualFunctor C).map ((leftDualRightDualIso C).inv.app Xᘁ)).unmop.unop ≫
        (leftDualRightDualIso C).hom.app X := by
  -- Restate the component for the composite equivalence, whose functors are the double dual
  -- functors by definition, so that the simp set for `Equivalence.trans` applies.
  change ((rightDualEquivalence C).trans (leftDualEquivalence C).symm).unitIso.inv.app X = _
  simp only [Equivalence.trans_functor, Equivalence.trans_inverse, Functor.comp_obj, Functor.id_obj,
    Equivalence.trans_unitIso, Functor.isoWhiskerRight_trans, Iso.trans_assoc, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Category.assoc,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.map_id, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  rw [Equivalence.symm_unitIso, Iso.symm_inv, leftDualEquivalence_counitIso_hom_app,
    rightDualEquivalence_unitIso, Iso.symm_inv]
  -- Applying the left dual functor through its opposite monoidal opposite and removing the
  -- wrappers is applying the left dual functor itself, by definition.
  rfl

/-- The component of `doubleLeftDualCompDoubleRightDual C` at `X`: the right dual of the inverse
of the trivialization `(ᘁᘁX)ᘁ ≅ ᘁX`, followed by the trivialization `(ᘁX)ᘁ ≅ X`. -/
@[simp]
theorem doubleLeftDualCompDoubleRightDual_hom_app (X : C) :
    (doubleLeftDualCompDoubleRightDual C).hom.app X =
      ((rightDualFunctor C).map ((rightDualLeftDualIso C).inv.app (ᘁX))).unmop.unop ≫
        (rightDualLeftDualIso C).hom.app X := by
  -- Restate the component for the composite equivalence, whose functors are the double dual
  -- functors by definition, so that the simp set for `Equivalence.trans` applies.
  change ((rightDualEquivalence C).trans (leftDualEquivalence C).symm).counitIso.hom.app X = _
  simp only [Equivalence.trans_inverse, Equivalence.trans_functor, Functor.comp_obj,
    Functor.id_obj, Equivalence.trans_counitIso, Functor.isoWhiskerRight_trans, Iso.trans_assoc,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.map_id, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  rw [Equivalence.symm_counitIso, Iso.symm_hom, rightDualEquivalence_counitIso_hom_app,
    leftDualEquivalence_unitIso, Iso.symm_inv]
  -- Applying the right dual functor through its opposite monoidal opposite and removing the
  -- wrappers is applying the right dual functor itself, by definition.
  rfl

end TauCeti
