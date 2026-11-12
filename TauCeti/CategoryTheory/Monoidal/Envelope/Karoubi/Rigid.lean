/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Envelope.Karoubi.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# Duals in the idempotent completion

Let `C` be a monoidal category, and let `(X, p)` and `(Y, q)` be formal direct factors, objects
of the idempotent completion `Karoubi C`. If `X` and `Y` form an exact pairing in `C` and `q` is
the right adjoint mate of `p` for that pairing, then `(X, p)` and `(Y, q)` form an exact pairing
in `Karoubi C`: the coevaluation is `η ≫ p ▷ Y` and the evaluation is `Y ◁ p ≫ ε`, the
coevaluation and evaluation of the pairing in `C` cut down by the idempotent `p`.

In particular the right dual of `(X, p)` is `(Xᘁ, pᘁ)` and its left dual is `(ᘁX, ᘁp)`, so the
idempotent completion of a right rigid, left rigid or rigid monoidal category is again right
rigid, left rigid or rigid, and the adjoint mate of a morphism of formal direct factors is the
adjoint mate of the underlying morphism. Together with the monoidal structure on `Karoubi C`,
this lets one dualize the summands that idempotents cut out of the objects of a rigid category.

The general exact pairing is stated for an arbitrary pairing of the underlying objects, not only
for the chosen duals of `C`, so that it also applies to self-dual summands: an idempotent of a
self-dual object that is its own mate cuts out a self-dual summand.

## Main declarations

* `CategoryTheory.Idempotents.Karoubi.exactPairing`: the exact pairing of `(X, p)` and `(Y, q)`
  induced by an exact pairing of `X` and `Y` for which `q` is the right adjoint mate of `p`.
* `CategoryTheory.Idempotents.Karoubi.instHasRightDual` and
  `CategoryTheory.Idempotents.Karoubi.instHasLeftDual`: the right dual `(Xᘁ, pᘁ)` and the left
  dual `(ᘁX, ᘁp)` of `(X, p)`, characterized by `Karoubi.rightDual_X`, `Karoubi.rightDual_p`,
  `Karoubi.leftDual_X` and `Karoubi.leftDual_p`.
* `CategoryTheory.Idempotents.Karoubi.instRigidCategory`: the idempotent completion of a rigid
  monoidal category is rigid, and likewise for right and left rigidity.
* `CategoryTheory.Idempotents.Karoubi.rightAdjointMate_f` and
  `CategoryTheory.Idempotents.Karoubi.leftAdjointMate_f`: adjoint mates in `Karoubi C` are
  computed on underlying morphisms.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10, for
  duals and adjoint mates in a monoidal category.
-/

public section

namespace CategoryTheory.Idempotents.Karoubi

open MonoidalCategory ExactPairing

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section ExactPairing

variable {P Q : Karoubi C} (e : ExactPairing P.X Q.X)

/-- Mate-sliding along the coevaluation: since the idempotent of `Q` is the right mate of the
idempotent of `P`, applying either one after the coevaluation gives the same morphism. -/
private theorem coevaluation_comp_whiskerLeft_p (h : Q.p = rightMate e e P.p) :
    η_ P.X Q.X ≫ P.X ◁ Q.p = η_ P.X Q.X ≫ P.p ▷ Q.X := by
  rw [h, coevaluation_comp_rightMate]

/-- Mate-sliding along the evaluation: since the idempotent of `Q` is the right mate of the
idempotent of `P`, applying either one before the evaluation gives the same morphism. -/
private theorem whiskerRight_p_comp_evaluation (h : Q.p = rightMate e e P.p) :
    Q.p ▷ P.X ≫ ε_ P.X Q.X = Q.X ◁ P.p ≫ ε_ P.X Q.X := by
  rw [h, rightMate_comp_evaluation]

/-- The idempotent of `P` cut out of the coevaluation is absorbed by the idempotent of `P ⊗ Q`,
since its right mate is the idempotent of `Q`. -/
private theorem coevaluation_comp_tensorHom (h : Q.p = rightMate e e P.p) :
    η_ P.X Q.X ≫ P.p ▷ Q.X ≫ (P.p ⊗ₘ Q.p) = η_ P.X Q.X ≫ P.p ▷ Q.X := by
  have hp (Z : C) : P.p ▷ Z ≫ P.p ▷ Z = P.p ▷ Z := by rw [← comp_whiskerRight, P.idem]
  simp only [tensorHom_def', ← whisker_exchange_assoc,
    reassoc_of% (coevaluation_comp_whiskerLeft_p e h), hp]

/-- The idempotent of `P` cut out of the evaluation is absorbed by the idempotent of `Q ⊗ P`,
since its right mate is the idempotent of `Q`. -/
private theorem tensorHom_comp_evaluation (h : Q.p = rightMate e e P.p) :
    (Q.p ⊗ₘ P.p) ≫ Q.X ◁ P.p ≫ ε_ P.X Q.X = Q.X ◁ P.p ≫ ε_ P.X Q.X := by
  have hp (W : C) : W ◁ P.p ≫ W ◁ P.p = W ◁ P.p := by rw [← whiskerLeft_comp, P.idem]
  simp only [tensorHom_def', Category.assoc, reassoc_of% hp, ← whisker_exchange_assoc,
    whiskerRight_p_comp_evaluation e h]

/-- An exact pairing of the underlying objects of `P` and `Q`, for which the idempotent of `Q` is
the right adjoint mate of the idempotent of `P`, induces an exact pairing of `P` and `Q` in
`Karoubi C`. Its coevaluation `η ≫ P.p ▷ Q.X` and evaluation `Q.X ◁ P.p ≫ ε` are those of the
pairing in `C`, cut down by the idempotent of `P`. -/
@[instance_reducible]
def exactPairing (h : Q.p = rightMate e e P.p) : ExactPairing P Q where
  coevaluation' := ⟨η_ P.X Q.X ≫ P.p ▷ Q.X, by simp [coevaluation_comp_tensorHom e h]⟩
  evaluation' := ⟨Q.X ◁ P.p ≫ ε_ P.X Q.X, by simp [tensorHom_comp_evaluation e h]⟩
  coevaluation_evaluation' := by
    ext
    dsimp
    -- Absorb the idempotents of `Q ⊗ P ⊗ Q` into the evaluation, and slide the idempotent of `P`
    -- along the coevaluation and the evaluation onto the strands of `Q`. Interchange then collects
    -- the idempotents of `Q` at the two ends of the zigzag of `C`.
    simp only [tensorHom_comp_tensorHom, Category.assoc, Q.idem, tensorHom_comp_evaluation e h]
    rw [← coevaluation_comp_whiskerLeft_p e h, ← whiskerRight_p_comp_evaluation e h]
    calc _ = (Q.p ≫ Q.p) ▷ 𝟙_ C ≫ (Q.X ◁ η_ P.X Q.X ≫ (α_ _ _ _).inv ≫ ε_ P.X Q.X ▷ Q.X) ≫
          𝟙_ C ◁ (Q.p ≫ Q.p) := by
          simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
            ← associator_inv_naturality_left_assoc, associator_inv_naturality_right_assoc,
            whisker_exchange_assoc]
      _ = _ := by simp
  evaluation_coevaluation' := by
    ext
    dsimp
    -- Absorb the idempotents of `P ⊗ Q ⊗ P` into the evaluation. Interchange then collects the
    -- idempotents of `P` at the two ends of the zigzag of `C`.
    simp only [tensorHom_comp_tensorHom, Category.assoc, P.idem, tensorHom_comp_evaluation e h]
    calc _ = 𝟙_ C ◁ (P.p ≫ P.p) ≫ (η_ P.X Q.X ▷ P.X ≫ (α_ _ _ _).hom ≫ P.X ◁ ε_ P.X Q.X) ≫
          (P.p ≫ P.p) ▷ 𝟙_ C := by
          simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
            associator_naturality_left_assoc, associator_naturality_right_assoc,
            whisker_exchange, whisker_exchange_assoc]
      _ = _ := by simp

/-- The coevaluation of `Karoubi.exactPairing` is that of `C`, cut down by the idempotent of
`P`. -/
@[simp]
theorem exactPairing_coevaluation_f (h : Q.p = rightMate e e P.p) :
    (@ExactPairing.coevaluation _ _ _ P Q (exactPairing e h)).f = η_ P.X Q.X ≫ P.p ▷ Q.X :=
  (rfl)

/-- The evaluation of `Karoubi.exactPairing` is that of `C`, cut down by the idempotent of `P`. -/
@[simp]
theorem exactPairing_evaluation_f (h : Q.p = rightMate e e P.p) :
    (@ExactPairing.evaluation _ _ _ P Q (exactPairing e h)).f = Q.X ◁ P.p ≫ ε_ P.X Q.X :=
  (rfl)

end ExactPairing

-- The dual objects are exposed so that the projection lemmas below are `rfl` lemmas, usable by
-- `dsimp` to rewrite duals occurring inside the types of morphisms.
@[expose] section Duals

/-- The right dual of a formal direct factor `(X, p)` is `(Xᘁ, pᘁ)`. -/
instance instHasRightDual (P : Karoubi C) [HasRightDual P.X] : HasRightDual P where
  rightDual := ⟨P.Xᘁ, P.pᘁ, by rw [← comp_rightAdjointMate, P.idem]⟩
  exact := exactPairing HasRightDual.exact (TauCeti.rightAdjointMate_eq_rightMate P.p)

/-- The underlying object of the right dual of `P` is the right dual of the underlying object. -/
@[simp]
theorem rightDual_X (P : Karoubi C) [HasRightDual P.X] : (Pᘁ).X = P.Xᘁ :=
  rfl

/-- The idempotent of the right dual of `P` is the right adjoint mate of the idempotent of `P`. -/
@[simp]
theorem rightDual_p (P : Karoubi C) [HasRightDual P.X] : (Pᘁ).p = P.pᘁ :=
  rfl

/-- The left dual of a formal direct factor `(X, p)` is `(ᘁX, ᘁp)`. -/
instance instHasLeftDual (P : Karoubi C) [HasLeftDual P.X] : HasLeftDual P where
  leftDual := ⟨ᘁP.X, ᘁP.p, by rw [← comp_leftAdjointMate, P.idem]⟩
  exact := exactPairing HasLeftDual.exact <| rightHom_ext (X := (ᘁP.X : C)) <| by
    rw [rightMate_comp_evaluation, leftAdjointMate_comp_evaluation]

/-- The underlying object of the left dual of `P` is the left dual of the underlying object. -/
@[simp]
theorem leftDual_X (P : Karoubi C) [HasLeftDual P.X] : (ᘁP : Karoubi C).X = (ᘁP.X : C) :=
  rfl

/-- The idempotent of the left dual of `P` is the left adjoint mate of the idempotent of `P`. -/
@[simp]
theorem leftDual_p (P : Karoubi C) [HasLeftDual P.X] : (ᘁP : Karoubi C).p = (ᘁP.p) :=
  rfl

/-- The idempotent completion of a right rigid monoidal category is right rigid. -/
instance instRightRigidCategory [RightRigidCategory C] : RightRigidCategory (Karoubi C) where

/-- The idempotent completion of a left rigid monoidal category is left rigid. -/
instance instLeftRigidCategory [LeftRigidCategory C] : LeftRigidCategory (Karoubi C) where

/-- The idempotent completion of a rigid monoidal category is rigid. -/
instance instRigidCategory [RigidCategory C] : RigidCategory (Karoubi C) where

end Duals

/-- The right adjoint mate of a morphism of formal direct factors is the right adjoint mate of
the underlying morphism. -/
@[simp]
theorem rightAdjointMate_f {P Q : Karoubi C} [HasRightDual P.X] [HasRightDual Q.X]
    (f : P ⟶ Q) : (fᘁ).f = (f.f)ᘁ := by
  -- Both sides are determined by their evaluation against `P.X`. In `Karoubi C` the evaluation
  -- is that of `C` cut down by idempotents, which slide along it and are absorbed by `f`.
  apply rightHom_ext (X := P.X) (Y := P.Xᘁ)
  have h := congrArg Hom.f (rightAdjointMate_comp_evaluation f)
  simp only [comp_f, whiskerRight_f, whiskerLeft_f, exactPairing_evaluation_f, rightDual_X,
    rightDual_p, tensorHom_def, Category.assoc, ← whiskerLeft_comp_assoc, P.idem, comp_p] at h
  rw [rightAdjointMate_comp_evaluation]
  calc
    _ = (fᘁ).f ▷ P.X ≫ P.Xᘁ ◁ P.p ≫ ε_ P.X P.Xᘁ := by
      rw [← rightAdjointMate_comp_evaluation, ← comp_whiskerRight_assoc, ← rightDual_p, comp_p]
    _ = Q.pᘁ ▷ P.X ≫ Q.Xᘁ ◁ f.f ≫ ε_ Q.X Q.Xᘁ := h
    _ = _ := by
      rw [← whisker_exchange_assoc, rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc,
        comp_p]

/-- The left adjoint mate of a morphism of formal direct factors is the left adjoint mate of the
underlying morphism. -/
@[simp]
theorem leftAdjointMate_f {P Q : Karoubi C} [HasLeftDual P.X] [HasLeftDual Q.X]
    (f : P ⟶ Q) : (ᘁf).f = ᘁf.f := by
  -- Both sides are determined by their evaluation against `P.X`. In `Karoubi C` the evaluation
  -- is that of `C` cut down by idempotents, which slide along it and are absorbed by `f`.
  apply leftDualHom_ext (X := (ᘁP.X : C)) (Y := P.X)
  have h := congrArg Hom.f (leftAdjointMate_comp_evaluation f)
  simp only [comp_f, whiskerRight_f, whiskerLeft_f, exactPairing_evaluation_f, tensorHom_def,
    Category.assoc, ← whiskerLeft_comp_assoc, comp_p, idem] at h
  rw [leftAdjointMate_comp_evaluation]
  calc
    _ = P.p ▷ (ᘁQ.X : C) ≫ P.X ◁ (ᘁf).f ≫ ε_ (ᘁP.X : C) P.X := by
      -- `dsimp` identifies the object `(ᘁP).X` in the type of `(ᘁf).f` with `ᘁP.X`.
      rw [← whisker_exchange_assoc]
      dsimp only [leftDual_X]
      rw [← leftAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc, ← leftDual_p, comp_p]
    _ = f.f ▷ (ᘁQ.X : C) ≫ Q.X ◁ (ᘁQ.p) ≫ ε_ (ᘁQ.X : C) Q.X := h
    _ = _ := by
      rw [leftAdjointMate_comp_evaluation, ← comp_whiskerRight_assoc, comp_p]

end CategoryTheory.Idempotents.Karoubi
