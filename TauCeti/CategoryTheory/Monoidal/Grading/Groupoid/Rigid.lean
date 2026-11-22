/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Groupoid.Basic
public import TauCeti.CategoryTheory.Semisimple.UnitSummands.Rigid

/-!
# Duality and rigidity in the universal grading groupoid

In a finite semisimple monoidal category `C` with `MonoidalPreadditive C`, exact pairings and right
duals invert degrees in any `GroupoidGrading` (`TauCeti.GroupoidGrading.degOf_of_exactPairing`)
and in `TauCeti.universalGradingGroupoid C`
(`TauCeti.universalGradingGroupoid.degreeOf_of_exactPairing`, `degreeOf_rightDual`, `degree_dual`).

Under `[RigidCategory C]`, every morphism in `universalGradingGroupoid C` is the degree of a simple
class (`exists_degree_eq`), hom-sets `mkObj I ⟶ mkObj J` are nonempty iff the `(I, J)` Peirce
corner contains a simple object (`nonempty_hom_mkObj_iff`), and finiteness of that corner (in
particular `[Finite (SimpleClasses C)]`) makes `x ⟶ y` finite (`finite_hom_of_finite_subtype`).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ v₂ u₁ u₂

namespace TauCeti

section ExactPairing

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

/-- In an exact pairing of simple objects, `γ.degOf Y` is the inverse of `γ.degOf X` up to
endpoint transports. -/
theorem GroupoidGrading.degOf_of_exactPairing {G : Type u₂} [Groupoid.{v₂} G]
    (γ : GroupoidGrading C G) {X Y : C} [ExactPairing X Y] [Simple X] [Simple Y] :
    γ.degOf Y = eqToHom (congrArg γ.obj leftUnitClass_of_exactPairing) ≫ inv (γ.degOf X) ≫
      eqToHom (congrArg γ.obj rightUnitClass_of_exactPairing).symm := by
  obtain ⟨I, hf⟩ := (UnitSimpleClasses.ne_zero_iff_exists_ι_comp_ne_zero _).1
    (coevaluation_ne_zero (Y := Y) (Simple.not_isZero X))
  have hcomp := γ.degOf_comp (UnitSimpleClasses.ι I ≫ η_ X Y) hf
  rw [γ.degOf_unitRepr] at hcomp
  have hinv : eqToHom (congrArg γ.obj (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)) ≫
      γ.degOf Y = inv (γ.degOf X) ≫
        eqToHom (congrArg γ.obj rightUnitClass_of_exactPairing).symm := by
    rw [IsIso.eq_inv_comp]
    simpa [Category.assoc] using
      eqToHom (congrArg γ.obj (leftUnitClass_eq_of_hom_ne_zero hf)).symm ≫= hcomp.symm =≫
        eqToHom (congrArg γ.obj (rightUnitClass_eq_of_hom_ne_zero hf))
  simpa [Category.assoc] using
    eqToHom (congrArg γ.obj (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)).symm ≫= hinv

/-- Right duals have inverse grading degrees up to endpoint transports in any groupoid grading. -/
@[simp] theorem GroupoidGrading.degOf_rightDual {G : Type u₂} [Groupoid.{v₂} G]
    (γ : GroupoidGrading C G) (X : C) [HasRightDual X] [Simple X] [Simple Xᘁ] :
    γ.degOf Xᘁ = eqToHom (by simp) ≫ inv (γ.degOf X) ≫ eqToHom (by simp) := by
  simpa using γ.degOf_of_exactPairing (X := X) (Y := Xᘁ)

/-- Dual simple classes have inverse grading degrees up to endpoint transports in any groupoid
grading. -/
@[simp] theorem GroupoidGrading.deg_dual [RigidCategory C] {G : Type u₂} [Groupoid.{v₂} G]
    (γ : GroupoidGrading C G) (S : SimpleClasses C) :
    γ.deg S.dual = eqToHom (by simp) ≫ inv (γ.deg S) ≫ eqToHom (by simp) := by
  rw [← γ.degOf_repr S.dual, γ.degOf_congr (SimpleClasses.dualReprIso S),
    γ.degOf_rightDual S.repr, γ.degOf_repr S]; simp [Category.assoc]

end ExactPairing

namespace universalGradingGroupoid

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

/-- In an exact pairing of simple objects, `degreeOf Y` is the inverse of `degreeOf X` up to
endpoint transports. -/
theorem degreeOf_of_exactPairing {X Y : C} [ExactPairing X Y] [Simple X] [Simple Y] :
    degreeOf Y = eqToHom (congrArg mkObj leftUnitClass_of_exactPairing) ≫ inv (degreeOf X) ≫
      eqToHom (congrArg mkObj rightUnitClass_of_exactPairing).symm := by
  have h := (idGrading (C := C)).degOf_of_exactPairing (X := X) (Y := Y)
  simp only [idGrading_degOf] at h
  simpa [Category.assoc] using eqToHom (idGrading_obj (leftUnitClass Y)).symm ≫= h =≫
    eqToHom (idGrading_obj (rightUnitClass Y))

@[simp] theorem degreeOf_rightDual (X : C) [HasRightDual X] [Simple X] [Simple Xᘁ] :
    degreeOf Xᘁ = eqToHom (by simp) ≫ inv (degreeOf X) ≫ eqToHom (by simp) := by
  simpa using degreeOf_of_exactPairing (X := X) (Y := Xᘁ)

section Rigid
variable [RigidCategory C]

/-- Dual simple classes have inverse degrees in `universalGradingGroupoid C`. -/
@[simp] theorem degree_dual (S : SimpleClasses C) :
    degree S.dual = eqToHom (by simp) ≫ inv (degree S) ≫ eqToHom (by simp) := by
  have h := (idGrading (C := C)).deg_dual S; simp only [idGrading_deg] at h
  simpa [Category.assoc] using eqToHom (idGrading_obj (leftUnitClass S.dual.repr)).symm ≫= h =≫
    eqToHom (idGrading_obj (rightUnitClass S.dual.repr))

/-- In a rigid finite semisimple monoidal category, every morphism in
`universalGradingGroupoid C` is the degree of some simple isomorphism class. -/
theorem exists_degree_eq {x y : universalGradingGroupoid C} (g : x ⟶ y) :
    ∃ (S : SimpleClasses C) (hL : mkObj (leftUnitClass S.repr) = x)
      (hR : mkObj (rightUnitClass S.repr) = y), g = eqToHom hL.symm ≫ degree S ≫ eqToHom hR := by
  induction g using hom_induction with
  | hdeg S => exact ⟨S, rfl, rfl, by simp⟩
  | hinv S =>
    refine ⟨S.dual, congrArg mkObj (leftUnitClass_dual_repr S),
      congrArg mkObj (rightUnitClass_dual_repr S), ?_⟩
    rw [degree_dual]; simp [Category.assoc]
  | hid z =>
    obtain ⟨I, rfl⟩ := mkObj.surjective z
    exact ⟨I.val, congrArg mkObj (leftUnitClass_unitRepr I),
      congrArg mkObj (rightUnitClass_unitRepr I), by simp⟩
  | hcomp f₁ f₂ ih₁ ih₂ =>
    obtain ⟨S, hSL, hSR, hf₁⟩ := ih₁; obtain ⟨T, hTL, hTR, hf₂⟩ := ih₂
    have hmid : rightUnitClass S.repr = leftUnitClass T.repr := mkObj.injective (hSR.trans hTL.symm)
    have hnz : ¬ IsZero (S.repr ⊗ T.repr) :=
      (not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass S.repr T.repr
        (Y' := T.reprᘁ)).2 hmid
    obtain ⟨W, hW, f, hf⟩ := exists_simple_hom_ne_zero hnz
    let _ := hW; let dW := SimpleClasses.classOfReprIso W
    have hf' : dW.hom ≫ f ≠ 0 := fun h ↦ hf <| by rw [← dW.inv_hom_id_assoc f, h, comp_zero]
    refine ⟨SimpleClasses.classOf W,
      (congrArg mkObj (leftUnitClass_eq_of_hom_ne_zero hf')).trans hSL,
      (congrArg mkObj (rightUnitClass_eq_of_hom_ne_zero hf')).trans hTR, ?_⟩
    rw [hf₁, hf₂, degree_comp (dW.hom ≫ f) hf']; simp [Category.assoc]

/-- Every morphism `mkObj I ⟶ mkObj J` in `universalGradingGroupoid C` comes from a simple class
`S` with `leftUnitClass S.repr = I` and `rightUnitClass S.repr = J`. -/
theorem exists_simple_degree_eq {I J : UnitSimpleClasses C} (g : mkObj I ⟶ mkObj J) :
    ∃ (S : SimpleClasses C) (hL : leftUnitClass S.repr = I) (hR : rightUnitClass S.repr = J),
      g = eqToHom (congrArg mkObj hL).symm ≫ degree S ≫ eqToHom (congrArg mkObj hR) := by
  obtain ⟨S, hL, hR, hg⟩ := exists_degree_eq g
  exact ⟨S, mkObj.injective hL, mkObj.injective hR, hg⟩

/-- In a rigid finite semisimple monoidal category, there is a morphism `mkObj I ⟶ mkObj J` in
`universalGradingGroupoid C` if and only if some simple class has left unit support `I` and right
unit support `J`. -/
theorem nonempty_hom_mkObj_iff (I J : UnitSimpleClasses C) :
    Nonempty (mkObj I ⟶ mkObj J) ↔
      ∃ S : SimpleClasses C, leftUnitClass S.repr = I ∧ rightUnitClass S.repr = J :=
  ⟨fun ⟨g⟩ ↦ by obtain ⟨S, hL, hR, _⟩ := exists_simple_degree_eq g; exact ⟨S, hL, hR⟩,
   fun ⟨S, hL, hR⟩ ↦ ⟨eqToHom (congrArg mkObj hL).symm ≫ degree S ≫ eqToHom (congrArg mkObj hR)⟩⟩

/-- If only finitely many simple classes connect `x` and `y`, then `x ⟶ y` is finite. -/
theorem finite_hom_of_finite_subtype (x y : universalGradingGroupoid C)
    [Finite {S : SimpleClasses C //
      mkObj (leftUnitClass S.repr) = x ∧ mkObj (rightUnitClass S.repr) = y}] : Finite (x ⟶ y) :=
  Finite.of_surjective
    (fun p : {S : SimpleClasses C //
        mkObj (leftUnitClass S.repr) = x ∧ mkObj (rightUnitClass S.repr) = y} ↦
      eqToHom p.property.left.symm ≫ degree p.val ≫ eqToHom p.property.right)
    fun g ↦ by obtain ⟨S, hL, hR, hg⟩ := exists_degree_eq g; exact ⟨⟨S, hL, hR⟩, hg.symm⟩

/-- In a multifusion category (finitely many simple classes), every hom-set of
`universalGradingGroupoid C` is finite. -/
instance [Finite (SimpleClasses C)] (x y : universalGradingGroupoid C) : Finite (x ⟶ y) :=
  finite_hom_of_finite_subtype x y

end Rigid

end universalGradingGroupoid

end TauCeti
