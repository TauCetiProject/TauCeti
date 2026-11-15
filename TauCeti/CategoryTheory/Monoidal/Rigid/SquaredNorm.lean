/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# Squared norms and pivot-free global dimension

In a rigid monoidal category `C`, an isomorphism `a : X ≅ Xᘁᘁ` between an object and its double
right dual does not require a pivotal structure on `C`. Any morphism `f : X ⟶ Xᘁᘁ` can be closed
up into a scalar `TauCeti.doubleDualTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ : 𝟙_ C ⟶ 𝟙_ C`.
For an isomorphism `a : X ≅ Xᘁᘁ`, the product

`squaredNorm a = doubleDualTrace a.hom ≫ doubleDualTrace (a.inv)ᘁ`

is the *squared norm* of `X` with respect to `a` (Etingof–Nikshych–Ostrik).

When `End X` consists purely of scalars from a commutative semiring `R` — that is,
`algebraMap R (End X)` is bijective, which holds for every split simple object over an
algebraically closed field by Schur's lemma — any two isomorphisms `a, b : X ≅ Xᘁᘁ` differ by a
unit scalar `r`, and their inverses differ by `r⁻¹`, so `squaredNorm a = squaredNorm b` is
independent of the choice of isomorphism (`TauCeti.squaredNorm_congr`). Without scalar
endomorphisms this fails: on a direct sum of two objects, scaling the two summands of `a`
independently changes `squaredNorm a`.

Summing `squaredNorm (a S)` over the simple isomorphism classes `S : SimpleClasses C` for a family
of double-dual isomorphisms `a S : S.repr ≅ S.reprᘁᘁ` defines the pivot-free global dimension
`TauCeti.normGlobalDim C a`, which is likewise independent of the family `a` when each simple
representative has scalar endomorphisms (`TauCeti.normGlobalDim_congr`). Comparison with the
pivotal global dimension `TauCeti.globalDim` is recorded in
`TauCeti.CategoryTheory.Monoidal.Pivotal.GlobalDim`.

## Main declarations

* `TauCeti.doubleDualTrace`: the scalar trace `η_ X Xᘁ ≫ a ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ` of `a : X ⟶ Xᘁᘁ`,
  with `TauCeti.doubleDualTrace_def`, `TauCeti.doubleDualTrace_rightAdjointMate`,
  `TauCeti.doubleDualTrace_conj`, and additivity/linearity lemmas;
* `TauCeti.squaredNorm`: the squared norm `doubleDualTrace a.hom ≫ doubleDualTrace (a.inv)ᘁ` of
  an isomorphism `a : X ≅ Xᘁᘁ`, with `TauCeti.squaredNorm_def`, `TauCeti.squaredNorm_conj`, and
  `TauCeti.squaredNorm_congr`;
* `TauCeti.normGlobalDim`: the sum of squared norms over `SimpleClasses C`, with
  `TauCeti.normGlobalDim_def` and `TauCeti.normGlobalDim_congr`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2.1
  (Proposition 2.1 and Definition 2.2)
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

section DoubleDualTrace

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The trace `η_ X Xᘁ ≫ a ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ` of a morphism `a : X ⟶ Xᘁᘁ`, closed with the
evaluation of `Xᘁ`. -/
noncomputable def doubleDualTrace {X : C} [HasRightDual X] [HasRightDual (Xᘁ : C)]
    (a : X ⟶ ((Xᘁ : C)ᘁ : C)) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Xᘁ ≫ a ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C)

/-- The defining formula of `TauCeti.doubleDualTrace`. -/
theorem doubleDualTrace_def {X : C} [HasRightDual X] [HasRightDual (Xᘁ : C)]
    (a : X ⟶ ((Xᘁ : C)ᘁ : C)) :
    doubleDualTrace a = η_ X Xᘁ ≫ a ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) :=
  (rfl)

/-- The double-dual trace of the right adjoint mate `fᘁ : Xᘁ ⟶ Xᘁᘁᘁ` of `f : Xᘁᘁ ⟶ X` is
`η_ Xᘁ Xᘁᘁ ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ`. -/
theorem doubleDualTrace_rightAdjointMate {X : C} [HasRightDual X] [HasRightDual (Xᘁ : C)]
    [HasRightDual ((Xᘁ : C)ᘁ : C)] (f : ((Xᘁ : C)ᘁ : C) ⟶ X) :
    doubleDualTrace (fᘁ) = η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ := by
  rw [doubleDualTrace_def, rightAdjointMate_comp_evaluation]

/-- `TauCeti.doubleDualTrace` is invariant under transport along an isomorphism `u : X ≅ Y`. -/
theorem doubleDualTrace_conj {X Y : C} [HasRightDual X] [HasRightDual (Xᘁ : C)]
    [HasRightDual Y] [HasRightDual (Yᘁ : C)] (u : X ≅ Y) (a : X ⟶ ((Xᘁ : C)ᘁ : C)) :
    doubleDualTrace (u.inv ≫ a ≫ ((u.hom)ᘁ)ᘁ) = doubleDualTrace a := by
  rw [doubleDualTrace_def, doubleDualTrace_def, comp_whiskerRight_assoc,
    ← coevaluation_comp_rightAdjointMate_assoc, whisker_exchange_assoc,
    comp_whiskerRight_assoc, ← rightAdjointMate_comp_evaluation,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc,
    ← comp_rightAdjointMate, ← comp_rightAdjointMate,
    u.hom_inv_id, rightAdjointMate_id, rightAdjointMate_id, Category.comp_id]

/-- The double-dual trace of zero is zero. -/
@[simp]
theorem doubleDualTrace_zero [HasZeroMorphisms C] {X : C} [HasRightDual X] [HasRightDual (Xᘁ : C)] :
    doubleDualTrace (0 : X ⟶ ((Xᘁ : C)ᘁ : C)) = 0 := by
  rw [doubleDualTrace_def, zero_whiskerRight_of_hasRightDual, zero_comp, comp_zero]

/-- `TauCeti.doubleDualTrace` is additive. -/
@[simp]
theorem doubleDualTrace_add [Preadditive C] [MonoidalPreadditive C] {X : C}
    [HasRightDual X] [HasRightDual (Xᘁ : C)] (a b : X ⟶ ((Xᘁ : C)ᘁ : C)) :
    doubleDualTrace (a + b) = doubleDualTrace a + doubleDualTrace b := by
  simp [doubleDualTrace_def]

/-- `TauCeti.doubleDualTrace` commutes with negation. -/
@[simp]
theorem doubleDualTrace_neg [Preadditive C] [MonoidalPreadditive C] {X : C}
    [HasRightDual X] [HasRightDual (Xᘁ : C)] (a : X ⟶ ((Xᘁ : C)ᘁ : C)) :
    doubleDualTrace (-a) = -doubleDualTrace a :=
  eq_neg_of_add_eq_zero_left (by rw [← doubleDualTrace_add, neg_add_cancel, doubleDualTrace_zero])

/-- `TauCeti.doubleDualTrace` commutes with subtraction. -/
@[simp]
theorem doubleDualTrace_sub [Preadditive C] [MonoidalPreadditive C] {X : C}
    [HasRightDual X] [HasRightDual (Xᘁ : C)] (a b : X ⟶ ((Xᘁ : C)ᘁ : C)) :
    doubleDualTrace (a - b) = doubleDualTrace a - doubleDualTrace b := by
  rw [sub_eq_add_neg, doubleDualTrace_add, doubleDualTrace_neg, sub_eq_add_neg]

/-- `TauCeti.doubleDualTrace` commutes with scalar multiplication. -/
@[simp]
theorem doubleDualTrace_smul {R : Type w} [Semiring R] [Preadditive C] [MonoidalPreadditive C]
    [Linear R C] [MonoidalLinear R C] {X : C} [HasRightDual X] [HasRightDual (Xᘁ : C)]
    (r : R) (a : X ⟶ ((Xᘁ : C)ᘁ : C)) :
    doubleDualTrace (r • a) = r • doubleDualTrace a := by
  simp [doubleDualTrace_def]

end DoubleDualTrace

section SquaredNorm

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The squared norm** of `X` with respect to an isomorphism `a : X ≅ Xᘁᘁ`
(Etingof–Nikshych–Ostrik, *On fusion categories*, §2.1):
`doubleDualTrace a.hom ≫ doubleDualTrace (rightAdjointMate a.inv)`. -/
noncomputable def squaredNorm {X : C} [HasRightDual X] [HasRightDual (Xᘁ : C)]
    [HasRightDual ((Xᘁ : C)ᘁ : C)] (a : X ≅ ((Xᘁ : C)ᘁ : C)) : 𝟙_ C ⟶ 𝟙_ C :=
  doubleDualTrace a.hom ≫ doubleDualTrace (rightAdjointMate a.inv)

/-- The defining formula of `TauCeti.squaredNorm`. -/
theorem squaredNorm_def {X : C} [HasRightDual X] [HasRightDual (Xᘁ : C)]
    [HasRightDual ((Xᘁ : C)ᘁ : C)] (a : X ≅ ((Xᘁ : C)ᘁ : C)) :
    squaredNorm a = doubleDualTrace a.hom ≫ doubleDualTrace (rightAdjointMate a.inv) :=
  (rfl)

/-- `TauCeti.squaredNorm` is invariant under transport along an isomorphism `u : X ≅ Y`. -/
theorem squaredNorm_conj {X Y : C} [HasRightDual X] [HasRightDual (Xᘁ : C)]
    [HasRightDual ((Xᘁ : C)ᘁ : C)] [HasRightDual Y] [HasRightDual (Yᘁ : C)]
    [HasRightDual ((Yᘁ : C)ᘁ : C)] (u : X ≅ Y) (a : X ≅ ((Xᘁ : C)ᘁ : C)) :
    squaredNorm (u.symm ≪≫ a ≪≫ u.rightAdjointMate.rightAdjointMate) = squaredNorm a := by
  have hinv : rightAdjointMate (u.symm ≪≫ a ≪≫ u.rightAdjointMate.rightAdjointMate).inv =
      u.rightAdjointMate.symm.inv ≫ rightAdjointMate a.inv ≫
        ((u.rightAdjointMate.symm.hom)ᘁ)ᘁ := by
    simp only [Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Iso.rightAdjointMate_inv,
      Iso.rightAdjointMate_hom, comp_rightAdjointMate, Category.assoc]
  rw [squaredNorm_def, squaredNorm_def, hinv, doubleDualTrace_conj u.rightAdjointMate.symm]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.rightAdjointMate_hom, doubleDualTrace_conj u]

/-- **Independence of the double-dual isomorphism**: if `End X` consists of `R`-scalars (i.e.
`algebraMap R (End X)` is bijective), then `TauCeti.squaredNorm a` does not depend on the choice
of isomorphism `a : X ≅ Xᘁᘁ`. -/
theorem squaredNorm_congr (R : Type w) [CommSemiring R] [Preadditive C] [Linear R C]
    [MonoidalPreadditive C] [MonoidalLinear R C] {X : C}
    [HasRightDual X] [HasRightDual (Xᘁ : C)] [HasRightDual ((Xᘁ : C)ᘁ : C)]
    (hX : Function.Bijective (algebraMap R (End X))) (a b : X ≅ ((Xᘁ : C)ᘁ : C)) :
    squaredNorm a = squaredNorm b := by
  obtain ⟨r, hr⟩ := hX.2 (End.of (a.hom ≫ b.inv))
  obtain ⟨s, hs⟩ := hX.2 (End.of (b.hom ≫ a.inv))
  have ha : a.hom = r • b.hom := by
    have h1 := congrArg End.asHom hr
    simp only [End.algebraMap_asHom] at h1
    calc a.hom = (a.hom ≫ b.inv) ≫ b.hom := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = (r • 𝟙 X) ≫ b.hom := by rw [← h1]
      _ = r • b.hom := by rw [Linear.smul_comp, Category.id_comp]
  have ha' : a.inv = s • b.inv := by
    have h1 := congrArg End.asHom hs
    simp only [End.algebraMap_asHom] at h1
    calc a.inv = b.inv ≫ (b.hom ≫ a.inv) := by rw [Iso.inv_hom_id_assoc]
      _ = b.inv ≫ (s • 𝟙 X) := by rw [← h1]
      _ = s • b.inv := by rw [Linear.comp_smul, Category.comp_id]
  have hrs : r * s = 1 := by
    apply hX.1
    rw [map_mul, hr, hs, ← End.of_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      End.of_id, map_one]
  rw [squaredNorm_def, squaredNorm_def, ha, ha', rightAdjointMate_smul, doubleDualTrace_smul,
    doubleDualTrace_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, hrs, one_smul]

end SquaredNorm

section NormGlobalDim

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C] [Preadditive C]
  [Fintype (SimpleClasses C)]

/-- **The global dimension without a pivotal structure** (Etingof–Nikshych–Ostrik, Definition 2.2):
the sum of the squared norms of the simple representatives, for a family of isomorphisms to their
double right duals. When every simple representative has scalar endomorphisms, the value does not
depend on the family (`TauCeti.normGlobalDim_congr`). -/
noncomputable def normGlobalDim (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    𝟙_ C ⟶ 𝟙_ C :=
  ∑ S : SimpleClasses C, squaredNorm (a S)

/-- The defining formula of `TauCeti.normGlobalDim`. -/
theorem normGlobalDim_def (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = ∑ S : SimpleClasses C, squaredNorm (a S) :=
  (rfl)

/-- **Independence of the family of double-dual isomorphisms**: if every simple representative has
scalar endomorphisms over a commutative semiring `R`, then `TauCeti.normGlobalDim C a` does not
depend on `a`. -/
theorem normGlobalDim_congr (R : Type w) [CommSemiring R] [Linear R C] [MonoidalPreadditive C]
    [MonoidalLinear R C]
    (hS : ∀ S : SimpleClasses C, Function.Bijective (algebraMap R (End S.repr)))
    (a b : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = normGlobalDim C b :=
  Finset.sum_congr rfl fun S _ ↦ squaredNorm_congr R (hS S) (a S) (b S)

end NormGlobalDim

end TauCeti
