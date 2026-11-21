/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import TauCeti.AlgebraicTopology.AlternatingCofaceMapComplex

/-!
# Augmented cosimplicial objects with an extra codegeneracy

An extra codegeneracy on an augmented cosimplicial object `X` consists of a retraction
`s' : X.right ^⦋0⦌ ⟶ X.left` of the augmentation and maps `s n : X.right ^⦋n + 1⦌ ⟶ X.right ^⦋n⦌`
which behave formally like a codegeneracy `σ (-1)`: they split the zeroth cofaces and commute
with the other cofaces and codegeneracies. This is the cosimplicial dual of Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy` (due to Joël Riou), whose definitions and proofs
this file follows.

## Main definitions

* `CosimplicialObject.Augmented.ExtraCodegeneracy`: extra codegeneracies.
* `ExtraCodegeneracy.map`: extra codegeneracies are preserved by any functor.
* `SimplicialObject.Augmented.ExtraDegeneracy.rightOp`: an extra degeneracy of an augmented
  simplicial object is an extra codegeneracy of the opposite augmented cosimplicial object.
  Composed with `ExtraCodegeneracy.map`, this turns an extra degeneracy into an extra
  codegeneracy after applying a contravariant functor such as a `Hom` functor `Hom(-, Y)`.
* `ExtraCodegeneracy.homotopyEquiv`: in a preadditive category with a zero object, the
  augmentation `AlgebraicTopology.AlternatingCofaceMapComplex.ε` of an augmented cosimplicial
  object with an extra codegeneracy is a homotopy equivalence from the augmentation object in
  degree `0` to the alternating coface map complex.
* `ExtraCodegeneracy.homotopyEquivOfOpFunctor`: the same conclusion from an extra
  codegeneracy of the reversal `CosimplicialObject.Augmented.opFunctor.obj X`, that is, from a
  contraction splitting the *last* cofaces of `X`. It is transported along the sign comparison
  `AlgebraicTopology.opFunctorCompAlternatingCofaceMapComplexIso`.

## References

* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]
* M. Barr, J. Beck, *Homology and standard constructions*, in *Seminar on Triples and
  Categorical Homology Theory*, Lecture Notes in Math. 80 (1969), §1.
-/

public noncomputable section

open CategoryTheory Category Limits Opposite AlgebraicTopology

open scoped Simplicial

universe v u

namespace CategoryTheory.CosimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- An extra codegeneracy of an augmented cosimplicial object `X`: a retraction `s'` of the
augmentation in degree `0` and maps `s n` which formally behave like a codegeneracy `σ (-1)`.
This is the cosimplicial dual of `SimplicialObject.Augmented.ExtraDegeneracy`. -/
@[ext]
structure ExtraCodegeneracy (X : CosimplicialObject.Augmented C) where
  /-- a retraction of the augmentation in degree `0` -/
  s' : X.right.obj ⦋0⦌ ⟶ X.left
  /-- the extra codegeneracy -/
  s : ∀ n : ℕ, X.right.obj ⦋n + 1⦌ ⟶ X.right.obj ⦋n⦌
  ε_comp_s' : X.hom.app ⦋0⦌ ≫ s' = 𝟙 X.left
  δ₁_comp_s₀ : X.right.δ 1 ≫ s 0 = s' ≫ X.hom.app ⦋0⦌
  δ₀_comp_s : ∀ n : ℕ, X.right.δ 0 ≫ s n = 𝟙 _
  δ_comp_s : ∀ (n : ℕ) (i : Fin (n + 2)), X.right.δ i.succ ≫ s (n + 1) = s n ≫ X.right.δ i
  σ_comp_s : ∀ (n : ℕ) (i : Fin (n + 1)), X.right.σ i.succ ≫ s n = s (n + 1) ≫ X.right.σ i

namespace ExtraCodegeneracy

attribute [reassoc] δ₁_comp_s₀ δ_comp_s σ_comp_s
attribute [reassoc (attr := simp)] ε_comp_s' δ₀_comp_s

variable {X : CosimplicialObject.Augmented C}

/-- If `ed` is an extra codegeneracy of `X` and `F : C ⥤ D` is a functor, then `ed.map F` is an
extra codegeneracy of the augmented cosimplicial object in `D` obtained by applying `F` to `X`. -/
def map {D : Type*} [Category D] (ed : ExtraCodegeneracy X) (F : C ⥤ D) :
    ExtraCodegeneracy (((whiskering C D).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  -- The augmentation of the image is `F` applied to the augmentation, after the identity
  -- components of `Functor.constComp`; the cofaces and codegeneracies are their images by `F`.
  ε_comp_s' := (assoc _ _ _).trans ((id_comp _).trans
    ((F.map_comp _ _).symm.trans ((congrArg F.map ed.ε_comp_s').trans (F.map_id _))))
  δ₁_comp_s₀ := (F.map_comp _ _).symm.trans ((congrArg F.map ed.δ₁_comp_s₀).trans
    ((F.map_comp _ _).trans (congrArg (F.map ed.s' ≫ ·) (id_comp _).symm)))
  δ₀_comp_s n := (F.map_comp _ _).symm.trans ((congrArg F.map (ed.δ₀_comp_s n)).trans (F.map_id _))
  δ_comp_s n i :=
    (F.map_comp _ _).symm.trans ((congrArg F.map (ed.δ_comp_s n i)).trans (F.map_comp _ _))
  σ_comp_s n i :=
    (F.map_comp _ _).symm.trans ((congrArg F.map (ed.σ_comp_s n i)).trans (F.map_comp _ _))

@[simp]
lemma map_s' {D : Type*} [Category D] (ed : ExtraCodegeneracy X) (F : C ⥤ D) :
    (ed.map F).s' = F.map ed.s' := (rfl)

@[simp]
lemma map_s {D : Type*} [Category D] (ed : ExtraCodegeneracy X) (F : C ⥤ D) (n : ℕ) :
    (ed.map F).s n = F.map (ed.s n) := (rfl)

section Preadditive

variable [Preadditive C]

/-- In degree `0`, the extra codegeneracy contracts the first differential up to the retraction
of the augmentation. -/
lemma objD_zero_comp_s_zero (ed : ExtraCodegeneracy X) :
    AlternatingCofaceMapComplex.objD X.right 0 ≫ ed.s 0 = 𝟙 _ - ed.s' ≫ X.hom.app ⦋0⦌ := by
  simp [Fin.sum_univ_two, sub_eq_add_neg, ed.δ₁_comp_s₀]

/-- In positive degrees, the extra codegeneracy is a contracting homotopy of the alternating
coface map complex. -/
lemma objD_succ_comp_s_add_s_comp_objD (ed : ExtraCodegeneracy X) (n : ℕ) :
    AlternatingCofaceMapComplex.objD X.right (n + 1) ≫ ed.s (n + 1) +
      ed.s n ≫ AlternatingCofaceMapComplex.objD X.right n = 𝟙 _ := by
  rw [AlternatingCofaceMapComplex.objD, AlternatingCofaceMapComplex.objD, Fin.sum_univ_succ,
    Preadditive.add_comp, Preadditive.sum_comp, Preadditive.comp_sum]
  simp only [Fin.val_zero, pow_zero, one_smul, δ₀_comp_s, Fin.val_succ, pow_succ, mul_neg_one,
    neg_smul, Preadditive.neg_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul, δ_comp_s,
    Finset.sum_neg_distrib]
  abel

/-- The components of the contracting homotopy: `-s j` from degree `j + 1` to degree `j`, and
zero otherwise. It is stated for a plain cosimplicial object `Y`, so that its computations do not
pass through the projections of augmented objects. -/
private def negSuccHom {Y : CosimplicialObject C} (s : ∀ n : ℕ, Y.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n⦌)
    (i j : ℕ) :
    ((alternatingCofaceMapComplex C).obj Y).X i ⟶ ((alternatingCofaceMapComplex C).obj Y).X j :=
  Pi.single (M := fun i ↦ ((alternatingCofaceMapComplex C).obj Y).X i ⟶
    ((alternatingCofaceMapComplex C).obj Y).X j) (j + 1) (-s j) i

private lemma negSuccHom_eq_zero {Y : CosimplicialObject C}
    (s : ∀ n : ℕ, Y.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n⦌) {i j : ℕ} (h : i ≠ j + 1) :
    negSuccHom s i j = 0 :=
  Pi.single_eq_of_ne h _

private lemma negSuccHom_succ {Y : CosimplicialObject C}
    (s : ∀ n : ℕ, Y.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n⦌) (j : ℕ) :
    negSuccHom s (j + 1) j = -s j :=
  Pi.single_eq_same _ _

/-- The homotopy relation in degree `0`, from the contraction identity in degree `0`. -/
private lemma comp_eq_dNext_zero_negSuccHom {Y : CosimplicialObject C} {A : C}
    (s : ∀ n : ℕ, Y.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n⦌) (e : A ⟶ Y.obj ⦋0⦌) (s' : Y.obj ⦋0⦌ ⟶ A)
    (h : AlternatingCofaceMapComplex.objD Y 0 ≫ s 0 = 𝟙 _ - s' ≫ e) :
    s' ≫ e = dNext 0 (negSuccHom s) + prevD 0 (negSuccHom s) +
      𝟙 (((alternatingCofaceMapComplex C).obj Y).X 0) := by
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
    alternatingCofaceMapComplex_obj_d, negSuccHom_succ]
  -- The terms of the alternating coface map complex are those of `Y`, by definition.
  have key : s' ≫ e = AlternatingCofaceMapComplex.objD Y 0 ≫ (-s 0) + 0 + 𝟙 (Y.obj ⦋0⦌) := by
    rw [Preadditive.comp_neg, h]
    abel
  exact key

/-- The homotopy relation in positive degrees, from the contraction identity there. -/
private lemma dNext_succ_negSuccHom_add_prevD {Y : CosimplicialObject C}
    (s : ∀ n : ℕ, Y.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n⦌) (n : ℕ)
    (h : AlternatingCofaceMapComplex.objD Y (n + 1) ≫ s (n + 1) +
      s n ≫ AlternatingCofaceMapComplex.objD Y n = 𝟙 _) :
    0 = dNext (n + 1) (negSuccHom s) + prevD (n + 1) (negSuccHom s) +
      𝟙 (((alternatingCofaceMapComplex C).obj Y).X (n + 1)) := by
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex,
    alternatingCofaceMapComplex_obj_d, alternatingCofaceMapComplex_obj_d, negSuccHom_succ,
    negSuccHom_succ]
  -- The terms of the alternating coface map complex are those of `Y`, by definition.
  have key : (0 : Y.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n + 1⦌) =
      AlternatingCofaceMapComplex.objD Y (n + 1) ≫ (-s (n + 1)) +
        (-s n) ≫ AlternatingCofaceMapComplex.objD Y n + 𝟙 _ := by
    rw [Preadditive.comp_neg, Preadditive.neg_comp, ← h]
    abel
  exact key

variable [HasZeroObject C]

/-- If `X` is an augmented cosimplicial object in a preadditive category with an extra
codegeneracy, then the augmentation `AlternatingCofaceMapComplex.ε.app X`, from the augmentation
object placed in degree `0` to the alternating coface map complex, is a homotopy equivalence. -/
def homotopyEquiv (ed : ExtraCodegeneracy X) :
    HomotopyEquiv ((CochainComplex.single₀ C).obj X.left)
      ((alternatingCofaceMapComplex C).obj X.right) where
  hom := AlternatingCofaceMapComplex.ε.app X
  inv := (CochainComplex.toSingle₀Equiv _ _).symm ed.s'
  -- The projections of augmented objects are stated for `Comma`, so `simp` and `rw` cannot
  -- match the degree `0` components of these cochain maps; we compose the component equations
  -- directly instead.
  homotopyHomInvId := Homotopy.ofEq <| HomologicalComplex.from_single_hom_ext <|
    ((HomologicalComplex.comp_f _ _ 0).trans
      ((congrArg₂ (· ≫ ·) (AlternatingCofaceMapComplex.ε_app_f_zero X)
        (CochainComplex.toSingle₀Equiv_symm_apply_f_zero ed.s')).trans ed.ε_comp_s')).trans
      (HomologicalComplex.id_f _ 0).symm
  homotopyInvHomId :=
    { hom := negSuccHom ed.s
      zero _ _ h := negSuccHom_eq_zero ed.s (Ne.symm h)
      comm
        | 0 => by
          have h := CochainComplex.toSingle₀Equiv_symm_apply_f_zero
            (C := (alternatingCofaceMapComplex C).obj X.right) ed.s'
          exact ((HomologicalComplex.comp_f _ _ 0).trans (congrArg₂ (· ≫ ·) h
            (AlternatingCofaceMapComplex.ε_app_f_zero X))).trans
            (comp_eq_dNext_zero_negSuccHom ed.s _ _ ed.objD_zero_comp_s_zero)
        | n + 1 =>
          ((HomologicalComplex.comp_f _ _ _).trans ((congrArg (· ≫ _)
            (CochainComplex.toSingle₀Equiv_symm_apply_f_succ ed.s' n)).trans zero_comp)).trans
            (dNext_succ_negSuccHom_add_prevD ed.s n (ed.objD_succ_comp_s_add_s_comp_objD n)) }

/-- The homotopy equivalence of an extra codegeneracy is the augmentation. -/
@[simp]
lemma homotopyEquiv_hom (ed : ExtraCodegeneracy X) :
    ed.homotopyEquiv.hom = AlternatingCofaceMapComplex.ε.app X := (rfl)

/-- The homotopy inverse of an extra codegeneracy is its retraction `s'` in degree `0`. -/
lemma homotopyEquiv_inv (ed : ExtraCodegeneracy X) :
    ed.homotopyEquiv.inv = (CochainComplex.toSingle₀Equiv _ _).symm ed.s' := (rfl)

/-- An extra codegeneracy of the reversal of `X`, that is, a contraction splitting the last cofaces
of `X`, also makes the augmentation of `X` a homotopy equivalence: the homotopy equivalence of
`homotopyEquiv` is transported along the sign comparison
`opFunctorCompAlternatingCofaceMapComplexIso` between the two alternating coface map complexes. -/
def homotopyEquivOfOpFunctor (ed : ExtraCodegeneracy (opFunctor.obj X)) :
    HomotopyEquiv ((CochainComplex.single₀ C).obj X.left)
      ((alternatingCofaceMapComplex C).obj X.right) :=
  ed.homotopyEquiv.trans
    (HomotopyEquiv.ofIso (opFunctorCompAlternatingCofaceMapComplexIso.app X.right))

/-- The homotopy equivalence obtained from an extra codegeneracy of the reversal is the
augmentation of `X`. -/
@[simp]
lemma homotopyEquivOfOpFunctor_hom (ed : ExtraCodegeneracy (opFunctor.obj X)) :
    ed.homotopyEquivOfOpFunctor.hom = AlternatingCofaceMapComplex.ε.app X :=
  ε_app_comp_opFunctorCompAlternatingCofaceMapComplexIso_hom_app X

end Preadditive

end ExtraCodegeneracy

end CategoryTheory.CosimplicialObject.Augmented

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

variable {C : Type u} [Category.{v} C]

/-- An extra degeneracy of an augmented simplicial object `X` gives an extra codegeneracy of the
augmented cosimplicial object `X.rightOp` in the opposite category. -/
def rightOp {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X) :
    CosimplicialObject.Augmented.ExtraCodegeneracy X.rightOp where
  s' := ed.s'.op
  s n := (ed.s n).op
  -- Composition in `Cᵒᵖ` is composition in `C` in the opposite order.
  ε_comp_s' := congrArg Quiver.Hom.op ed.s'_comp_ε
  δ₁_comp_s₀ := congrArg Quiver.Hom.op ed.s₀_comp_δ₁
  δ₀_comp_s n := congrArg Quiver.Hom.op (ed.s_comp_δ₀ n)
  δ_comp_s n i := congrArg Quiver.Hom.op (ed.s_comp_δ n i)
  σ_comp_s n i := congrArg Quiver.Hom.op (ed.s_comp_σ n i)

@[simp]
lemma rightOp_s' {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X) :
    ed.rightOp.s' = ed.s'.op := (rfl)

@[simp]
lemma rightOp_s {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X) (n : ℕ) :
    ed.rightOp.s n = (ed.s n).op := (rfl)

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy
