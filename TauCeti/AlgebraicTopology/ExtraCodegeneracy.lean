/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import TauCeti.Algebra.Homology.Homotopy
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
* `ExtraCodegeneracy.ofIso`: extra codegeneracies are transported along isomorphisms.
* `SimplicialObject.Augmented.ExtraDegeneracy.rightOp`: an extra degeneracy of an augmented
  simplicial object is an extra codegeneracy of the opposite augmented cosimplicial object.
  Composed with `ExtraCodegeneracy.map`, this turns an extra degeneracy into an extra
  codegeneracy after applying a contravariant functor such as a `Hom` functor `Hom(-, Y)`.
* `ExtraCodegeneracy.homotopyEquiv`: in a preadditive category with a zero object, the
  augmentation `AlgebraicTopology.AlternatingCofaceMapComplex.ε` of an augmented cosimplicial
  object with an extra codegeneracy is a homotopy equivalence from the augmentation object in
  degree `0` to the alternating coface map complex. Its inverse is the retraction `s'` in degree
  `0` and its contracting homotopy is `-s n` from degree `n + 1` to degree `n`
  (`ExtraCodegeneracy.homotopyEquiv_inv`,
  `ExtraCodegeneracy.homotopyEquiv_homotopyInvHomId_hom_succ`).
* `ExtraCodegeneracy.homotopyEquivOfOpFunctor`: the same conclusion from an extra
  codegeneracy of the reversal `CosimplicialObject.Augmented.opFunctor.obj X`, that is, from maps
  splitting the *last* cofaces of `X` and a retraction of its augmentation which, once reversed,
  satisfy all the identities of an extra codegeneracy, including those involving the
  augmentation. It is transported along the sign comparison
  `AlgebraicTopology.opFunctorCompAlternatingCofaceMapComplexIso`, which multiplies the
  contracting homotopy by `(-1) ^ (n + 1)` in degree `n + 1`.

## Implementation notes

Unlike Mathlib's `SimplicialObject.Augmented`, the type `CosimplicialObject.Augmented` is not
`@[implicit_reducible]`. A goal mentioning a projection such as `X.right` of an augmented
cosimplicial object `X` is therefore not type-correct at the transparency used by `simp`, `dsimp`
and `rw`, which fail on it (`simp made no progress`, with the note that the target is not
type-correct under the `implicit` transparency level). Mathlib's dual proofs in
`Mathlib.AlgebraicTopology.ExtraDegeneracy` close such goals by `simp`; here the proofs compose
the component equations by hand instead.

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
  -- `simp [← F.map_comp]` fails on these goals (see the implementation notes), so we compose
  -- the equations by hand.
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

/-- If `ed` is an extra codegeneracy of `X` and `e : X ≅ Y` is an isomorphism of augmented
cosimplicial objects, then `ed.ofIso e` is the extra codegeneracy of `Y` obtained by conjugating
`ed` with the components of `e`. -/
def ofIso {Y : CosimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraCodegeneracy X) :
    ExtraCodegeneracy Y where
  s' := e.inv.right.app ⦋0⦌ ≫ ed.s' ≫ e.hom.left
  s n := e.inv.right.app ⦋n + 1⦌ ≫ ed.s n ≫ e.hom.right.app ⦋n⦌
  -- The components of `e` are stated for `Comma`, so `rw` cannot recombine them; we use the
  -- equations of `e.inv_hom_id` and the augmentation square of `e.hom` directly.
  ε_comp_s' := by
    rw [← w_app_assoc, ed.ε_comp_s'_assoc]
    exact (congrArg (e.inv.left ≫ ·) (id_comp _)).trans (congrArg CommaMorphism.left e.inv_hom_id)
  δ₁_comp_s₀ := by
    rw [δ_naturality_assoc, ed.δ₁_comp_s₀_assoc, assoc, assoc]
    exact congrArg (e.inv.right.app ⦋0⦌ ≫ ed.s' ≫ ·) (w_app (η := e.hom)).symm
  δ₀_comp_s n := by
    rw [δ_naturality_assoc, ed.δ₀_comp_s_assoc]
    exact congrArg (fun f ↦ f.right.app ⦋n⦌) e.inv_hom_id
  δ_comp_s n i := by
    rw [δ_naturality_assoc, ed.δ_comp_s_assoc, assoc, assoc, δ_naturality]
  σ_comp_s n i := by
    rw [σ_naturality_assoc, ed.σ_comp_s_assoc, assoc, assoc, σ_naturality]

@[simp]
lemma ofIso_s' {Y : CosimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraCodegeneracy X) :
    (ed.ofIso e).s' = e.inv.right.app ⦋0⦌ ≫ ed.s' ≫ e.hom.left := (rfl)

@[simp]
lemma ofIso_s {Y : CosimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraCodegeneracy X)
    (n : ℕ) : (ed.ofIso e).s n = e.inv.right.app ⦋n + 1⦌ ≫ ed.s n ≫ e.hom.right.app ⦋n⦌ := (rfl)

section Preadditive

variable [Preadditive C]

/-- In degree `0`, the first differential followed by the extra codegeneracy is the identity minus
the retraction `s'` followed by the augmentation. -/
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

/-- The homotopy identity in degree `0`, from the contraction identity in degree `0`. It is
stated for a plain cosimplicial object `Y`, so that its computations do not pass through the
projections of augmented objects. -/
private lemma sub_id_eq_d_zero_comp_neg {Y : CosimplicialObject C} {A : C}
    (s₀ : Y.obj ⦋1⦌ ⟶ Y.obj ⦋0⦌) (e : A ⟶ Y.obj ⦋0⦌) (s' : Y.obj ⦋0⦌ ⟶ A)
    (h : AlternatingCofaceMapComplex.objD Y 0 ≫ s₀ = 𝟙 _ - s' ≫ e) :
    s' ≫ e - 𝟙 _ = ((alternatingCofaceMapComplex C).obj Y).d 0 1 ≫ (-s₀) := by
  rw [alternatingCofaceMapComplex_obj_d]
  -- The terms of the alternating coface map complex are those of `Y`, by definition.
  have key : s' ≫ e - 𝟙 (Y.obj ⦋0⦌) = AlternatingCofaceMapComplex.objD Y 0 ≫ (-s₀) := by
    rw [Preadditive.comp_neg, h, neg_sub]
  exact key

/-- The homotopy identity in positive degrees, from the contraction identity there. -/
private lemma zero_sub_id_eq_d_comp_neg_add {Y : CosimplicialObject C}
    (s : ∀ n : ℕ, Y.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n⦌) (n : ℕ)
    (h : AlternatingCofaceMapComplex.objD Y (n + 1) ≫ s (n + 1) +
      s n ≫ AlternatingCofaceMapComplex.objD Y n = 𝟙 _) :
    0 - 𝟙 (((alternatingCofaceMapComplex C).obj Y).X (n + 1)) =
      (((alternatingCofaceMapComplex C).obj Y).d (n + 1) (n + 2) ≫ (-s (n + 1)) :
        ((alternatingCofaceMapComplex C).obj Y).X (n + 1) ⟶
          ((alternatingCofaceMapComplex C).obj Y).X (n + 1)) +
        ((-s n) ≫ ((alternatingCofaceMapComplex C).obj Y).d n (n + 1) :
          ((alternatingCofaceMapComplex C).obj Y).X (n + 1) ⟶
            ((alternatingCofaceMapComplex C).obj Y).X (n + 1)) := by
  rw [alternatingCofaceMapComplex_obj_d, alternatingCofaceMapComplex_obj_d]
  -- The terms of the alternating coface map complex are those of `Y`, by definition.
  have key : (0 : Y.obj ⦋n + 1⦌ ⟶ Y.obj ⦋n + 1⦌) - 𝟙 _ =
      AlternatingCofaceMapComplex.objD Y (n + 1) ≫ (-s (n + 1)) +
        (-s n) ≫ AlternatingCofaceMapComplex.objD Y n := by
    rw [Preadditive.comp_neg, Preadditive.neg_comp, ← neg_add, h, zero_sub]
  exact key

variable [HasZeroObject C]

/-- The retraction `s'` of an extra codegeneracy, as a cochain map to the augmentation object in
degree `0`, is a left inverse of the augmentation cochain map. -/
@[reassoc]
lemma ε_app_comp_toSingle₀Equiv_symm_s' (ed : ExtraCodegeneracy X) :
    AlternatingCofaceMapComplex.ε.app X ≫
      (CochainComplex.toSingle₀Equiv ((alternatingCofaceMapComplex C).obj X.right) X.left).symm
        ed.s' = 𝟙 _ :=
  -- `simp` and `rw` fail on the degree `0` components of these cochain maps (see the
  -- implementation notes), so we compose the component equations directly instead.
  HomologicalComplex.from_single_hom_ext <|
    ((HomologicalComplex.comp_f _ _ 0).trans
      ((congrArg₂ (· ≫ ·) (AlternatingCofaceMapComplex.ε_app_f_zero X)
        (CochainComplex.toSingle₀Equiv_symm_apply_f_zero ed.s')).trans ed.ε_comp_s')).trans
      (HomologicalComplex.id_f _ 0).symm

/-- If `X` is an augmented cosimplicial object in a preadditive category with an extra
codegeneracy, then the augmentation `AlternatingCofaceMapComplex.ε.app X`, from the augmentation
object placed in degree `0` to the alternating coface map complex, is a homotopy equivalence. Its
inverse is the retraction `s'` in degree `0`, and its contracting homotopy is `-s n` from degree
`n + 1` to degree `n`. -/
def homotopyEquiv (ed : ExtraCodegeneracy X) :
    HomotopyEquiv ((CochainComplex.single₀ C).obj X.left)
      ((alternatingCofaceMapComplex C).obj X.right) where
  hom := AlternatingCofaceMapComplex.ε.app X
  inv := (CochainComplex.toSingle₀Equiv _ _).symm ed.s'
  homotopyHomInvId := Homotopy.ofEq ed.ε_app_comp_toSingle₀Equiv_symm_s'
  homotopyInvHomId := Homotopy.equivSubZero.symm <|
    Homotopy.mkCochainComplex _ (fun n ↦ -ed.s n)
      -- `simp` and `rw` fail on the components of these cochain maps (see the implementation
      -- notes), so we compose the component equations directly.
      (by
        have h : ((CochainComplex.toSingle₀Equiv ((alternatingCofaceMapComplex C).obj X.right)
            X.left).symm ed.s' ≫ AlternatingCofaceMapComplex.ε.app X).f 0 =
              ed.s' ≫ X.hom.app ⦋0⦌ :=
          (HomologicalComplex.comp_f _ _ 0).trans (congrArg₂ (· ≫ ·)
            (CochainComplex.toSingle₀Equiv_symm_apply_f_zero _)
            (AlternatingCofaceMapComplex.ε_app_f_zero X))
        exact (HomologicalComplex.sub_f_apply _ _ 0).trans
          ((congrArg (fun a : X.right.obj ⦋0⦌ ⟶ X.right.obj ⦋0⦌ ↦ a - _) h).trans
            (sub_id_eq_d_zero_comp_neg (ed.s 0) _ _ ed.objD_zero_comp_s_zero)))
      (fun n ↦ by
        have h : ((CochainComplex.toSingle₀Equiv ((alternatingCofaceMapComplex C).obj X.right)
            X.left).symm ed.s' ≫ AlternatingCofaceMapComplex.ε.app X).f (n + 1) = 0 :=
          (HomologicalComplex.comp_f _ _ _).trans ((congrArg (· ≫ _)
            (CochainComplex.toSingle₀Equiv_symm_apply_f_succ ed.s' n)).trans zero_comp)
        exact (HomologicalComplex.sub_f_apply _ _ _).trans
          ((congrArg (fun a : X.right.obj ⦋n + 1⦌ ⟶ X.right.obj ⦋n + 1⦌ ↦ a - _) h).trans
            (zero_sub_id_eq_d_comp_neg_add ed.s n (ed.objD_succ_comp_s_add_s_comp_objD n))))

/-- The forward cochain map of the homotopy equivalence of an extra codegeneracy is the
augmentation. -/
@[simp]
lemma homotopyEquiv_hom (ed : ExtraCodegeneracy X) :
    ed.homotopyEquiv.hom = AlternatingCofaceMapComplex.ε.app X := (rfl)

/-- The homotopy inverse of an extra codegeneracy is its retraction `s'` in degree `0`. -/
@[simp]
lemma homotopyEquiv_inv (ed : ExtraCodegeneracy X) :
    ed.homotopyEquiv.inv = (CochainComplex.toSingle₀Equiv _ _).symm ed.s' := (rfl)

/-- The contracting homotopy of an extra codegeneracy is `-s n` from degree `n + 1` to
degree `n`. -/
@[simp]
lemma homotopyEquiv_homotopyInvHomId_hom_succ (ed : ExtraCodegeneracy X) (n : ℕ) :
    ed.homotopyEquiv.homotopyInvHomId.hom (n + 1) n = -ed.s n :=
  Homotopy.mkCochainComplex_hom_succ _ _ _ _ n

/-- An extra codegeneracy of the reversal of `X` also makes the augmentation of `X` a homotopy
equivalence: the homotopy equivalence of `homotopyEquiv` is transported along the sign comparison
`opFunctorCompAlternatingCofaceMapComplexIso` between the two alternating coface map complexes.
Such an extra codegeneracy consists of maps splitting the last cofaces of `X` and a retraction of
its augmentation, subject to all the identities of an extra codegeneracy of the reversal. -/
def homotopyEquivOfOpFunctor (ed : ExtraCodegeneracy (opFunctor.obj X)) :
    HomotopyEquiv ((CochainComplex.single₀ C).obj X.left)
      ((alternatingCofaceMapComplex C).obj X.right) where
  hom := AlternatingCofaceMapComplex.ε.app X
  inv := (opFunctorCompAlternatingCofaceMapComplexIso.inv.app X.right) ≫ ed.homotopyEquiv.inv
  -- `simp` and `rw` fail on these composites (see the implementation notes), so we compose the
  -- equations directly. The augmentation of `X` is that of its reversal followed by the sign
  -- comparison.
  homotopyHomInvId := Homotopy.ofEq <|
    (congrArg (· ≫ _) (ε_app_comp_opFunctorCompAlternatingCofaceMapComplexIso_hom_app X).symm).trans
      ((assoc _ _ _).trans ((congrArg (AlternatingCofaceMapComplex.ε.app (opFunctor.obj X) ≫ ·)
        (opFunctorCompAlternatingCofaceMapComplexIso.hom_inv_id_app_assoc X.right _)).trans
          ed.ε_app_comp_toSingle₀Equiv_symm_s'))
  homotopyInvHomId :=
    (Homotopy.ofEq ((congrArg (_ ≫ ·)
      (ε_app_comp_opFunctorCompAlternatingCofaceMapComplexIso_hom_app X).symm).trans
        ((assoc _ _ _).trans (congrArg (_ ≫ ·) (assoc _ _ _).symm)))).trans
      (((ed.homotopyEquiv.homotopyInvHomId.compRight
        (opFunctorCompAlternatingCofaceMapComplexIso.hom.app X.right)).compLeft
          (opFunctorCompAlternatingCofaceMapComplexIso.inv.app X.right)).trans
        (Homotopy.ofEq ((congrArg (_ ≫ ·) (id_comp _)).trans (Iso.inv_hom_id_app _ _))))

/-- The forward cochain map of the homotopy equivalence obtained from an extra codegeneracy of
the reversal is the augmentation of `X`. -/
@[simp]
lemma homotopyEquivOfOpFunctor_hom (ed : ExtraCodegeneracy (opFunctor.obj X)) :
    ed.homotopyEquivOfOpFunctor.hom = AlternatingCofaceMapComplex.ε.app X := (rfl)

/-- The homotopy inverse obtained from an extra codegeneracy of the reversal is the retraction
`s'` in degree `0`, precomposed with the identity isomorphism `opObjIso`. -/
@[simp]
lemma homotopyEquivOfOpFunctor_inv (ed : ExtraCodegeneracy (opFunctor.obj X)) :
    ed.homotopyEquivOfOpFunctor.inv =
      (CochainComplex.toSingle₀Equiv _ _).symm (CosimplicialObject.opObjIso.inv ≫ ed.s') := by
  apply HomologicalComplex.to_single_hom_ext
  exact (HomologicalComplex.comp_f _ _ 0).trans ((congrArg₂ (· ≫ ·)
    (opFunctorCompAlternatingCofaceMapComplexIso_inv_app_f_zero X.right)
    (CochainComplex.toSingle₀Equiv_symm_apply_f_zero
      (C := (alternatingCofaceMapComplex C).obj (opFunctor.obj X).right) ed.s')).trans
    (CochainComplex.toSingle₀Equiv_symm_apply_f_zero
      (C := (alternatingCofaceMapComplex C).obj X.right) (X := X.left)
      (CosimplicialObject.opObjIso.inv ≫ ed.s')).symm)

/-- The contracting homotopy obtained from an extra codegeneracy of the reversal is
`-(-1) ^ (n + 1) • s n`, conjugated by the identity isomorphisms `opObjIso`, from degree `n + 1`
to degree `n`. -/
@[simp]
lemma homotopyEquivOfOpFunctor_homotopyInvHomId_hom_succ
    (ed : ExtraCodegeneracy (opFunctor.obj X)) (n : ℕ) :
    ed.homotopyEquivOfOpFunctor.homotopyInvHomId.hom (n + 1) n =
      -((-1 : ℤˣ) ^ (n + 1) •
        (CosimplicialObject.opObjIso.inv ≫ ed.s n ≫ CosimplicialObject.opObjIso.hom)) := by
  have h : ed.homotopyEquivOfOpFunctor.homotopyInvHomId.hom (n + 1) n =
      (opFunctorCompAlternatingCofaceMapComplexIso.inv.app X.right).f (n + 1) ≫
        ed.homotopyEquiv.homotopyInvHomId.hom (n + 1) n ≫
          (opFunctorCompAlternatingCofaceMapComplexIso.hom.app X.right).f n :=
    -- By the definitions of `homotopyEquivOfOpFunctor`, `Homotopy.trans`, `Homotopy.compLeft`,
    -- `Homotopy.compRight` and `Homotopy.ofEq`, the left side unfolds to `0 + (i ≫ h ≫ j + 0)`
    -- for the composite `i ≫ h ≫ j` on the right. `simp` with their `_hom` lemmas fails on
    -- this goal (see the implementation notes), so we rely on that unfolding.
    (zero_add _).trans (add_zero _)
  rw [h, homotopyEquiv_homotopyInvHomId_hom_succ,
    opFunctorCompAlternatingCofaceMapComplexIso_inv_app_f,
    opFunctorCompAlternatingCofaceMapComplexIso_hom_app_f,
    TauCeti.neg_one_pow_mul_succ_div_two_succ]
  -- The signs combine as `v * (u * v)⁻¹ = u`, since every unit of `ℤ` is its own inverse. We
  -- state this for plain objects, as the terms of the complexes are only definitionally those of
  -- the cosimplicial objects.
  have key {P Q R S : C} (i : P ⟶ Q) (s : Q ⟶ R) (h : R ⟶ S) (u v : ℤˣ) :
      ((u * v)⁻¹ • i) ≫ (-s) ≫ (v • h) = -(u • (i ≫ s ≫ h)) := by
    simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      Preadditive.neg_comp, Preadditive.comp_neg, smul_neg, smul_smul]
    rw [Int.units_inv_eq_self, ← Units.val_mul, mul_left_comm, Int.units_mul_self, mul_one]
  exact key _ _ _ _ _

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
