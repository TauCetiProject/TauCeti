/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Group terms and free-group words

Terms in the group language with named coefficients denote words in the variables and
coefficient names. A reduced word has a canonical left-associated term representative, and
translating that term back to a word recovers the original group element. In every group,
evaluation of a term agrees with evaluation of its word. This translates atomic equalities into
word equations.

The term–word interpretation follows Kharlampovich and Myasnikov, *Implicit function theorem
over free groups*, §2.3. Mathlib's `FreeGroup.lift` supplies the universal evaluation map.
-/

public section

namespace FirstOrder.Language.group

open FirstOrder TauCeti

variable {A X : Type*}

/-- Interpret a group term with coefficient names as a word in the variables and names. -/
def Term.toWord : Language.group[[A]].Term X → FreeGroup (X ⊕ A)
  | .var x => FreeGroup.of (Sum.inl x)
  | .func (Sum.inl .one) _ => 1
  | .func (Sum.inl .inv) ts => (Term.toWord (ts 0))⁻¹
  | .func (Sum.inl .mul) ts => Term.toWord (ts 0) * Term.toWord (ts 1)
  | .func (l := 0) (Sum.inr a) _ => FreeGroup.of (Sum.inr a)
  | .func (l := _ + 1) (Sum.inr a) _ => isEmptyElim a

@[simp] theorem Term.toWord_var (x : X) :
    Term.toWord (Language.Term.var x : Language.group[[A]].Term X) =
      FreeGroup.of (Sum.inl x) := by
  simp [Term.toWord]

@[simp] theorem Term.toWord_coeff (a : A) :
    Term.toWord (Language.Constants.term (Sum.inr a) : Language.group[[A]].Term X) =
      FreeGroup.of (Sum.inr a) := by
  simp [Term.toWord, Language.Constants.term]

@[simp] theorem Term.toWord_one :
    Term.toWord (1 : Language.group[[A]].Term X) = 1 := by
  rfl

@[simp] theorem Term.toWord_inv (t : Language.group[[A]].Term X) :
    Term.toWord t⁻¹ = (Term.toWord t)⁻¹ := by
  rfl

@[simp] theorem Term.toWord_mul (t s : Language.group[[A]].Term X) :
    Term.toWord (t * s) = Term.toWord t * Term.toWord s := by
  rfl

/-- The term for a positive or negative variable or coefficient letter. -/
def Term.letter (e : (X ⊕ A) × Bool) : Language.group[[A]].Term X :=
  let t : Language.group[[A]].Term X :=
    e.1.elim Language.Term.var (fun a => Language.Constants.term (Sum.inr a))
  if e.2 then t else t⁻¹

@[simp] theorem Term.toWord_letter (e : (X ⊕ A) × Bool) :
    Term.toWord (Term.letter e) = if e.2 then FreeGroup.of e.1 else (FreeGroup.of e.1)⁻¹ := by
  rcases e with ⟨x | a, b⟩ <;> cases b <;> rfl

/-- A canonical left-associated term spelling the reduced word of a free-group element. -/
noncomputable def Term.ofWord (w : FreeGroup (X ⊕ A)) : Language.group[[A]].Term X := by
  classical
  exact (FreeGroup.toWord w).foldl (fun t e => t * Term.letter e) 1

open Classical in
/-- The canonical term is the left-associated product of the reduced word's letters. -/
theorem Term.ofWord_def (w : FreeGroup (X ⊕ A)) :
    Term.ofWord w = (FreeGroup.toWord w).foldl (fun t e => t * Term.letter e) 1 := by
  unfold Term.ofWord
  rfl

private theorem toWord_foldl (l : List ((X ⊕ A) × Bool))
    (t : Language.group[[A]].Term X) :
    Term.toWord (l.foldl (fun u e => u * Term.letter e) t) =
      Term.toWord t * FreeGroup.mk l := by
  induction l generalizing t with
  | nil => simp [FreeGroup.one_eq_mk]
  | cons e es ih =>
    rw [List.foldl_cons, ih, Term.toWord_mul, Term.toWord_letter]
    cases e with
    | mk x b =>
      cases b <;> simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev,
        FreeGroup.mul_mk, mul_assoc]

/-- Converting a word to a term and back recovers the word. -/
@[simp] theorem Term.toWord_ofWord (w : FreeGroup (X ⊕ A)) :
    Term.toWord (Term.ofWord w) = w := by
  classical
  rw [Term.ofWord, toWord_foldl, Term.toWord_one, one_mul, FreeGroup.mk_toWord]

/-- The canonical term for the empty word is the identity term. -/
@[simp] theorem Term.ofWord_one :
    Term.ofWord (1 : FreeGroup (X ⊕ A)) = 1 := by
  classical
  simp [Term.ofWord]

private theorem coeff_funMap_one {G : Type*} [Group G] (c : A → G) (xs : Fin 0 → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    @Language.Structure.funMap Language.group[[A]] G (inferInstance) 0
      (Sum.inl TauCeti.Group.oneFunc) xs = 1 := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  rw [Language.withConstants_funMap_sumInl]
  exact TauCeti.Group.funMap_one xs

private theorem coeff_funMap_inv {G : Type*} [Group G] (c : A → G) (xs : Fin 1 → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    @Language.Structure.funMap Language.group[[A]] G (inferInstance) 1
      (Sum.inl TauCeti.Group.invFunc) xs = (xs 0)⁻¹ := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  rw [Language.withConstants_funMap_sumInl]
  exact TauCeti.Group.funMap_inv xs

private theorem coeff_funMap_mul {G : Type*} [Group G] (c : A → G) (xs : Fin 2 → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    @Language.Structure.funMap Language.group[[A]] G (inferInstance) 2
      (Sum.inl TauCeti.Group.mulFunc) xs = xs 0 * xs 1 := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  rw [Language.withConstants_funMap_sumInl]
  exact TauCeti.Group.funMap_mul xs

private theorem coeff_funMap_const {G : Type*} [Group G] (c : A → G) (a : A)
    (xs : Fin 0 → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    @Language.Structure.funMap Language.group[[A]] G (inferInstance) 0
      (Sum.inr a) xs = c a := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  rw [Language.withConstants_funMap_sumInr]
  rfl

/-- Evaluating a group term agrees with evaluating its free-group word. -/
theorem Term.realize_eq_lift {G : Type*} [Group G] (c : A → G) (v : X → G)
    (t : Language.group[[A]].Term X) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    t.realize v = FreeGroup.lift (Sum.elim v c) (Term.toWord t) := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  induction t with
  | var x => simp
  | @func n f ts ih =>
    cases f with
    | inl f =>
      cases f with
      | one =>
        simpa only [Language.Term.realize, Term.toWord, map_one] using
          (coeff_funMap_one c (fun i => (ts i).realize v))
      | inv =>
        simp only [Language.Term.realize, Term.toWord, map_inv]
        rw [coeff_funMap_inv c (fun i => (ts i).realize v), ih 0]
      | mul =>
        simp only [Language.Term.realize, Term.toWord, map_mul]
        rw [coeff_funMap_mul c (fun i => (ts i).realize v), ih 0, ih 1]
    | inr a =>
      cases n with
      | zero =>
        simp only [Language.Term.realize, Term.toWord, FreeGroup.lift_apply_of]
        -- The explicit coefficient symbol reduces to its chosen group element.
        change _ = c a
        exact coeff_funMap_const c a (fun i => (ts i).realize v)
      | succ n => exact isEmptyElim a

/-- An interpreted atomic equality is the equation given by the quotient of its words. -/
theorem Term.realize_equal_iff {G : Type*} [Group G] (c : A → G) (v : X → G)
    (t s : Language.group[[A]].Term X) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    t.realize v = s.realize v ↔
      FreeGroup.lift (Sum.elim v c) (Term.toWord t * (Term.toWord s)⁻¹) = 1 := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  rw [Term.realize_eq_lift (G := G) c v t, Term.realize_eq_lift (G := G) c v s]
  simp only [map_mul, map_inv, mul_inv_eq_one]

example (a : A) (x : X) :
    Term.toWord ((Language.Constants.term (Sum.inr a) : Language.group[[A]].Term X)⁻¹ *
      (Language.Term.var x * Language.Constants.term (Sum.inr a))) =
      (FreeGroup.of (Sum.inr a))⁻¹ * FreeGroup.of (Sum.inl x) *
        FreeGroup.of (Sum.inr a) := by
  simp only [Term.toWord_mul, Term.toWord_inv, Term.toWord_coeff, Term.toWord_var]
  rfl

end FirstOrder.Language.group
