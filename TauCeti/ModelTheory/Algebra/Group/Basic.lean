/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.ModelTheory.Semantics
public import TauCeti.ModelTheory.LanguageMap

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic.FinCases

/-!
# The first-order language of groups

This file defines the first-order language of groups, `FirstOrder.Language.group`, with a constant
symbol `1`, a unary function symbol `⁻¹` and a binary function symbol `*`, and no relation
symbols, together with the theory of groups `FirstOrder.Language.Theory.group`.

A type with `1`, `⁻¹` and `*` is a `Language.group`-structure, and a structure is a model of the
theory of groups exactly when these operations satisfy the group axioms. Equations over a group
with coefficients are expressed in the language `L_A = Language.group[[A]]` obtained by adding a
constant symbol for each coefficient name `a : A`: a group `G` with a coefficient map `c : A → G`
is an `L_A`-structure through Mathlib's `constantsOn.structure c`. This is the language in which
existential and universal sentences over a free group `F(A)` with basis constants are written.

## Main definitions

* `FirstOrder.Language.group`: the language of groups.
* `FirstOrder.Language.group.instStructure`: a type with `1`, `⁻¹` and `*` is a structure for the
  language of groups, interpreting the symbols by these operations.
* `FirstOrder.Language.Theory.group`: the theory of groups, consisting of associativity, the left
  identity law and the left inverse law.
* `FirstOrder.Language.group.groupOfModel`: the group carried by a model of the theory of groups.
* `FirstOrder.Language.group.commSentence`: the `L_A`-sentence `a * b = b * a`.

## Main results

* `FirstOrder.Language.group.model_group_iff`: a structure for the language of groups is a model of
  the theory of groups if and only if its operations satisfy the group axioms; in particular every
  group is a model.
* `FirstOrder.Language.group.instStructure_groupOfModel`: the structure induced by the group of a
  model is the original structure.
* `FirstOrder.Language.group.realize_commSentence_iff`: `a * b = b * a` holds exactly when the
  coefficients of `a` and `b` commute.
* `FirstOrder.Language.group.not_realize_commSentence_freeGroup`: `a * b = b * a` is false in the
  free group on two letters, with the basis as coefficients.
* `FirstOrder.Language.group.realize_commSentence_multiplicative_pi`: `a * b = b * a` is true in
  `ℤ²`, with the standard basis as coefficients.

## Implementation notes

The language, its term operations and the passage from a model to a group follow Mathlib's
`FirstOrder.Language.ring` and `FirstOrder.Language.Theory.field`. Unlike there, the structure on a
type with `1`, `⁻¹` and `*` is an instance: the passage back from a structure to a group is the
non-instance `groupOfModel`, and `instStructure_groupOfModel` identifies the two structures.

## References

* O. Kharlampovich and A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.3.
-/

public section

universe u v w

namespace FirstOrder

/-- The function symbols of the language of groups: the constant `one`, the unary `inv` and the
binary `mul`. -/
inductive groupFunc : ℕ → Type
  | one : groupFunc 0
  | inv : groupFunc 1
  | mul : groupFunc 2
  deriving DecidableEq

/-- The first-order language of groups, with function symbols `1`, `⁻¹` and `*` and no relation
symbols. -/
@[expose] protected def Language.group : Language :=
  { Functions := groupFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace Language.group

open Structure

variable {α : Type u} {A : Type v} {G : Type w}

/-- `groupFunc.one`, as a constant symbol of `Language.group`. -/
abbrev oneFunc : Language.group.Functions 0 := groupFunc.one

/-- `groupFunc.inv`, as a unary function symbol of `Language.group`. -/
abbrev invFunc : Language.group.Functions 1 := groupFunc.inv

/-- `groupFunc.mul`, as a binary function symbol of `Language.group`. -/
abbrev mulFunc : Language.group.Functions 2 := groupFunc.mul

instance : One (Language.group.Term α) :=
  ⟨Constants.term oneFunc⟩

instance : Inv (Language.group.Term α) :=
  ⟨invFunc.apply₁⟩

instance : Mul (Language.group.Term α) :=
  ⟨mulFunc.apply₂⟩

theorem one_def : (1 : Language.group.Term α) = Constants.term oneFunc := (rfl)

theorem inv_def (t : Language.group.Term α) : t⁻¹ = invFunc.apply₁ t := (rfl)

theorem mul_def (t s : Language.group.Term α) : t * s = mulFunc.apply₂ t s := (rfl)

/-- A type with `1`, `⁻¹` and `*` is a structure for the language of groups, interpreting the
symbols by these operations. -/
instance instStructure [One G] [Inv G] [Mul G] : Language.group.Structure G where
  funMap := fun {n} f =>
    match n, f with
    | _, .one => fun _ => 1
    | _, .inv => fun x => (x 0)⁻¹
    | _, .mul => fun x => x 0 * x 1

section Operations

variable [One G] [Inv G] [Mul G]

@[simp]
theorem funMap_one (x : Fin 0 → G) : funMap oneFunc x = (1 : G) := (rfl)

@[simp]
theorem funMap_inv (x : Fin 1 → G) : funMap invFunc x = (x 0)⁻¹ := (rfl)

@[simp]
theorem funMap_mul (x : Fin 2 → G) : funMap mulFunc x = x 0 * x 1 := (rfl)

/-- The term `1` denotes the identity. -/
@[simp]
theorem realize_one (v : α → G) : (1 : Language.group.Term α).realize v = 1 := (rfl)

/-- The term `t⁻¹` denotes the inverse of the value of `t`. -/
@[simp]
theorem realize_inv (t : Language.group.Term α) (v : α → G) :
    t⁻¹.realize v = (t.realize v)⁻¹ := (rfl)

/-- The term `t * s` denotes the product of the values of `t` and `s`. -/
@[simp]
theorem realize_mul (t s : Language.group.Term α) (v : α → G) :
    (t * s).realize v = t.realize v * s.realize v := (rfl)

end Operations

end Language.group

/-- The theory of groups, as sentences of the language of groups: associativity, the left
identity law `1 * x = x` and the left inverse law `x⁻¹ * x = 1`. -/
protected def Language.Theory.group : Language.group.Theory :=
  {∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2))),
    ∀' ((1 * &0) =' &0),
    ∀' (((&0)⁻¹ * &0) =' 1)}

namespace Language.group

open Structure

variable {α : Type u} {A : Type v} {G : Type w} {H : Type*}

/-- A structure for the language of groups is a model of the theory of groups exactly when its
operations satisfy the group axioms. -/
theorem model_group_iff [One G] [Inv G] [Mul G] :
    G ⊨ Theory.group ↔ (∀ x y z : G, x * y * z = x * (y * z)) ∧ (∀ x : G, 1 * x = x) ∧
      ∀ x : G, x⁻¹ * x = 1 := by
  simp [Theory.model_iff, Theory.group, Sentence.Realize, Formula.Realize, Fin.snoc]

/-- Every group is a model of the theory of groups. -/
instance [Group G] : G ⊨ Theory.group :=
  model_group_iff.2 ⟨mul_assoc, one_mul, inv_mul_cancel⟩

/-- The multiplicative monoid `ℕ` is not a model of the theory of groups, however `⁻¹` is
interpreted: the theory of groups is not satisfied by every monoid. -/
theorem not_model_group_multiplicative_nat [Inv (Multiplicative ℕ)] :
    ¬ Multiplicative ℕ ⊨ Theory.group := fun h => by
  have := (model_group_iff.1 h).2.2 (Multiplicative.ofAdd 1)
  have h1 := congrArg Multiplicative.toAdd this
  simp only [toAdd_mul, toAdd_ofAdd, toAdd_one] at h1
  omega

section OfStructure

variable (G) [S : Language.group.Structure G]

/-- The identity of a structure for the language of groups. -/
abbrev oneOfStructure : One G := ⟨funMap oneFunc ![]⟩

/-- The inversion of a structure for the language of groups. -/
abbrev invOfStructure : Inv G := ⟨fun x => funMap invFunc ![x]⟩

/-- The multiplication of a structure for the language of groups. -/
abbrev mulOfStructure : Mul G := ⟨fun x y => funMap mulFunc ![x, y]⟩

/-- A structure for the language of groups is the structure `instStructure` induced by its own
identity, inversion and multiplication. -/
theorem instStructure_ofStructure :
    @instStructure G (oneOfStructure G) (invOfStructure G) (mulOfStructure G) = S := by
  obtain ⟨funMap, RelMap⟩ := S
  unfold instStructure
  congr 1
  · funext n f x
    -- both sides apply `funMap f`, to `x` and to the vector of its entries
    cases f <;> exact congrArg (funMap _) (funext fun i => by fin_cases i <;> rfl)
  · funext n r
    exact isEmptyElim r

/-- The group carried by a model of the theory of groups, with the operations of the structure. -/
abbrev groupOfModel [G ⊨ Theory.group] : Group G :=
  letI := oneOfStructure G
  letI := invOfStructure G
  letI := mulOfStructure G
  have h : @Theory.Model _ G instStructure Theory.group := by
    rwa [instStructure_ofStructure G]
  Group.ofLeftAxioms (model_group_iff.1 h).1 (model_group_iff.1 h).2.1 (model_group_iff.1 h).2.2

/-- The structure induced by the group of a model of the theory of groups is the original
structure. -/
theorem instStructure_groupOfModel [G ⊨ Theory.group] :
    letI := groupOfModel G
    (instStructure : Language.group.Structure G) = S :=
  -- `Group.ofLeftAxioms` keeps the supplied `Mul`, `Inv` and `One`, so the operations of
  -- `groupOfModel G` are definitionally `mulOfStructure G`, `invOfStructure G` and
  -- `oneOfStructure G`
  instStructure_ofStructure G

end OfStructure

/-- Group homomorphisms are homomorphisms of structures for the language of groups. -/
instance [Group G] [Group H] {F : Type*} [FunLike F G H] [MonoidHomClass F G H] :
    Language.group.HomClass F G H where
  map_fun φ n f x := by
    cases f <;> simp [map_one, map_inv, map_mul]
  map_rel _ _ r := isEmptyElim r

/-- Group isomorphisms are isomorphisms of structures for the language of groups. -/
instance [Group G] [Group H] {F : Type*} [EquivLike F G H] [MulEquivClass F G H] :
    Language.group.StrongHomClass F G H where
  map_fun := HomClass.map_fun
  map_rel _ _ r := isEmptyElim r

section Coefficients

/-! ### Coefficients

For a type `A` of coefficient names, `L_A = Language.group[[A]]`. A group `G` with a coefficient
map `c : A → G` is an `L_A`-structure through `constantsOn.structure c`. A group homomorphism
`φ` with `φ ∘ c = d` is then a homomorphism of `L_A`-structures,
`FirstOrder.Language.withConstantsHom c d φ h`, through the `Language.group.HomClass` instance
above.

The symbols `1`, `⁻¹` and `*` of `Language.group` are also symbols of `L_A`, so `L_A`-terms carry
the same operations, and in any `L_A`-structure expanding a `Language.group`-structure they denote
the group operations. Under `constantsOn.structure c` the constant term of `a : A` denotes `c a`,
by `Term.realize_constants` and `FirstOrder.Language.coe_con_constantsOn`. -/

instance : One (Language.group[[A]].Term α) :=
  ⟨Constants.term ((Language.group.lhomWithConstants A).onFunction oneFunc)⟩

instance : Inv (Language.group[[A]].Term α) :=
  ⟨Functions.apply₁ ((Language.group.lhomWithConstants A).onFunction invFunc)⟩

instance : Mul (Language.group[[A]].Term α) :=
  ⟨Functions.apply₂ ((Language.group.lhomWithConstants A).onFunction mulFunc)⟩

theorem one_withConstants_def :
    (1 : Language.group[[A]].Term α) =
      Constants.term ((Language.group.lhomWithConstants A).onFunction oneFunc) := (rfl)

theorem inv_withConstants_def (t : Language.group[[A]].Term α) :
    t⁻¹ = Functions.apply₁ ((Language.group.lhomWithConstants A).onFunction invFunc) t := (rfl)

theorem mul_withConstants_def (t s : Language.group[[A]].Term α) :
    t * s = Functions.apply₂ ((Language.group.lhomWithConstants A).onFunction mulFunc) t s := (rfl)

/-- Including `Language.group`-terms into `L_A` preserves `1`. -/
@[simp]
theorem onTerm_one :
    (Language.group.lhomWithConstants A).onTerm (1 : Language.group.Term α) = 1 := by
  rw [one_def, one_withConstants_def, Constants.term, Constants.term, LHom.onTerm]
  exact congrArg _ (funext fun i => i.elim0)

/-- Including `Language.group`-terms into `L_A` preserves `⁻¹`. -/
@[simp]
theorem onTerm_inv (t : Language.group.Term α) :
    (Language.group.lhomWithConstants A).onTerm t⁻¹ =
      ((Language.group.lhomWithConstants A).onTerm t)⁻¹ := by
  rw [inv_def, inv_withConstants_def, Functions.apply₁, Functions.apply₁, LHom.onTerm]
  exact congrArg _ (funext fun i => by fin_cases i; rfl)

/-- Including `Language.group`-terms into `L_A` preserves `*`. -/
@[simp]
theorem onTerm_mul (t s : Language.group.Term α) :
    (Language.group.lhomWithConstants A).onTerm (t * s) =
      (Language.group.lhomWithConstants A).onTerm t *
        (Language.group.lhomWithConstants A).onTerm s := by
  rw [mul_def, mul_withConstants_def, Functions.apply₂, Functions.apply₂, LHom.onTerm]
  exact congrArg _ (funext fun i => by fin_cases i <;> rfl)

section Operations

variable [One G] [Inv G] [Mul G]

section Expansion

variable [Language.group[[A]].Structure G] [(Language.group.lhomWithConstants A).IsExpansionOn G]

/-- The `L_A`-term `1` denotes the identity. -/
@[simp]
theorem realize_one_withConstants (v : α → G) :
    (1 : Language.group[[A]].Term α).realize v = 1 := by
  rw [one_withConstants_def, Term.realize_constants, ← funMap_eq_coe_constants (x := ![]),
    LHom.map_onFunction, funMap_one]

/-- The `L_A`-term `t⁻¹` denotes the inverse of the value of `t`. -/
@[simp]
theorem realize_inv_withConstants (t : Language.group[[A]].Term α) (v : α → G) :
    t⁻¹.realize v = (t.realize v)⁻¹ := by
  rw [inv_withConstants_def, Term.realize_functions_apply₁, LHom.map_onFunction, funMap_inv,
    Matrix.cons_val_zero]

/-- The `L_A`-term `t * s` denotes the product of the values of `t` and `s`. -/
@[simp]
theorem realize_mul_withConstants (t s : Language.group[[A]].Term α) (v : α → G) :
    (t * s).realize v = t.realize v * s.realize v := by
  rw [mul_withConstants_def, Term.realize_functions_apply₂, LHom.map_onFunction, funMap_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]

end Expansion

/-- The `L_A`-sentence `a * b = b * a`, for coefficient names `a b : A`. -/
def commSentence (a b : A) : Language.group[[A]].Sentence :=
  Term.bdEqual ((Language.group.con a).term * (Language.group.con b).term)
    ((Language.group.con b).term * (Language.group.con a).term)

/-- The sentence `a * b = b * a` holds exactly when the coefficients of `a` and `b` commute. -/
@[simp]
theorem realize_commSentence_iff (c : A → G) (a b : A) :
    letI := constantsOn.structure c
    G ⊨ commSentence a b ↔ Commute (c a) (c b) := by
  let := constantsOn.structure c
  simp [commSentence, Sentence.Realize, Formula.Realize, Commute, SemiconjBy]

end Operations

/-- The sentence `a * b = b * a`, for the two basis constants, is false in the free group on two
letters: an equation with constants can distinguish groups. -/
theorem not_realize_commSentence_freeGroup :
    letI := constantsOn.structure (FreeGroup.of : Fin 2 → FreeGroup (Fin 2))
    ¬ FreeGroup (Fin 2) ⊨ commSentence (0 : Fin 2) 1 := by
  rw [realize_commSentence_iff, Commute, SemiconjBy]
  decide

/-- The sentence `a * b = b * a` is true in `ℤ²`, with the standard basis as constants. -/
theorem realize_commSentence_multiplicative_pi :
    letI := constantsOn.structure
      (fun i => Multiplicative.ofAdd (Pi.single i 1) : Fin 2 → Multiplicative (Fin 2 → ℤ))
    Multiplicative (Fin 2 → ℤ) ⊨ commSentence (0 : Fin 2) 1 := by
  rw [realize_commSentence_iff]
  exact Commute.all _ _

end Coefficients

end Language.group

end FirstOrder
