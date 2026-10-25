/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic.FinCases

/-!
# The first-order language of groups

The language has a constant for the identity, a unary inverse symbol and a binary
multiplication symbol. Adding named coefficients uses Mathlib's `Language.withConstants`.
The interpretation in a group, and the three left-hand group axioms, give the semantic
interface needed to turn group formulas into equations in words.
A model of the group theory yields a group whose operations recover the symbol interpretations.
Group homomorphisms, including those preserving named coefficients, induce language homomorphisms.

The choice of symbols and coefficient letters follows Kharlampovich and Myasnikov,
*Implicit function theorem over free groups*, §2.3. The language and structure interface
follows Mathlib's first-order language of rings. The axiom, theory and model construction
follow `Mathlib.ModelTheory.Algebra.Field.Basic`.
-/

public section

namespace TauCeti

open FirstOrder

/-- Function symbols for the identity, inverse and multiplication of a group. -/
inductive groupFunc : ℕ → Type
  | one : groupFunc 0
  | inv : groupFunc 1
  | mul : groupFunc 2
  deriving DecidableEq

end TauCeti

namespace FirstOrder

/-- The first-order language of groups, with equality as the only atomic relation. -/
@[expose] def Language.group : Language where
  Functions := TauCeti.groupFunc
  Relations := fun _ => Empty

end FirstOrder

namespace TauCeti

open FirstOrder FirstOrder.Language

/-- The three left-hand axioms characterizing a group: associativity, identity and inverse. -/
inductive GroupAxiom
  | mulAssoc
  | oneMul
  | invMulCancel

namespace Group

open Language groupFunc Language.Structure

/-- The identity symbol, viewed as a symbol of `Language.group`. -/
abbrev oneFunc : Language.group.Functions 0 := groupFunc.one

/-- The inverse symbol, viewed as a symbol of `Language.group`. -/
abbrev invFunc : Language.group.Functions 1 := groupFunc.inv

/-- The multiplication symbol, viewed as a symbol of `Language.group`. -/
abbrev mulFunc : Language.group.Functions 2 := groupFunc.mul

instance (α : Type*) : One (Language.group.Term α) :=
  ⟨Language.Constants.term oneFunc⟩

instance (α : Type*) : Inv (Language.group.Term α) :=
  ⟨invFunc.apply₁⟩

instance (α : Type*) : Mul (Language.group.Term α) :=
  ⟨mulFunc.apply₂⟩

theorem one_def (α : Type*) :
    (1 : Language.group.Term α) = Language.Constants.term oneFunc := rfl

theorem inv_def (α : Type*) (t : Language.group.Term α) :
    t⁻¹ = invFunc.apply₁ t := rfl

theorem mul_def (α : Type*) (t s : Language.group.Term α) :
    t * s = mulFunc.apply₂ t s := rfl

/-- Interpret the group language using identity, inverse and multiplication operations. -/
@[instance_reducible] def structureOfGroup (G : Type*) [One G] [Inv G] [Mul G] :
    Language.group.Structure G where
  funMap {n} f := by
    cases f with
    | one => exact fun _ => 1
    | inv => exact fun xs => (xs 0)⁻¹
    | mul => exact fun xs => xs 0 * xs 1
  RelMap r := nomatch r

section GroupStructure

variable {G : Type*} [One G] [Inv G] [Mul G]

attribute [local instance] structureOfGroup

/-- The identity symbol denotes the chosen identity operation. -/
@[simp] theorem funMap_one (xs : Fin 0 → G) :
    Language.Structure.funMap oneFunc xs = (1 : G) := (rfl)

/-- The inverse symbol denotes the chosen inversion operation. -/
@[simp] theorem funMap_inv (xs : Fin 1 → G) :
    Language.Structure.funMap invFunc xs = (xs 0)⁻¹ := (rfl)

/-- The multiplication symbol denotes the chosen multiplication operation. -/
@[simp] theorem funMap_mul (xs : Fin 2 → G) :
    Language.Structure.funMap mulFunc xs = xs 0 * xs 1 := (rfl)

@[simp] theorem realize_one {α : Type*} (v : α → G) :
    Language.Term.realize v (1 : Language.group.Term α) = 1 := (rfl)

@[simp] theorem realize_inv {α : Type*} (v : α → G) (t : Language.group.Term α) :
    Language.Term.realize v t⁻¹ = (Language.Term.realize v t)⁻¹ := (rfl)

@[simp] theorem realize_mul {α : Type*} (v : α → G) (t s : Language.group.Term α) :
    Language.Term.realize v (t * s) =
      Language.Term.realize v t * Language.Term.realize v s := (rfl)

end GroupStructure

/-- Identity as a term in the group language with named coefficients. -/
instance (A X : Type*) : One (Language.group[[A]].Term X) :=
  ⟨Language.Constants.term (Sum.inl oneFunc)⟩

/-- Inversion as a term in the group language with named coefficients. -/
instance (A X : Type*) : Inv (Language.group[[A]].Term X) :=
  ⟨Language.Functions.apply₁ (Sum.inl invFunc : Language.group[[A]].Functions 1)⟩

/-- Multiplication as a term in the group language with named coefficients. -/
instance (A X : Type*) : Mul (Language.group[[A]].Term X) :=
  ⟨Language.Functions.apply₂ (Sum.inl mulFunc : Language.group[[A]].Functions 2)⟩

section Coefficients

variable {G A X : Type*} [One G] [Inv G] [Mul G]
  [(Language.constantsOn A).Structure G] (v : X → G)

attribute [local instance] structureOfGroup

-- The withConstants structure interprets each Sum.inl symbol using the base language,
-- so realization reduces definitionally to the corresponding group operation below.
/-- The identity term evaluates to the group identity in the coefficient language. -/
@[simp] theorem realize_coeff_one :
    Language.Term.realize v (1 : Language.group[[A]].Term X) = 1 := by
  rfl

/-- Inversion of a coefficient term evaluates by inversion. -/
@[simp] theorem realize_coeff_inv (t : Language.group[[A]].Term X) :
    Language.Term.realize v t⁻¹ = (Language.Term.realize v t)⁻¹ := by
  rfl

/-- Multiplication of coefficient terms evaluates by multiplication. -/
@[simp] theorem realize_coeff_mul (t s : Language.group[[A]].Term X) :
    Language.Term.realize v (t * s) =
      Language.Term.realize v t * Language.Term.realize v s := by
  rfl

end Coefficients

end Group

open Language BoundedFormula

namespace GroupAxiom

/-- The sentence expressing one of the three left-hand group axioms. -/
def toSentence : GroupAxiom → Language.group.Sentence
  | .mulAssoc => ∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .oneMul => ∀' (((1 : Language.group.Term _) * &0) =' &0)
  | .invMulCancel => ∀' (((&0 : Language.group.Term _)⁻¹ * &0) =' 1)

/-- The ordinary group law expressed by each first-order group axiom. -/
def toProp (G : Type*) [Mul G] [Inv G] [One G] : GroupAxiom → Prop
  | .mulAssoc => ∀ x y z : G, (x * y) * z = x * (y * z)
  | .oneMul => ∀ x : G, 1 * x = x
  | .invMulCancel => ∀ x : G, x⁻¹ * x = 1

end GroupAxiom

end TauCeti

namespace FirstOrder.Language.Theory

/-- The first-order theory axiomatizing groups. -/
def group : Language.group.Theory :=
  Set.range TauCeti.GroupAxiom.toSentence

end FirstOrder.Language.Theory

namespace TauCeti

open FirstOrder FirstOrder.Language

namespace Group

open Language.Structure

section Axioms

/-- The multiplication extracted from a group-language structure. -/
@[instance_reducible] def mulOfStructure (G : Type*) [Language.group.Structure G] : Mul G :=
  ⟨fun x y => funMap mulFunc ![x, y]⟩

/-- The inversion extracted from a group-language structure. -/
@[instance_reducible] def invOfStructure (G : Type*) [Language.group.Structure G] : Inv G :=
  ⟨fun x => funMap invFunc ![x]⟩

/-- The identity extracted from a group-language structure. -/
@[instance_reducible] def oneOfStructure (G : Type*) [Language.group.Structure G] : One G :=
  ⟨funMap oneFunc ![]⟩

variable (G : Type*)

end Axioms
end Group

namespace Group

open Language.Structure

/-- The extracted identity is the interpretation of the identity symbol. -/
theorem oneOfStructure_one (G : Type*) [Language.group.Structure G] :
    letI : One G := oneOfStructure G
    (1 : G) = funMap oneFunc ![] := (rfl)

/-- The extracted inversion is the interpretation of the inverse symbol. -/
theorem invOfStructure_inv (G : Type*) [Language.group.Structure G] (x : G) :
    letI : Inv G := invOfStructure G
    x⁻¹ = funMap invFunc ![x] := (rfl)

/-- The extracted multiplication is the interpretation of the multiplication symbol. -/
theorem mulOfStructure_mul (G : Type*) [Language.group.Structure G] (x y : G) :
    letI : Mul G := mulOfStructure G
    x * y = funMap mulFunc ![x, y] := (rfl)

/-- Interpreting the operations extracted from a language structure recovers that structure. -/
theorem structureOfGroup_ofStructure (G : Type*) [Language.group.Structure G] :
    letI : One G := oneOfStructure G
    letI : Inv G := invOfStructure G
    letI : Mul G := mulOfStructure G
    structureOfGroup G = ‹Language.group.Structure G› := by
  apply Language.Structure.ext
  · funext n f xs
    cases f
    · rw [@funMap_one G (oneOfStructure G) (invOfStructure G) (mulOfStructure G),
        oneOfStructure_one G]
      congr 1
      exact Subsingleton.elim _ _
    · rw [@funMap_inv G (oneOfStructure G) (invOfStructure G) (mulOfStructure G),
        invOfStructure_inv G]
      congr 1
      funext i
      fin_cases i
      rfl
    · rw [@funMap_mul G (oneOfStructure G) (invOfStructure G) (mulOfStructure G),
        mulOfStructure_mul G]
      congr 1
      funext i
      fin_cases i <;> rfl
  · funext n r xs
    cases r

end Group

namespace GroupAxiom

attribute [local instance] Group.structureOfGroup

/-- A group axiom holds in the canonical interpretation exactly when its group law holds. -/
theorem realize_toSentence_iff_toProp [One G] [Inv G] [Mul G] (a : GroupAxiom) :
    (G ⊨ a.toSentence) ↔ a.toProp G := by
  cases a <;> simp [GroupAxiom.toSentence, GroupAxiom.toProp,
    Sentence.Realize, Formula.Realize, Fin.snoc]

end GroupAxiom

namespace Group

open Language.Structure

section Axioms

variable (G : Type*)

attribute [local instance] structureOfGroup

/-- Every group with its canonical language structure satisfies the group theory. -/
instance model_group [Group G] : G ⊨ Language.Theory.group := by
  rw [Language.Theory.model_iff]
  intro φ hφ
  obtain ⟨a, rfl⟩ := hφ
  rw [GroupAxiom.realize_toSentence_iff_toProp]
  cases a <;> simp [GroupAxiom.toProp, mul_assoc, one_mul, inv_mul_cancel]

end Axioms

section Models

variable (G : Type*) [Language.group.Structure G] [G ⊨ Language.Theory.group]

attribute [local instance] mulOfStructure invOfStructure oneOfStructure

end Models
end Group

namespace GroupAxiom

open _root_.TauCeti.Group Language.Structure

variable (G : Type*) [Language.group.Structure G] [G ⊨ Language.Theory.group]

/-- Each axiom of a group-language model holds for its extracted operations. -/
theorem toProp_of_model (a : GroupAxiom) :
    @GroupAxiom.toProp G (mulOfStructure G) (invOfStructure G) (oneOfStructure G) a := by
  have h : G ⊨ a.toSentence :=
    Language.Theory.realize_sentence_of_mem Language.Theory.group (Set.mem_range_self a)
  rw [← Group.structureOfGroup_ofStructure G] at h
  exact (@realize_toSentence_iff_toProp G (oneOfStructure G) (invOfStructure G)
    (mulOfStructure G) a).1 h

end GroupAxiom

namespace Group

open Language.Structure

section Models

variable (G : Type*) [Language.group.Structure G] [G ⊨ Language.Theory.group]

attribute [local instance] mulOfStructure invOfStructure oneOfStructure

/-- A model of the three group axioms carries the group structure given by its symbols. -/
@[instance_reducible] def groupOfModel : _root_.Group G :=
  _root_.Group.ofLeftAxioms
    (GroupAxiom.toProp_of_model G .mulAssoc)
    (GroupAxiom.toProp_of_model G .oneMul)
    (GroupAxiom.toProp_of_model G .invMulCancel)

omit [G ⊨ Language.Theory.group] in
/-- The extracted group's identity is the interpretation of its identity symbol. -/
theorem groupOfModel_one :
    letI : _root_.Group G := groupOfModel G
    (1 : G) = funMap oneFunc ![] :=
  oneOfStructure_one G

omit [G ⊨ Language.Theory.group] in
/-- Inversion in the group extracted from a model is the interpretation of its inverse symbol. -/
theorem groupOfModel_inv (x : G) :
    letI : _root_.Group G := groupOfModel G
    x⁻¹ = funMap invFunc ![x] :=
  invOfStructure_inv G x

omit [G ⊨ Language.Theory.group] in
/-- Multiplication in the group extracted from a model is its multiplication symbol. -/
theorem groupOfModel_mul (x y : G) :
    letI : _root_.Group G := groupOfModel G
    x * y = funMap mulFunc ![x, y] :=
  mulOfStructure_mul G x y

end Models

end Group
end TauCeti

namespace MonoidHom

open FirstOrder TauCeti TauCeti.Group

section Homomorphisms

variable {G H A : Type*} [Group G] [Group H]

attribute [local instance] TauCeti.Group.structureOfGroup

/-- A group homomorphism is a homomorphism of canonical group-language structures. -/
def groupLanguageHom (φ : G →* H) :
    Language.group.Hom G H where
  toFun := φ
  map_fun' := by
    intro n f xs
    cases f <;> simp
  map_rel' := by
    intro n r
    cases r

/-- A coefficient-preserving group homomorphism respects the language with named constants. -/
def coeffGroupLanguageHom (φ : G →* H) (c : A → G) (d : A → H)
    (hc : ∀ a, φ (c a) = d a) :
    @Language.Hom Language.group[[A]] G H
      (@Language.withConstantsStructure Language.group G (structureOfGroup G) A
        (Language.constantsOn.structure c))
      (@Language.withConstantsStructure Language.group H (structureOfGroup H) A
        (Language.constantsOn.structure d)) := by
  letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure d
  refine { toFun := φ, map_fun' := ?_, map_rel' := ?_ }
  · intro n f xs
    cases f with
    | inl f =>
      rw [Language.withConstants_funMap_sumInl, Language.withConstants_funMap_sumInl]
      exact (groupLanguageHom φ).map_fun f xs
    | inr f =>
      cases n with
      | zero =>
        -- At arity zero the constantsOn symbol type reduces to A.
        dsimp only [Language.constantsOn, Language.constantsOnFunc] at f
        simp only [Language.withConstants_funMap_sumInr]
        -- The coercion of a named constant uses the chosen coefficient map.
        change φ (c f) = d f
        exact hc f
      | succ n => exact isEmptyElim f
  · intro n r
    cases r with
    | inl r => cases r
    | inr r => cases r

/-- The canonical language homomorphism acts as the original group homomorphism. -/
@[simp] theorem groupLanguageHom_apply (φ : G →* H) (x : G) :
    groupLanguageHom φ x = φ x := by
  -- Unfold the bundled homomorphism to expose its underlying monoid homomorphism.
  change φ x = φ x
  rfl

/-- The coefficient language homomorphism acts as the original group homomorphism. -/
@[simp] theorem coeffGroupLanguageHom_apply (φ : G →* H) (c : A → G) (d : A → H)
    (hc : ∀ a, φ (c a) = d a) (x : G) :
    coeffGroupLanguageHom φ c d hc x = φ x := by
  -- Unfold the bundled homomorphism to expose its underlying monoid homomorphism.
  change φ x = φ x
  rfl

end Homomorphisms

end MonoidHom
