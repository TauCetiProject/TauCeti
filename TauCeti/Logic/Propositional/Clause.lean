/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Union
public import Std.Sat.CNF.Literal

/-!
# Clauses, models and entailment

This file sets up the semantics of clausal propositional logic over an arbitrary type `V` of
variables. A literal is an element of Lean core's `Std.Sat.Literal V`, the product `V × Bool`, in
which `(v, true)` is the positive and `(v, false)` the negative literal of `v`; its negation is
`Std.Sat.Literal.negate`. A clause is a finite set of literals and a formula in conjunctive normal
form is a finite set of clauses, while a clause set is an arbitrary, possibly infinite, set of
clauses. An assignment `τ : V → Bool` makes the literal `l` true when `τ l.1 = l.2`.

These are the objects on which restriction, compactness, the translation of formulas into clause
sets, resolution and unit propagation are stated. No hypothesis is placed on `V` for the semantic
notions; decidable equality is assumed only where clauses are built (`Clause.vars`, `CNF.vars`,
`Clause.relabel`).

Lean core's `Std.Sat.CNF`, with its `Std.Sat.CNF.Sat` and `Std.Sat.CNF.Entails`, stores a clause
as an array of literals and a formula as an array of clauses, so that order and multiplicity are
data and infinite clause sets cannot be expressed; only its literal type is reused here.

## Main definitions

* `TauCeti.Propositional.Clause V`, `TauCeti.Propositional.CNF V`: clauses and formulas in
  conjunctive normal form.
* `TauCeti.Propositional.Satisfies τ C`: some literal of `C` is true under `τ`.
* `TauCeti.Propositional.Models τ S`: `τ` satisfies every clause of the clause set `S`.
* `TauCeti.Propositional.Satisfiable S`: `S` has a model.
* `TauCeti.Propositional.Entails S C`: every model of `S` satisfies `C`.
* `TauCeti.Propositional.Clause.IsTautology C`: `C` contains a literal and its negation.
* `TauCeti.Propositional.Clause.vars`, `TauCeti.Propositional.CNF.vars`: the variables occurring
  in a clause and in a formula.
* `TauCeti.Propositional.Clause.relabel f C`: the clause obtained by renaming the variables of `C`
  along `f`.

## Main results

* `TauCeti.Propositional.not_satisfies_empty`, `TauCeti.Propositional.models_empty`,
  `TauCeti.Propositional.not_satisfiable_of_empty_mem`: the empty clause is satisfied by no
  assignment, the empty clause set by every assignment, and a clause set containing the empty
  clause is unsatisfiable.
* `TauCeti.Propositional.Clause.isTautology_iff_forall_satisfies`: a clause is tautological
  exactly when every assignment satisfies it.
* `TauCeti.Propositional.satisfies_congr`, `TauCeti.Propositional.models_congr`: satisfaction of a
  clause and of a formula depends only on the values of the assignment at their variables.
* `TauCeti.Propositional.Models.mono`, `TauCeti.Propositional.Satisfiable.mono`,
  `TauCeti.Propositional.Entails.mono_left`: models and satisfiability are antitone and
  entailment is monotone in the clause set.
* `TauCeti.Propositional.entails_of_mem_of_subset`, `TauCeti.Propositional.Entails.trans`: a clause
  with a subset in `S` is entailed by `S`, and entailment is transitive.
* `TauCeti.Propositional.entails_iff_not_satisfiable_union`: `S` entails `C` exactly when `S`
  together with the unit clauses of the negations of the literals of `C` is unsatisfiable;
  `TauCeti.Propositional.not_satisfiable_iff_entails_empty` is the case `C = ∅`.
* `TauCeti.Propositional.models_image_relabel`: `τ` is a model of the relabelled clause set
  exactly when `τ ∘ f` is a model of the original one.
-/

public section

open Std.Sat (Literal)

namespace Std.Sat.Literal

variable {V : Type*}

@[simp]
theorem negate_fst (l : Literal V) : l.negate.1 = l.1 := rfl

@[simp]
theorem negate_snd (l : Literal V) : l.negate.2 = !l.2 := rfl

@[simp]
theorem negate_mk (v : V) (b : Bool) : Literal.negate (v, b) = (v, !b) := rfl

@[simp]
theorem negate_negate (l : Literal V) : l.negate.negate = l := by
  simp [negate]

end Std.Sat.Literal

namespace TauCeti.Propositional

/-- A **clause** over the variables `V` is a finite set of literals. -/
abbrev Clause (V : Type*) : Type _ := Finset (Literal V)

/-- A **formula in conjunctive normal form** over the variables `V` is a finite set of clauses.
It is used as a clause set through the coercion of `Finset` to `Set`. -/
abbrev CNF (V : Type*) : Type _ := Finset (Clause V)

variable {V W : Type*}

/-- The assignment `τ` **satisfies** the clause `C` when some literal `l` of `C` is true under
`τ`, that is `τ l.1 = l.2`. -/
def Satisfies (τ : V → Bool) (C : Clause V) : Prop := ∃ l ∈ C, τ l.1 = l.2

/-- The assignment `τ` is a **model** of the clause set `S` when it satisfies every clause of
`S`. -/
def Models (τ : V → Bool) (S : Set (Clause V)) : Prop := ∀ C ∈ S, Satisfies τ C

/-- A clause set is **satisfiable** when it has a model. -/
def Satisfiable (S : Set (Clause V)) : Prop := ∃ τ, Models τ S

/-- The clause set `S` **entails** the clause `C` when every model of `S` satisfies `C`. -/
def Entails (S : Set (Clause V)) (C : Clause V) : Prop := ∀ τ, Models τ S → Satisfies τ C

/-- A clause is **tautological** when it contains a literal together with its negation. -/
def Clause.IsTautology (C : Clause V) : Prop := ∃ l ∈ C, l.negate ∈ C

/-- The **variables** of a clause: the variables of its literals. -/
def Clause.vars [DecidableEq V] (C : Clause V) : Finset V := C.image Prod.fst

/-- The **variables** of a formula in conjunctive normal form: the union of the variables of its
clauses. -/
def CNF.vars [DecidableEq V] (F : CNF V) : Finset V := F.biUnion Clause.vars

/-- The **relabelling** of a clause along `f : V → W`: each literal `(v, b)` becomes
`(f v, b)`. -/
def Clause.relabel [DecidableEq W] (f : V → W) (C : Clause V) : Clause W :=
  C.image (Prod.map f id)

variable {τ τ' : V → Bool} {S T : Set (Clause V)} {C D : Clause V} {l : Literal V}

/-! ### Satisfaction of a clause -/

theorem satisfies_iff : Satisfies τ C ↔ ∃ l ∈ C, τ l.1 = l.2 := Iff.rfl

instance : Decidable (Satisfies τ C) :=
  inferInstanceAs (Decidable (∃ l ∈ C, τ l.1 = l.2))

theorem satisfies_of_mem (hl : l ∈ C) (h : τ l.1 = l.2) : Satisfies τ C := ⟨l, hl, h⟩

/-- The empty clause is satisfied by no assignment. -/
@[simp]
theorem not_satisfies_empty : ¬Satisfies τ ∅ := by
  simp [satisfies_iff]

@[simp]
theorem satisfies_singleton : Satisfies τ {l} ↔ τ l.1 = l.2 := by
  simp [satisfies_iff]

@[simp]
theorem satisfies_insert [DecidableEq V] :
    Satisfies τ (insert l C) ↔ τ l.1 = l.2 ∨ Satisfies τ C := by
  simp [satisfies_iff]

@[simp]
theorem satisfies_union [DecidableEq V] :
    Satisfies τ (C ∪ D) ↔ Satisfies τ C ∨ Satisfies τ D := by
  simp only [satisfies_iff, Finset.mem_union, or_and_right, exists_or]

/-- Satisfaction is monotone in the clause: a clause containing a satisfied clause is
satisfied. -/
theorem Satisfies.mono (h : Satisfies τ C) (hCD : C ⊆ D) : Satisfies τ D :=
  let ⟨l, hl, hτ⟩ := h
  ⟨l, hCD hl, hτ⟩

/-! ### Tautologies -/

namespace Clause

theorem isTautology_iff : C.IsTautology ↔ ∃ l ∈ C, l.negate ∈ C := Iff.rfl

instance [DecidableEq V] : DecidablePred (IsTautology (V := V)) := fun C ↦
  inferInstanceAs (Decidable (∃ l ∈ C, l.negate ∈ C))

@[simp]
theorem not_isTautology_empty : ¬(∅ : Clause V).IsTautology := by
  simp [isTautology_iff]

theorem IsTautology.mono (h : C.IsTautology) (hCD : C ⊆ D) : D.IsTautology :=
  let ⟨l, hl, hn⟩ := h
  ⟨l, hCD hl, hCD hn⟩

/-- A tautological clause is satisfied by every assignment. -/
theorem IsTautology.satisfies (h : C.IsTautology) (τ : V → Bool) : Satisfies τ C := by
  obtain ⟨l, hl, hn⟩ := h
  by_cases hτ : τ l.1 = l.2
  · exact satisfies_of_mem hl hτ
  · exact satisfies_of_mem hn (Bool.eq_not_of_ne hτ)

/-- A clause is tautological exactly when every assignment satisfies it. -/
theorem isTautology_iff_forall_satisfies : C.IsTautology ↔ ∀ τ : V → Bool, Satisfies τ C := by
  classical
  refine ⟨fun h τ ↦ h.satisfies τ, fun h ↦ ?_⟩
  -- If `C` is not tautological, `v ↦ decide ((v, false) ∈ C)` makes every literal of `C` false.
  obtain ⟨⟨v, b⟩, hl, hτ⟩ := h fun v ↦ decide ((v, false) ∈ C)
  refine ⟨(v, b), hl, ?_⟩
  cases b <;> simp_all

end Clause

/-! ### Variables -/

namespace Clause

variable [DecidableEq V]

@[simp]
theorem mem_vars {v : V} : v ∈ C.vars ↔ ∃ b, (v, b) ∈ C := by
  simp [vars]

theorem mem_vars_of_mem (hl : l ∈ C) : l.1 ∈ C.vars :=
  mem_vars.2 ⟨l.2, hl⟩

@[simp]
theorem vars_empty : (∅ : Clause V).vars = ∅ := by
  simp [vars]

@[simp]
theorem vars_singleton : ({l} : Clause V).vars = {l.1} := by
  simp [vars]

@[simp]
theorem vars_insert : (insert l C).vars = insert l.1 C.vars := by
  simp [vars]

@[simp]
theorem vars_union : (C ∪ D).vars = C.vars ∪ D.vars := by
  simp [vars, Finset.image_union]

theorem vars_mono (h : C ⊆ D) : C.vars ⊆ D.vars :=
  Finset.image_subset_image h

end Clause

namespace CNF

variable [DecidableEq V] {F G : CNF V} {v : V}

@[simp]
theorem mem_vars : v ∈ F.vars ↔ ∃ C ∈ F, v ∈ C.vars := by
  simp [vars]

@[simp]
theorem vars_empty : (∅ : CNF V).vars = ∅ := by
  simp [vars]

@[simp]
theorem vars_singleton : ({C} : CNF V).vars = C.vars := by
  simp [vars]

@[simp]
theorem vars_insert : (insert C F).vars = C.vars ∪ F.vars := by
  simp [vars, Finset.biUnion_insert]

@[simp]
theorem vars_union : (F ∪ G).vars = F.vars ∪ G.vars := by
  simp [vars, Finset.union_biUnion]

theorem vars_mono (h : F ⊆ G) : F.vars ⊆ G.vars :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- The variables of a clause of a formula are variables of the formula. -/
theorem subset_vars_of_mem (h : C ∈ F) : C.vars ⊆ F.vars :=
  Finset.subset_biUnion_of_mem _ h

end CNF

/-- Satisfaction of a clause depends only on the values of the assignment at the variables of the
clause. -/
theorem satisfies_congr [DecidableEq V] (h : ∀ v ∈ C.vars, τ v = τ' v) :
    Satisfies τ C ↔ Satisfies τ' C :=
  exists_congr fun l ↦ and_congr_right fun hl ↦ by rw [h l.1 (Clause.mem_vars_of_mem hl)]

/-! ### Models -/

theorem models_iff : Models τ S ↔ ∀ C ∈ S, Satisfies τ C := Iff.rfl

theorem Models.satisfies (h : Models τ S) (hC : C ∈ S) : Satisfies τ C := h C hC

/-- The empty clause set is modelled by every assignment. -/
@[simp]
theorem models_empty : Models τ (∅ : Set (Clause V)) := by
  simp [models_iff]

@[simp]
theorem models_singleton : Models τ {C} ↔ Satisfies τ C := by
  simp [models_iff]

@[simp]
theorem models_insert : Models τ (insert C S) ↔ Satisfies τ C ∧ Models τ S := by
  simp [models_iff]

@[simp]
theorem models_union : Models τ (S ∪ T) ↔ Models τ S ∧ Models τ T := by
  simp only [models_iff, Set.mem_union, or_imp, forall_and]

/-- Being a model is antitone in the clause set. -/
theorem Models.mono (h : Models τ T) (hST : S ⊆ T) : Models τ S :=
  fun _ hC ↦ h _ (hST hC)

/-- Whether an assignment is a model of a formula depends only on its values at the variables of
the formula. -/
theorem models_congr [DecidableEq V] {F : CNF V} (h : ∀ v ∈ F.vars, τ v = τ' v) :
    Models τ (F : Set (Clause V)) ↔ Models τ' (F : Set (Clause V)) :=
  forall₂_congr fun _ hC ↦ satisfies_congr fun v hv ↦
    h v (CNF.subset_vars_of_mem (Finset.mem_coe.1 hC) hv)

/-! ### Satisfiability -/

theorem satisfiable_iff : Satisfiable S ↔ ∃ τ, Models τ S := Iff.rfl

theorem Models.satisfiable (h : Models τ S) : Satisfiable S := ⟨τ, h⟩

/-- The empty clause set is satisfiable. -/
@[simp]
theorem satisfiable_empty : Satisfiable (∅ : Set (Clause V)) :=
  ⟨fun _ ↦ true, models_empty⟩

/-- Satisfiability is antitone in the clause set. -/
theorem Satisfiable.mono (h : Satisfiable T) (hST : S ⊆ T) : Satisfiable S :=
  let ⟨τ, hτ⟩ := h
  ⟨τ, hτ.mono hST⟩

/-- A clause set containing the empty clause is unsatisfiable. -/
theorem not_satisfiable_of_empty_mem (h : ∅ ∈ S) : ¬Satisfiable S :=
  fun ⟨_, hτ⟩ ↦ not_satisfies_empty (hτ.satisfies h)

/-! ### Entailment -/

theorem entails_iff : Entails S C ↔ ∀ τ, Models τ S → Satisfies τ C := Iff.rfl

theorem Entails.satisfies (h : Entails S C) (hτ : Models τ S) : Satisfies τ C := h τ hτ

/-- Every clause of a clause set is entailed by it. -/
theorem entails_of_mem (h : C ∈ S) : Entails S C := fun _ hτ ↦ hτ.satisfies h

/-- Entailment is monotone in the clause set. -/
theorem Entails.mono_left (h : Entails S C) (hST : S ⊆ T) : Entails T C :=
  fun τ hτ ↦ h τ (hτ.mono hST)

/-- An entailed clause stays entailed when literals are added to it. -/
theorem Entails.mono_right (h : Entails S C) (hCD : C ⊆ D) : Entails S D :=
  fun τ hτ ↦ (h τ hτ).mono hCD

/-- A clause with a subset in `S` is entailed by `S`. -/
theorem entails_of_mem_of_subset (hD : D ∈ S) (hDC : D ⊆ C) : Entails S C :=
  (entails_of_mem hD).mono_right hDC

/-- A tautological clause is entailed by every clause set. -/
theorem Clause.IsTautology.entails (h : C.IsTautology) : Entails S C :=
  fun τ _ ↦ h.satisfies τ

/-- A model of `S` is a model of every clause set all of whose clauses `S` entails. -/
theorem Models.of_forall_entails (hτ : Models τ S) (h : ∀ D ∈ T, Entails S D) : Models τ T :=
  fun D hD ↦ h D hD τ hτ

/-- Entailment is transitive: if `S` entails every clause of `T` and `T` entails `C`, then `S`
entails `C`. -/
theorem Entails.trans (hC : Entails T C) (h : ∀ D ∈ T, Entails S D) : Entails S C :=
  fun τ hτ ↦ hC τ (hτ.of_forall_entails h)

/-- An assignment is a model of the unit clauses `{¬l}`, `l ∈ C`, exactly when it does not
satisfy `C`. -/
theorem models_image_singleton_negate_iff :
    Models τ ((fun l ↦ ({l.negate} : Clause V)) '' (C : Set (Literal V))) ↔ ¬Satisfies τ C := by
  simp only [models_iff, Set.forall_mem_image, satisfies_singleton, Finset.mem_coe,
    Literal.negate_fst, Literal.negate_snd]
  rw [satisfies_iff]
  push Not
  exact forall₂_congr fun _ _ ↦ Bool.eq_not

/-- Entailment as refutation: `S` entails `C` exactly when `S` together with the unit clauses
`{¬l}`, `l ∈ C`, is unsatisfiable. -/
theorem entails_iff_not_satisfiable_union :
    Entails S C ↔
      ¬Satisfiable (S ∪ (fun l ↦ ({l.negate} : Clause V)) '' (C : Set (Literal V))) := by
  simp [entails_iff, satisfiable_iff, models_image_singleton_negate_iff]

/-- A clause set is unsatisfiable exactly when it entails the empty clause. -/
theorem not_satisfiable_iff_entails_empty : ¬Satisfiable S ↔ Entails S ∅ := by
  simp [entails_iff, satisfiable_iff]

/-! ### Relabelling -/

namespace Clause

variable [DecidableEq W] {f : V → W}

@[simp]
theorem mem_relabel {l : Literal W} : l ∈ C.relabel f ↔ ∃ v, (v, l.2) ∈ C ∧ f v = l.1 := by
  obtain ⟨w, b⟩ := l
  simp [relabel]

@[simp]
theorem relabel_empty : (∅ : Clause V).relabel f = ∅ := by
  simp [relabel]

@[simp]
theorem relabel_singleton : ({l} : Clause V).relabel f = {(f l.1, l.2)} :=
  Finset.image_singleton _ _

@[simp]
theorem relabel_insert [DecidableEq V] :
    (insert l C).relabel f = insert (f l.1, l.2) (C.relabel f) :=
  Finset.image_insert _ _ _

@[simp]
theorem relabel_union [DecidableEq V] : (C ∪ D).relabel f = C.relabel f ∪ D.relabel f := by
  simp [relabel, Finset.image_union]

@[simp]
theorem relabel_id [DecidableEq V] : C.relabel id = C := by
  simp [relabel]

@[simp]
theorem relabel_relabel {X : Type*} [DecidableEq X] {g : W → X} :
    (C.relabel f).relabel g = C.relabel (g ∘ f) := by
  simp [relabel, Finset.image_image, Prod.map_comp_map]

theorem vars_relabel [DecidableEq V] : (C.relabel f).vars = C.vars.image f := by
  ext w
  simp only [mem_vars, mem_relabel, Finset.mem_image]
  grind

end Clause

/-- The relabelled clause `C.relabel f` is satisfied by `τ` exactly when `C` is satisfied by
`τ ∘ f`. -/
@[simp]
theorem satisfies_relabel [DecidableEq W] {f : V → W} {τ : W → Bool} :
    Satisfies τ (C.relabel f) ↔ Satisfies (τ ∘ f) C := by
  simp only [satisfies_iff, Clause.relabel, Finset.mem_image, exists_exists_and_eq_and,
    Prod.map_fst, Prod.map_snd, id_eq, Function.comp_apply]

/-- Relabelling: the image of `S` under the relabelling along `f` has `τ` as a model exactly when
`S` has `τ ∘ f` as a model. -/
@[simp]
theorem models_image_relabel [DecidableEq W] {f : V → W} {τ : W → Bool} :
    Models τ (Clause.relabel f '' S) ↔ Models (τ ∘ f) S := by
  simp [models_iff]

end TauCeti.Propositional
