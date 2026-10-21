/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Reindex
public import TauCeti.ModelTheory.Infinitary.Operations
public import TauCeti.ModelTheory.Infinitary.Substitution
public import TauCeti.ModelTheory.Term.FreeVariables
public import Mathlib.Data.Set.Countable

/-!
# Free variables of infinitary formulas

`TauCeti.BoundedFormulaInf.freeVarSupport` records the free variables occurring syntactically
in an infinitary formula. Unlike first-order support, this is a set rather than a finite set:
a countable conjunction can use infinitely many free variables. Quantifiers bind the last
bound-variable slot and therefore do not change this support.

Realization depends only on the free valuation on this set. For a countable branching carrier
the support is countable, and for an embedded first-order formula it is exactly Mathlib's
`BoundedFormula.freeVarFinset`. Coded connectives collect the support of their original branches,
and carrier transport and bound-variable relabelling preserve support.
Substitution collects the supports of the replacement terms, while free-variable relabelling
keeps exactly the support images that remain free rather than becoming bound slots.

Use the support API with the `TauCeti.BoundedFormulaInf` qualification or after
`open TauCeti.BoundedFormulaInf`, including the finitary embedding laws
`freeVarSupport_toInf` and `finite_freeVarSupport_toInf`.
-/

public section

universe u v uι uκ uα w

namespace TauCeti

open FirstOrder.Language

variable {L : FirstOrder.Language.{u, v}} {ι : Type uι} {α : Type uα} {n : ℕ}

namespace BoundedFormulaInf

/-- The set of free variables occurring in an infinitary formula. This is syntactic support,
not the smallest set on which its truth value depends. -/
noncomputable def freeVarSupport : ∀ {n}, L.BoundedFormulaInf ι α n → Set α
  | _, .falsum => ∅
  | _, .equal t₁ t₂ => by classical exact ↑t₁.varFinsetLeft ∪ ↑t₂.varFinsetLeft
  | _, .rel _ ts => by classical exact ⋃ i, ↑(ts i).varFinsetLeft
  | _, .imp φ ψ => freeVarSupport φ ∪ freeVarSupport ψ
  | _, .all φ => freeVarSupport φ
  | _, .iSup φs => ⋃ i, freeVarSupport (φs i)
  | _, .iInf φs => ⋃ i, freeVarSupport (φs i)

@[simp]
theorem freeVarSupport_falsum :
    freeVarSupport (.falsum : L.BoundedFormulaInf ι α n) = ∅ := (rfl)

@[simp]
theorem freeVarSupport_equal [DecidableEq α] (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    freeVarSupport (.equal t₁ t₂ : L.BoundedFormulaInf ι α n) =
      ↑t₁.varFinsetLeft ∪ ↑t₂.varFinsetLeft := by
  -- Reconcile the definition's classical instance with the caller's decidable equality.
  simp only [freeVarSupport]
  congr!

@[simp]
theorem freeVarSupport_rel [DecidableEq α] {k : ℕ} (R : L.Relations k)
    (ts : Fin k → L.Term (α ⊕ Fin n)) :
    freeVarSupport (.rel R ts : L.BoundedFormulaInf ι α n) = ⋃ i, ↑(ts i).varFinsetLeft := by
  -- Reconcile the definition's classical instance with the caller's decidable equality.
  simp only [freeVarSupport]
  congr!

@[simp]
theorem freeVarSupport_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    freeVarSupport (φ.imp ψ) = freeVarSupport φ ∪ freeVarSupport ψ := (rfl)

@[simp]
theorem freeVarSupport_all (φ : L.BoundedFormulaInf ι α (n + 1)) :
    freeVarSupport φ.all = freeVarSupport φ := (rfl)

@[simp]
theorem freeVarSupport_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    freeVarSupport (.iSup φs) = ⋃ i, freeVarSupport (φs i) := (rfl)

@[simp]
theorem freeVarSupport_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    freeVarSupport (.iInf φs) = ⋃ i, freeVarSupport (φs i) := (rfl)

@[simp]
theorem freeVarSupport_not (φ : L.BoundedFormulaInf ι α n) :
    freeVarSupport φ.not = freeVarSupport φ := by
  simp [FirstOrder.Language.BoundedFormulaInf.not]

@[simp]
theorem freeVarSupport_bot :
    freeVarSupport (⊥ : L.BoundedFormulaInf ι α n) = ∅ := by
  rw [FirstOrder.Language.BoundedFormulaInf.bot_def, freeVarSupport_falsum]

@[simp]
theorem freeVarSupport_top :
    freeVarSupport (⊤ : L.BoundedFormulaInf ι α n) = ∅ := by
  rw [FirstOrder.Language.BoundedFormulaInf.top_def, freeVarSupport_not, freeVarSupport_falsum]

@[simp]
theorem freeVarSupport_inf (φ ψ : L.BoundedFormulaInf ι α n) :
    freeVarSupport (φ ⊓ ψ) = freeVarSupport φ ∪ freeVarSupport ψ := by
  simp [FirstOrder.Language.BoundedFormulaInf.inf_def]

@[simp]
theorem freeVarSupport_sup (φ ψ : L.BoundedFormulaInf ι α n) :
    freeVarSupport (φ ⊔ ψ) = freeVarSupport φ ∪ freeVarSupport ψ := by
  simp [FirstOrder.Language.BoundedFormulaInf.sup_def]

@[simp]
theorem freeVarSupport_iff (φ ψ : L.BoundedFormulaInf ι α n) :
    freeVarSupport (φ.iff ψ) = freeVarSupport φ ∪ freeVarSupport ψ := by
  simp [FirstOrder.Language.BoundedFormulaInf.iff_def, Set.union_comm]

@[simp]
theorem freeVarSupport_ex (φ : L.BoundedFormulaInf ι α (n + 1)) :
    freeVarSupport φ.ex = freeVarSupport φ := by
  simp [FirstOrder.Language.BoundedFormulaInf.ex]

@[simp]
theorem freeVarSupport_alls (φ : L.BoundedFormulaInf ι α n) :
    freeVarSupport φ.alls = freeVarSupport φ := by
  induction n with
  | zero => rw [FirstOrder.Language.BoundedFormulaInf.alls_zero]
  | succ n ih => rw [FirstOrder.Language.BoundedFormulaInf.alls_succ, ih, freeVarSupport_all]

@[simp]
theorem freeVarSupport_exs (φ : L.BoundedFormulaInf ι α n) :
    freeVarSupport φ.exs = freeVarSupport φ := by
  induction n with
  | zero => rw [FirstOrder.Language.BoundedFormulaInf.exs_zero]
  | succ n ih => rw [FirstOrder.Language.BoundedFormulaInf.exs_succ, ih, freeVarSupport_ex]

/-- Relabelling bound-variable slots preserves syntactic free-variable support. -/
@[simp]
theorem freeVarSupport_mapBound {m : ℕ} (f : Fin m → Fin n)
    (φ : L.BoundedFormulaInf ι α m) : freeVarSupport (φ.mapBound f) = freeVarSupport φ := by
  classical
  induction φ generalizing n with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Weakening the bound-variable context preserves syntactic free-variable support. -/
@[simp]
theorem freeVarSupport_castLE {m : ℕ} (h : m ≤ n) (φ : L.BoundedFormulaInf ι α m) :
    freeVarSupport (φ.castLE h) = freeVarSupport φ := by
  rw [FirstOrder.Language.BoundedFormulaInf.castLE_def, freeVarSupport_mapBound]

/-- Substitution collects the variables of the substituted terms over the original support. -/
@[simp]
theorem freeVarSupport_subst {β : Type*} [DecidableEq β]
    (φ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    freeVarSupport (subst φ f) = ⋃ a ∈ freeVarSupport φ, ↑(f a).varFinset := by
  classical
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [subst_equal, freeVarSupport_equal, varFinsetLeft_subst_sumElim, Set.biUnion_union]
  | rel R ts =>
    simp only [subst_rel, freeVarSupport_rel, varFinsetLeft_subst_sumElim, Set.biUnion_iUnion]
  | imp φ ψ ihφ ihψ =>
    simp only [subst_imp, freeVarSupport_imp, ihφ, ihψ, Set.biUnion_union]
  | all φ ih => simp [ih]
  | iSup φs ih => simp only [subst_iSup, freeVarSupport_iSup, ih, Set.biUnion_iUnion]
  | iInf φs ih => simp only [subst_iInf, freeVarSupport_iInf, ih, Set.biUnion_iUnion]

/-- Relabelling retains exactly the support images that remain free variables. -/
@[simp]
theorem freeVarSupport_relabel {β : Type*} {m : ℕ} (g : α → β ⊕ Fin m)
    (φ : L.BoundedFormulaInf ι α n) :
    freeVarSupport (relabel g φ) = Sum.inl ⁻¹' (g '' freeVarSupport φ) := by
  classical
  have haux (k : ℕ) : BoundedFormula.relabelAux g k =
      Sum.elim (Sum.map id (Fin.castAdd k) ∘ g) (Sum.inr ∘ Fin.natAdd m) := by
    funext a
    cases a with
    | inl a => cases h : g a <;> simp [BoundedFormula.relabelAux, h]
    | inr b => simp [BoundedFormula.relabelAux]
  have hterm {k : ℕ} (t : L.Term (α ⊕ Fin k)) :
      (↑(t.relabel (BoundedFormula.relabelAux g k)).varFinsetLeft : Set β) =
        Sum.inl ⁻¹' (g '' (t.varFinsetLeft : Set α)) := by
    rw [haux, varFinsetLeft_relabel_sumElim]
    ext b
    simp only [Set.mem_preimage, Set.mem_image, Function.comp_apply]
    exact exists_congr fun a => by cases g a <;> simp
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [hterm, Set.image_union, Set.preimage_union]
  | rel R ts => simp [hterm, Set.image_iUnion, Set.preimage_iUnion]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ, Set.image_union, Set.preimage_union]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih, Set.image_iUnion, Set.preimage_iUnion]
  | iInf φs ih => simp [ih, Set.image_iUnion, Set.preimage_iUnion]

private theorem mem_freeVarSupport_pad {κ : Type uκ} (c : IndexCoding ι κ)
    (d : L.BoundedFormulaInf κ α n) (φs : ι → L.BoundedFormulaInf κ α n) (k : κ) (a : α) :
    a ∈ freeVarSupport (c.pad d φs k) ↔
      c.pad (a ∈ freeVarSupport d) (fun i => a ∈ freeVarSupport (φs i)) k :=
  Iff.of_eq (congrFun (c.comp_pad (fun φ : L.BoundedFormulaInf κ α n =>
    a ∈ freeVarSupport φ) d φs) k)

/-- A coded conjunction has exactly the free variables of its original branches. -/
@[simp]
theorem freeVarSupport_iInfAlong {κ : Type uκ} (c : IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    freeVarSupport (FirstOrder.Language.BoundedFormulaInf.iInfAlong c φs) =
      ⋃ i, freeVarSupport (φs i) := by
  ext a
  simp only [FirstOrder.Language.BoundedFormulaInf.iInfAlong_def, freeVarSupport_iInf,
    Set.mem_iUnion, mem_freeVarSupport_pad, freeVarSupport_top, Set.mem_empty_iff_false]
  exact c.exists_pad_false_iff _

/-- A coded disjunction has exactly the free variables of its original branches. -/
@[simp]
theorem freeVarSupport_iSupAlong {κ : Type uκ} (c : IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    freeVarSupport (FirstOrder.Language.BoundedFormulaInf.iSupAlong c φs) =
      ⋃ i, freeVarSupport (φs i) := by
  ext a
  simp only [FirstOrder.Language.BoundedFormulaInf.iSupAlong_def, freeVarSupport_iSup,
    Set.mem_iUnion, mem_freeVarSupport_pad, freeVarSupport_bot, Set.mem_empty_iff_false]
  exact c.exists_pad_false_iff _

/-- Transport along any carrier coding preserves syntactic free-variable support. -/
@[simp]
theorem freeVarSupport_reindex {κ : Type uκ} (c : IndexCoding ι κ)
    (φ : L.BoundedFormulaInf ι α n) : freeVarSupport (φ.reindex c) = freeVarSupport φ := by
  classical
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Recoding into `L_{ω₁ω}` preserves syntactic free-variable support. -/
@[simp]
theorem freeVarSupport_toOmega [Encodable ι] (φ : L.BoundedFormulaInf ι α n) :
    freeVarSupport (FirstOrder.Language.BoundedFormulaInf.toOmega φ) = freeVarSupport φ := by
  rw [FirstOrder.Language.BoundedFormulaInf.toOmega_def, freeVarSupport_reindex]

/-- Changing the free valuation away from syntactic support does not affect realization.
The bound-variable valuation is arbitrary and is held fixed. -/
theorem realize_congr_freeVarSupport {M : Type w} [L.Structure M]
    (φ : L.BoundedFormulaInf ι α n) {v₁ v₂ : α → M} (xs : Fin n → M)
    (h : Set.EqOn v₁ v₂ (freeVarSupport φ)) : φ.Realize v₁ xs ↔ φ.Realize v₂ xs := by
  classical
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [freeVarSupport_equal] at h
    simp only [FirstOrder.Language.BoundedFormulaInf.realize_equal,
      realize_congr_varFinsetLeft t₁ xs (h.mono Set.subset_union_left),
      realize_congr_varFinsetLeft t₂ xs (h.mono Set.subset_union_right)]
  | rel R ts =>
    rw [freeVarSupport_rel] at h
    simp only [FirstOrder.Language.BoundedFormulaInf.realize_rel]
    have ht (i) := realize_congr_varFinsetLeft (ts i) xs
      (h.mono (Set.subset_iUnion (fun i => ((ts i).varFinsetLeft : Set α)) i))
    simp only [ht]
  | imp φ ψ ihφ ihψ =>
    simp only [FirstOrder.Language.BoundedFormulaInf.realize_imp]
    exact imp_congr (ihφ xs (h.mono Set.subset_union_left))
      (ihψ xs (h.mono Set.subset_union_right))
  | all φ ih =>
    simp only [FirstOrder.Language.BoundedFormulaInf.realize_all]
    exact forall_congr' fun y => ih (Fin.snoc xs y) h
  | iSup φs ih =>
    rw [freeVarSupport_iSup] at h
    simp only [FirstOrder.Language.BoundedFormulaInf.realize_iSup]
    exact exists_congr fun i => ih i xs
      (h.mono (Set.subset_iUnion (fun i => freeVarSupport (φs i)) i))
  | iInf φs ih =>
    rw [freeVarSupport_iInf] at h
    simp only [FirstOrder.Language.BoundedFormulaInf.realize_iInf]
    exact forall_congr' fun i => ih i xs
      (h.mono (Set.subset_iUnion (fun i => freeVarSupport (φs i)) i))

/-- Formulas with a countable branching carrier have countable free-variable support,
without any restriction on the language or the ambient free-variable type. -/
theorem countable_freeVarSupport [Countable ι] (φ : L.BoundedFormulaInf ι α n) :
    (freeVarSupport φ).Countable := by
  classical
  induction φ with
  | falsum => exact Set.countable_empty
  | equal t₁ t₂ => exact t₁.varFinsetLeft.countable_toSet.union t₂.varFinsetLeft.countable_toSet
  | rel R ts => exact Set.countable_iUnion fun i => (ts i).varFinsetLeft.countable_toSet
  | imp φ ψ ihφ ihψ => exact ihφ.union ihψ
  | all φ ih => exact ih
  | iSup φs ih => exact Set.countable_iUnion ih
  | iInf φs ih => exact Set.countable_iUnion ih

/-- The finitary embedding preserves the set of free variables, independently of its
branching carrier. -/
@[simp]
theorem freeVarSupport_toInf [DecidableEq α] (φ : L.BoundedFormula α n) :
    freeVarSupport (φ.toInf (ι := ι)) = ↑φ.freeVarFinset := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp [Finset.coe_biUnion]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

/-- An embedded first-order formula has finite free-variable support even at an
uncountable branching carrier. -/
theorem finite_freeVarSupport_toInf (φ : L.BoundedFormula α n) :
    (freeVarSupport (φ.toInf (ι := ι))).Finite := by
  classical
  rw [freeVarSupport_toInf]
  exact φ.freeVarFinset.finite_toSet

end BoundedFormulaInf

end TauCeti
