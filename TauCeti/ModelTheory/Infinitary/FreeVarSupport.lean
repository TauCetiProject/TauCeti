/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Operations
public import TauCeti.ModelTheory.Infinitary.Reindex
public import TauCeti.ModelTheory.Infinitary.Substitution
public import TauCeti.ModelTheory.Semantics
public import TauCeti.ModelTheory.Syntax

/-!
# The free-variable support of an infinitary formula

The free-variable support `φ.freeVarSupport` of an infinitary formula `φ` is the set of free
variables occurring in one of its atoms. It is a set rather than a `Finset`: an infinitary
conjunction or disjunction may mention infinitely many free variables, one in each branch.
For a finitary formula it is the coercion of Mathlib's `BoundedFormula.freeVarFinset`, and over a
countable carrier, in particular in `L_{ω₁ω}`, it is countable.

The main result `realize_congr_freeVarSupport` says that the realization of a formula depends
only on the values of the free-variable valuation on the support. This is the infinitary
analogue of the finitary fact that a formula only sees the variables it mentions.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.freeVarSupport`: the set of free variables of an
  infinitary formula.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.realize_congr_freeVarSupport`: valuations of the free
  variables that agree on the support give the same realization.
* `FirstOrder.Language.BoundedFormula.freeVarSupport_toInf`: on finitary formulas the support is
  `BoundedFormula.freeVarFinset`.
* `FirstOrder.Language.BoundedFormulaInf.countable_freeVarSupport`: over a countable carrier the
  support is countable.
* `FirstOrder.Language.BoundedFormulaInf.freeVarSupport_mapBound`,
  `FirstOrder.Language.BoundedFormulaInf.freeVarSupport_castLE` and
  `FirstOrder.Language.BoundedFormulaInf.freeVarSupport_reindex`: relabelling bound slots,
  weakening and carrier transport keep the support.
* `TauCeti.BoundedFormulaInf.freeVarSupport_subst` and
  `TauCeti.BoundedFormulaInf.freeVarSupport_relabel`: the support after substitution and
  free-variable relabelling.

## References

* The definition and the congruence law follow Mathlib's finitary
  `FirstOrder.Language.BoundedFormula.freeVarFinset` and its realization lemma
  `BoundedFormula.realize_restrictFreeVar` in `Mathlib/ModelTheory/Syntax.lean` and
  `Mathlib/ModelTheory/Semantics.lean`.
-/

public section

universe u v u' uι uκ uβ w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'}

namespace BoundedFormulaInf

variable {ι : Type uι} {n : ℕ}

open scoped Classical in
/-- The **free-variable support** of an infinitary formula: the set of free variables that occur
in one of its atoms. Infinitary connectives take the union over all their branches, so the support
may be infinite. -/
noncomputable def freeVarSupport : ∀ {n}, L.BoundedFormulaInf ι α n → Set α
  | _, .falsum => ∅
  | _, .equal t₁ t₂ => ↑t₁.varFinsetLeft ∪ ↑t₂.varFinsetLeft
  | _, .rel _ ts => ⋃ i, ↑(ts i).varFinsetLeft
  | _, .imp φ ψ => freeVarSupport φ ∪ freeVarSupport ψ
  | _, .all φ => freeVarSupport φ
  | _, .iSup φs => ⋃ i, freeVarSupport (φs i)
  | _, .iInf φs => ⋃ i, freeVarSupport (φs i)

/-! ### Defining equations -/

/-- The false formula has no free variables. -/
@[simp]
theorem freeVarSupport_falsum : (falsum : L.BoundedFormulaInf ι α n).freeVarSupport = ∅ := by
  rw [freeVarSupport]

/-- The free variables of an equation are those of its two terms. -/
@[simp]
theorem freeVarSupport_equal [DecidableEq α] (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).freeVarSupport =
      ↑t₁.varFinsetLeft ∪ ↑t₂.varFinsetLeft := by
  rw [freeVarSupport]
  congr!

/-- The free variables of a relational atom are those of its argument terms. -/
@[simp]
theorem freeVarSupport_rel [DecidableEq α] {l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaInf ι α n).freeVarSupport = ⋃ i, ↑(ts i).varFinsetLeft := by
  rw [freeVarSupport]
  congr!

/-- The free variables of an implication are those of either side. -/
@[simp]
theorem freeVarSupport_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.imp ψ).freeVarSupport = φ.freeVarSupport ∪ ψ.freeVarSupport := by
  rw [freeVarSupport]

/-- Universal quantification binds a slot, not a free variable, so it keeps the support. -/
@[simp]
theorem freeVarSupport_all (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.all.freeVarSupport = φ.freeVarSupport := by
  rw [freeVarSupport]

/-- The free variables of a disjunction over the carrier are those of its branches. -/
@[simp]
theorem freeVarSupport_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    (iSup φs).freeVarSupport = ⋃ i, (φs i).freeVarSupport := by
  rw [freeVarSupport]

/-- The free variables of a conjunction over the carrier are those of its branches. -/
@[simp]
theorem freeVarSupport_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    (iInf φs).freeVarSupport = ⋃ i, (φs i).freeVarSupport := by
  rw [freeVarSupport]

/-! ### Derived connectives -/

/-- Negation keeps the support. -/
@[simp]
theorem freeVarSupport_not (φ : L.BoundedFormulaInf ι α n) :
    φ.not.freeVarSupport = φ.freeVarSupport := by
  simp [BoundedFormulaInf.not]

/-- `⊥` has no free variables. -/
@[simp]
theorem freeVarSupport_bot : (⊥ : L.BoundedFormulaInf ι α n).freeVarSupport = ∅ := by
  rw [bot_def, freeVarSupport_falsum]

/-- `⊤` has no free variables. -/
@[simp]
theorem freeVarSupport_top : (⊤ : L.BoundedFormulaInf ι α n).freeVarSupport = ∅ := by
  rw [top_def, freeVarSupport_not, freeVarSupport_falsum]

/-- The free variables of `φ ⊓ ψ` are those of `φ` or `ψ`. -/
@[simp]
theorem freeVarSupport_inf (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊓ ψ).freeVarSupport = φ.freeVarSupport ∪ ψ.freeVarSupport := by
  rw [inf_def, freeVarSupport_not, freeVarSupport_imp, freeVarSupport_not]

/-- The free variables of `φ ⊔ ψ` are those of `φ` or `ψ`. -/
@[simp]
theorem freeVarSupport_sup (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊔ ψ).freeVarSupport = φ.freeVarSupport ∪ ψ.freeVarSupport := by
  rw [sup_def, freeVarSupport_imp, freeVarSupport_not]

/-- The free variables of `φ.iff ψ` are those of `φ` or `ψ`. -/
@[simp]
theorem freeVarSupport_iff (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.iff ψ).freeVarSupport = φ.freeVarSupport ∪ ψ.freeVarSupport := by
  rw [iff_def, freeVarSupport_inf, freeVarSupport_imp, freeVarSupport_imp, Set.union_comm
    ψ.freeVarSupport, Set.union_self]

/-- Existential quantification keeps the support. -/
@[simp]
theorem freeVarSupport_ex (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.ex.freeVarSupport = φ.freeVarSupport := by
  simp [BoundedFormulaInf.ex]

/-- Universally closing the bound-variable slots keeps the support. -/
@[simp]
theorem freeVarSupport_alls (φ : L.BoundedFormulaInf ι α n) :
    φ.alls.freeVarSupport = φ.freeVarSupport := by
  induction n with
  | zero => rw [alls_zero]
  | succ n ih => rw [alls_succ, ih, freeVarSupport_all]

/-- Existentially closing the bound-variable slots keeps the support. -/
@[simp]
theorem freeVarSupport_exs (φ : L.BoundedFormulaInf ι α n) :
    φ.exs.freeVarSupport = φ.freeVarSupport := by
  induction n with
  | zero => rw [exs_zero]
  | succ n ih => rw [exs_succ, ih, freeVarSupport_ex]

/-! ### Bound-variable relabelling, weakening and carrier transport -/

/-- Relabelling the bound-variable slots keeps the support. -/
@[simp]
theorem freeVarSupport_mapBound {m : ℕ} (f : Fin m → Fin n) (φ : L.BoundedFormulaInf ι α m) :
    (mapBound f φ).freeVarSupport = φ.freeVarSupport := by
  classical
  have hterm {k l : ℕ} (g : Fin k → Fin l) (t : L.Term (α ⊕ Fin k)) :
      ((t.relabel (Sum.map id g)).varFinsetLeft : Set α) = t.varFinsetLeft := by
    ext a
    rw [Finset.mem_coe, Finset.mem_coe, Term.mem_varFinsetLeft_relabel, Term.mem_varFinsetLeft_iff]
    constructor
    · rintro ⟨x | x, hx, h⟩ <;> simp_all
    · exact fun h => ⟨_, h, rfl⟩
  induction φ generalizing n with
  | falsum => simp
  | equal t₁ t₂ => simp [hterm]
  | rel R ts => simp [hterm]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Weakening keeps the support. -/
@[simp]
theorem freeVarSupport_castLE {m : ℕ} (h : m ≤ n) (φ : L.BoundedFormulaInf ι α m) :
    (castLE h φ).freeVarSupport = φ.freeVarSupport := by
  rw [castLE_def, freeVarSupport_mapBound]

section Coded

variable {κ : Type uκ}

/-- The support of a coded conjunction is the union of the supports of its conjuncts: the
padding `⊤` has no free variables. -/
@[simp]
theorem freeVarSupport_iInfAlong (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    (iInfAlong c φs).freeVarSupport = ⋃ i, (φs i).freeVarSupport := by
  rw [iInfAlong_def, freeVarSupport_iInf]
  refine (Set.iUnion_subset fun k => ?_).antisymm
    (Set.iUnion_subset fun i => Set.subset_iUnion_of_subset (c.encode i) ?_)
  · rw [c.pad_apply]
    cases c.decode k with
    | none => simp
    | some i => exact Set.subset_iUnion_of_subset i subset_rfl
  · rw [c.pad_encode]

/-- The support of a coded disjunction is the union of the supports of its disjuncts: the
padding `⊥` has no free variables. -/
@[simp]
theorem freeVarSupport_iSupAlong (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    (iSupAlong c φs).freeVarSupport = ⋃ i, (φs i).freeVarSupport := by
  rw [iSupAlong_def, freeVarSupport_iSup]
  refine (Set.iUnion_subset fun k => ?_).antisymm
    (Set.iUnion_subset fun i => Set.subset_iUnion_of_subset (c.encode i) ?_)
  · rw [c.pad_apply]
    cases c.decode k with
    | none => simp
    | some i => exact Set.subset_iUnion_of_subset i subset_rfl
  · rw [c.pad_encode]

/-- Transporting a formula along a coding of its carrier keeps the support. -/
@[simp]
theorem freeVarSupport_reindex (c : TauCeti.IndexCoding ι κ) (φ : L.BoundedFormulaInf ι α n) :
    (reindex c φ).freeVarSupport = φ.freeVarSupport := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => classical simp
  | rel R ts => classical simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

end Coded

/-! ### Countability -/

/-- Over a countable carrier, in particular in `L_{ω₁ω}`, an infinitary formula has countably many
free variables. -/
theorem countable_freeVarSupport [Countable ι] (φ : L.BoundedFormulaInf ι α n) :
    φ.freeVarSupport.Countable := by
  classical
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simpa using (t₁.varFinsetLeft ∪ t₂.varFinsetLeft).countable_toSet
  | rel R ts => simpa using Set.countable_iUnion fun i => (ts i).varFinsetLeft.countable_toSet
  | imp φ ψ ihφ ihψ => simpa using ihφ.union ihψ
  | all φ ih => simpa using ih
  | iSup φs ih => simpa using Set.countable_iUnion ih
  | iInf φs ih => simpa using Set.countable_iUnion ih

/-! ### Realization depends only on the support -/

/-- **Realization depends only on the free-variable support**: two valuations of the free
variables that agree on `φ.freeVarSupport` realize `φ` at the same bound-variable valuations. -/
theorem realize_congr_freeVarSupport {M : Type w} [L.Structure M]
    {φ : L.BoundedFormulaInf ι α n} {v v' : α → M} (h : Set.EqOn v v' φ.freeVarSupport)
    (xs : Fin n → M) : φ.Realize v xs ↔ φ.Realize v' xs := by
  classical
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    rw [freeVarSupport_equal] at h
    rw [realize_equal, realize_equal,
      Term.realize_congr_varFinsetLeft (h.mono Set.subset_union_left),
      Term.realize_congr_varFinsetLeft (h.mono Set.subset_union_right)]
  | rel R ts =>
    rw [freeVarSupport_rel] at h
    simp only [realize_rel]
    congr! 2 with i
    exact Term.realize_congr_varFinsetLeft (h.mono (Set.subset_iUnion_of_subset i subset_rfl)) xs
  | imp φ ψ ihφ ihψ =>
    rw [freeVarSupport_imp] at h
    simp only [realize_imp, ihφ (h.mono Set.subset_union_left),
      ihψ (h.mono Set.subset_union_right)]
  | all φ ih =>
    rw [freeVarSupport_all] at h
    simp only [realize_all, ih h]
  | iSup φs ih =>
    rw [freeVarSupport_iSup] at h
    simp only [realize_iSup]
    exact exists_congr fun i => ih i (h.mono (Set.subset_iUnion_of_subset i subset_rfl)) xs
  | iInf φs ih =>
    rw [freeVarSupport_iInf] at h
    simp only [realize_iInf]
    exact forall_congr' fun i => ih i (h.mono (Set.subset_iUnion_of_subset i subset_rfl)) xs

end BoundedFormulaInf

namespace BoundedFormula

/-- On a finitary formula, embedded at any carrier, the free-variable support is the coercion of
Mathlib's `BoundedFormula.freeVarFinset`. In particular it is finite. -/
@[simp]
theorem freeVarSupport_toInf [DecidableEq α] {ι : Type uι} {n : ℕ} (φ : L.BoundedFormula α n) :
    (φ.toInf : L.BoundedFormulaInf ι α n).freeVarSupport = ↑φ.freeVarFinset := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [freeVarFinset]
  | rel R ts => simp [freeVarFinset]
  | imp φ ψ ihφ ihψ => simp [freeVarFinset, ihφ, ihψ]
  | all φ ih => simp [freeVarFinset, ih]

end BoundedFormula

end Language

end FirstOrder

namespace TauCeti

open FirstOrder Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {β : Type uβ} {n : ℕ}

/-- The support after substitution is the union of the variables of the terms substituted for
the free variables in the support. -/
@[simp]
theorem freeVarSupport_subst [DecidableEq β] (φ : L.BoundedFormulaInf ι α n)
    (f : α → L.Term β) :
    (subst φ f).freeVarSupport = ⋃ a ∈ φ.freeVarSupport, ↑(f a).varFinset := by
  classical
  have hterm {k : ℕ} (t : L.Term (α ⊕ Fin k)) :
      ((t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))).varFinsetLeft :
        Set β) = ⋃ a ∈ (t.varFinsetLeft : Set α), ↑(f a).varFinset := by
    ext b
    simp only [Finset.mem_coe, Term.mem_varFinsetLeft_subst, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x | x, hx, h⟩
      · simp only [Sum.elim_inl, Function.comp_apply, Term.mem_varFinsetLeft_relabel,
          Sum.inl.injEq, exists_eq_right] at h
        exact ⟨x, Term.mem_varFinsetLeft_iff.2 hx, h⟩
      · simp at h
    · rintro ⟨a, ha, h⟩
      exact ⟨Sum.inl a, Term.mem_varFinsetLeft_iff.1 ha, by simpa [Term.mem_varFinsetLeft_relabel]⟩
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [subst_equal, Language.BoundedFormulaInf.freeVarSupport_equal, hterm,
      Set.biUnion_union]
  | rel R ts =>
    simp only [subst_rel, Language.BoundedFormulaInf.freeVarSupport_rel, hterm,
      Set.biUnion_iUnion]
  | imp φ ψ ihφ ihψ =>
    simp only [subst_imp, Language.BoundedFormulaInf.freeVarSupport_imp, ihφ, ihψ,
      Set.biUnion_union]
  | all φ ih => simp only [subst_all, Language.BoundedFormulaInf.freeVarSupport_all, ih]
  | iSup φs ih =>
    simp only [subst_iSup, Language.BoundedFormulaInf.freeVarSupport_iSup, ih, Set.biUnion_iUnion]
  | iInf φs ih =>
    simp only [subst_iInf, Language.BoundedFormulaInf.freeVarSupport_iInf, ih, Set.biUnion_iUnion]

/-- The support after relabelling consists of the free variables `b` such that `g` sends a
variable of the original support to `Sum.inl b`. Variables sent to new bound slots drop out. -/
@[simp]
theorem freeVarSupport_relabel {m : ℕ} (g : α → β ⊕ Fin m) (φ : L.BoundedFormulaInf ι α n) :
    (relabel g φ).freeVarSupport = Sum.inl ⁻¹' (g '' φ.freeVarSupport) := by
  classical
  have hterm {k : ℕ} (t : L.Term (α ⊕ Fin k)) :
      ((t.relabel (BoundedFormula.relabelAux g k)).varFinsetLeft : Set β) =
        Sum.inl ⁻¹' (g '' t.varFinsetLeft) := by
    ext b
    simp only [Finset.mem_coe, Term.mem_varFinsetLeft_relabel, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨x | x, hx, h⟩
      · refine ⟨x, Term.mem_varFinsetLeft_iff.2 hx, ?_⟩
        rcases hg : g x with c | c
        · simpa [BoundedFormula.relabelAux, hg] using h
        · simp [BoundedFormula.relabelAux, hg] at h
      · simp [BoundedFormula.relabelAux] at h
    · rintro ⟨a, ha, h⟩
      exact ⟨Sum.inl a, Term.mem_varFinsetLeft_iff.1 ha, by simp [BoundedFormula.relabelAux, h]⟩
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [hterm, Set.image_union]
  | rel R ts => simp [hterm, Set.image_iUnion]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ, Set.image_union]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih, Set.image_iUnion]
  | iInf φs ih => simp [ih, Set.image_iUnion]

end BoundedFormulaInf

end TauCeti
