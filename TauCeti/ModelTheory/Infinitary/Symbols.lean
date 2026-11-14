/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Term.Symbols
public import TauCeti.ModelTheory.Infinitary.LanguageMap
public import TauCeti.ModelTheory.Infinitary.Reindex
public import TauCeti.ModelTheory.Infinitary.Operations
public import TauCeti.ModelTheory.Infinitary.Substitution
public import Mathlib.Data.Set.Countable

/-!
# Symbols occurring in infinitary formulas

`BoundedFormulaInf.functionsIn` and `BoundedFormulaInf.relationsIn` record the symbols
occurring in a formula, tagged by arity, and `BoundedFormulaInf.functionsInSet` and
`BoundedFormulaInf.relationsInSet` collect those occurring across a set of formulas. Equality
contributes only the function symbols of its terms: it is a logical symbol. At a countable
branching carrier the symbol sets of a formula and of any countable set of formulas are countable,
with no restriction on the size of the language. This is the input for restricting formulas and
theories to countable sublanguages.

`BoundedFormulaInf.realize_congr_of_agreeOn` is symbol locality: two interpretations on one
carrier which agree on the occurring symbols give the formula the same truth value. Language
maps take occurrence sets to their exact images; bound-variable and free-variable relabelling
and carrier coding preserve them, and free-variable substitution preserves relation symbols and
adds at most the function symbols of the substituted terms.
-/

public section

universe u v u' v' uα uβ uι uκ w

namespace FirstOrder.Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {n : ℕ}

/-- The function symbols occurring in an infinitary formula, tagged by arity. -/
def functionsIn : ∀ {n}, L.BoundedFormulaInf ι α n → Set (Σ k, L.Functions k)
  | _, .falsum => ∅
  | _, .equal t₁ t₂ => t₁.functionsIn ∪ t₂.functionsIn
  | _, .rel _ ts => ⋃ i, (ts i).functionsIn
  | _, .imp φ ψ => functionsIn φ ∪ functionsIn ψ
  | _, .all φ => functionsIn φ
  | _, .iSup φs => ⋃ i, functionsIn (φs i)
  | _, .iInf φs => ⋃ i, functionsIn (φs i)

/-- The relation symbols occurring in an infinitary formula, tagged by arity.
Logical equality does not contribute a relation symbol. -/
def relationsIn : ∀ {n}, L.BoundedFormulaInf ι α n → Set (Σ k, L.Relations k)
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel R _ => {⟨_, R⟩}
  | _, .imp φ ψ => relationsIn φ ∪ relationsIn ψ
  | _, .all φ => relationsIn φ
  | _, .iSup φs => ⋃ i, relationsIn (φs i)
  | _, .iInf φs => ⋃ i, relationsIn (φs i)

@[simp]
theorem functionsIn_falsum :
    (falsum : L.BoundedFormulaInf ι α n).functionsIn = ∅ := (rfl)

@[simp]
theorem functionsIn_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).functionsIn =
      t₁.functionsIn ∪ t₂.functionsIn := (rfl)

@[simp]
theorem functionsIn_rel {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaInf ι α n).functionsIn = ⋃ i, (ts i).functionsIn := (rfl)

@[simp]
theorem functionsIn_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.imp ψ).functionsIn = φ.functionsIn ∪ ψ.functionsIn := (rfl)

@[simp]
theorem functionsIn_all (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.all.functionsIn = φ.functionsIn := (rfl)

@[simp]
theorem functionsIn_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    (iSup φs).functionsIn = ⋃ i, (φs i).functionsIn := (rfl)

@[simp]
theorem functionsIn_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    (iInf φs).functionsIn = ⋃ i, (φs i).functionsIn := (rfl)

@[simp]
theorem functionsIn_not (φ : L.BoundedFormulaInf ι α n) :
    φ.not.functionsIn = φ.functionsIn := by
  simp [BoundedFormulaInf.not]

@[simp]
theorem functionsIn_bot :
    (⊥ : L.BoundedFormulaInf ι α n).functionsIn = ∅ := by
  rw [bot_def, functionsIn_falsum]

@[simp]
theorem functionsIn_top :
    (⊤ : L.BoundedFormulaInf ι α n).functionsIn = ∅ := by
  rw [top_def, functionsIn_not, functionsIn_falsum]

@[simp]
theorem functionsIn_inf (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊓ ψ).functionsIn = φ.functionsIn ∪ ψ.functionsIn := by
  simp [inf_def]

@[simp]
theorem functionsIn_sup (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊔ ψ).functionsIn = φ.functionsIn ∪ ψ.functionsIn := by
  simp [sup_def]

@[simp]
theorem functionsIn_iff (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.iff ψ).functionsIn = φ.functionsIn ∪ ψ.functionsIn := by
  simp [iff_def, Set.union_comm]

@[simp]
theorem functionsIn_ex (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.ex.functionsIn = φ.functionsIn := by
  simp [BoundedFormulaInf.ex]

@[simp]
theorem functionsIn_alls (φ : L.BoundedFormulaInf ι α n) :
    φ.alls.functionsIn = φ.functionsIn := by
  induction n with
  | zero => simp
  | succ n ih => rw [alls_succ, ih, functionsIn_all]

@[simp]
theorem functionsIn_exs (φ : L.BoundedFormulaInf ι α n) :
    φ.exs.functionsIn = φ.functionsIn := by
  induction n with
  | zero => simp
  | succ n ih => rw [exs_succ, ih, functionsIn_ex]

@[simp]
theorem functionsIn_exsLast {k : ℕ} (φ : L.BoundedFormulaInf ι α (n + k)) :
    (exsLast φ).functionsIn = φ.functionsIn := by
  induction k with
  | zero => rw [exsLast_zero]
  | succ k ih => rw [exsLast_succ, ih, functionsIn_ex]

@[simp]
theorem relationsIn_falsum :
    (falsum : L.BoundedFormulaInf ι α n).relationsIn = ∅ := (rfl)

@[simp]
theorem relationsIn_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).relationsIn = ∅ := (rfl)

@[simp]
theorem relationsIn_rel {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaInf ι α n).relationsIn = {⟨k, R⟩} := (rfl)

@[simp]
theorem relationsIn_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.imp ψ).relationsIn = φ.relationsIn ∪ ψ.relationsIn := (rfl)

@[simp]
theorem relationsIn_all (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.all.relationsIn = φ.relationsIn := (rfl)

@[simp]
theorem relationsIn_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    (iSup φs).relationsIn = ⋃ i, (φs i).relationsIn := (rfl)

@[simp]
theorem relationsIn_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    (iInf φs).relationsIn = ⋃ i, (φs i).relationsIn := (rfl)

@[simp]
theorem relationsIn_not (φ : L.BoundedFormulaInf ι α n) :
    φ.not.relationsIn = φ.relationsIn := by
  simp [BoundedFormulaInf.not]

@[simp]
theorem relationsIn_bot :
    (⊥ : L.BoundedFormulaInf ι α n).relationsIn = ∅ := by
  rw [bot_def, relationsIn_falsum]

@[simp]
theorem relationsIn_top :
    (⊤ : L.BoundedFormulaInf ι α n).relationsIn = ∅ := by
  rw [top_def, relationsIn_not, relationsIn_falsum]

@[simp]
theorem relationsIn_inf (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊓ ψ).relationsIn = φ.relationsIn ∪ ψ.relationsIn := by
  simp [inf_def]

@[simp]
theorem relationsIn_sup (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊔ ψ).relationsIn = φ.relationsIn ∪ ψ.relationsIn := by
  simp [sup_def]

@[simp]
theorem relationsIn_iff (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.iff ψ).relationsIn = φ.relationsIn ∪ ψ.relationsIn := by
  simp [iff_def, Set.union_comm]

@[simp]
theorem relationsIn_ex (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.ex.relationsIn = φ.relationsIn := by
  simp [BoundedFormulaInf.ex]

@[simp]
theorem relationsIn_alls (φ : L.BoundedFormulaInf ι α n) :
    φ.alls.relationsIn = φ.relationsIn := by
  induction n with
  | zero => simp
  | succ n ih => rw [alls_succ, ih, relationsIn_all]

@[simp]
theorem relationsIn_exs (φ : L.BoundedFormulaInf ι α n) :
    φ.exs.relationsIn = φ.relationsIn := by
  induction n with
  | zero => simp
  | succ n ih => rw [exs_succ, ih, relationsIn_ex]

@[simp]
theorem relationsIn_exsLast {k : ℕ} (φ : L.BoundedFormulaInf ι α (n + k)) :
    (exsLast φ).relationsIn = φ.relationsIn := by
  induction k with
  | zero => rw [exsLast_zero]
  | succ k ih => rw [exsLast_succ, ih, relationsIn_ex]

/-- At a countable branching carrier the set of occurring function symbols is countable. -/
theorem functionsIn_countable [Countable ι] (φ : L.BoundedFormulaInf ι α n) :
    φ.functionsIn.Countable := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    exact t₁.functionsIn_finite.countable.union t₂.functionsIn_finite.countable
  | rel _ ts => exact Set.countable_iUnion fun i => (ts i).functionsIn_finite.countable
  | imp φ ψ ihφ ihψ => exact ihφ.union ihψ
  | all _ ih => exact ih
  | iSup φs ih => exact Set.countable_iUnion ih
  | iInf φs ih => exact Set.countable_iUnion ih

/-- At a countable branching carrier, the subtype of function symbols occurring in a formula is
countable. -/
instance countable_functionsIn [Countable ι] (φ : L.BoundedFormulaInf ι α n) :
    Countable φ.functionsIn :=
  φ.functionsIn_countable.to_subtype

/-- Relabelling bound positions preserves the occurring function symbols. -/
@[simp]
theorem functionsIn_mapBound {m : ℕ} (f : Fin m → Fin n) (φ : L.BoundedFormulaInf ι α m) :
    (mapBound f φ).functionsIn = φ.functionsIn := by
  induction φ generalizing n with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

@[simp]
theorem functionsIn_castLE {m : ℕ} (h : m ≤ n) (φ : L.BoundedFormulaInf ι α m) :
    (castLE h φ).functionsIn = φ.functionsIn := by
  rw [castLE_def, functionsIn_mapBound]

/-- Coded conjunction adds no symbols through its padding. -/
@[simp]
theorem functionsIn_iInfAlong {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    (iInfAlong c φs).functionsIn = ⋃ i, (φs i).functionsIn := by
  rw [iInfAlong_def, functionsIn_iInf, c.iUnion_pad_of_eq_empty functionsIn_top]

/-- Coded disjunction adds no symbols through its padding. -/
@[simp]
theorem functionsIn_iSupAlong {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    (iSupAlong c φs).functionsIn = ⋃ i, (φs i).functionsIn := by
  rw [iSupAlong_def, functionsIn_iSup, c.iUnion_pad_of_eq_empty functionsIn_bot]

/-- Changing the branching carrier by a coding preserves occurrence sets. -/
@[simp]
theorem functionsIn_reindex {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φ : L.BoundedFormulaInf ι α n) :
    (reindex c φ).functionsIn = φ.functionsIn := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- At a countable branching carrier the set of occurring relation symbols is countable. -/
theorem relationsIn_countable [Countable ι] (φ : L.BoundedFormulaInf ι α n) :
    φ.relationsIn.Countable := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => exact ihφ.union ihψ
  | all _ ih => exact ih
  | iSup φs ih => exact Set.countable_iUnion ih
  | iInf φs ih => exact Set.countable_iUnion ih

/-- At a countable branching carrier, the subtype of relation symbols occurring in a formula is
countable. -/
instance countable_relationsIn [Countable ι] (φ : L.BoundedFormulaInf ι α n) :
    Countable φ.relationsIn :=
  φ.relationsIn_countable.to_subtype

/-- Relabelling bound positions preserves the occurring relation symbols. -/
@[simp]
theorem relationsIn_mapBound {m : ℕ} (f : Fin m → Fin n) (φ : L.BoundedFormulaInf ι α m) :
    (mapBound f φ).relationsIn = φ.relationsIn := by
  induction φ generalizing n with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

@[simp]
theorem relationsIn_castLE {m : ℕ} (h : m ≤ n) (φ : L.BoundedFormulaInf ι α m) :
    (castLE h φ).relationsIn = φ.relationsIn := by
  rw [castLE_def, relationsIn_mapBound]

/-- Coded conjunction adds no symbols through its padding. -/
@[simp]
theorem relationsIn_iInfAlong {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    (iInfAlong c φs).relationsIn = ⋃ i, (φs i).relationsIn := by
  rw [iInfAlong_def, relationsIn_iInf, c.iUnion_pad_of_eq_empty relationsIn_top]

/-- Coded disjunction adds no symbols through its padding. -/
@[simp]
theorem relationsIn_iSupAlong {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    (iSupAlong c φs).relationsIn = ⋃ i, (φs i).relationsIn := by
  rw [iSupAlong_def, relationsIn_iSup, c.iUnion_pad_of_eq_empty relationsIn_bot]

/-- Changing the branching carrier by a coding preserves occurrence sets. -/
@[simp]
theorem relationsIn_reindex {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φ : L.BoundedFormulaInf ι α n) :
    (reindex c φ).relationsIn = φ.relationsIn := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- **Symbol locality.** Structures on the same carrier which agree on every symbol occurring
in a formula give it the same realization. No agreement on other symbols is required. -/
theorem realize_congr_of_agreeOn {M : Type w} (φ : L.BoundedFormulaInf ι α n)
    (S S' : L.Structure M)
    (hF : ∀ {k} (f : L.Functions k), ⟨k, f⟩ ∈ φ.functionsIn →
      ∀ xs, @Structure.funMap L M S k f xs = @Structure.funMap L M S' k f xs)
    (hR : ∀ {k} (R : L.Relations k), ⟨k, R⟩ ∈ φ.relationsIn →
      ∀ xs, @Structure.RelMap L M S k R xs ↔ @Structure.RelMap L M S' k R xs)
    (v : α → M) (xs : Fin n → M) :
    @Realize L ι α M S n φ v xs ↔ @Realize L ι α M S' n φ v xs := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [realize_equal]
    rw [t₁.realize_congr_of_agreeOn S S' (fun f hf => hF f (Set.mem_union_left _ hf)),
      t₂.realize_congr_of_agreeOn S S' (fun f hf => hF f (Set.mem_union_right _ hf))]
  | rel R ts =>
    simp only [realize_rel]
    have ht : ∀ i, @Term.realize L M S _ (Sum.elim v xs) (ts i) =
        @Term.realize L M S' _ (Sum.elim v xs) (ts i) := fun i =>
      (ts i).realize_congr_of_agreeOn S S'
        (fun f hf => hF f (Set.mem_iUnion.mpr ⟨i, hf⟩)) _
    simp_rw [ht]
    exact hR R (by simp) _
  | imp φ ψ ihφ ihψ =>
    simp only [realize_imp]
    exact imp_congr
      (ihφ (fun f hf => hF f (Set.mem_union_left _ hf))
        (fun R hR' => hR R (Set.mem_union_left _ hR')) xs)
      (ihψ (fun f hf => hF f (Set.mem_union_right _ hf))
        (fun R hR' => hR R (Set.mem_union_right _ hR')) xs)
  | all φ ih =>
    simp only [realize_all]
    exact forall_congr' fun y => ih hF hR (Fin.snoc xs y)
  | iSup φs ih =>
    simp only [realize_iSup]
    exact exists_congr fun i => ih i
      (fun f hf => hF f (Set.mem_iUnion.mpr ⟨i, hf⟩))
      (fun R hR' => hR R (Set.mem_iUnion.mpr ⟨i, hR'⟩)) xs
  | iInf φs ih =>
    simp only [realize_iInf]
    exact forall_congr' fun i => ih i
      (fun f hf => hF f (Set.mem_iUnion.mpr ⟨i, hf⟩))
      (fun R hR' => hR R (Set.mem_iUnion.mpr ⟨i, hR'⟩)) xs

/-! ### Symbols occurring across a set of formulas -/

/-- The arity-tagged function symbols occurring in at least one formula of `S`. -/
def functionsInSet (S : Set (L.BoundedFormulaInf ι α n)) : Set (Σ k, L.Functions k) :=
  ⋃ φ ∈ S, φ.functionsIn

/-- The arity-tagged relation symbols occurring in at least one formula of `S`. -/
def relationsInSet (S : Set (L.BoundedFormulaInf ι α n)) : Set (Σ k, L.Relations k) :=
  ⋃ φ ∈ S, φ.relationsIn

/-- Unfolding equation for `functionsInSet`. -/
theorem functionsInSet_def (S : Set (L.BoundedFormulaInf ι α n)) :
    functionsInSet S = ⋃ φ ∈ S, φ.functionsIn :=
  (rfl)

/-- Unfolding equation for `relationsInSet`. -/
theorem relationsInSet_def (S : Set (L.BoundedFormulaInf ι α n)) :
    relationsInSet S = ⋃ φ ∈ S, φ.relationsIn :=
  (rfl)

/-- A function symbol lies in `functionsInSet S` iff it occurs in some member of `S`. -/
@[simp]
theorem mem_functionsInSet_iff {S : Set (L.BoundedFormulaInf ι α n)}
    {s : Σ k, L.Functions k} :
    s ∈ functionsInSet S ↔ ∃ φ ∈ S, s ∈ φ.functionsIn := by
  simp [functionsInSet]

/-- A relation symbol lies in `relationsInSet S` iff it occurs in some member of `S`. -/
@[simp]
theorem mem_relationsInSet_iff {S : Set (L.BoundedFormulaInf ι α n)}
    {s : Σ k, L.Relations k} :
    s ∈ relationsInSet S ↔ ∃ φ ∈ S, s ∈ φ.relationsIn := by
  simp [relationsInSet]

/-- `functionsInSet S` is contained in `F` iff every formula of `S` has its function symbols in
`F`. -/
@[simp]
theorem functionsInSet_subset_iff {S : Set (L.BoundedFormulaInf ι α n)}
    {F : Set (Σ k, L.Functions k)} :
    functionsInSet S ⊆ F ↔ ∀ φ ∈ S, φ.functionsIn ⊆ F :=
  Set.iUnion₂_subset_iff

/-- `relationsInSet S` is contained in `R` iff every formula of `S` has its relation symbols in
`R`. -/
@[simp]
theorem relationsInSet_subset_iff {S : Set (L.BoundedFormulaInf ι α n)}
    {R : Set (Σ k, L.Relations k)} :
    relationsInSet S ⊆ R ↔ ∀ φ ∈ S, φ.relationsIn ⊆ R :=
  Set.iUnion₂_subset_iff

/-- No function symbols occur in the empty set of formulas. -/
@[simp]
theorem functionsInSet_empty :
    functionsInSet (∅ : Set (L.BoundedFormulaInf ι α n)) = ∅ := by
  simp [functionsInSet_def]

/-- No relation symbols occur in the empty set of formulas. -/
@[simp]
theorem relationsInSet_empty :
    relationsInSet (∅ : Set (L.BoundedFormulaInf ι α n)) = ∅ := by
  simp [relationsInSet_def]

/-- The function symbols of a singleton `{φ}` are those of `φ`. -/
@[simp]
theorem functionsInSet_singleton (φ : L.BoundedFormulaInf ι α n) :
    functionsInSet ({φ} : Set (L.BoundedFormulaInf ι α n)) = φ.functionsIn := by
  simp [functionsInSet_def]

/-- The relation symbols of a singleton `{φ}` are those of `φ`. -/
@[simp]
theorem relationsInSet_singleton (φ : L.BoundedFormulaInf ι α n) :
    relationsInSet ({φ} : Set (L.BoundedFormulaInf ι α n)) = φ.relationsIn := by
  simp [relationsInSet_def]

/-- Inserting a formula adds its occurring function symbols. -/
@[simp]
theorem functionsInSet_insert (φ : L.BoundedFormulaInf ι α n)
    (S : Set (L.BoundedFormulaInf ι α n)) :
    functionsInSet (insert φ S) = φ.functionsIn ∪ functionsInSet S := by
  simp [functionsInSet_def]

/-- Inserting a formula adds its occurring relation symbols. -/
@[simp]
theorem relationsInSet_insert (φ : L.BoundedFormulaInf ι α n)
    (S : Set (L.BoundedFormulaInf ι α n)) :
    relationsInSet (insert φ S) = φ.relationsIn ∪ relationsInSet S := by
  simp [relationsInSet_def]

/-- The function symbols of a union of formula sets are the union of their function symbols. -/
@[simp]
theorem functionsInSet_union (S₁ S₂ : Set (L.BoundedFormulaInf ι α n)) :
    functionsInSet (S₁ ∪ S₂) = functionsInSet S₁ ∪ functionsInSet S₂ := by
  rw [functionsInSet_def, Set.biUnion_union]
  rfl

/-- The relation symbols of a union of formula sets are the union of their relation symbols. -/
@[simp]
theorem relationsInSet_union (S₁ S₂ : Set (L.BoundedFormulaInf ι α n)) :
    relationsInSet (S₁ ∪ S₂) = relationsInSet S₁ ∪ relationsInSet S₂ := by
  rw [relationsInSet_def, Set.biUnion_union]
  rfl

/-- Every member of `S` has its occurring function symbols in `functionsInSet S`. -/
theorem subset_functionsInSet_of_mem {φ : L.BoundedFormulaInf ι α n}
    {S : Set (L.BoundedFormulaInf ι α n)} (hφ : φ ∈ S) :
    φ.functionsIn ⊆ functionsInSet S :=
  Set.subset_biUnion_of_mem hφ

/-- Every member of `S` has its occurring relation symbols in `relationsInSet S`. -/
theorem subset_relationsInSet_of_mem {φ : L.BoundedFormulaInf ι α n}
    {S : Set (L.BoundedFormulaInf ι α n)} (hφ : φ ∈ S) :
    φ.relationsIn ⊆ relationsInSet S :=
  Set.subset_biUnion_of_mem hφ

/-- `functionsInSet` is monotone in the set of formulas. -/
theorem functionsInSet_mono {S₁ S₂ : Set (L.BoundedFormulaInf ι α n)} (h : S₁ ⊆ S₂) :
    functionsInSet S₁ ⊆ functionsInSet S₂ :=
  Set.biUnion_mono h fun _ _ => subset_rfl

/-- `relationsInSet` is monotone in the set of formulas. -/
theorem relationsInSet_mono {S₁ S₂ : Set (L.BoundedFormulaInf ι α n)} (h : S₁ ⊆ S₂) :
    relationsInSet S₁ ⊆ relationsInSet S₂ :=
  Set.biUnion_mono h fun _ _ => subset_rfl

/-- At a countable branching carrier, a countable set of formulas mentions only countably many
function symbols. -/
theorem functionsInSet_countable [Countable ι] {S : Set (L.BoundedFormulaInf ι α n)}
    (hS : S.Countable) : (functionsInSet S).Countable :=
  hS.biUnion fun φ _ => φ.functionsIn_countable

/-- At a countable branching carrier, a countable set of formulas mentions only countably many
relation symbols. -/
theorem relationsInSet_countable [Countable ι] {S : Set (L.BoundedFormulaInf ι α n)}
    (hS : S.Countable) : (relationsInSet S).Countable :=
  hS.biUnion fun φ _ => φ.relationsIn_countable

/-- At a countable branching carrier, `functionsInSet S` is countable for any countable `S`. -/
instance countable_functionsInSet [Countable ι] (S : Set (L.BoundedFormulaInf ι α n))
    [Countable S] : Countable (functionsInSet S) :=
  (functionsInSet_countable (Set.to_countable S)).to_subtype

/-- At a countable branching carrier, `relationsInSet S` is countable for any countable `S`. -/
instance countable_relationsInSet [Countable ι] (S : Set (L.BoundedFormulaInf ι α n))
    [Countable S] : Countable (relationsInSet S) :=
  (relationsInSet_countable (Set.to_countable S)).to_subtype

end BoundedFormulaInf

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {ι : Type uι} {α : Type uα} {n : ℕ}

/-- Language translation takes the occurring function symbols to their exact image. -/
@[simp]
theorem functionsIn_onBoundedFormulaInf (g : L →ᴸ L') (φ : L.BoundedFormulaInf ι α n) :
    (g.onBoundedFormulaInf φ).functionsIn =
      (fun s => ⟨s.1, g.onFunction s.2⟩) '' φ.functionsIn := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [Set.image_union]
  | rel R ts => simp [Set.image_iUnion]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ, Set.image_union]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih, Set.image_iUnion]
  | iInf φs ih => simp [ih, Set.image_iUnion]

/-- Language translation takes the occurring relation symbols to their exact image. -/
@[simp]
theorem relationsIn_onBoundedFormulaInf (g : L →ᴸ L') (φ : L.BoundedFormulaInf ι α n) :
    (g.onBoundedFormulaInf φ).relationsIn =
      (fun s => ⟨s.1, g.onRelation s.2⟩) '' φ.relationsIn := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ, Set.image_union]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih, Set.image_iUnion]
  | iInf φs ih => simp [ih, Set.image_iUnion]

/-- Language translation takes the function symbols occurring across a set of formulas to their
exact image. -/
@[simp]
theorem functionsInSet_image_onBoundedFormulaInf (g : L →ᴸ L')
    (S : Set (L.BoundedFormulaInf ι α n)) :
    BoundedFormulaInf.functionsInSet (g.onBoundedFormulaInf '' S) =
      (fun s => ⟨s.1, g.onFunction s.2⟩) '' BoundedFormulaInf.functionsInSet S := by
  rw [BoundedFormulaInf.functionsInSet_def, BoundedFormulaInf.functionsInSet_def,
    Set.biUnion_image, Set.image_iUnion₂]
  simp_rw [functionsIn_onBoundedFormulaInf]

/-- Language translation takes the relation symbols occurring across a set of formulas to their
exact image. -/
@[simp]
theorem relationsInSet_image_onBoundedFormulaInf (g : L →ᴸ L')
    (S : Set (L.BoundedFormulaInf ι α n)) :
    BoundedFormulaInf.relationsInSet (g.onBoundedFormulaInf '' S) =
      (fun s => ⟨s.1, g.onRelation s.2⟩) '' BoundedFormulaInf.relationsInSet S := by
  rw [BoundedFormulaInf.relationsInSet_def, BoundedFormulaInf.relationsInSet_def,
    Set.biUnion_image, Set.image_iUnion₂]
  simp_rw [relationsIn_onBoundedFormulaInf]

end LHom

end FirstOrder.Language

namespace TauCeti.BoundedFormulaInf

open FirstOrder Language

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {β : Type uβ} {m n : ℕ}

/-- Free-variable relabelling preserves the occurring function symbols. -/
@[simp]
theorem functionsIn_relabel (g : α → β ⊕ Fin m) (φ : L.BoundedFormulaInf ι α n) :
    (relabel g φ).functionsIn = φ.functionsIn := by
  induction φ with
  | imp _ _ ihφ ihψ => simp [ihφ, ihψ]
  | all _ ih | iSup _ ih | iInf _ ih => simp [ih]
  | _ => simp

/-- Free-variable relabelling preserves the occurring relation symbols. -/
@[simp]
theorem relationsIn_relabel (g : α → β ⊕ Fin m) (φ : L.BoundedFormulaInf ι α n) :
    (relabel g φ).relationsIn = φ.relationsIn := by
  induction φ with
  | imp _ _ ihφ ihψ => simp [ihφ, ihψ]
  | all _ ih | iSup _ ih | iInf _ ih => simp [ih]
  | _ => simp

/-- Free-variable substitution keeps every function symbol of the formula. -/
theorem functionsIn_subset_functionsIn_subst (φ : L.BoundedFormulaInf ι α n)
    (f : α → L.Term β) : φ.functionsIn ⊆ (subst φ f).functionsIn := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [subst_equal, Language.BoundedFormulaInf.functionsIn_equal]
    exact Set.union_subset_union (t₁.functionsIn_subset_functionsIn_subst _)
      (t₂.functionsIn_subset_functionsIn_subst _)
  | rel _ ts =>
    simp only [subst_rel, Language.BoundedFormulaInf.functionsIn_rel]
    exact Set.iUnion_mono fun i => (ts i).functionsIn_subset_functionsIn_subst _
  | imp _ _ ihφ ihψ =>
    simp only [subst_imp, Language.BoundedFormulaInf.functionsIn_imp]
    exact Set.union_subset_union ihφ ihψ
  | all _ ih => simpa using ih
  | iSup _ ih | iInf _ ih =>
    simp only [subst_iSup, subst_iInf, Language.BoundedFormulaInf.functionsIn_iSup,
      Language.BoundedFormulaInf.functionsIn_iInf]
    exact Set.iUnion_mono ih

/-- Free-variable substitution adds at most the function symbols of the substituted terms. -/
theorem functionsIn_subst_subset (φ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    (subst φ f).functionsIn ⊆ φ.functionsIn ∪ ⋃ a, (f a).functionsIn := by
  have hatom {k : ℕ} (t : L.Term (α ⊕ Fin k)) :
      (t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))).functionsIn ⊆
        t.functionsIn ∪ ⋃ a, (f a).functionsIn :=
    (t.functionsIn_subst_subset _).trans <| Set.union_subset_union_right _ <|
      Set.iUnion_subset fun
        | .inl a => by simpa using Set.subset_iUnion (fun a => (f a).functionsIn) a
        | .inr _ => by simp
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [subst_equal, Language.BoundedFormulaInf.functionsIn_equal]
    exact Set.union_subset ((hatom t₁).trans (Set.union_subset_union_left _ (by simp)))
      ((hatom t₂).trans (Set.union_subset_union_left _ (by simp)))
  | rel _ ts =>
    simp only [subst_rel, Language.BoundedFormulaInf.functionsIn_rel]
    exact Set.iUnion_subset fun i => (hatom (ts i)).trans <|
      Set.union_subset_union_left _ (Set.subset_iUnion (fun i => (ts i).functionsIn) i)
  | imp _ _ ihφ ihψ =>
    simp only [subst_imp, Language.BoundedFormulaInf.functionsIn_imp]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ (by simp)))
      (ihψ.trans (Set.union_subset_union_left _ (by simp)))
  | all _ ih => simpa using ih
  | iSup φs ih | iInf φs ih =>
    simp only [subst_iSup, subst_iInf, Language.BoundedFormulaInf.functionsIn_iSup,
      Language.BoundedFormulaInf.functionsIn_iInf]
    exact Set.iUnion_subset fun i => (ih i).trans <|
      Set.union_subset_union_left _ (Set.subset_iUnion (fun i => (φs i).functionsIn) i)

/-- Free-variable substitution preserves the occurring relation symbols. -/
@[simp]
theorem relationsIn_subst (φ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    (subst φ f).relationsIn = φ.relationsIn := by
  induction φ with
  | imp _ _ ihφ ihψ => simp [ihφ, ihψ]
  | all _ ih | iSup _ ih | iInf _ ih => simp [ih]
  | _ => simp

end TauCeti.BoundedFormulaInf
