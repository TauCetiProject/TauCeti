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
public import Mathlib.Data.Set.Countable

/-!
# Symbols occurring in infinitary formulas

`BoundedFormulaInf.functionsIn` and `BoundedFormulaInf.relationsIn` record the symbols
occurring in a formula, tagged by arity. Equality contributes only the function symbols of its
terms: it is a logical symbol. At a countable branching carrier both sets are countable, with
no restriction on the size of the language. This is the input for restricting a sentence to
a countable sublanguage.

`BoundedFormulaInf.realize_congr_of_agreeOn` is symbol locality: two interpretations on one
carrier which agree on the occurring symbols give the formula the same truth value. Language
maps take occurrence sets to their exact images; bound-variable relabelling and carrier coding
preserve them.
-/

public section

universe u v u' v' uα uι uκ w

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

/-- At a countable branching carrier the set of occurring function symbols is countable. -/
theorem functionsIn_countable [Countable ι] (φ : L.BoundedFormulaInf ι α n) :
    φ.functionsIn.Countable := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    exact t₁.functionsIn_finite.countable.union t₂.functionsIn_finite.countable
  | rel R ts => exact Set.countable_iUnion fun i => (ts i).functionsIn_finite.countable
  | imp φ ψ ihφ ihψ => exact ihφ.union ihψ
  | all φ ih => exact ih
  | iSup φs ih => exact Set.countable_iUnion ih
  | iInf φs ih => exact Set.countable_iUnion ih

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
  | all φ ih => exact ih
  | iSup φs ih => exact Set.countable_iUnion ih
  | iInf φs ih => exact Set.countable_iUnion ih

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

end LHom

end FirstOrder.Language
