/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.ConstantAbstraction
public import TauCeti.ModelTheory.Infinitary.SubstBounds

/-!
# Universal and existential infinitary formulas

The signed predicate `BoundedFormulaInf.universalSigned` defines the `∀₁` and `∃₁` classes:
all quantifiers have the designated polarity, while arbitrary conjunctions and disjunctions
preserve the class. These are not prenex classes: a conjunction of existential formulas is
existential even when its witnesses cannot be collected into a finite quantifier prefix.

Universal formulas descend along structure embeddings, and existential formulas ascend.
Both statements allow function symbols and empty structures; the branching carrier and all
universes are arbitrary. The syntax classes are unchanged by substitution, variable renaming,
carrier recoding, language translation, and the abstraction of constants into variables.

## References

* M. Harrison-Trainor and M. Kretschmer, *Infinitary logic has no expressive efficiency over
  finitary logic*, Journal of Symbolic Logic 89 (2024), §2, for the `∀ₙ`/`∃ₙ` hierarchy.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, 2016, Chapter 4.
-/

public section

universe u v u' v' uα uβ uγ uι uκ w w'

namespace FirstOrder.Language
namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {n : ℕ}

/-- Signed universal syntax: `true` permits only positive universal quantifiers, and `false`
permits only negative ones. Implication flips the sign of its antecedent. Infinitary conjunctions
and disjunctions do not count as quantifiers. -/
def universalSigned : ∀ {n}, Bool → L.BoundedFormulaInf ι α n → Prop
  | _, _, .falsum => True
  | _, _, .equal _ _ => True
  | _, _, .rel _ _ => True
  | _, s, .imp φ ψ => universalSigned (!s) φ ∧ universalSigned s ψ
  | _, s, .all φ => s = true ∧ universalSigned s φ
  | _, s, .iSup φs => ∀ i, universalSigned s (φs i)
  | _, s, .iInf φs => ∀ i, universalSigned s (φs i)

/-- The `∀₁` class of infinitary formulas, allowing conjunctions and disjunctions throughout. -/
abbrev IsUniversal (φ : L.BoundedFormulaInf ι α n) : Prop := universalSigned true φ

/-- The `∃₁` class of infinitary formulas, allowing conjunctions and disjunctions throughout. -/
abbrev IsExistential (φ : L.BoundedFormulaInf ι α n) : Prop := universalSigned false φ

@[simp]
theorem universalSigned_falsum (s : Bool) :
    universalSigned s (falsum : L.BoundedFormulaInf ι α n) := ⟨⟩

@[simp]
theorem universalSigned_equal (s : Bool) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    universalSigned s (equal t₁ t₂ : L.BoundedFormulaInf ι α n) := ⟨⟩

@[simp]
theorem universalSigned_rel (s : Bool) {k : ℕ} (R : L.Relations k)
    (ts : Fin k → L.Term (α ⊕ Fin n)) :
    universalSigned s (rel R ts : L.BoundedFormulaInf ι α n) := ⟨⟩

@[simp]
theorem universalSigned_imp (s : Bool) (φ ψ : L.BoundedFormulaInf ι α n) :
    universalSigned s (φ.imp ψ) ↔ universalSigned (!s) φ ∧ universalSigned s ψ := (Iff.rfl)

@[simp]
theorem universalSigned_all (s : Bool) (φ : L.BoundedFormulaInf ι α (n + 1)) :
    universalSigned s φ.all ↔ s = true ∧ universalSigned s φ := (Iff.rfl)

@[simp]
theorem universalSigned_iSup (s : Bool) (φs : ι → L.BoundedFormulaInf ι α n) :
    universalSigned s (iSup φs) ↔ ∀ i, universalSigned s (φs i) := (Iff.rfl)

@[simp]
theorem universalSigned_iInf (s : Bool) (φs : ι → L.BoundedFormulaInf ι α n) :
    universalSigned s (iInf φs) ↔ ∀ i, universalSigned s (φs i) := (Iff.rfl)

/-- Negation exchanges the universal and existential classes. -/
@[simp]
theorem universalSigned_not (s : Bool) (φ : L.BoundedFormulaInf ι α n) :
    universalSigned s φ.not ↔ universalSigned (!s) φ := by
  simp [BoundedFormulaInf.not]

@[simp]
theorem universalSigned_bot (s : Bool) :
    universalSigned s (⊥ : L.BoundedFormulaInf ι α n) := by simp [bot_def]

@[simp]
theorem universalSigned_top (s : Bool) :
    universalSigned s (⊤ : L.BoundedFormulaInf ι α n) := by simp [top_def]

@[simp]
theorem universalSigned_inf (s : Bool) (φ ψ : L.BoundedFormulaInf ι α n) :
    universalSigned s (φ ⊓ ψ) ↔ universalSigned s φ ∧ universalSigned s ψ := by
  simp [inf_def]

@[simp]
theorem universalSigned_sup (s : Bool) (φ ψ : L.BoundedFormulaInf ι α n) :
    universalSigned s (φ ⊔ ψ) ↔ universalSigned s φ ∧ universalSigned s ψ := by
  simp [sup_def]

/-- A biconditional belongs to either class exactly when both sides belong to both classes. -/
@[simp]
theorem universalSigned_iff (s : Bool) (φ ψ : L.BoundedFormulaInf ι α n) :
    universalSigned s (φ.iff ψ) ↔
      (universalSigned s φ ∧ universalSigned (!s) φ) ∧
        (universalSigned s ψ ∧ universalSigned (!s) ψ) := by
  simp only [iff_def, universalSigned_inf, universalSigned_imp]
  tauto

@[simp]
theorem universalSigned_ex (s : Bool) (φ : L.BoundedFormulaInf ι α (n + 1)) :
    universalSigned s φ.ex ↔ s = false ∧ universalSigned s φ := by
  cases s <;> simp [BoundedFormulaInf.ex]

/-- Universal closure adds positive universal quantifiers exactly when a slot is present. -/
@[simp]
theorem universalSigned_alls (s : Bool) (φ : L.BoundedFormulaInf ι α n) :
    universalSigned s φ.alls ↔ (n = 0 ∨ s = true) ∧ universalSigned s φ := by
  induction n with
  | zero => simp
  | succ n ih => cases s <;> simp [ih]

/-- Existential closure adds negative universal quantifiers exactly when a slot is present. -/
@[simp]
theorem universalSigned_exs (s : Bool) (φ : L.BoundedFormulaInf ι α n) :
    universalSigned s φ.exs ↔ (n = 0 ∨ s = false) ∧ universalSigned s φ := by
  induction n with
  | zero => simp
  | succ n ih => cases s <;> simp [ih]

@[simp]
theorem universalSigned_exsLast (s : Bool) {k : ℕ}
    (φ : L.BoundedFormulaInf ι α (n + k)) :
    universalSigned s (exsLast φ) ↔ (k = 0 ∨ s = false) ∧ universalSigned s φ := by
  induction k with
  | zero => simp
  | succ k ih => cases s <;> simp [ih]

/-- Atomic formulas belong to either signed class. -/
theorem IsAtomic.universalSigned {φ : L.BoundedFormulaInf ι α n} (h : φ.IsAtomic) (s : Bool) :
    universalSigned s φ := by
  cases h <;> simp

/-- Coded conjunction preserves precisely the class of all its branches. -/
@[simp]
theorem universalSigned_iInfAlong (s : Bool) {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    universalSigned s (iInfAlong c φs) ↔ ∀ i, universalSigned s (φs i) := by
  rw [iInfAlong_def, universalSigned_iInf]
  have h := c.comp_pad (universalSigned s) ⊤ φs
  simp only [universalSigned_top] at h
  simpa only [← congrFun h, Function.comp_apply] using
    c.forall_pad_true_iff (universalSigned s ∘ φs)

/-- Coded disjunction preserves precisely the class of all its branches. -/
@[simp]
theorem universalSigned_iSupAlong (s : Bool) {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φs : ι → L.BoundedFormulaInf κ α n) :
    universalSigned s (iSupAlong c φs) ↔ ∀ i, universalSigned s (φs i) := by
  rw [iSupAlong_def, universalSigned_iSup]
  have h := c.comp_pad (universalSigned s) ⊥ φs
  simp only [universalSigned_bot] at h
  simpa only [← congrFun h, Function.comp_apply] using
    c.forall_pad_true_iff (universalSigned s ∘ φs)

/-! ### Invariance under syntax operations -/

/-- Bound-term substitution changes no quantifier polarity. -/
@[simp]
theorem universalSigned_substBounds (s : Bool) {m k : ℕ}
    (σ : Fin m → L.Term (α ⊕ Fin k)) (φ : L.BoundedFormulaInf ι α m) :
    universalSigned s (substBounds σ φ) ↔ universalSigned s φ := by
  induction φ generalizing s k with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

@[simp]
theorem universalSigned_inst (s : Bool) (φ : L.BoundedFormulaInf ι α 1)
    (t : L.Term (α ⊕ Fin 0)) :
    universalSigned s (φ.inst t) ↔ universalSigned s φ := by
  rw [inst_def, universalSigned_substBounds]

/-- Bound-position renaming changes no quantifier polarity. -/
@[simp]
theorem universalSigned_mapBound (s : Bool) {m : ℕ} (f : Fin m → Fin n)
    (φ : L.BoundedFormulaInf ι α m) :
    universalSigned s (mapBound f φ) ↔ universalSigned s φ := by
  rw [mapBound_eq_substBounds, universalSigned_substBounds]

@[simp]
theorem universalSigned_castLE (s : Bool) {m : ℕ} (h : m ≤ n)
    (φ : L.BoundedFormulaInf ι α m) :
    universalSigned s (castLE h φ) ↔ universalSigned s φ := by
  rw [castLE_def, universalSigned_mapBound]

/-- Recoding the branching carrier changes no quantifier polarity. -/
@[simp]
theorem universalSigned_reindex (s : Bool) {κ : Type uκ} (c : TauCeti.IndexCoding ι κ)
    (φ : L.BoundedFormulaInf ι α n) :
    universalSigned s (reindex c φ) ↔ universalSigned s φ := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Substituting free variables by terms changes no quantifier polarity. -/
@[simp]
theorem universalSigned_subst {β : Type uβ} (s : Bool)
    (φ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    universalSigned s (TauCeti.BoundedFormulaInf.subst φ f) ↔ universalSigned s φ := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Renaming free variables, including into new bound positions, preserves quantifier polarity. -/
@[simp]
theorem universalSigned_relabel {β : Type uβ} {m : ℕ} (s : Bool) (g : α → β ⊕ Fin m)
    (φ : L.BoundedFormulaInf ι α n) :
    universalSigned s (TauCeti.BoundedFormulaInf.relabel g φ) ↔ universalSigned s φ := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Turning the added constants into free variables preserves quantifier polarity. -/
@[simp]
theorem universalSigned_constantsVarsEquiv {γ : Type uγ} (s : Bool)
    (φ : L[[γ]].BoundedFormulaInf ι α n) :
    universalSigned s (constantsVarsEquiv φ) ↔ universalSigned s φ := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Turning free variables back into constants preserves quantifier polarity. -/
@[simp]
theorem universalSigned_constantsVarsEquiv_symm {γ : Type uγ} (s : Bool)
    (φ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    universalSigned s (constantsVarsEquiv.symm φ) ↔ universalSigned s φ := by
  rw [← universalSigned_constantsVarsEquiv, constantsVarsEquiv.apply_symm_apply]

/-- Abstracting one constant into a new bound position preserves quantifier polarity. -/
@[simp]
theorem universalSigned_abstractConst {γ : Type uγ} [DecidableEq γ] (s : Bool) (c : γ)
    (φ : L[[γ]].BoundedFormulaInf ι α n) :
    universalSigned s (abstractConst c φ) ↔ universalSigned s φ := by
  rw [abstractConst_def, universalSigned_constantsVarsEquiv_symm, universalSigned_mapBound,
    universalSigned_relabel, universalSigned_constantsVarsEquiv]

end BoundedFormulaInf

namespace LHom

/-- Language translation preserves and reflects either signed quantifier class. -/
@[simp]
theorem universalSigned_onBoundedFormulaInf {L : Language.{u, v}} {L' : Language.{u', v'}}
    {ι : Type uι} {α : Type uα} {n : ℕ} (g : L →ᴸ L') (s : Bool)
    (φ : L.BoundedFormulaInf ι α n) :
    BoundedFormulaInf.universalSigned s (g.onBoundedFormulaInf φ) ↔
      BoundedFormulaInf.universalSigned s φ := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

end LHom

namespace BoundedFormulaInf

section Preservation

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {n : ℕ}
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
variable {F : Type*} [FunLike F M N] [EmbeddingLike F M N] [StrongHomClass L F M N]

/-- Signed preservation along embeddings: positive universal syntax descends, and negative
universal syntax ascends. -/
theorem universalSigned.realize_embedding {φ : L.BoundedFormulaInf ι α n} {s : Bool}
    (hφ : universalSigned s φ) (f : F) (v : α → M) (xs : Fin n → M) :
    if s then (φ.Realize (f ∘ v) (f ∘ xs) → φ.Realize v xs)
    else (φ.Realize v xs → φ.Realize (f ∘ v) (f ∘ xs)) := by
  induction φ generalizing s with
  | falsum => cases s <;> simp
  | equal =>
    cases s <;>
      simp only [Bool.false_eq_true, ↓reduceIte, realize_equal, ← Sum.comp_elim,
        HomClass.realize_term, EmbeddingLike.apply_eq_iff_eq f, imp_self]
  | rel R ts =>
    have h := StrongHomClass.map_rel f R (fun i => (ts i).realize (Sum.elim v xs))
    cases s <;>
      simp only [Bool.false_eq_true, ↓reduceIte, realize_rel, ← Sum.comp_elim,
        HomClass.realize_term]
    · exact h.mpr
    · exact h.mp
  | imp φ ψ ihφ ihψ =>
    rw [universalSigned_imp] at hφ
    cases s <;> simp only [Bool.not_false, Bool.not_true] at hφ
    · exact fun h hφ' => ihψ hφ.2 xs (h (ihφ hφ.1 xs hφ'))
    · exact fun h hφ' => ihψ hφ.2 xs (h (ihφ hφ.1 xs hφ'))
  | all φ ih =>
    obtain ⟨rfl, hφ⟩ := (universalSigned_all s φ).mp hφ
    intro h y
    have hy := h (f y)
    rw [← Fin.comp_snoc] at hy
    exact ih hφ (Fin.snoc xs y) hy
  | iSup φs ih =>
    rw [universalSigned_iSup] at hφ
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, realize_iSup]
    · rintro ⟨i, hi⟩; exact ⟨i, ih i (hφ i) xs hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i, ih i (hφ i) xs hi⟩
  | iInf φs ih =>
    rw [universalSigned_iInf] at hφ
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, realize_iInf]
    · exact fun h i => ih i (hφ i) xs (h i)
    · exact fun h i => ih i (hφ i) xs (h i)

/-- Universal infinitary formulas are preserved on passing to an embedded substructure. -/
theorem IsUniversal.realize_of_embedding {φ : L.BoundedFormulaInf ι α n} (hφ : φ.IsUniversal)
    (f : F) {v : α → M} {xs : Fin n → M}
    (h : φ.Realize (f ∘ v) (f ∘ xs)) : φ.Realize v xs :=
  universalSigned.realize_embedding hφ f v xs h

/-- Existential infinitary formulas are preserved on passing to an extension. -/
theorem IsExistential.realize_embedding {φ : L.BoundedFormulaInf ι α n} (hφ : φ.IsExistential)
    (f : F) {v : α → M} {xs : Fin n → M}
    (h : φ.Realize v xs) : φ.Realize (f ∘ v) (f ∘ xs) :=
  universalSigned.realize_embedding hφ f v xs h

/-- A universal sentence true in the target of an embedding is true in its source. -/
theorem IsUniversal.realize_sentence_of_embedding {φ : L.SentenceInf ι} (hφ : φ.IsUniversal)
    (f : F) (h : φ.Realize N) : φ.Realize M := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def] at h ⊢
  apply hφ.realize_of_embedding f
  simpa only [Subsingleton.elim (f ∘ (Empty.elim : Empty → M)) Empty.elim,
    Unique.eq_default (f ∘ (default : Fin 0 → M))] using h

/-- An existential sentence true in the source of an embedding is true in its target. -/
theorem IsExistential.realize_sentence_embedding {φ : L.SentenceInf ι} (hφ : φ.IsExistential)
    (f : F) (h : φ.Realize M) : φ.Realize N := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def] at h ⊢
  simpa only [Subsingleton.elim (f ∘ (Empty.elim : Empty → M)) Empty.elim,
    Unique.eq_default (f ∘ (default : Fin 0 → M))] using hφ.realize_embedding f h

end Preservation
end BoundedFormulaInf
end FirstOrder.Language
