/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.AElementary
public import TauCeti.ModelTheory.Infinitary.Equiv
public import TauCeti.ModelTheory.Infinitary.LanguageMap
public import TauCeti.ModelTheory.Infinitary.Substitution
public import TauCeti.ModelTheory.Infinitary.SubstBounds

/-!
# The Morleyization of a language by a family of infinitary formulas

Given a set `Φ` of tagged `L_{ω₁ω}` formulas `⟨n, φ⟩`, with `φ` having `n` bound positions and no
free variables, the **Morleyization** `morleyize L Φ` adds to `L` one new `n`-ary relation symbol
`R_φ` for each member. Every `L`-structure has a **canonical expansion** `morleyExpansion Φ M`,
interpreting `R_φ(a)` as `φ(a)`; nothing is chosen, so the construction commutes with
isomorphisms and with embeddings that preserve the members of `Φ`.

This is how infinitary information is made atomic. The canonical expansion is the unique model,
among expansions, of the *defining theory* `∀ xs, (R_φ(xs) ↔ φ(xs))`
(`eq_morleyExpansion_of_model_definingTheory`), and every formula of the Morleyization has a
back-translation into `L`, replacing each atom `R_φ(ts)` by `φ` at the terms `ts`, that it is
equivalent to in the canonical expansion (`BoundedFormulaInf.realize_unMorleyize`). For a fragment
`A`, the `A`-elementary embeddings are exactly the embeddings of canonical expansions
(`exists_morleyEmbedding_iff_aElementary`). The first-order presentation of a countable fragment
by a theory and omitted types of the Morleyization rests on this material.

## Main definitions

* `FirstOrder.Language.morleyize`: the Morleyization of `L` by `Φ`, and `morleyRel`, the relation
  symbol of a member.
* `FirstOrder.Language.lhomMorleyize`: the inclusion of `L` into its Morleyization.
* `FirstOrder.Language.morleyExpansion`: the canonical expansion of an `L`-structure.
* `FirstOrder.Language.definingTheory`: the sentences `∀ xs, (R_φ(xs) ↔ φ(xs))`.
* `FirstOrder.Language.BoundedFormulaInf.unMorleyize`: the back-translation into `L`.
* `FirstOrder.Language.Equiv.morleyEquiv`: the lift of an isomorphism to the canonical expansions.

## Main results

* `FirstOrder.Language.eq_morleyExpansion_of_model_definingTheory`: an expansion that models the
  defining theory is the canonical expansion, which does model it (`definingTheory_model`).
* `FirstOrder.Language.BoundedFormulaInf.realize_unMorleyize`: a formula of the Morleyization
  holds in the canonical expansion exactly when its back-translation holds.
* `FirstOrder.Language.nonempty_morleyEquiv_iff`: canonical expansions are isomorphic exactly when
  the structures are.
* `FirstOrder.Language.exists_morleyEmbedding_iff_aElementary`: an embedding lifts to an embedding
  of the canonical expansions by a fragment exactly when it is elementary for the fragment.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1
  (Morleyization of a countable fragment).
* M. Morley, *Omitting classes of elements*, in *The Theory of Models*, North-Holland, 1965,
  265–273.
-/

public section

universe u v w w' uα uβ

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-! ### The Morleyized language -/

/-- The **Morleyization** of `L` by a family `Φ` of tagged formulas: the function symbols of `L`,
and as `n`-ary relation symbols those of `L` together with one symbol `R_φ` for each member
`⟨n, φ⟩` of `Φ`. No closure property of `Φ` is assumed.

It is not built as a `Language.sum` with a relational language, so that its function symbols are
literally those of `L`. It is an abbreviation, as `Language.sum` is: a structure on the
Morleyization is given by cases on the sum type of relation symbols. -/
abbrev morleyize (L : Language.{u, v}) (Φ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Language.{u, max u v} where
  Functions := L.Functions
  Relations n := L.Relations n ⊕ {φ : L.BoundedFormulaω Empty n // ⟨n, φ⟩ ∈ Φ}

variable {Φ : Set (Σ n, L.BoundedFormulaω Empty n)}

/-- The relation symbol `R_φ` of the Morleyization attached to a member `⟨n, φ⟩` of `Φ`. -/
abbrev morleyRel {n : ℕ} (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ Φ) :
    (morleyize L Φ).Relations n :=
  Sum.inr ⟨φ, hφ⟩

/-- The Morleyization of a relational language is relational: it has the function symbols
of `L`. -/
instance isRelational_morleyize [L.IsRelational] : (morleyize L Φ).IsRelational :=
  fun n => (inferInstance : IsEmpty (L.Functions n))

/-- Morleyizing a language with countably many relation symbols by a countable family keeps the
relation symbols countable. No countability of the function symbols is involved. -/
theorem countable_relations_morleyize [Countable (Σ n, L.Relations n)] (hΦ : Φ.Countable) :
    Countable (Σ n, (morleyize L Φ).Relations n) := by
  have := hΦ.to_subtype
  let e : (Σ n, (morleyize L Φ).Relations n) → (Σ n, L.Relations n) ⊕ Φ
    | ⟨n, Sum.inl R⟩ => Sum.inl ⟨n, R⟩
    | ⟨n, Sum.inr φ⟩ => Sum.inr ⟨⟨n, φ.1⟩, φ.2⟩
  refine Function.Injective.countable (f := e) ?_
  rintro ⟨n, R | ⟨φ, hφ⟩⟩ ⟨m, R' | ⟨ψ, hψ⟩⟩ h <;>
    simp only [e, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Subtype.mk.injEq,
      Sigma.mk.injEq] at h
  · obtain ⟨rfl, ⟨⟩⟩ := h
    rfl
  · obtain ⟨rfl, ⟨⟩⟩ := h
    rfl

variable (Φ) in
/-- The inclusion of `L` into its Morleyization: function symbols are kept and each relation
symbol of `L` goes to itself. -/
def lhomMorleyize : L →ᴸ morleyize L Φ where
  onFunction _ f := f
  onRelation _ R := Sum.inl R

@[simp]
theorem lhomMorleyize_onFunction {n : ℕ} (f : L.Functions n) :
    (lhomMorleyize Φ).onFunction f = f := (rfl)

@[simp]
theorem lhomMorleyize_onRelation {n : ℕ} (R : L.Relations n) :
    (lhomMorleyize Φ).onRelation R = Sum.inl R := (rfl)

/-- The inclusion of `L` into its Morleyization is injective on symbols. -/
theorem lhomMorleyize_injective : (lhomMorleyize Φ).Injective :=
  ⟨fun h => h, fun h => Sum.inl_injective h⟩

/-! ### The canonical expansion -/

section Expansion

variable (Φ) (M : Type w) [L.Structure M]

/-- The **canonical expansion** of an `L`-structure to the Morleyization: the symbols of `L`
keep their interpretation, and `R_φ(a)` holds exactly when `φ` holds of `a`. -/
@[instance_reducible]
def morleyExpansion : (morleyize L Φ).Structure M where
  funMap f x := Structure.funMap (L := L) f x
  RelMap
    | Sum.inl R, x => Structure.RelMap R x
    | Sum.inr φ, x => φ.1.Realize Empty.elim x

variable {Φ M}

@[simp]
theorem morleyExpansion_funMap {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    (morleyExpansion Φ M).funMap f x = Structure.funMap (L := L) f x := (rfl)

@[simp]
theorem morleyExpansion_relMap_inl {n : ℕ} (R : L.Relations n) (x : Fin n → M) :
    (morleyExpansion Φ M).RelMap (Sum.inl R) x ↔ Structure.RelMap R x := Iff.rfl

/-- In the canonical expansion, `R_φ` holds of a tuple exactly when `φ` does. -/
@[simp]
theorem morleyExpansion_relMap_morleyRel {n : ℕ} {φ : L.BoundedFormulaω Empty n}
    (hφ : ⟨n, φ⟩ ∈ Φ) (x : Fin n → M) :
    (morleyExpansion Φ M).RelMap (morleyRel φ hφ) x ↔ φ.Realize Empty.elim x := Iff.rfl

/-- The canonical expansion is an expansion along the inclusion of `L`. -/
instance isExpansionOn_morleyExpansion :
    @LHom.IsExpansionOn L (morleyize L Φ) (lhomMorleyize Φ) M _ (morleyExpansion Φ M) :=
  @LHom.IsExpansionOn.mk L (morleyize L Φ) (lhomMorleyize Φ) M _ (morleyExpansion Φ M)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The reduct of the canonical expansion is the original structure. -/
theorem reduct_morleyExpansion :
    @LHom.reduct L (morleyize L Φ) (lhomMorleyize Φ) M (morleyExpansion Φ M) = ‹L.Structure M› :=
  (rfl)

end Expansion

/-! ### The defining theory -/

variable (Φ) in
/-- The **defining axiom** `∀ xs, (R_φ(xs) ↔ φ(xs))` of the relation symbol of a member `⟨n, φ⟩`,
where `φ` is read in the Morleyization. -/
def definingAxiom {n : ℕ} (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ Φ) :
    (morleyize L Φ).Sentenceω :=
  ((BoundedFormulaInf.rel (morleyRel φ hφ) fun i => Term.var (Sum.inr i)).iff
    ((lhomMorleyize Φ).onBoundedFormulaInf φ)).alls

variable (Φ) in
/-- The **defining theory** of the Morleyization: the defining axioms of all members of `Φ`. -/
def definingTheory : (morleyize L Φ).Theoryω :=
  Set.range fun p : Φ => definingAxiom Φ p.1.2 p.2

theorem mem_definingTheory {ψ : (morleyize L Φ).Sentenceω} :
    ψ ∈ definingTheory Φ ↔
      ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ Φ), definingAxiom Φ φ hφ = ψ := by
  simp only [definingTheory, Set.mem_range, Subtype.exists, Sigma.exists]

/-- The defining theory of a countable family is countable. -/
theorem countable_definingTheory (hΦ : Φ.Countable) : (definingTheory Φ).Countable := by
  have := hΦ.to_subtype
  exact Set.countable_range _

section DefiningTheory

variable {M : Type w} [L.Structure M]

/-- In an expansion of an `L`-structure to the Morleyization, the defining axiom of `R_φ` holds
exactly when `R_φ` is interpreted as `φ`. -/
theorem realize_definingAxiom_iff (S : (morleyize L Φ).Structure M)
    [@LHom.IsExpansionOn L (morleyize L Φ) (lhomMorleyize Φ) M _ S] {n : ℕ}
    {φ : L.BoundedFormulaω Empty n} (hφ : ⟨n, φ⟩ ∈ Φ) :
    @SentenceInf.Realize _ ℕ (definingAxiom Φ φ hφ) M S ↔
      ∀ x : Fin n → M, S.RelMap (morleyRel φ hφ) x ↔ φ.Realize Empty.elim x := by
  rw [SentenceInf.realize_def, FormulaInf.realize_def, definingAxiom,
    BoundedFormulaInf.realize_alls]
  refine forall_congr' fun x => ?_
  simp only [BoundedFormulaInf.realize_iff, BoundedFormulaInf.realize_rel,
    LHom.realize_onBoundedFormulaInf, Term.realize_var, Sum.elim_inr]

/-- An expansion of an `L`-structure models the defining theory exactly when each `R_φ` is
interpreted as `φ`. -/
theorem model_definingTheory_iff (S : (morleyize L Φ).Structure M)
    [@LHom.IsExpansionOn L (morleyize L Φ) (lhomMorleyize Φ) M _ S] :
    @Theoryω.Model _ (definingTheory Φ) M S ↔
      ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ Φ) (x : Fin n → M),
        S.RelMap (morleyRel φ hφ) x ↔ φ.Realize Empty.elim x := by
  simp only [Theoryω.model_iff, mem_definingTheory, forall_exists_index]
  constructor
  · intro h n φ hφ
    exact (realize_definingAxiom_iff S hφ).1 (h _ n φ hφ rfl)
  · rintro h _ n φ hφ rfl
    exact (realize_definingAxiom_iff S hφ).2 (h φ hφ)

/-- The canonical expansion models the defining theory. -/
theorem definingTheory_model :
    @Theoryω.Model _ (definingTheory Φ) M (morleyExpansion Φ M) :=
  (model_definingTheory_iff _).2 fun _ _ _ => Iff.rfl

/-- **Uniqueness of the canonical expansion.** An expansion of an `L`-structure to the
Morleyization that models the defining theory is the canonical expansion. -/
theorem eq_morleyExpansion_of_model_definingTheory (S : (morleyize L Φ).Structure M)
    [hS : @LHom.IsExpansionOn L (morleyize L Φ) (lhomMorleyize Φ) M _ S]
    (h : @Theoryω.Model _ (definingTheory Φ) M S) : S = morleyExpansion Φ M := by
  have hrel := @(model_definingTheory_iff S).1 h
  refine Structure.ext (funext fun n => funext fun f => funext fun x => ?_)
    (funext fun n => funext fun R => funext fun x => ?_)
  · exact hS.map_onFunction f x
  · rcases R with R | ⟨φ, hφ⟩
    · exact hS.map_onRelation R x
    · exact propext (hrel φ hφ x)

end DefiningTheory

/-! ### Back-translation into `L` -/

namespace Term

variable {β : Type uβ}

/-- A term of the Morleyization as a term of `L`: the two languages have the same function
symbols. -/
def unMorleyize : (morleyize L Φ).Term β → L.Term β
  | var b => var b
  | func f ts => func f fun i => (ts i).unMorleyize

@[simp]
theorem unMorleyize_var (b : β) : (var b : (morleyize L Φ).Term β).unMorleyize = var b := (rfl)

@[simp]
theorem unMorleyize_func {n : ℕ} (f : L.Functions n) (ts : Fin n → (morleyize L Φ).Term β) :
    (func (L := morleyize L Φ) f ts).unMorleyize = func f fun i => (ts i).unMorleyize :=
  (rfl)

/-- Translating a term of `L` into the Morleyization and back gives the term. -/
@[simp]
theorem unMorleyize_onTerm (t : L.Term β) : ((lhomMorleyize Φ).onTerm t).unMorleyize = t := by
  induction t with
  | var b => rfl
  | func f ts ih => simp [LHom.onTerm, ih]

/-- Translating a term of the Morleyization back to `L` and then into the Morleyization gives the
term. -/
@[simp]
theorem onTerm_unMorleyize (t : (morleyize L Φ).Term β) :
    (lhomMorleyize Φ).onTerm t.unMorleyize = t := by
  induction t with
  | var b => rfl
  | func f ts ih => simp [LHom.onTerm, ih]

/-- A term of the Morleyization takes the same value in the canonical expansion as its
back-translation does in the original structure. -/
@[simp]
theorem realize_unMorleyize {M : Type w} [L.Structure M] (t : (morleyize L Φ).Term β)
    (v : β → M) :
    t.unMorleyize.realize v = (letI := morleyExpansion Φ M; t.realize v) := by
  rw [← onTerm_unMorleyize t]
  let := morleyExpansion Φ M
  rw [LHom.realize_onTerm, unMorleyize_onTerm]

end Term

namespace BoundedFormulaInf

variable {α : Type uα} {n : ℕ}

/-- The **back-translation** of a formula of the Morleyization into `L`: an atom `R_φ(ts)` of the
relation symbol of a member becomes `φ` with the back-translated terms `ts` substituted for its
bound positions; atoms of `L` and equations keep their symbols, and connectives and quantifiers
are translated structurally. -/
def unMorleyize : ∀ {n : ℕ}, (morleyize L Φ).BoundedFormulaω α n → L.BoundedFormulaω α n
  | _, falsum => falsum
  | _, equal t₁ t₂ => equal t₁.unMorleyize t₂.unMorleyize
  | _, rel (Sum.inl R) ts => rel R fun i => (ts i).unMorleyize
  | _, rel (Sum.inr φ) ts =>
      substBounds (fun i => (ts i).unMorleyize) (TauCeti.BoundedFormulaInf.subst φ.1 Empty.elim)
  | _, imp φ ψ => φ.unMorleyize.imp ψ.unMorleyize
  | _, all φ => φ.unMorleyize.all
  | _, iSup φs => iSup fun i => (φs i).unMorleyize
  | _, iInf φs => iInf fun i => (φs i).unMorleyize

@[simp]
theorem unMorleyize_falsum :
    (falsum : (morleyize L Φ).BoundedFormulaω α n).unMorleyize = falsum := (rfl)

@[simp]
theorem unMorleyize_equal (t₁ t₂ : (morleyize L Φ).Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : (morleyize L Φ).BoundedFormulaω α n).unMorleyize =
      equal t₁.unMorleyize t₂.unMorleyize := (rfl)

/-- An atom of a relation symbol of `L` back-translates to the same atom. -/
@[simp]
theorem unMorleyize_rel_inl {l : ℕ} (R : L.Relations l)
    (ts : Fin l → (morleyize L Φ).Term (α ⊕ Fin n)) :
    (rel (Sum.inl R) ts : (morleyize L Φ).BoundedFormulaω α n).unMorleyize =
      rel R fun i => (ts i).unMorleyize := (rfl)

/-- An atom `R_φ(ts)` back-translates to `φ` with the terms `ts` substituted for its bound
positions. -/
@[simp]
theorem unMorleyize_rel_morleyRel {l : ℕ} {φ : L.BoundedFormulaω Empty l} (hφ : ⟨l, φ⟩ ∈ Φ)
    (ts : Fin l → (morleyize L Φ).Term (α ⊕ Fin n)) :
    (rel (morleyRel φ hφ) ts : (morleyize L Φ).BoundedFormulaω α n).unMorleyize =
      substBounds (fun i => (ts i).unMorleyize) (TauCeti.BoundedFormulaInf.subst φ Empty.elim) :=
  (rfl)

@[simp]
theorem unMorleyize_imp (φ ψ : (morleyize L Φ).BoundedFormulaω α n) :
    (φ.imp ψ).unMorleyize = φ.unMorleyize.imp ψ.unMorleyize := (rfl)

@[simp]
theorem unMorleyize_all (φ : (morleyize L Φ).BoundedFormulaω α (n + 1)) :
    φ.all.unMorleyize = φ.unMorleyize.all := (rfl)

@[simp]
theorem unMorleyize_iSup (φs : ℕ → (morleyize L Φ).BoundedFormulaω α n) :
    (iSup φs).unMorleyize = iSup fun i => (φs i).unMorleyize := (rfl)

@[simp]
theorem unMorleyize_iInf (φs : ℕ → (morleyize L Φ).BoundedFormulaω α n) :
    (iInf φs).unMorleyize = iInf fun i => (φs i).unMorleyize := (rfl)

@[simp]
theorem unMorleyize_not (φ : (morleyize L Φ).BoundedFormulaω α n) :
    φ.not.unMorleyize = φ.unMorleyize.not := (rfl)

@[simp]
theorem unMorleyize_bot : (⊥ : (morleyize L Φ).BoundedFormulaω α n).unMorleyize = ⊥ := (rfl)

@[simp]
theorem unMorleyize_top : (⊤ : (morleyize L Φ).BoundedFormulaω α n).unMorleyize = ⊤ := by
  rw [top_def, top_def, unMorleyize_not, unMorleyize_falsum]

@[simp]
theorem unMorleyize_ex (φ : (morleyize L Φ).BoundedFormulaω α (n + 1)) :
    φ.ex.unMorleyize = φ.unMorleyize.ex := (rfl)

@[simp]
theorem unMorleyize_iff (φ ψ : (morleyize L Φ).BoundedFormulaω α n) :
    (φ.iff ψ).unMorleyize = φ.unMorleyize.iff ψ.unMorleyize := by
  simp only [iff_def, inf_def, unMorleyize_not, unMorleyize_imp]

/-- **The back-translation is faithful.** A formula of the Morleyization holds in the canonical
expansion exactly when its back-translation holds in the original structure. -/
@[simp]
theorem realize_unMorleyize {M : Type w} [L.Structure M] (φ : (morleyize L Φ).BoundedFormulaω α n)
    (v : α → M) (xs : Fin n → M) :
    φ.unMorleyize.Realize v xs ↔ (letI := morleyExpansion Φ M; φ.Realize v xs) := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts =>
    rcases R with R | ⟨φ, hφ⟩
    · simp
    · simp only [unMorleyize_rel_morleyRel hφ, realize_substBounds,
        TauCeti.BoundedFormulaInf.realize_subst, realize_rel, morleyExpansion_relMap_morleyRel,
        Term.realize_unMorleyize]
      -- the two valuations of the absent free variables agree
      exact iff_of_eq (congrArg₂ _ (Subsingleton.elim _ _) rfl)
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Translating a formula of `L` into the Morleyization and back gives the formula. -/
@[simp]
theorem unMorleyize_onBoundedFormulaInf (φ : L.BoundedFormulaω α n) :
    ((lhomMorleyize Φ).onBoundedFormulaInf φ).unMorleyize = φ := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

end BoundedFormulaInf

/-! ### Isomorphisms -/

section Equiv

variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- An isomorphism of `L`-structures, as an isomorphism of their canonical expansions with the
same underlying bijection: isomorphisms preserve every infinitary formula. -/
def Equiv.morleyEquiv (e : M ≃[L] N) (Φ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    letI := morleyExpansion Φ M
    letI := morleyExpansion Φ N
    M ≃[Language.morleyize L Φ] N :=
  letI := morleyExpansion Φ M
  letI := morleyExpansion Φ N
  { e.toEquiv with
    map_fun' := fun f x => e.map_fun f x
    map_rel' := fun R x => by
      rcases R with R | ⟨φ, hφ⟩
      · exact e.map_rel R x
      · have := StrongHomClass.realize_boundedFormulaInf e φ (v := Empty.elim) (xs := x)
        rwa [Subsingleton.elim (e ∘ (Empty.elim : Empty → M)) Empty.elim] at this }

@[simp]
theorem Equiv.coe_morleyEquiv (e : M ≃[L] N) : ⇑(e.morleyEquiv Φ) = ⇑e := (rfl)

/-- An isomorphism of canonical expansions restricts to an isomorphism of the `L`-structures with
the same underlying bijection. -/
def Equiv.ofMorleyEquiv
    (e : letI := morleyExpansion Φ M; letI := morleyExpansion Φ N; M ≃[Language.morleyize L Φ] N) :
    M ≃[L] N :=
  letI := morleyExpansion Φ M
  letI := morleyExpansion Φ N
  { e.toEquiv with
    map_fun' := fun f x => e.map_fun (L := Language.morleyize L Φ) f x
    map_rel' := fun R x => e.map_rel (L := Language.morleyize L Φ) (Sum.inl R) x }

@[simp]
theorem Equiv.coe_ofMorleyEquiv
    (e : letI := morleyExpansion Φ M; letI := morleyExpansion Φ N; M ≃[Language.morleyize L Φ] N) :
    ⇑(Equiv.ofMorleyEquiv e) = ⇑e := (rfl)

variable (Φ) in
/-- The canonical expansions of two `L`-structures are isomorphic exactly when the structures
are. -/
theorem nonempty_morleyEquiv_iff :
    letI := morleyExpansion Φ M
    letI := morleyExpansion Φ N
    Nonempty (M ≃[morleyize L Φ] N) ↔ Nonempty (M ≃[L] N) :=
  ⟨fun ⟨e⟩ => ⟨Equiv.ofMorleyEquiv e⟩, fun ⟨e⟩ => ⟨e.morleyEquiv Φ⟩⟩

end Equiv

/-! ### Fragment-elementary embeddings -/

variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- **Elementarity as an embedding of Morleyizations.** For a fragment `A`, an embedding of
`L`-structures is `A`-elementary exactly when its underlying map is an embedding of the canonical
expansions by `A`. Such a lift is unique, since an embedding is determined by its underlying
map. -/
theorem exists_morleyEmbedding_iff_aElementary (A : Fragment L) (f : N ↪[L] M) :
    letI := morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) N
    letI := morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) M
    (∃ g : N ↪[morleyize L A] M, ⇑g = ⇑f) ↔ AElementary A f := by
  let := morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) N
  let := morleyExpansion (A : Set (Σ n, L.BoundedFormulaω Empty n)) M
  rw [aElementary_iff]
  constructor
  · rintro ⟨g, hg⟩ n φ hφ a
    have := g.map_rel (morleyRel φ hφ) a
    rwa [hg] at this
  · intro h
    refine ⟨{ toFun := f
              inj' := f.injective
              map_fun' := fun F x => f.map_fun F x
              map_rel' := fun R x => ?_ }, rfl⟩
    rcases R with R | ⟨φ, hφ⟩
    · exact f.map_rel R x
    · exact h φ hφ x

end Language

end FirstOrder
