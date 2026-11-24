/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Semantics
public import Mathlib.ModelTheory.LanguageMap
public import TauCeti.ModelTheory.Infinitary.Operations
public import TauCeti.ModelTheory.Infinitary.Reindex
public import TauCeti.ModelTheory.Infinitary.ToFormula
import TauCeti.ModelTheory.Term.Substitution

/-!
# Language maps on infinitary formulas

A language homomorphism `g : L →ᴸ L'` acts on the infinitary formulas of `L`, at every carrier
`ι`, symbol by symbol: each term is mapped by Mathlib's `LHom.onTerm`, each relation symbol by
`g.onRelation`, and the logical structure is kept. This is the infinitary form of Mathlib's
`LHom.onBoundedFormula`.

When an `L'`-structure on `M` expands an `L`-structure along `g` (`g.IsExpansionOn M`), the image
of a formula is realized exactly when the formula is. Every passage between languages, such as
adding constants or restricting to the symbols a formula mentions, transfers truth through this
result. An injective language map acts injectively, and a language equivalence acts by an
equivalence of formula types, so that translating along it loses no formula.

## Main definitions

* `FirstOrder.Language.LHom.onBoundedFormulaInf`: the action of a language homomorphism on
  infinitary formulas.
* `FirstOrder.Language.LEquiv.onBoundedFormulaInf`: the equivalence of formula types induced by a
  language equivalence.

## Main results

* `FirstOrder.Language.LHom.realize_onBoundedFormulaInf`: along an expansion, the image of a
  formula is realized exactly when the formula is.
* `FirstOrder.Language.LHom.realize_sentenceInf_onBoundedFormulaInf`: its form for sentences.
* `FirstOrder.Language.LHom.id_onBoundedFormulaInf` and
  `FirstOrder.Language.LHom.comp_onBoundedFormulaInf`: the action is functorial.
* `FirstOrder.Language.LHom.onBoundedFormulaInf_toInf`,
  `FirstOrder.Language.LHom.onBoundedFormulaInf_mapBound`,
  `FirstOrder.Language.LHom.onBoundedFormulaInf_castLE`,
  `FirstOrder.Language.LHom.onBoundedFormulaInf_reindex`,
  `FirstOrder.Language.LHom.onBoundedFormulaInf_subst`,
  `FirstOrder.Language.LHom.onBoundedFormulaInf_relabel` and
  `FirstOrder.Language.LHom.onBoundedFormulaInf_toFormula`: the action commutes with the embedding
  of finitary formulas, with relabelling and weakening of bound-variable slots, with transport
  along a coding of carriers, with free-variable substitution and relabelling, and with opening
  bound positions as free variables; along the way it commutes with `⊥`, `⊤`, negation, the binary
  connectives `⊓`, `⊔` and `iff`, existential quantification, the quantifier closures `alls`, `exs`
  and `exsLast`, and the coded connectives `iInfAlong` and `iSupAlong`, and preserves atomicity
  (`FirstOrder.Language.LHom.isAtomic_onBoundedFormulaInf`,
  `FirstOrder.Language.BoundedFormulaInf.IsAtomic.onBoundedFormulaInf`).
* `FirstOrder.Language.LHom.exists_of_onBoundedFormulaInf_eq_imp`,
  `FirstOrder.Language.LHom.exists_of_onBoundedFormulaInf_eq_all`,
  `FirstOrder.Language.LHom.exists_of_onBoundedFormulaInf_eq_iSup` and
  `FirstOrder.Language.LHom.exists_of_onBoundedFormulaInf_eq_iInf`: a language map reflects the
  compound constructors onto preimages, with no injectivity hypothesis.
* `FirstOrder.Language.LHom.Injective.onBoundedFormulaInf_injective`: an injective language map
  acts injectively on infinitary formulas.
* `FirstOrder.Language.LEquiv.onBoundedFormulaInf_refl` and
  `FirstOrder.Language.LEquiv.onBoundedFormulaInf_trans`: the equivalence action respects identity
  and composition of language equivalences.
* `FirstOrder.Language.LEquiv.realize_onBoundedFormulaInf` and
  `FirstOrder.Language.LEquiv.realize_sentenceInf_onBoundedFormulaInf`: realization of formulas and
  sentences is preserved by translation along a language equivalence, the target structure being
  the reduct along the inverse map.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`: `mapLanguage` and `realize_mapLanguage` in
  `InfinitaryLogic/Lomega1omega/Operations.lean`.
* Divergences from that source: the action is defined at every carrier `ι` rather than at `ℕ`,
  between languages in arbitrary universes rather than a common one, and as a method of the
  language homomorphism named after Mathlib's finitary `LHom.onBoundedFormula`; the functor laws,
  commutation with mixed free/bound `relabel`, `toFormula`, `alls`, `exs`, `exsLast` and the binary
  connectives, preservation of `IsAtomic`, constructor inversion, injectivity, and the equivalence
  along a language equivalence (following Mathlib's finitary `LEquiv.onBoundedFormula`) are new or
  generalized to arbitrary carriers and universes.
-/

public section

universe u v u' v' u'' v'' uα uβ uι w

namespace FirstOrder

namespace Language

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}
  {ι : Type uι} {α : Type uα}

/-- The action of a language homomorphism on infinitary formulas: each term is mapped by
`g.onTerm`, each relation symbol by `g.onRelation`, and the logical structure is kept. -/
def onBoundedFormulaInf (g : L →ᴸ L') :
    ∀ {n : ℕ}, L.BoundedFormulaInf ι α n → L'.BoundedFormulaInf ι α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (g.onTerm t₁) (g.onTerm t₂)
  | _, .rel R ts => .rel (g.onRelation R) fun i => g.onTerm (ts i)
  | _, .imp φ ψ => (onBoundedFormulaInf g φ).imp (onBoundedFormulaInf g ψ)
  | _, .all φ => (onBoundedFormulaInf g φ).all
  | _, .iSup φs => .iSup fun i => onBoundedFormulaInf g (φs i)
  | _, .iInf φs => .iInf fun i => onBoundedFormulaInf g (φs i)

section ConstructorEqs

variable (g : L →ᴸ L') {n : ℕ}

/-- A language map fixes the false formula. -/
@[simp]
theorem onBoundedFormulaInf_falsum :
    g.onBoundedFormulaInf (.falsum : L.BoundedFormulaInf ι α n) = .falsum := (rfl)

/-- A language map maps both sides of an equation. -/
@[simp]
theorem onBoundedFormulaInf_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    g.onBoundedFormulaInf (.equal t₁ t₂ : L.BoundedFormulaInf ι α n) =
      .equal (g.onTerm t₁) (g.onTerm t₂) := (rfl)

/-- A language map maps the relation symbol and the terms of a relational atom. -/
@[simp]
theorem onBoundedFormulaInf_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    g.onBoundedFormulaInf (.rel R ts : L.BoundedFormulaInf ι α n) =
      .rel (g.onRelation R) fun i => g.onTerm (ts i) := (rfl)

/-- A language map commutes with implication. -/
@[simp]
theorem onBoundedFormulaInf_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf (φ.imp ψ) = (g.onBoundedFormulaInf φ).imp (g.onBoundedFormulaInf ψ) :=
  (rfl)

/-- A language map commutes with universal quantification. -/
@[simp]
theorem onBoundedFormulaInf_all (φ : L.BoundedFormulaInf ι α (n + 1)) :
    g.onBoundedFormulaInf φ.all = (g.onBoundedFormulaInf φ).all := (rfl)

/-- A language map commutes with disjunctions over the carrier. -/
@[simp]
theorem onBoundedFormulaInf_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf (.iSup φs) = .iSup fun i => g.onBoundedFormulaInf (φs i) := (rfl)

/-- A language map commutes with conjunctions over the carrier. -/
@[simp]
theorem onBoundedFormulaInf_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf (.iInf φs) = .iInf fun i => g.onBoundedFormulaInf (φs i) := (rfl)

end ConstructorEqs

section ConstructorInversion

variable {g : L →ᴸ L'} {n : ℕ}

/-- If the image of a formula under a language map is an implication, the formula is itself an
implication of preimages of the two sides. -/
theorem exists_of_onBoundedFormulaInf_eq_imp {χ : L.BoundedFormulaInf ι α n}
    {φ ψ : L'.BoundedFormulaInf ι α n} (h : g.onBoundedFormulaInf χ = φ.imp ψ) :
    ∃ χ₁ χ₂ : L.BoundedFormulaInf ι α n, χ = χ₁.imp χ₂ ∧
      g.onBoundedFormulaInf χ₁ = φ ∧ g.onBoundedFormulaInf χ₂ = ψ := by
  cases χ <;> simp only [onBoundedFormulaInf_falsum, onBoundedFormulaInf_equal,
    onBoundedFormulaInf_rel, onBoundedFormulaInf_imp, onBoundedFormulaInf_all,
    onBoundedFormulaInf_iSup, onBoundedFormulaInf_iInf, reduceCtorEq,
    BoundedFormulaInf.imp.injEq] at h
  exact ⟨_, _, rfl, h⟩

/-- If the image of a formula under a language map is a universal quantification, the formula is
itself a universal quantification of a preimage of the body. -/
theorem exists_of_onBoundedFormulaInf_eq_all {χ : L.BoundedFormulaInf ι α n}
    {φ : L'.BoundedFormulaInf ι α (n + 1)} (h : g.onBoundedFormulaInf χ = φ.all) :
    ∃ χ₁ : L.BoundedFormulaInf ι α (n + 1), χ = χ₁.all ∧ g.onBoundedFormulaInf χ₁ = φ := by
  cases χ <;> simp only [onBoundedFormulaInf_falsum, onBoundedFormulaInf_equal,
    onBoundedFormulaInf_rel, onBoundedFormulaInf_imp, onBoundedFormulaInf_all,
    onBoundedFormulaInf_iSup, onBoundedFormulaInf_iInf, reduceCtorEq,
    BoundedFormulaInf.all.injEq] at h
  exact ⟨_, rfl, h⟩

/-- If the image of a formula under a language map is a disjunction over the carrier, the formula
is itself a disjunction of preimages of the disjuncts. -/
theorem exists_of_onBoundedFormulaInf_eq_iSup {χ : L.BoundedFormulaInf ι α n}
    {φs : ι → L'.BoundedFormulaInf ι α n} (h : g.onBoundedFormulaInf χ = .iSup φs) :
    ∃ χs : ι → L.BoundedFormulaInf ι α n, χ = .iSup χs ∧
      ∀ i, g.onBoundedFormulaInf (χs i) = φs i := by
  cases χ <;> simp only [onBoundedFormulaInf_falsum, onBoundedFormulaInf_equal,
    onBoundedFormulaInf_rel, onBoundedFormulaInf_imp, onBoundedFormulaInf_all,
    onBoundedFormulaInf_iSup, onBoundedFormulaInf_iInf, reduceCtorEq,
    BoundedFormulaInf.iSup.injEq] at h
  exact ⟨_, rfl, congrFun h⟩

/-- If the image of a formula under a language map is a conjunction over the carrier, the formula
is itself a conjunction of preimages of the conjuncts. -/
theorem exists_of_onBoundedFormulaInf_eq_iInf {χ : L.BoundedFormulaInf ι α n}
    {φs : ι → L'.BoundedFormulaInf ι α n} (h : g.onBoundedFormulaInf χ = .iInf φs) :
    ∃ χs : ι → L.BoundedFormulaInf ι α n, χ = .iInf χs ∧
      ∀ i, g.onBoundedFormulaInf (χs i) = φs i := by
  cases χ <;> simp only [onBoundedFormulaInf_falsum, onBoundedFormulaInf_equal,
    onBoundedFormulaInf_rel, onBoundedFormulaInf_imp, onBoundedFormulaInf_all,
    onBoundedFormulaInf_iSup, onBoundedFormulaInf_iInf, reduceCtorEq,
    BoundedFormulaInf.iInf.injEq] at h
  exact ⟨_, rfl, congrFun h⟩

end ConstructorInversion

/-- **Realization along an expansion.** If the `L'`-structure on `M` expands its `L`-structure
along `g`, the image of an infinitary formula under `g` is realized exactly when the formula is.
This is the infinitary form of Mathlib's `LHom.realize_onBoundedFormula`. -/
@[simp]
theorem realize_onBoundedFormulaInf (g : L →ᴸ L') {M : Type w} [L.Structure M] [L'.Structure M]
    [g.IsExpansionOn M] {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M) :
    (g.onBoundedFormulaInf φ).Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [BoundedFormulaInf.realize_equal, realize_onTerm]
  | rel R ts => simp [BoundedFormulaInf.realize_rel, realize_onTerm, map_onRelation]
  | imp φ ψ ihφ ihψ => simp [BoundedFormulaInf.realize_imp, ihφ, ihψ]
  | all φ ih => simp [BoundedFormulaInf.realize_all, ih]
  | iSup φs ih => simp [BoundedFormulaInf.realize_iSup, ih]
  | iInf φs ih => simp [BoundedFormulaInf.realize_iInf, ih]

/-- **Realization of sentences along an expansion.** If the `L'`-structure on `M` expands its
`L`-structure along `g`, the image of an infinitary sentence under `g` holds exactly when the
sentence does. -/
@[simp]
theorem realize_sentenceInf_onBoundedFormulaInf (g : L →ᴸ L') {M : Type w} [L.Structure M]
    [L'.Structure M] [g.IsExpansionOn M] (φ : L.SentenceInf ι) :
    SentenceInf.Realize (g.onBoundedFormulaInf φ) M ↔ SentenceInf.Realize φ M := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_onBoundedFormulaInf]

/-- The identity language map acts as the identity on infinitary formulas. -/
@[simp]
theorem id_onBoundedFormulaInf {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    (LHom.id L).onBoundedFormulaInf φ = φ := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- The action of a composite language map is the composite of the actions. -/
@[simp]
theorem comp_onBoundedFormulaInf (g : L' →ᴸ L'') (f : L →ᴸ L') {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) :
    (g.comp f).onBoundedFormulaInf φ = g.onBoundedFormulaInf (f.onBoundedFormulaInf φ) := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-! ### Commutation with the operations on formulas -/

section Connectives

variable (g : L →ᴸ L') {n : ℕ}

/-- A language map fixes `⊥`. -/
@[simp]
theorem onBoundedFormulaInf_bot :
    g.onBoundedFormulaInf (⊥ : L.BoundedFormulaInf ι α n) = ⊥ := by
  rw [BoundedFormulaInf.bot_def, BoundedFormulaInf.bot_def, onBoundedFormulaInf_falsum]

/-- A language map commutes with negation. -/
@[simp]
theorem onBoundedFormulaInf_not (φ : L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf φ.not = (g.onBoundedFormulaInf φ).not := by
  rw [BoundedFormulaInf.not, BoundedFormulaInf.not, onBoundedFormulaInf_imp,
    onBoundedFormulaInf_falsum]

/-- A language map commutes with existential quantification. -/
@[simp]
theorem onBoundedFormulaInf_ex (φ : L.BoundedFormulaInf ι α (n + 1)) :
    g.onBoundedFormulaInf φ.ex = (g.onBoundedFormulaInf φ).ex := by
  rw [BoundedFormulaInf.ex, BoundedFormulaInf.ex, onBoundedFormulaInf_not, onBoundedFormulaInf_all,
    onBoundedFormulaInf_not]

/-- A language map fixes `⊤`. -/
@[simp]
theorem onBoundedFormulaInf_top :
    g.onBoundedFormulaInf (⊤ : L.BoundedFormulaInf ι α n) = ⊤ := by
  rw [BoundedFormulaInf.top_def, BoundedFormulaInf.top_def, onBoundedFormulaInf_not,
    onBoundedFormulaInf_falsum]

/-- A language map commutes with binary conjunction. -/
@[simp]
theorem onBoundedFormulaInf_inf (φ ψ : L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf (φ ⊓ ψ) = g.onBoundedFormulaInf φ ⊓ g.onBoundedFormulaInf ψ := by
  rw [BoundedFormulaInf.inf_def, BoundedFormulaInf.inf_def, onBoundedFormulaInf_not,
    onBoundedFormulaInf_imp, onBoundedFormulaInf_not]

/-- A language map commutes with binary disjunction. -/
@[simp]
theorem onBoundedFormulaInf_sup (φ ψ : L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf (φ ⊔ ψ) = g.onBoundedFormulaInf φ ⊔ g.onBoundedFormulaInf ψ := by
  rw [BoundedFormulaInf.sup_def, BoundedFormulaInf.sup_def, onBoundedFormulaInf_imp,
    onBoundedFormulaInf_not]

/-- A language map commutes with the biconditional. -/
@[simp]
theorem onBoundedFormulaInf_iff (φ ψ : L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf (φ.iff ψ) =
      (g.onBoundedFormulaInf φ).iff (g.onBoundedFormulaInf ψ) := by
  rw [BoundedFormulaInf.iff_def, BoundedFormulaInf.iff_def, onBoundedFormulaInf_inf,
    onBoundedFormulaInf_imp, onBoundedFormulaInf_imp]

/-- A language map commutes with coded conjunctions. -/
@[simp]
theorem onBoundedFormulaInf_iInfAlong {ι' : Type*} (c : TauCeti.IndexCoding ι' ι)
    (φs : ι' → L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf (BoundedFormulaInf.iInfAlong c φs) =
      BoundedFormulaInf.iInfAlong c fun i => g.onBoundedFormulaInf (φs i) := by
  rw [BoundedFormulaInf.iInfAlong_def, BoundedFormulaInf.iInfAlong_def, onBoundedFormulaInf_iInf]
  -- padding with `⊤` commutes with the map, which fixes `⊤`
  have := TauCeti.IndexCoding.comp_pad c g.onBoundedFormulaInf ⊤ φs
  rw [onBoundedFormulaInf_top] at this
  exact congrArg _ this

/-- A language map commutes with coded disjunctions. -/
@[simp]
theorem onBoundedFormulaInf_iSupAlong {ι' : Type*} (c : TauCeti.IndexCoding ι' ι)
    (φs : ι' → L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf (BoundedFormulaInf.iSupAlong c φs) =
      BoundedFormulaInf.iSupAlong c fun i => g.onBoundedFormulaInf (φs i) := by
  rw [BoundedFormulaInf.iSupAlong_def, BoundedFormulaInf.iSupAlong_def, onBoundedFormulaInf_iSup]
  -- padding with `⊥` commutes with the map, which fixes `⊥`
  have := TauCeti.IndexCoding.comp_pad c g.onBoundedFormulaInf ⊥ φs
  rw [onBoundedFormulaInf_bot] at this
  exact congrArg _ this

end Connectives

/-- A language map commutes with the universal closure of all bound-variable slots. -/
@[simp]
theorem onBoundedFormulaInf_alls (g : L →ᴸ L') :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ι α n),
      g.onBoundedFormulaInf φ.alls = (g.onBoundedFormulaInf φ).alls := by
  intro n
  induction n with
  | zero =>
    intro φ
    rw [BoundedFormulaInf.alls_zero, BoundedFormulaInf.alls_zero]
  | succ n ih =>
    intro φ
    rw [BoundedFormulaInf.alls_succ, BoundedFormulaInf.alls_succ, ih, onBoundedFormulaInf_all]

/-- A language map commutes with the existential closure of all bound-variable slots. -/
@[simp]
theorem onBoundedFormulaInf_exs (g : L →ᴸ L') :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ι α n),
      g.onBoundedFormulaInf φ.exs = (g.onBoundedFormulaInf φ).exs := by
  intro n
  induction n with
  | zero =>
    intro φ
    rw [BoundedFormulaInf.exs_zero, BoundedFormulaInf.exs_zero]
  | succ n ih =>
    intro φ
    rw [BoundedFormulaInf.exs_succ, BoundedFormulaInf.exs_succ, ih, onBoundedFormulaInf_ex]

/-- A language map commutes with existential quantification over the last `k` bound-variable
slots. -/
@[simp]
theorem onBoundedFormulaInf_exsLast (g : L →ᴸ L') {n : ℕ} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaInf ι α (n + k)),
      g.onBoundedFormulaInf φ.exsLast = (g.onBoundedFormulaInf φ).exsLast := by
  intro k
  induction k with
  | zero =>
    intro φ
    rw [BoundedFormulaInf.exsLast_zero, BoundedFormulaInf.exsLast_zero]
  | succ k ih =>
    intro φ
    rw [BoundedFormulaInf.exsLast_succ, BoundedFormulaInf.exsLast_succ, ih, onBoundedFormulaInf_ex]

/-- The image of an infinitary formula under any language map is atomic if and only if the formula
is atomic; no injectivity on symbols is required. -/
@[simp]
theorem isAtomic_onBoundedFormulaInf (g : L →ᴸ L') {n : ℕ}
    {φ : L.BoundedFormulaInf ι α n} :
    (g.onBoundedFormulaInf φ).IsAtomic ↔ φ.IsAtomic := by
  cases φ with
  | equal t₁ t₂ => exact ⟨fun _ => .equal t₁ t₂, fun _ => .equal _ _⟩
  | rel R ts => exact ⟨fun _ => .rel R ts, fun _ => .rel _ _⟩
  | falsum | imp _ _ | all _ | iSup _ | iInf _ =>
    constructor <;> · rintro ⟨⟩

/-- A language map commutes with the embedding of finitary formulas: translating a finitary
formula and then embedding it is embedding it and then translating. -/
@[simp]
theorem onBoundedFormulaInf_toInf (g : L →ᴸ L') {n : ℕ} (φ : L.BoundedFormula α n) :
    g.onBoundedFormulaInf (φ.toInf : L.BoundedFormulaInf ι α n) = (g.onBoundedFormula φ).toInf := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [Term.bdEqual]
  | rel R ts => simp [LHom.onBoundedFormula, Relations.boundedFormula, Function.comp_def]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

/-- A language map commutes with relabelling the bound-variable slots. -/
@[simp]
theorem onBoundedFormulaInf_mapBound (g : L →ᴸ L') :
    ∀ {m n : ℕ} (f : Fin m → Fin n) (φ : L.BoundedFormulaInf ι α m),
      g.onBoundedFormulaInf (φ.mapBound f) = (g.onBoundedFormulaInf φ).mapBound f := by
  intro m n f φ
  induction φ generalizing n with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- A language map commutes with weakening. -/
@[simp]
theorem onBoundedFormulaInf_castLE (g : L →ᴸ L') {m n : ℕ} (h : m ≤ n)
    (φ : L.BoundedFormulaInf ι α m) :
    g.onBoundedFormulaInf (φ.castLE h) = (g.onBoundedFormulaInf φ).castLE h := by
  rw [BoundedFormulaInf.castLE_def, BoundedFormulaInf.castLE_def, onBoundedFormulaInf_mapBound]

/-- A language map commutes with transporting formulas along a coding of carriers. -/
@[simp]
theorem onBoundedFormulaInf_reindex {κ : Type*} (g : L →ᴸ L') (c : TauCeti.IndexCoding ι κ) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ι α n),
      g.onBoundedFormulaInf (φ.reindex c) = (g.onBoundedFormulaInf φ).reindex c := by
  intro n φ
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- A language map commutes with substituting terms for free variables, acting on each substituted
term by `g.onTerm`. -/
@[simp]
theorem onBoundedFormulaInf_subst {β : Type uβ} (g : L →ᴸ L') {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    g.onBoundedFormulaInf (TauCeti.BoundedFormulaInf.subst φ f) =
      TauCeti.BoundedFormulaInf.subst (g.onBoundedFormulaInf φ) fun a => g.onTerm (f a) := by
  have hatom {k : ℕ} :
      (fun x : α ⊕ Fin k =>
        g.onTerm (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr) x)) =
      Sum.elim (Term.relabel Sum.inl ∘ fun a => g.onTerm (f a)) (Term.var ∘ Sum.inr) := by
    funext x
    cases x <;> simp
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [hatom]
  | rel R ts => simp [hatom]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- A language map commutes with relabelling free variables into free variables and new bound
slots. -/
@[simp]
theorem onBoundedFormulaInf_relabel {β : Type uβ} (g : L →ᴸ L') {m n : ℕ}
    (h : α → β ⊕ Fin m) (φ : L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf (TauCeti.BoundedFormulaInf.relabel h φ) =
      TauCeti.BoundedFormulaInf.relabel h (g.onBoundedFormulaInf φ) := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- A language map commutes with opening the in-scope bound positions as free variables. -/
@[simp]
theorem onBoundedFormulaInf_toFormula (g : L →ᴸ L') {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) :
    g.onBoundedFormulaInf φ.toFormula = (g.onBoundedFormulaInf φ).toFormula := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- **Injectivity along an injective map.** An injective language map acts injectively on
infinitary formulas. -/
theorem Injective.onBoundedFormulaInf_injective {g : L →ᴸ L'} (hg : g.Injective) {n : ℕ} :
    Function.Injective (g.onBoundedFormulaInf : L.BoundedFormulaInf ι α n → _) := by
  intro φ ψ h
  induction φ with
  | falsum =>
    cases ψ with
    | falsum => rfl
    | _ => simp at h
  | equal t₁ t₂ =>
    cases ψ with
    | equal t₁' t₂' =>
      simp only [onBoundedFormulaInf_equal, BoundedFormulaInf.equal.injEq] at h
      rw [hg.onTerm_injective h.1, hg.onTerm_injective h.2]
    | _ => simp at h
  | rel R ts =>
    cases ψ with
    | rel R' ts' =>
      simp only [onBoundedFormulaInf_rel, BoundedFormulaInf.rel.injEq] at h
      obtain ⟨rfl, hR, hts⟩ := h
      rw [hg.onRelation (eq_of_heq hR)]
      exact congrArg _ (funext fun i => hg.onTerm_injective (congrFun (eq_of_heq hts) i))
    | _ => simp at h
  | imp φ₁ φ₂ ih₁ ih₂ =>
    cases ψ with
    | imp ψ₁ ψ₂ =>
      simp only [onBoundedFormulaInf_imp, BoundedFormulaInf.imp.injEq] at h
      rw [ih₁ h.1, ih₂ h.2]
    | _ => simp at h
  | all φ ih =>
    cases ψ with
    | all ψ => rw [ih (BoundedFormulaInf.all.inj h)]
    | _ => simp at h
  | iSup φs ih =>
    cases ψ with
    | iSup ψs =>
      exact congrArg _ (funext fun i => ih i (congrFun (BoundedFormulaInf.iSup.inj h) i))
    | _ => simp at h
  | iInf φs ih =>
    cases ψ with
    | iInf ψs =>
      exact congrArg _ (funext fun i => ih i (congrFun (BoundedFormulaInf.iInf.inj h) i))
    | _ => simp at h

end LHom

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {ι : Type uι} {α : Type uα}

/-- A language map sends atomic infinitary formulas to atomic infinitary formulas. -/
theorem IsAtomic.onBoundedFormulaInf {n : ℕ} {φ : L.BoundedFormulaInf ι α n}
    (h : φ.IsAtomic) (g : L →ᴸ L') : (g.onBoundedFormulaInf φ).IsAtomic :=
  g.isAtomic_onBoundedFormulaInf.2 h

end BoundedFormulaInf

namespace LEquiv

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}
  {ι : Type uι} {α : Type uα}

/-- A language equivalence acts on infinitary formulas by an equivalence, whose inverse is the
action of the inverse map. This is the infinitary form of Mathlib's `LEquiv.onBoundedFormula`. -/
def onBoundedFormulaInf (e : L ≃ᴸ L') {n : ℕ} :
    L.BoundedFormulaInf ι α n ≃ L'.BoundedFormulaInf ι α n where
  toFun := e.toLHom.onBoundedFormulaInf
  invFun := e.invLHom.onBoundedFormulaInf
  left_inv φ := by
    rw [← LHom.comp_onBoundedFormulaInf, e.left_inv, LHom.id_onBoundedFormulaInf]
  right_inv φ := by
    rw [← LHom.comp_onBoundedFormulaInf, e.right_inv, LHom.id_onBoundedFormulaInf]

/-- The action of a language equivalence is the action of its forward map. -/
@[simp]
theorem onBoundedFormulaInf_apply (e : L ≃ᴸ L') {n : ℕ} (φ : L.BoundedFormulaInf ι α n) :
    e.onBoundedFormulaInf φ = e.toLHom.onBoundedFormulaInf φ :=
  (rfl)

/-- The inverse of the action of a language equivalence is the action of its inverse map. -/
@[simp]
theorem onBoundedFormulaInf_symm_apply (e : L ≃ᴸ L') {n : ℕ} (φ : L'.BoundedFormulaInf ι α n) :
    e.onBoundedFormulaInf.symm φ = e.invLHom.onBoundedFormulaInf φ :=
  (rfl)

/-- The inverse of the action of a language equivalence is the action of its inverse. -/
theorem onBoundedFormulaInf_symm (e : L ≃ᴸ L') {n : ℕ} :
    (e.onBoundedFormulaInf.symm : L'.BoundedFormulaInf ι α n ≃ L.BoundedFormulaInf ι α n) =
      e.symm.onBoundedFormulaInf :=
  (rfl)

/-- The identity language equivalence acts as the identity equivalence on infinitary formulas. -/
@[simp]
theorem onBoundedFormulaInf_refl {n : ℕ} :
    ((LEquiv.refl L).onBoundedFormulaInf : L.BoundedFormulaInf ι α n ≃ L.BoundedFormulaInf ι α n) =
      _root_.Equiv.refl _ :=
  _root_.Equiv.ext LHom.id_onBoundedFormulaInf

/-- A composite language equivalence acts as the composite of the equivalences on infinitary
formulas. -/
theorem onBoundedFormulaInf_trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') {n : ℕ} :
    ((e.trans e').onBoundedFormulaInf : L.BoundedFormulaInf ι α n ≃ L''.BoundedFormulaInf ι α n) =
      e.onBoundedFormulaInf.trans e'.onBoundedFormulaInf :=
  _root_.Equiv.ext (LHom.comp_onBoundedFormulaInf e'.toLHom e.toLHom)

/-- **Realization along a language equivalence.** An `L`-structure, reinterpreted as an
`L'`-structure along the inverse map, realizes the translation of an infinitary formula exactly
when it realizes the formula. -/
@[simp]
theorem realize_onBoundedFormulaInf (e : L ≃ᴸ L') {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M) :
    letI := e.invLHom.reduct M
    (e.toLHom.onBoundedFormulaInf φ).Realize v xs ↔ φ.Realize v xs := by
  let := e.invLHom.reduct M
  -- translating back along the inverse map, an expansion of the reduct, gives `φ` again
  rw [← LHom.realize_onBoundedFormulaInf e.invLHom, ← LHom.comp_onBoundedFormulaInf, e.left_inv,
    LHom.id_onBoundedFormulaInf]

/-- **Sentence realization along a language equivalence.** An `L`-structure, reinterpreted as an
`L'`-structure along the inverse map, satisfies the translation of an infinitary sentence exactly
when it satisfies the sentence. -/
@[simp]
theorem realize_sentenceInf_onBoundedFormulaInf (e : L ≃ᴸ L') {M : Type w} [L.Structure M]
    (φ : L.SentenceInf ι) :
    letI := e.invLHom.reduct M
    SentenceInf.Realize (e.toLHom.onBoundedFormulaInf φ) M ↔ SentenceInf.Realize φ M := by
  let := e.invLHom.reduct M
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, e.realize_onBoundedFormulaInf]

end LEquiv

end Language

end FirstOrder
