/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Semantics
public import Mathlib.ModelTheory.LanguageMap

/-!
# Language maps on infinitary formulas

A language homomorphism `g : L →ᴸ L'` acts on the infinitary formulas of `L`, at every carrier
`ι`, symbol by symbol: each term is mapped by Mathlib's `LHom.onTerm`, each relation symbol by
`g.onRelation`, and the logical structure is kept. This is the infinitary form of Mathlib's
`LHom.onBoundedFormula`.

When an `L'`-structure on `M` expands an `L`-structure along `g` (`g.IsExpansionOn M`), the image
of a formula is realized exactly when the formula is. Every passage between languages, such as
adding constants or restricting to the symbols a formula mentions, transfers truth through this
result.

## Main definitions

* `FirstOrder.Language.LHom.onBoundedFormulaInf`: the action of a language homomorphism on
  infinitary formulas.

## Main results

* `FirstOrder.Language.LHom.realize_onBoundedFormulaInf`: along an expansion, the image of a
  formula is realized exactly when the formula is.
* `FirstOrder.Language.LHom.id_onBoundedFormulaInf` and
  `FirstOrder.Language.LHom.comp_onBoundedFormulaInf`: the action is functorial.
* `FirstOrder.Language.LEquiv.realize_onBoundedFormulaInf`: realization is preserved by
  translation along a language equivalence, the target structure being the reduct along the
  inverse map.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`: `mapLanguage` and `realize_mapLanguage` in
  `InfinitaryLogic/Lomega1omega/Operations.lean`.
* Divergences from that source: the action is defined at every carrier `ι` rather than at `ℕ`,
  between languages in arbitrary universes rather than a common one, and as a method of the
  language homomorphism named after Mathlib's finitary `LHom.onBoundedFormula`; the functor laws
  are new.
-/

public section

universe u v u' v' u'' v'' uα uι w

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

end LHom

namespace LEquiv

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {ι : Type uι} {α : Type uα}

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

end LEquiv

end Language

end FirstOrder
