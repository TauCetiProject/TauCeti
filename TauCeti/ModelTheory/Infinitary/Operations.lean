/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Semantics

import TauCeti.Data.Fin.Tuple.Basic

/-!
# Bound-variable relabelling and weakening of infinitary formulas

A bounded formula with `m` bound-variable slots can be relabelled along any map
`f : Fin m → Fin n` of slots. A quantifier binds the last slot, so the relabelling extends `f`
past each quantifier by sending the newly quantified slot to the new last slot. Quantified
variables therefore move with their binders, and the relabelled formula is realized at a valuation
`xs` exactly when the original is realized at `xs ∘ f`. The map `f` need not be injective:
relabelling along it may identify bound variables.

Weakening `castLE` along `m ≤ n` is relabelling along `Fin.castLE`. It corresponds to Mathlib's
finitary weakening `BoundedFormula.liftAt` that inserts the new slots after the `m` existing ones,
not to Mathlib's finitary `BoundedFormula.castLE`, which keeps a quantified variable at its old
slot and so preserves realization only when `m = n`.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.mapBound`: relabelling of bound-variable slots.
* `FirstOrder.Language.BoundedFormulaInf.castLE`: weakening along `m ≤ n`.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.realize_mapBound`: relabelling along `f` is realization
  at `xs ∘ f`.
* `FirstOrder.Language.BoundedFormulaInf.realize_castLE`: weakening is realization at
  `xs ∘ Fin.castLE h`, for every `m ≤ n`.
* `FirstOrder.Language.BoundedFormulaInf.mapBound_id`,
  `FirstOrder.Language.BoundedFormulaInf.mapBound_mapBound`,
  `FirstOrder.Language.BoundedFormulaInf.castLE_rfl` and
  `FirstOrder.Language.BoundedFormulaInf.castLE_castLE`: identity and composition.

## References

* `cameronfreer/infinitary-logic` at commit `9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4` has
  `castLE` at carrier `ℕ` in `InfinitaryLogic/Lomega1omega/Operations.lean`, with realization only
  for equal slot counts.
* Divergences from that source: weakening is defined for every carrier, through the general
  relabelling `mapBound`, which moves quantified variables with their binders, so that realization
  holds for every `m ≤ n`.
-/

public section

universe u v u' uι w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'}

namespace BoundedFormulaInf

/-- Extend a slot map past a quantifier: the new last slot goes to the new last slot. -/
private def extend {m n : ℕ} (f : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.snoc (Fin.castSucc ∘ f) (Fin.last n)

private theorem extend_id {m : ℕ} : extend (id : Fin m → Fin m) = id := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [extend]
  | cast i => simp [extend]

private theorem extend_comp {k m n : ℕ} (g : Fin m → Fin n) (f : Fin k → Fin m) :
    extend g ∘ extend f = extend (g ∘ f) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [extend]
  | cast i => simp [extend]

/-- **Relabel the bound-variable slots** of an infinitary formula along `f : Fin m → Fin n`. Past a
quantifier, `f` is extended by sending the quantified slot to the new last slot, so quantified
variables move with their binders. -/
def mapBound : ∀ {m n : ℕ}, (Fin m → Fin n) → L.BoundedFormulaInf ι α m →
    L.BoundedFormulaInf ι α n
  | _, _, _, .falsum => .falsum
  | _, _, f, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map id f)) (t₂.relabel (Sum.map id f))
  | _, _, f, .rel R ts => .rel R fun i => (ts i).relabel (Sum.map id f)
  | _, _, f, .imp φ ψ => (mapBound f φ).imp (mapBound f ψ)
  | _, _, f, .all φ => (mapBound (extend f) φ).all
  | _, _, f, .iSup φs => .iSup fun i => mapBound f (φs i)
  | _, _, f, .iInf φs => .iInf fun i => mapBound f (φs i)

section MapBoundEqs

variable {m n : ℕ} (f : Fin m → Fin n)

/-- Relabelling fixes the false formula. -/
@[simp]
theorem mapBound_falsum : mapBound f (.falsum : L.BoundedFormulaInf ι α m) = .falsum := (rfl)

/-- Relabelling relabels the bound variables of an equation. -/
@[simp]
theorem mapBound_equal (t₁ t₂ : L.Term (α ⊕ Fin m)) :
    mapBound f (.equal t₁ t₂ : L.BoundedFormulaInf ι α m) =
      .equal (t₁.relabel (Sum.map id f)) (t₂.relabel (Sum.map id f)) := (rfl)

/-- Relabelling relabels the bound variables of a relational atom. -/
@[simp]
theorem mapBound_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin m)) :
    mapBound f (.rel R ts : L.BoundedFormulaInf ι α m) =
      .rel R fun i => (ts i).relabel (Sum.map id f) := (rfl)

/-- Relabelling commutes with implication. -/
@[simp]
theorem mapBound_imp (φ ψ : L.BoundedFormulaInf ι α m) :
    mapBound f (φ.imp ψ) = (mapBound f φ).imp (mapBound f ψ) := (rfl)

/-- Past a quantifier, relabelling sends the quantified slot to the new last slot. -/
@[simp]
theorem mapBound_all (φ : L.BoundedFormulaInf ι α (m + 1)) :
    mapBound f φ.all = (mapBound (Fin.snoc (fun i => (f i).castSucc) (Fin.last n)) φ).all := (rfl)

/-- Relabelling commutes with disjunctions over the carrier. -/
@[simp]
theorem mapBound_iSup (φs : ι → L.BoundedFormulaInf ι α m) :
    mapBound f (.iSup φs) = .iSup fun i => mapBound f (φs i) := (rfl)

/-- Relabelling commutes with conjunctions over the carrier. -/
@[simp]
theorem mapBound_iInf (φs : ι → L.BoundedFormulaInf ι α m) :
    mapBound f (.iInf φs) = .iInf fun i => mapBound f (φs i) := (rfl)

end MapBoundEqs

/-- **Relabelling is realization along the slot map**: the relabelled formula is realized at `xs`
exactly when the original is realized at `xs ∘ f`. -/
@[simp]
theorem realize_mapBound {M : Type w} [L.Structure M] :
    ∀ {m n : ℕ} (f : Fin m → Fin n) (φ : L.BoundedFormulaInf ι α m) (v : α → M)
      (xs : Fin n → M), (mapBound f φ).Realize v xs ↔ φ.Realize v (xs ∘ f) := by
  intro m n f φ
  induction φ generalizing n with
  | falsum => intro v xs; simp [mapBound]
  | equal t₁ t₂ =>
    intro v xs
    simp only [mapBound, realize_equal, Term.realize_relabel]
    rw [Sum.elim_comp_map]
    rfl
  | rel R ts =>
    intro v xs
    simp only [mapBound, realize_rel, Term.realize_relabel]
    rw [Sum.elim_comp_map]
    rfl
  | imp φ ψ ihφ ihψ => intro v xs; simp only [mapBound, realize_imp, ihφ, ihψ]
  | all φ ih =>
    intro v xs
    simp only [mapBound, realize_all, ih, extend, Fin.snoc_comp_snoc_castSucc_comp]
  | iSup φs ih => intro v xs; simp only [mapBound, realize_iSup, ih]
  | iInf φs ih => intro v xs; simp only [mapBound, realize_iInf, ih]

/-- Relabelling along the identity is the identity. -/
@[simp]
theorem mapBound_id : ∀ {m : ℕ} (φ : L.BoundedFormulaInf ι α m), mapBound id φ = φ := by
  intro m φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [mapBound, Sum.map_id_id, Term.relabel_id]
  | rel R ts => simp [mapBound, Sum.map_id_id, Term.relabel_id]
  | imp φ ψ ihφ ihψ => simp [mapBound, ihφ, ihψ]
  | all φ ih => simp only [mapBound, extend_id, ih]
  | iSup φs ih => simp [mapBound, ih]
  | iInf φs ih => simp [mapBound, ih]

/-- Relabelling along `f` and then `g` is relabelling along `g ∘ f`. -/
@[simp]
theorem mapBound_mapBound : ∀ {k m n : ℕ} (f : Fin k → Fin m) (g : Fin m → Fin n)
    (φ : L.BoundedFormulaInf ι α k), mapBound g (mapBound f φ) = mapBound (g ∘ f) φ := by
  intro k m n f g φ
  induction φ generalizing m n with
  | falsum => rfl
  | equal t₁ t₂ => simp [mapBound, Term.relabel_relabel, Sum.map_comp_map]
  | rel R ts => simp [mapBound, Term.relabel_relabel, Sum.map_comp_map]
  | imp φ ψ ihφ ihψ => simp [mapBound, ihφ, ihψ]
  | all φ ih => simp only [mapBound, ih, extend_comp]
  | iSup φs ih => simp [mapBound, ih]
  | iInf φs ih => simp [mapBound, ih]

/-! ### Weakening -/

/-- **Weakening** an infinitary formula from `m` to `n ≥ m` bound-variable slots, by relabelling
along `Fin.castLE`. Quantified variables move with their binders, so the result has the same
meaning at every valuation of the `n` slots that agrees on the first `m`. This corresponds to
Mathlib's finitary `BoundedFormula.liftAt` inserting the new slots after the existing ones, not
to Mathlib's finitary `BoundedFormula.castLE`. -/
def castLE {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormulaInf ι α m) : L.BoundedFormulaInf ι α n :=
  mapBound (Fin.castLE h) φ

/-- Weakening is relabelling along `Fin.castLE`. -/
theorem castLE_def {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormulaInf ι α m) :
    castLE h φ = mapBound (Fin.castLE h) φ := (rfl)

/-- **Weakening preserves meaning**, for every `m ≤ n`: the weakened formula is realized at `xs`
exactly when the original is realized at the first `m` slots of `xs`. -/
@[simp]
theorem realize_castLE {M : Type w} [L.Structure M] {m n : ℕ} (h : m ≤ n)
    (φ : L.BoundedFormulaInf ι α m) (v : α → M) (xs : Fin n → M) :
    (castLE h φ).Realize v xs ↔ φ.Realize v (xs ∘ Fin.castLE h) :=
  realize_mapBound _ φ v xs

/-- Weakening along `m ≤ m` is the identity. -/
@[simp]
theorem castLE_rfl {m : ℕ} (φ : L.BoundedFormulaInf ι α m) : castLE le_rfl φ = φ := by
  rw [castLE_def, Fin.castLE_rfl]
  exact mapBound_id φ

/-- Weakening twice is weakening once. -/
@[simp]
theorem castLE_castLE {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) (φ : L.BoundedFormulaInf ι α k) :
    castLE h₂ (castLE h₁ φ) = castLE (h₁.trans h₂) φ := by
  rw [castLE_def, castLE_def, castLE_def, mapBound_mapBound, Fin.castLE_comp_castLE]

end BoundedFormulaInf

end Language

end FirstOrder
