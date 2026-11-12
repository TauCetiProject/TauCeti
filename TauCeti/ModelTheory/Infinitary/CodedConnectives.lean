/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.IndexCoding
public import TauCeti.ModelTheory.Infinitary.Semantics

/-!
# Coded infinitary connectives

An infinitary formula branches over one fixed carrier `κ`. A conjunction or disjunction indexed
by another type `ι` is expressed at `κ` along an index coding `c : IndexCoding ι κ`: each index
`k : κ` that decodes to `i : ι` carries the `i`-th branch, and each undecodable index carries a
semantically neutral branch, `⊤` for a conjunction and `⊥` for a disjunction. Indices that decode
to the same `i` carry the same branch. The realization of the coded connective is therefore the
`ι`-indexed conjunction or disjunction, whatever the coding.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.iInfAlong`: the `ι`-indexed conjunction at carrier `κ`.
* `FirstOrder.Language.BoundedFormulaInf.iSupAlong`: the `ι`-indexed disjunction at carrier `κ`.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.realize_iInfAlong`: the coded conjunction is realized
  exactly when every branch is.
* `FirstOrder.Language.BoundedFormulaInf.realize_iSupAlong`: the coded disjunction is realized
  exactly when some branch is.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, whose coded connectives are in
  `Mathlib/ModelTheory/Infinitary/Reindex.lean` in `cameronfreer/mathlib4` at commit
  `346a4bd3f95e8591976c91259badc6d2c300f638`.
* Divergences from these sources: the coded connectives have their own module, apart from
  whole-formula transport; their bodies are not exposed and are used through the defining
  equations `iInfAlong_def` and `iSupAlong_def`; the realization laws are derived from the padding
  laws `IndexCoding.comp_pad`, `IndexCoding.forall_pad_true_iff` and
  `IndexCoding.exists_pad_false_iff`.
-/

public section

universe u v u' uι uκ w

namespace FirstOrder

namespace Language

open TauCeti

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- The **coded conjunction** of an `ι`-indexed family at carrier `κ`, along a coding: an index
decoding to `i` carries the `i`-th conjunct, and an undecodable index carries `⊤`. -/
def iInfAlong (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaInf κ α n) :
    L.BoundedFormulaInf κ α n :=
  .iInf (c.pad ⊤ φs)

/-- The **coded disjunction** of an `ι`-indexed family at carrier `κ`, along a coding: an index
decoding to `i` carries the `i`-th disjunct, and an undecodable index carries `⊥`. -/
def iSupAlong (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaInf κ α n) :
    L.BoundedFormulaInf κ α n :=
  .iSup (c.pad ⊥ φs)

/-- The coded conjunction is the carrier conjunction of the family padded with `⊤`. -/
theorem iInfAlong_def (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaInf κ α n) :
    iInfAlong c φs = .iInf (c.pad ⊤ φs) := (rfl)

/-- The coded disjunction is the carrier disjunction of the family padded with `⊥`. -/
theorem iSupAlong_def (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaInf κ α n) :
    iSupAlong c φs = .iSup (c.pad ⊥ φs) := (rfl)

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

/-- Realizing a padded family branch by branch is padding the realizations, with the realization
of the default as the new default. -/
private theorem realize_pad (c : IndexCoding ι κ) (d : L.BoundedFormulaInf κ α n)
    (φs : ι → L.BoundedFormulaInf κ α n) (k : κ) :
    (c.pad d φs k).Realize v xs ↔ c.pad (d.Realize v xs) (fun i => (φs i).Realize v xs) k :=
  Iff.of_eq (congrFun (c.comp_pad (fun φ : L.BoundedFormulaInf κ α n => φ.Realize v xs) d φs) k)

/-- **The coded conjunction is realized exactly when every conjunct is.** The padding branches
are `⊤`, which is always realized. -/
@[simp]
theorem realize_iInfAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaInf κ α n} :
    (iInfAlong c φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [iInfAlong_def, realize_iInf, realize_pad, realize_top]
  exact c.forall_pad_true_iff _

/-- **The coded disjunction is realized exactly when some disjunct is.** The padding branches are
`⊥`, which is never realized. -/
@[simp]
theorem realize_iSupAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaInf κ α n} :
    (iSupAlong c φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [iSupAlong_def, realize_iSup, realize_pad, realize_bot]
  exact c.exists_pad_false_iff _

end BoundedFormulaInf

end Language

end FirstOrder
