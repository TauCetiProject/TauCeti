/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.Reindex

/-!
# Regression examples: carrier transport of infinitary formulas

These examples exercise carrier transport from a downstream module, through public statements only:

* recoding a `Bool`-indexed conjunction into `L_{ω₁ω}` keeps its meaning, the padding branches of
  `ℕ` being `⊤`;
* transport along a sum injection preserves realization;
* transport along a universe lift and back is the identity on syntax;
* transport fixes the image of the finitary embedding.
-/

universe u v u' uι w

open FirstOrder FirstOrder.Language BoundedFormulaInf

-- Recoding a `Bool`-indexed conjunction into `L_{ω₁ω}` keeps its meaning: the conjunction of the
-- two branches, the padding branches of `ℕ` being `⊤`.
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (φs : Bool → L.BoundedFormulaInf Bool α n) (v : α → M) (xs : Fin n → M) :
    (toOmega (iInf φs)).Realize v xs ↔ (φs false).Realize v xs ∧ (φs true).Realize v xs := by
  simp [Bool.forall_bool]

-- Transport along a sum injection preserves realization.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M) :
    (reindex (TauCeti.IndexCoding.sumInl ι ℕ) φ).Realize v xs ↔ φ.Realize v xs :=
  realize_reindex _ φ v xs

-- Lifting the carrier to a higher universe and back is the identity on syntax.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) :
    (reindexEquiv (Equiv.ulift.{w} (α := ι)).symm).symm
      (reindexEquiv (Equiv.ulift.{w} (α := ι)).symm φ) = φ :=
  Equiv.symm_apply_apply _ φ

-- Transport fixes the image of the finitary embedding.
example {L : Language.{u, v}} {α : Type u'} {n : ℕ} (φ : L.BoundedFormula α n) :
    reindex (TauCeti.IndexCoding.ofEncodable Bool) (φ.toInf (ι := Bool)) = φ.toOmega :=
  reindex_toInf _ φ
