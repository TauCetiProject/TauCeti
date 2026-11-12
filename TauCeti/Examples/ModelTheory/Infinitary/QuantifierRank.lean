/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.QuantifierRank

/-!
# Regression examples: quantifier rank of infinitary formulas

These examples exercise the quantifier rank from a downstream module, through public statements
only:

* a formula `∀ ∃ φ` with `φ` atomic has rank `2`;
* an `ℕ`-indexed conjunction whose conjuncts have every finite rank has rank `ω`;
* transport from an empty carrier keeps rank `0`, every branch being padding;
* recoding into `L_{ω₁ω}` preserves rank, up to lifting into a common universe.
-/

universe u v u' uι

open FirstOrder FirstOrder.Language BoundedFormulaInf

-- A formula `∀ ∃ φ` with `φ` atomic has rank `2`.
example {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {n : ℕ}
    (t₁ t₂ : L.Term (α ⊕ Fin (n + 2))) :
    (BoundedFormulaInf.all (equal t₁ t₂ : L.BoundedFormulaInf ι α (n + 2)).ex).qrank = 2 := by
  simp [Order.succ_eq_add_one, one_add_one_eq_two]

-- The `ℕ`-indexed conjunction whose `k`-th conjunct closes `k` slots of `⊥` has rank `ω`.
example {L : Language.{u, v}} {α : Type u'} :
    (iInf fun k : ℕ => ((⊥ : L.BoundedFormulaω α k).alls : L.Formulaω α)).qrank =
      Ordinal.omega0 := by
  simp [Ordinal.iSup_natCast]

-- Transport from the empty carrier into `ℕ` keeps rank `0`: every branch is padding.
example {L : Language.{u, v}} {α : Type u'} {n : ℕ} :
    Ordinal.lift.{0} (reindex (TauCeti.IndexCoding.ofEncodable Empty)
      (iInf Empty.elim : L.BoundedFormulaInf Empty α n)).qrank = 0 := by
  rw [qrank_reindex]
  simp

-- Recoding into `L_{ω₁ω}` preserves rank, up to lifting into a common universe.
example {L : Language.{u, v}} {ι : Type uι} [Encodable ι] {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) :
    Ordinal.lift.{uι} (toOmega φ).qrank = Ordinal.lift.{0} φ.qrank := by
  rw [toOmega_def, qrank_reindex]
