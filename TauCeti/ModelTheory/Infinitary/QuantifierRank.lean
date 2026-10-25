/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Reindex
public import Mathlib.SetTheory.Ordinal.Family
-- Non-public: `TauCeti.Ordinal.lift_iSup` moves the lift through a supremum of ranks.
import TauCeti.SetTheory.Ordinal.Family

/-!
# Quantifier rank of infinitary formulas

The quantifier rank of an infinitary formula is `0` on atoms, the maximum on implication, the
successor under a quantifier, and the supremum of the branches at an infinitary conjunction or
disjunction.

The supremum ranges over the branching carrier `ι`, so the rank is valued in `Ordinal.{uι}`, the
carrier's own ordinal universe; at `ι := ℕ` this is `Ordinal.{0}`. Ranks at different carriers live
in different universes, and are compared after `Ordinal.lift` into a common one: carrier transport
preserves rank up to this lift. Padding does not raise the rank, since the padding branches `⊤`
and `⊥` have rank `0`; this includes an empty source carrier, where every branch is padding.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.qrank`: the quantifier rank.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.qrank_alls` and
  `FirstOrder.Language.BoundedFormulaInf.qrank_exs`: closing all `n` bound-variable slots adds `n`.
* `FirstOrder.Language.BoundedFormulaInf.qrank_reindex`: carrier transport preserves rank, up to
  `Ordinal.lift`.
* `FirstOrder.Language.BoundedFormulaInf.qrank_toInf`: the rank of a finitary formula does not
  depend on the carrier, up to `Ordinal.lift`.
* `FirstOrder.Language.BoundedFormulaInf.qrank_toInf_lt_omega0`: the rank of a finitary formula is
  finite.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, whose quantifier rank is
  `Mathlib/ModelTheory/Infinitary/QuantifierRank.lean` in `cameronfreer/mathlib4` at commit
  `346a4bd3f95e8591976c91259badc6d2c300f638`.
* Divergences from these sources: the body of `qrank` is not exposed and is used through its
  constructor equations, and the proofs use only the public equations of the syntax and of carrier
  transport.
-/

public section

universe u v u' uι uκ w

namespace FirstOrder

namespace Language

open TauCeti

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- The **quantifier rank** of an infinitary formula, valued in the carrier's ordinal universe:
`0` on atoms, the maximum on implication, the successor under `∀`, and the supremum of the
branches at an infinitary node. -/
noncomputable def qrank : ∀ {n}, L.BoundedFormulaInf ι α n → Ordinal.{uι}
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (qrank φ) (qrank ψ)
  | _, .all φ => Order.succ (qrank φ)
  | _, .iSup φs => ⨆ i, qrank (φs i)
  | _, .iInf φs => ⨆ i, qrank (φs i)

section Equations

/-- The false formula has rank `0`. -/
@[simp]
theorem qrank_falsum : (falsum : L.BoundedFormulaInf ι α n).qrank = 0 := (rfl)

/-- An equation has rank `0`. -/
@[simp]
theorem qrank_equal {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).qrank = 0 := (rfl)

/-- A relational atom has rank `0`. -/
@[simp]
theorem qrank_rel {l : ℕ} {R : L.Relations l} {ts : Fin l → L.Term (α ⊕ Fin n)} :
    (rel R ts : L.BoundedFormulaInf ι α n).qrank = 0 := (rfl)

/-- An implication has the larger rank of its two sides. -/
@[simp]
theorem qrank_imp {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ.imp ψ).qrank = max φ.qrank ψ.qrank := (rfl)

/-- Universal quantification raises the rank by one. -/
@[simp]
theorem qrank_all {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.all.qrank = Order.succ φ.qrank := (rfl)

/-- A disjunction over the carrier has the supremum of the ranks of its branches. -/
@[simp]
theorem qrank_iSup {φs : ι → L.BoundedFormulaInf ι α n} :
    (iSup φs).qrank = ⨆ i, (φs i).qrank := (rfl)

/-- A conjunction over the carrier has the supremum of the ranks of its branches. -/
@[simp]
theorem qrank_iInf {φs : ι → L.BoundedFormulaInf ι α n} :
    (iInf φs).qrank = ⨆ i, (φs i).qrank := (rfl)

/-- Negation does not change the rank. -/
@[simp]
theorem qrank_not {φ : L.BoundedFormulaInf ι α n} : φ.not.qrank = φ.qrank := by
  rw [BoundedFormulaInf.not, qrank_imp, qrank_falsum]
  exact max_eq_left zero_le

/-- `⊥` has rank `0`. -/
@[simp]
theorem qrank_bot : (⊥ : L.BoundedFormulaInf ι α n).qrank = 0 := by
  rw [bot_def, qrank_falsum]

/-- `⊤` has rank `0`. -/
@[simp]
theorem qrank_top : (⊤ : L.BoundedFormulaInf ι α n).qrank = 0 := by
  rw [top_def, qrank_not, qrank_falsum]

/-- Existential quantification raises the rank by one. -/
@[simp]
theorem qrank_ex {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.ex.qrank = Order.succ φ.qrank := by
  simp [BoundedFormulaInf.ex]

end Equations

section Closure

/-- Closing all `n` bound-variable slots universally adds `n` to the rank. -/
@[simp]
theorem qrank_alls : ∀ {n} {φ : L.BoundedFormulaInf ι α n}, φ.alls.qrank = φ.qrank + n
  | 0, φ => by rw [alls_zero, Nat.cast_zero, add_zero]
  | n + 1, φ => by
    rw [alls_succ, qrank_alls, qrank_all, Order.succ_eq_add_one, add_assoc, Nat.cast_succ,
      Nat.cast_add_one_comm]

/-- Closing all `n` bound-variable slots existentially adds `n` to the rank. -/
@[simp]
theorem qrank_exs : ∀ {n} {φ : L.BoundedFormulaInf ι α n}, φ.exs.qrank = φ.qrank + n
  | 0, φ => by rw [exs_zero, Nat.cast_zero, add_zero]
  | n + 1, φ => by
    rw [exs_succ, qrank_exs, qrank_ex, Order.succ_eq_add_one, add_assoc, Nat.cast_succ,
      Nat.cast_add_one_comm]

end Closure

section Transport

/-- Padding with a rank-`0` formula does not change the lifted supremum of the ranks. Both
infinitary cases of `qrank_reindex` are this statement, with the padding `⊤` or `⊥`. -/
private theorem lift_iSup_qrank_pad {n : ℕ} (c : IndexCoding ι κ)
    (d : L.BoundedFormulaInf κ α n) (hd : d.qrank = 0)
    (φs : ι → L.BoundedFormulaInf ι α n) (ψs : ι → L.BoundedFormulaInf κ α n)
    (ih : ∀ i, Ordinal.lift.{uι} (ψs i).qrank = Ordinal.lift.{uκ} (φs i).qrank) :
    Ordinal.lift.{uι} (⨆ k, (c.pad d ψs k).qrank) = Ordinal.lift.{uκ} (⨆ i, (φs i).qrank) := by
  rw [TauCeti.Ordinal.lift_iSup Ordinal.bddAbove_of_small,
    TauCeti.Ordinal.lift_iSup Ordinal.bddAbove_of_small]
  refine le_antisymm (Ordinal.iSup_le fun k => ?_) (Ordinal.iSup_le fun i => ?_)
  · rcases hdec : c.decode k with _ | i
    · rw [c.pad_of_decode_none hdec, hd, Ordinal.lift_zero]
      exact Ordinal.bot_eq_zero ▸ bot_le
    · rw [c.pad_of_decode_some hdec, ih i]
      exact Ordinal.le_iSup (fun i => Ordinal.lift.{uκ} (φs i).qrank) i
  · rw [← ih i]
    have hb := Ordinal.le_iSup (fun k => Ordinal.lift.{uι} (c.pad d ψs k).qrank) (c.encode i)
    rwa [IndexCoding.pad_encode] at hb

/-- **Carrier transport preserves quantifier rank**, up to `Ordinal.lift` into a common universe,
for every coding, including from an empty carrier. -/
theorem qrank_reindex (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n),
      Ordinal.lift.{uι} (reindex c φ).qrank = Ordinal.lift.{uκ} φ.qrank := by
  -- The padding branches `⊤` and `⊥` have rank `0`, so they never raise a supremum.
  intro n φ
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ =>
    rw [reindex_imp, qrank_imp, qrank_imp, Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h),
      Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h), ihφ, ihψ]
  | all φ ih =>
    rw [reindex_all, qrank_all, qrank_all]
    simp only [Order.succ_eq_add_one, Ordinal.lift_add_one, ih]
  | iSup φs ih =>
    rw [reindex_iSup, iSupAlong_def, qrank_iSup, qrank_iSup]
    exact lift_iSup_qrank_pad c ⊥ qrank_bot φs _ ih
  | iInf φs ih =>
    rw [reindex_iInf, iInfAlong_def, qrank_iInf, qrank_iInf]
    exact lift_iSup_qrank_pad c ⊤ qrank_top φs _ ih

end Transport

section Finitary

/-- **The rank of a finitary formula does not depend on the carrier**, up to `Ordinal.lift`. -/
theorem qrank_toInf : ∀ {n} (φ : L.BoundedFormula α n),
    Ordinal.lift.{uκ} (BoundedFormula.toInf (ι := ι) φ).qrank =
      Ordinal.lift.{uι} (BoundedFormula.toInf (ι := κ) φ).qrank := by
  -- A finitary formula has no infinitary nodes, so no carrier supremum ever arises.
  intro n φ
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ =>
    rw [BoundedFormula.toInf_imp, BoundedFormula.toInf_imp, qrank_imp, qrank_imp,
      Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h),
      Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h), ihφ, ihψ]
  | all φ ih =>
    rw [BoundedFormula.toInf_all, BoundedFormula.toInf_all, qrank_all, qrank_all]
    simp only [Order.succ_eq_add_one, Ordinal.lift_add_one, ih]

/-- **The rank of a finitary formula is finite.** -/
theorem qrank_toInf_lt_omega0 : ∀ {n} (φ : L.BoundedFormula α n),
    (BoundedFormula.toInf (ι := ι) φ).qrank < Ordinal.omega0 := by
  intro n φ
  induction φ with
  | falsum => simp [Ordinal.omega0_pos]
  | equal t₁ t₂ => simp [Ordinal.omega0_pos]
  | rel R ts => simp [Ordinal.omega0_pos]
  | imp φ ψ ihφ ihψ => simpa only [BoundedFormula.toInf_imp, qrank_imp] using max_lt ihφ ihψ
  | all φ ih =>
    simpa only [BoundedFormula.toInf_all, qrank_all] using Ordinal.isSuccLimit_omega0.succ_lt ih

end Finitary

end BoundedFormulaInf

end Language

end FirstOrder
