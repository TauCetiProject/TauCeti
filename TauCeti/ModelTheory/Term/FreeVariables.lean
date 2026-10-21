/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics

/-!
# Left-variable support of first-order terms

Term realization depends only on the valuation of the variables in `Term.varFinsetLeft`
when the right-variable valuation is fixed. Relabelling right variables preserves this support.
Substitution collects the supports of the replacement terms; relabelling into either summand
retains exactly those support images that remain left variables.

Use the lemmas with the `TauCeti` qualification or after `open TauCeti`, including
`realize_congr_varFinsetLeft` and the support laws for substitution and relabelling.
-/

public section

universe u v uα w

namespace TauCeti

open FirstOrder.Language

variable {L : FirstOrder.Language.{u, v}} {α : Type uα}

/-- Term realization depends only on the free valuation on its finite left-variable support;
the valuation of the right variables is held fixed. -/
theorem realize_congr_varFinsetLeft [DecidableEq α] {β : Type*} {M : Type w} [L.Structure M]
    (t : L.Term (α ⊕ β)) {v₁ v₂ : α → M} (ys : β → M)
    (h : Set.EqOn v₁ v₂ ↑t.varFinsetLeft) :
    t.realize (Sum.elim v₁ ys) = t.realize (Sum.elim v₂ ys) := by
  rw [← t.realize_restrictVarLeft' (Set.Subset.refl _),
    ← t.realize_restrictVarLeft' (Set.Subset.refl _)]
  have hv : v₁ ∘ ((↑) : (↑t.varFinsetLeft : Set α) → α) = v₂ ∘ (↑) :=
    funext fun a => h a.property
  rw [hv]

/-- Relabelling right variables preserves a term's finite left-variable support. -/
@[simp]
theorem varFinsetLeft_relabel [DecidableEq α] {β γ : Type*}
    (t : L.Term (α ⊕ β)) (f : β → γ) :
    (t.relabel (Sum.map id f)).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var a => cases a <;> simp
  | func g ts ih => simp [ih]

/-- Relabelling every variable into the left summand preserves the full variable support. -/
@[simp]
theorem varFinsetLeft_relabel_inl [DecidableEq α] {β : Type*} (t : L.Term α) :
    (t.relabel (Sum.inl : α → α ⊕ β)).varFinsetLeft = t.varFinset := by
  induction t with
  | var a => simp
  | func g ts ih => simp [ih]

/-- Substituting free terms collects their variables over the original left-variable support. -/
@[simp]
theorem varFinsetLeft_subst_sumElim [DecidableEq α] {β γ : Type*} [DecidableEq γ]
    (t : L.Term (α ⊕ β)) (f : α → L.Term γ) :
    (↑(t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))).varFinsetLeft :
      Set γ) = ⋃ a ∈ (t.varFinsetLeft : Set α), ↑(f a).varFinset := by
  induction t with
  | var a => cases a <;> simp [Term.subst]
  | func g ts ih =>
    ext b
    simp only [Term.subst, Term.varFinsetLeft, Finset.coe_biUnion, Finset.mem_univ,
      Set.iUnion_true, ih, Set.mem_iUnion, Finset.mem_coe]
    aesop

/-- Relabelling into either summand keeps exactly the images that are left variables. -/
@[simp]
theorem varFinsetLeft_relabel_sumElim [DecidableEq α] {β γ δ : Type*} [DecidableEq γ]
    (t : L.Term (α ⊕ β)) (g : α → γ ⊕ δ) (f : β → δ) :
    (↑(t.relabel (Sum.elim g (Sum.inr ∘ f))).varFinsetLeft : Set γ) =
      Sum.inl ⁻¹' (g '' (t.varFinsetLeft : Set α)) := by
  induction t with
  | var a => cases a with
    | inl a => cases h : g a <;> ext b <;> simp [h]
    | inr b => simp
  | func g ts ih =>
    ext b
    simp only [Term.relabel, Term.varFinsetLeft, Finset.coe_biUnion, Finset.mem_univ,
      Set.iUnion_true, ih, Set.mem_iUnion, Set.mem_preimage, Set.mem_image, Finset.mem_coe]
    aesop

end TauCeti
