/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.PEquiv
public import Mathlib.Basic.Opposite

/-!
# Partial equivalences between opposite types

A partial equivalence `f : α ≃. β` induces the partial equivalence `f.op : αᵒᵖ ≃. βᵒᵖ`, which acts
as `f` on the underlying elements. It is the partial bijection of vertices carried by the opposite
of a quiver with a partial translation: there arrows are reversed, and the vertices are relabelled
along `Opposite.op`.
-/

public section

namespace PEquiv

open Opposite

variable {α β γ : Type*}

/-- The partial equivalence `αᵒᵖ ≃. βᵒᵖ` which acts as `f` on the underlying elements. -/
protected def op (f : α ≃. β) : αᵒᵖ ≃. βᵒᵖ where
  toFun a := (f (unop a)).map op
  invFun b := (f.symm (unop b)).map op
  inv a b := by
    simp only [Option.map_eq_some_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨unop b, (eq_some_iff f).1 hx, op_unop b⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨unop a, (eq_some_iff f).2 hy, op_unop a⟩

@[simp]
theorem op_apply (f : α ≃. β) (a : αᵒᵖ) : f.op a = (f (unop a)).map op :=
  (rfl)

/-- `f.op` sends `a` to `b` exactly when `f` sends `unop a` to `unop b`. -/
theorem op_eq_some (f : α ≃. β) {a : αᵒᵖ} {b : βᵒᵖ} :
    f.op a = some b ↔ f (unop a) = some (unop b) := by
  rw [op_apply, Option.map_eq_some_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · exact fun h ↦ ⟨unop b, h, op_unop b⟩

@[simp]
theorem symm_op (f : α ≃. β) : f.op.symm = f.symm.op :=
  (rfl)

@[simp]
theorem op_refl : (PEquiv.refl α).op = PEquiv.refl αᵒᵖ := by
  ext
  simp

@[simp]
theorem op_trans (f : α ≃. β) (g : β ≃. γ) : (f.trans g).op = f.op.trans g.op := by
  refine PEquiv.ext fun a ↦ Option.ext fun c ↦ ?_
  simp only [op_eq_some, trans_eq_some]
  exact ⟨fun ⟨b, hb, hc⟩ ↦ ⟨op b, hb, hc⟩, fun ⟨b, hb, hc⟩ ↦ ⟨unop b, hb, hc⟩⟩

@[simp]
theorem op_bot : (⊥ : α ≃. β).op = ⊥ := by
  ext
  simp

end PEquiv
