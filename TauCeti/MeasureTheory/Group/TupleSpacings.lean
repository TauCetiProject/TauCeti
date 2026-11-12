/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Data.Fin.Tuple.Spacing
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of tuple spacings

Taking the successive gaps of a finite tuple, with fixed endpoints adjoined, is
measurable whenever subtraction is measurable. This allows the spacing map to
transport laws on finite products.
-/

public section

namespace TauCeti

variable {R : Type*} [AddCommGroup R] {n : ℕ}

/-- Taking spacings is measurable for any measurable subtraction. -/
@[fun_prop]
theorem measurable_tupleSpacings [MeasurableSpace R] [MeasurableSub₂ R] (a b : R) :
    Measurable (tupleSpacings a b (n := n)) := by
  have he (i : Fin (n + 2)) : Measurable (fun x : Fin n → R ↦
      (Fin.cons a (Fin.snoc x b) : Fin (n + 2) → R) i) := by
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using (measurable_pi_apply i : Measurable (fun x : Fin n → R ↦ x i))
  refine Measurable.of_eval fun i ↦ ?_
  convert (he i.succ).sub (he i.castSucc) using 1
  ext x
  exact tupleSpacings_apply a b x i

end TauCeti
