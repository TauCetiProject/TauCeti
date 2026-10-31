/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Network.Nonnegative

/-!
# Nonnegative coefficient examples

On two vertices with two arrows for each ordered pair, the only positive capacities are on the
two parallel arrows from `false` to `true`. Saturating them gives an optimal flow, with the
singleton source cut as certificate. The natural example has capacity three on each arrow;
the nonnegative rational and real examples have capacity one half on each arrow. All examples
also include zero-capacity loops and reverse arrows.
-/

namespace TauCeti

open Finset
open scoped NNRat NNReal

-- Natural capacities return natural arrow values while terminal excess stays integer-valued.
example :
    let cap : Assignment (fun _ _ : Bool ↦ Bool) ℕ :=
      fun x y _ ↦ if x = false ∧ y = true then 3 else 0
    ∃ f : NatFlow cap false true,
      f.toNat = cap ∧ f.toNat ≤ cap ∧ f.val = 6 ∧
        f.val = ((arrowSum cap {false} {true} : ℕ) : ℤ) := by
  intro cap
  let f : NatFlow cap false true :=
    { toFun := cap.map (Nat.castAddMonoidHom ℤ)
      mem_Icc := ⟨fun _ _ e ↦ Int.natCast_nonneg (cap e), le_rfl⟩
      conserve v hvs hvt := by cases v <;> simp_all
      excessAt_sink_nonneg := by norm_num [excessAt_def, cap, Assignment.map] }
  refine ⟨f, f.toNat_eq_iff.mpr rfl, f.toNat_le, ?_, ?_⟩
  · norm_num [f, BoundedFlow.val_def, excessAt_def, cap, Assignment.map]
  · norm_num [f, BoundedFlow.val_def, excessAt_def, arrowSum_def, cap, Assignment.map]

-- Rational capacities return values in the named nonnegative rational type.
example :
    let cap : Assignment (fun _ _ : Bool ↦ Bool) ℚ≥0 :=
      fun x y _ ↦ if x = false ∧ y = true then ⟨1 / 2, by norm_num⟩ else 0
    ∃ f : NNRatFlow cap false true,
      f.toNNRat = cap ∧ f.toNNRat ≤ cap ∧ f.val = 1 ∧
        f.val = ((arrowSum cap {false} {true} : ℚ≥0) : ℚ) := by
  intro cap
  let f : NNRatFlow cap false true :=
    { toFun := cap.map NNRat.coeHom
      mem_Icc := ⟨fun _ _ e ↦ (cap e).property, le_rfl⟩
      conserve v hvs hvt := by cases v <;> simp_all
      excessAt_sink_nonneg := by norm_num [excessAt_def, cap, Assignment.map] }
  refine ⟨f, f.toNNRat_eq_iff.mpr rfl, f.toNNRat_le, ?_, ?_⟩
  · norm_num [f, BoundedFlow.val_def, excessAt_def, cap, Assignment.map]
  · rw [nnratCast_arrowSum]
    norm_num [f, BoundedFlow.val_def, excessAt_def, arrowSum_def, cap,
      Assignment.map]

-- Real capacities return nonnegative real arrow values and retain real excess.
example :
    let cap : Assignment (fun _ _ : Bool ↦ Bool) ℝ≥0 :=
      fun x y _ ↦ if x = false ∧ y = true then NNReal.mk (1 / 2) (by norm_num) else 0
    ∃ f : NNRealFlow cap false true,
      f.toNNReal = cap ∧ f.toNNReal ≤ cap ∧ f.val = 1 ∧
        f.val = ((arrowSum cap {false} {true} : ℝ≥0) : ℝ) := by
  intro cap
  let f : NNRealFlow cap false true :=
    { toFun := cap.map NNReal.toRealHom
      mem_Icc := ⟨fun _ _ e ↦ (cap e).property, le_rfl⟩
      conserve v hvs hvt := by cases v <;> simp_all
      excessAt_sink_nonneg := by norm_num [excessAt_def, cap, Assignment.map] }
  refine ⟨f, f.toNNReal_eq_iff.mpr rfl, f.toNNReal_le, ?_, ?_⟩
  · norm_num [f, BoundedFlow.val_def, excessAt_def, cap, Assignment.map]
  · rw [nnrealCast_arrowSum]
    norm_num [f, BoundedFlow.val_def, excessAt_def, arrowSum_def, cap,
      Assignment.map]

end TauCeti
