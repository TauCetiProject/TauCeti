/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.BackAndForth.WellOrder

/-!
# Regression examples: back-and-forth equivalence of ordinal multiples

Through public statements only, these examples check:

* the well-orders `ω ^ 2` and `ω ^ 2 * 2` are back-and-forth equivalent at level `2`, yet not
  isomorphic, so equivalence at level `γ` does not count the copies of `ω ^ γ`;
* the nonzero multiples are needed: the empty order `ω * 0` is not equivalent at level `1` to
  the nonempty `ω * 1`.
-/

open FirstOrder FirstOrder.Language Ordinal TauCeti

attribute [local instance] orderStructure

-- `ω ^ 2` and `ω ^ 2 * 2` are back-and-forth equivalent at level `2`.
example : BFEquiv (L := Language.order) (2 : Ordinal.{0}) 0
    (Fin.elim0 : Fin 0 → (ω ^ (2 : Ordinal.{0}) * 1).ToType)
    (Fin.elim0 : Fin 0 → (ω ^ (2 : Ordinal.{0}) * 2).ToType) :=
  bfEquiv_omega0_opow_mul 2 one_ne_zero two_ne_zero

-- `ω ^ 2` and `ω ^ 2 * 2` are not isomorphic.
example : IsEmpty ((ω ^ (2 : Ordinal.{0}) * 1).ToType ≃[Language.order]
    (ω ^ (2 : Ordinal.{0}) * 2).ToType) := by
  refine ⟨fun e => ?_⟩
  let := StrongHomClass.toOrderIsoClass Language.order _ _
    ((ω ^ (2 : Ordinal.{0}) * 1).ToType ≃[Language.order] (ω ^ (2 : Ordinal.{0}) * 2).ToType)
  have h := (OrderIso.ofClass e).ordinalType_congr
  rw [type_toType, type_toType] at h
  exact absurd (mul_left_cancel₀ (opow_ne_zero 2 omega0_ne_zero) h) (by simp)

-- The empty order `ω * 0` and the nonempty `ω * 1` are not equivalent at level `1`: the back step
-- has no answer to a point of `ω * 1`.
example : ¬ BFEquiv (L := Language.order) (1 : Ordinal.{0}) 0
    (Fin.elim0 : Fin 0 → (ω ^ (1 : Ordinal.{0}) * 0).ToType)
    (Fin.elim0 : Fin 0 → (ω ^ (1 : Ordinal.{0}) * 1).ToType) := by
  intro h
  have : Nonempty (ω ^ (1 : Ordinal.{0}) * 1).ToType := by simp
  obtain ⟨m, -⟩ := ((BFEquiv.add_one (0 : Ordinal.{0}) _ _).1 (by rwa [zero_add])).2.2
    (Classical.arbitrary _)
  rw [mul_zero] at m
  exact isEmptyElim m
