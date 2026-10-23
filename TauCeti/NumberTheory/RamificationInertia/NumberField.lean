/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.NumberTheory.RamificationInertia.Tower

/-!
# Ramification indices in an extension of number fields

A consequence of the general ramification bounds for the rings of integers of number fields.
`TauCeti.NumberTheory.RamificationInertia.Tower` states it for a finite flat extension of
domains; here it is transported to the fields themselves, so the bound is `[F : K]` rather than
the rank of `𝓞 F` over `𝓞 K`.

## Main results

* `Ideal.ramificationIdx_le_finrank_of_numberField`: for a prime `𝔔` of `𝓞 F` in an extension
  `F / K` of number fields, `e(𝔔 / 𝓞 K) ≤ [F : K]`.
* `Ideal.finrank_eq_one_of_ramificationIdx_eq_finrank`: in a tower `K ≤ E ≤ B`, a
  prime of `𝓞 B` with `e(𝔔 / 𝓞 E) = [B : K]` — the full tower degree, not merely `[B : E]` —
  forces `[E : K] = 1`.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K]

-- Source. Both declarations are recovered from the retired PR #5538, at commit
-- 70421db267d9bd6252256f873d27e99e739a931c.

/-- **A relative ramification index is at most the degree of the extension.** For a prime `𝔔` of
`𝓞 F` in an extension `F / K` of number fields, `e(𝔔 / 𝓞 K) ≤ [F : K]`.

It is the number-field form of `TauCeti.RamificationInertia.ramificationIdx_le_finrank`, whose
bound is the rank of `𝓞 F` over `𝓞 K`; the two agree, and this is the one a caller holding a field
extension can use directly. Only the top field needs a number-field hypothesis. -/
theorem _root_.Ideal.ramificationIdx_le_finrank_of_numberField {F : Type*} [Field F]
    [NumberField F] [Algebra K F] (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] :
    𝔔.ramificationIdx (𝓞 K) ≤ Module.finrank K F := by
  have : CharZero K := RingHom.charZero (algebraMap K F)
  have : NumberField K := NumberField.of_tower ℚ F K
  -- The fundamental identity `∑ eᵢ fᵢ = [F : K]` bounds each `eᵢ`, and `[𝓞 F : 𝓞 K] = [F : K]`.
  exact (TauCeti.RamificationInertia.ramificationIdx_le_finrank (𝔔.under (𝓞 K)) 𝔔).trans_eq
    (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F) F).symm

/-- **A relative ramification index equal to the full tower degree leaves no room for an
intermediate field.** In a tower `K ≤ E ≤ B`, a prime `𝔔` of `𝓞 B` with
`e(𝔔 / 𝓞 E) = [B : K]` forces `[E : K] = 1`.

Only `B` needs a number-field hypothesis; `K` and `E` are arbitrary fields. The action of `K` on
`B` need only be a module structure compatible with the tower.

The hypothesis is stronger than total ramification of `B / E`, which asks only
`e(𝔔 / 𝓞 E) = [B : E]`; here the index must reach the degree of the *whole* tower. That is what a
"no proper intermediate field" argument supplies, and what collapses the bottom step. -/
theorem _root_.Ideal.finrank_eq_one_of_ramificationIdx_eq_finrank {K : Type*} [Field K]
    {E B : Type*} [Field E] [Field B] [NumberField B] [Algebra K E] [Module K B]
    [Algebra E B] [IsScalarTower K E B]
    (𝔔 : Ideal (𝓞 B)) [𝔔.IsPrime]
    (he : 𝔔.ramificationIdx (𝓞 E) = Module.finrank K B) :
    Module.finrank K E = 1 := by
  -- Both lower fields embed into `B`, so they have characteristic zero and finite degree.
  have : CharZero E := RingHom.charZero (algebraMap E B)
  have : NumberField E := NumberField.of_tower ℚ B E
  have : CharZero K := RingHom.charZero (algebraMap K E)
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  have hb := Ideal.ramificationIdx_le_finrank_of_numberField (K := E) (F := B) 𝔔
  have hle : Module.finrank K E * Module.finrank E B ≤ 1 * Module.finrank E B := by
    rw [one_mul, Module.finrank_mul_finrank K E B, ← he]; exact hb
  exact le_antisymm (Nat.le_of_mul_le_mul_right hle Module.finrank_pos) Module.finrank_pos

end TauCeti.NumberField
