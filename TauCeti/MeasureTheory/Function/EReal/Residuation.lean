/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.EReal.Quantale
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability of extended real additive residuation

The residual `AddQuantale.rightAddResiduation a c`, the largest `b` satisfying `a + b ≤ c`,
is Borel measurable in both arguments. Consequently Borel extended costs and potentials give
Borel residual integrands, even at infinite values. Infimal transforms of these integrands
can then use analytic projections to obtain completion measurability.
-/

public section

namespace TauCeti

open MeasureTheory

/-- Additive residuation of measurable extended real functions is measurable. -/
@[fun_prop]
theorem _root_.Measurable.ereal_rightAddResiduation {α : Type*} [MeasurableSpace α]
    {a c : α → EReal} (ha : Measurable a) (hc : Measurable c) :
    Measurable fun x ↦ AddQuantale.rightAddResiduation (a x) (c x) := by
  simp_rw [EReal.rightAddResiduation_eq]
  exact Measurable.ite
    ((hc (measurableSet_singleton ⊤)).union (ha (measurableSet_singleton ⊥)))
    measurable_const (hc.sub ha)

end TauCeti
