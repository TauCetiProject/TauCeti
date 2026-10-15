/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# A computed constant graphon density

This file records an exact homomorphism density for a constant graphon, giving a concrete check
of the general constant-graphon formula.
-/

public section

open MeasureTheory
open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

/-- The triangle density of the constant `1/2` graphon is `1/8`. -/
theorem homDensity_top_three_const_half :
    homDensity (⊤ : SimpleGraph (Fin 3))
      (Graphon.const (volume : Measure I) ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩) = 1 / 8 := by
  rw [homDensity_const]
  have hcard : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by decide
  rw [hcard]
  norm_num

end DenseGraphLimits

end TauCeti
