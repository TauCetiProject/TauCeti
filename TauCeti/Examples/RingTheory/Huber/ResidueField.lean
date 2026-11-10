/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.ResidueField
import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.LaurentSeries

/-!
# Checks for infinite residue fields of complete Tate rings

These examples test mixed and equal characteristic, exclusion of finite nonzero targets,
and the necessary properness assumption on quotients. Algebraic residue fields of a Tate
ring are infinite even when its valuation ring has finite residue field.
-/

namespace TauCeti.Examples

variable (p : ℕ) [Fact p.Prime]

/-- The algebraic residue fields of the complete Tate field `ℚ_p` are infinite. -/
example (I : Ideal ℚ_[p]) [I.IsPrime] : Infinite I.ResidueField :=
  I.infinite_residueField_of_isTateRing

/-- The conclusion also holds in characteristic `p`, even with finite coefficient field. -/
example (I : Ideal (LaurentSeries (ZMod p))) [I.IsPrime] : Infinite I.ResidueField :=
  I.infinite_residueField_of_isTateRing

/-- There is no abstract ring homomorphism from `𝔽_p((t))` to a finite nonzero ring. -/
example {R : Type*} [Ring R] [Nontrivial R] [Finite R]
    (f : LaurentSeries (ZMod p) →+* R) : False := by
  have := f.infinite_of_isTateRing
  exact not_finite R

/-- A quotient by the unit ideal is instead the zero ring, so properness is essential. -/
example : Subsingleton (ℚ_[p] ⧸ (⊤ : Ideal ℚ_[p])) := inferInstance

end TauCeti.Examples
