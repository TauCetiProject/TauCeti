/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic

/-!
# Reversal and the even comparison of opposite real signatures

The even-algebra comparison `TauCeti.CliffordAlgebra.realCliffordEvenEquivNeg p q` of
`TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic` is the composite of Mathlib's
`CliffordAlgebra.evenEquivEvenNeg` with the even-algebra map of a coordinate isometry. Both factors
commute with Clifford reversal on even subalgebras, so the comparison does too. This file is kept
apart from the basic real forms so that their importers need not load reversal theory.

## Main results

* `TauCeti.CliffordAlgebra.realCliffordEvenEquivNeg_reverseEven`: the even comparison commutes
  with Clifford reversal.
-/

public section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

/-- `realCliffordEvenEquivNeg` commutes with Clifford reversal. Grade involution is the identity
on both even algebras (`CliffordAlgebra.involute_eq_of_mem_even`), so the comparison also commutes
with it, and hence with Clifford conjugation `star`. -/
theorem realCliffordEvenEquivNeg_reverseEven (p q : ℕ) (x : even (realCliffordForm p q)) :
    realCliffordEvenEquivNeg p q (reverseEven (realCliffordForm p q) x) =
      reverseEven (realCliffordForm q p) (realCliffordEvenEquivNeg p q x) := by
  rw [realCliffordEvenEquivNeg_apply, realCliffordEvenEquivNeg_apply,
    evenEquivEvenNeg_reverseEven, evenEquivOfIsometry_reverseEven]

end TauCeti.CliffordAlgebra
