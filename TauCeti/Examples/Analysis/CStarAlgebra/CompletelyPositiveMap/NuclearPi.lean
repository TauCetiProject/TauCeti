/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Pi

/-!
# Check: finite direct sums of matrix algebras are nuclear

`M_1(ℂ) ⊕ M_2(ℂ) ⊕ M_3(ℂ)` is nuclear, through its block-diagonal embedding in `M_6(ℂ)` and the
compression back to the diagonal blocks.
-/

public section

open scoped ComplexOrder

namespace TauCeti.CStarAlgebra

/-- `M_1(ℂ) ⊕ M_2(ℂ) ⊕ M_3(ℂ)` is nuclear. -/
example : IsNuclear (∀ i : Fin 3, CStarMatrix (Fin (i + 1)) (Fin (i + 1)) ℂ) := inferInstance

end TauCeti.CStarAlgebra
