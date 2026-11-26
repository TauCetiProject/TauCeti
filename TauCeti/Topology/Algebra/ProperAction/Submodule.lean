/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Proper translation actions of subspaces

A finite-dimensional subspace `W` of a normed space `V` over a complete nontrivially normed field
is closed, so it acts properly on `V` by translations (`Submodule.properVAdd`). Through
`Multiplicative.properSMul`, so does the group `Multiplicative W`.

## Main results

* `Submodule.properVAdd`: a finite-dimensional subspace acts properly by translations.
-/

public section

namespace Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- A finite-dimensional subspace `W` of a normed space `V` over a complete field acts properly on
`V` by translations, since it is closed. Through `Multiplicative.properSMul`, so does the group
`Multiplicative W`. -/
instance properVAdd (W : Submodule 𝕜 V) [FiniteDimensional 𝕜 W] : ProperVAdd W V :=
  have : IsClosed (W.toAddSubgroup : Set V) := W.isClosed_of_finiteDimensional
  inferInstanceAs (ProperVAdd W.toAddSubgroup V)

end Submodule
