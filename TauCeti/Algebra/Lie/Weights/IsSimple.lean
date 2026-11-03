/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.IsSimple

/-!
# A simple Lie algebra has a root

Let `L` be a finite-dimensional simple Lie algebra over a field of characteristic zero, with a
splitting Cartan subalgebra `H`. The root system `LieAlgebra.IsKilling.rootSystem H` is irreducible,
so its weight space `H^*` is nontrivial; since the roots span `H^*`, there is at least one root.

## Main results

* `TauCeti.LieAlgebra.IsKilling.nonempty_root_of_isSimple`: the type `H.root` of roots is
  nonempty.
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule

namespace TauCeti.LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- **A simple Lie algebra has a root** with respect to every splitting Cartan subalgebra: its root
system is irreducible, so its weight space `H^*` is nontrivial and spanned by the roots. -/
instance nonempty_root_of_isSimple [IsSimple K L] : Nonempty H.root := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := RootPairing.IsIrreducible.nontrivial (P := rootSystem H)
  have hspan := RootPairing.IsRootSystem.span_root_eq_top (P := rootSystem H)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

end TauCeti.LieAlgebra.IsKilling
