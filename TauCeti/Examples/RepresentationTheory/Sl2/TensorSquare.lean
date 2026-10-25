/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.ClebschGordan

/-!
# The tensor square of the two-dimensional standard sl₂ module

The two actual Clebsch–Gordan submodules of `V(1) ⊗ V(1)` are an internal direct sum,
isomorphic to `V(2)` and `V(0)`, and have dimensions three and one respectively.
The assertions concern the constructed Lie submodules, not merely a formal character identity.


-/

public section

namespace TauCeti.Sl2Std

open LieAlgebra

variable (K : Type*) [Field K] [CharZero K]

/-- The two actual summands span `V(1) ⊗ V(1)` independently. -/
example :
    DirectSum.IsInternal fun k : Fin 2 ↦ (cgSummand K 1 1 k).toSubmodule :=
  isInternal_cgSummand (K := K) (m := 1) (n := 1)

/-- The highest-weight-two summand in the tensor square is `V(2)`. -/
example :
    Nonempty ((cgSummand K 1 1 (0 : Fin 2) : Type _) ≃ₗ⁅K,
      SpecialLinear.sl (Fin 2) K⁆ Sl2Std K 2) :=
  nonempty_lieModuleEquiv_cgSummand (K := K) (m := 1) (n := 1) (0 : Fin 2)

/-- The highest-weight-zero summand in the tensor square is `V(0)`. -/
example :
    Nonempty ((cgSummand K 1 1 (1 : Fin 2) : Type _) ≃ₗ⁅K,
      SpecialLinear.sl (Fin 2) K⁆ Sl2Std K 0) :=
  nonempty_lieModuleEquiv_cgSummand (K := K) (m := 1) (n := 1) (1 : Fin 2)

/-- The two actual summands have dimensions three and one. -/
example :
    Module.finrank K (cgSummand K 1 1 (0 : Fin 2)) = 3 ∧
    Module.finrank K (cgSummand K 1 1 (1 : Fin 2)) = 1 :=
  ⟨finrank_cgSummand (K := K) (m := 1) (n := 1) (0 : Fin 2),
    finrank_cgSummand (K := K) (m := 1) (n := 1) (1 : Fin 2)⟩

end TauCeti.Sl2Std
