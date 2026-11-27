/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Products of finitely many fibres of a finite-rank vector bundle

For a vector bundle `E` with finite-dimensional model fibre `F` and finitely many base points
`x : ι → B`, the product `Π i, E (x i)` of the fibres is finite-dimensional
(`VectorBundle.finiteDimensional_pi`), of dimension `Nat.card ι * finrank R F`
(`VectorBundle.finrank_pi`).
-/

public section

namespace VectorBundle

open Bundle Module

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
  [NontriviallyNormedField R] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]
  [NormedAddCommGroup F] [NormedSpace R F]
  [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module R (E x)] [VectorBundle R F E]
  [FiniteDimensional R F]

include F

/-- The product of the fibres of a finite-rank vector bundle at finitely many points is
finite-dimensional. -/
protected theorem finiteDimensional_pi {ι : Type*} [Finite ι] (x : ι → B) :
    FiniteDimensional R (Π i, E (x i)) :=
  have (i : ι) : FiniteDimensional R (E (x i)) := VectorBundle.finiteDimensional R F E (x i)
  inferInstance

/-- The product of the fibres of a finite-rank vector bundle at finitely many points has dimension
the number of points times the rank. -/
protected theorem finrank_pi {ι : Type*} [Finite ι] (x : ι → B) :
    finrank R (Π i, E (x i)) = Nat.card ι * finrank R F := by
  have := Fintype.ofFinite ι
  have (i : ι) : FiniteDimensional R (E (x i)) := VectorBundle.finiteDimensional R F E (x i)
  simp [Module.finrank_pi_fintype, VectorBundle.finrank_eq R F E, Nat.card_eq_fintype_card]

end VectorBundle
