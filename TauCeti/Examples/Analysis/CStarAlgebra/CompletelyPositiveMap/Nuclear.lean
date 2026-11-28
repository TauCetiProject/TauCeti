/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear.Commutative
public import Mathlib.Topology.UnitInterval

/-!
# Checks for nuclear completely positive maps

The full matrix algebras `M_n(ℂ)`, over any finite index type, and `ℂ` itself are nuclear
C⋆-algebras: the identity factors exactly through a matrix algebra. So is the finite direct sum
`M_1(ℂ) ⊕ M_2(ℂ) ⊕ M_3(ℂ)`, through its block-diagonal embedding in `M_6(ℂ)` and the compression
back to the diagonal blocks. The zero map between any two C⋆-algebras is a nuclear contraction,
through the zero matrix algebra `M_0`, and multiples `c • φ` with `c ≤ 1` of nuclear contractions
are nuclear contractions. The commutative C⋆-algebra `C[0,1]` is nuclear.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti.NuclearExample

/-- `ℂ` is nuclear. -/
example : TauCeti.CStarAlgebra.IsNuclear ℂ := inferInstance

/-- `M_3(ℂ)` is nuclear. -/
example : TauCeti.CStarAlgebra.IsNuclear (CStarMatrix (Fin 3) (Fin 3) ℂ) := inferInstance

/-- `M_{Bool × Bool}(ℂ)`, a matrix algebra over an index type other than `Fin n`, is nuclear. -/
example : TauCeti.CStarAlgebra.IsNuclear (CStarMatrix (Bool × Bool) (Bool × Bool) ℂ) :=
  inferInstance

/-- `M_1(ℂ) ⊕ M_2(ℂ) ⊕ M_3(ℂ)` is nuclear. -/
example : TauCeti.CStarAlgebra.IsNuclear (∀ i : Fin 3, CStarMatrix (Fin (i + 1)) (Fin (i + 1)) ℂ) :=
  inferInstance

/-- The zero map `ℂ → M_2(ℂ)` is a nuclear contraction, through `M_0`. -/
example : (0 : ℂ →CP CStarMatrix (Fin 2) (Fin 2) ℂ).IsNuclearContraction :=
  CompletelyPositiveMap.isNuclearContraction_zero

/-- Half the identity of `ℂ` is a nuclear contraction, and so it is nuclear. -/
example : ((1 / 2 : NNReal) • CompletelyPositiveMap.id ℂ).IsNuclear :=
  (TauCeti.CStarAlgebra.IsNuclear.isNuclearContraction_id.smul (by norm_num)).isNuclear

/-- The identity of `C[0,1]` is a nuclear completely positive map. -/
example : TauCeti.CStarAlgebra.IsNuclear C(unitInterval, ℂ) := inferInstance

end TauCeti.NuclearExample
