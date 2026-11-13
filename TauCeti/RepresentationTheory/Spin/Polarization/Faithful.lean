/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.Representation
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation
import TauCeti.RepresentationTheory.Spin.OddStructure

/-!
# Faithfulness of the spin Lie representations

The full spin representations of the split odd and even orthogonal Lie algebras are
faithful over every field in which two is invertible. This supplies the injective Lie action
needed to regard their admissible spin lattices as faithful Chevalley representations.
The type-D result concerns the full exterior spinor module, not either half-spin summand.

In odd dimension the action of the whole Clifford algebra is not faithful. Its restriction
to the even subalgebra is nevertheless faithful, and the quadratic Lie algebra lies in that
subalgebra. In even dimension the whole Clifford action is faithful. We combine these two
structure theorems as `TauCeti.spinAction_injOn_even` and apply it to the independently
constructed quadratic realizations of the orthogonal Lie algebras.

The central formal inputs are `TauCeti.spinAction_injective`,
`TauCeti.evenSpinAction_injective`, and the numbered quadratic realizations
`TauCeti.SpinPolarizationData.typeBQuadraticEquiv` and
`TauCeti.SpinPolarizationData.typeDQuadraticEquiv`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v w

/-- The Clifford action of a finite-dimensional polarized quadratic space is faithful on
the even subalgebra, in either parity of the dimension. In odd dimension this does not
extend to the whole Clifford algebra. -/
theorem spinAction_injOn_even {K : Type u} [Field K] [Invertible (2 : K)]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (P : SpinPolarizationData Q) :
    Set.InjOn (spinAction Q P) (even Q : Set (CliffordAlgebra Q)) := by
  rcases Nat.even_or_odd (finrank K V) with heven | hodd
  · exact (spinAction_injective P heven).injOn
  · have : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
    intro x hx y hy hxy
    have h := evenSpinAction_injective P hodd
      (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩)
      (by simpa only [evenSpinAction_apply] using hxy)
    exact congrArg Subtype.val h

namespace SpinPolarizationData

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W)
  [Invertible (2 : K)]

/-- The spin representation of the split odd orthogonal Lie algebra is faithful.
No characteristic-zero assumption is needed. -/
theorem typeBSpinLieRep_injective (z : P.line) (hz : Q (z : V) = 1) :
    Function.Injective (P.typeBSpinLieRep b z hz) := by
  have := Module.Finite.of_basis (P.typeBBasis b z hz)
  intro x y hxy
  apply (P.typeBQuadraticEquiv b z hz).injective
  apply Subtype.ext
  exact spinAction_injOn_even P
    (quadraticLieSubalgebra_le_even Q (P.typeBQuadraticEquiv b z hz x).property)
    (quadraticLieSubalgebra_le_even Q (P.typeBQuadraticEquiv b z hz y).property)
    (by simpa only [typeBSpinLieRep_apply, LieEquiv.coe_toLieHom] using hxy)

/-- The full spin representation of the split even orthogonal Lie algebra is faithful.
This asserts faithfulness on the sum of the two half-spin modules, not on either summand. -/
theorem typeDSpinLieRep_injective (hline : P.line = ⊥) :
    Function.Injective (P.typeDSpinLieRep b hline) := by
  have := Module.Finite.of_basis (P.typeDBasis b hline)
  intro x y hxy
  apply (P.typeDQuadraticEquiv b hline).injective
  apply Subtype.ext
  exact spinAction_injOn_even P
    (quadraticLieSubalgebra_le_even Q (P.typeDQuadraticEquiv b hline x).property)
    (quadraticLieSubalgebra_le_even Q (P.typeDQuadraticEquiv b hline y).property)
    (by simpa only [typeDSpinLieRep_apply, LieEquiv.coe_toLieHom] using hxy)

end SpinPolarizationData

end TauCeti
