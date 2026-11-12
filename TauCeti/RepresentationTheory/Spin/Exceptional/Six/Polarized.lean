/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import TauCeti.RepresentationTheory.Spin.Exceptional.Six.HalfSpinDual
import TauCeti.RepresentationTheory.Spin.HalfSpin.Standard

/-!
# The standard half-spin modules of a polarized six-dimensional space

Over a field of characteristic different from two, polarization identifies the even Clifford
algebra of a six-dimensional quadratic space with a product of two four-by-four matrix algebras.
Its first factor gives an equivalence from the Spin group to `SL₄`, under which the even
half-spin module is the standard representation. The odd half-spin module is its dual.

This packages the group equivalence and both representation equivalences together, with both
half-spin identifications taken along the same equivalence `f : spinGroup Q ≃* SL₄`.

## Main result

* `exists_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_and_halfSpin_equiv_stdSLRep_and_dual`:
  a polarization of a six-dimensional quadratic space over a field of characteristic different
  from two identifies its Spin group with `SL₄`, its even half-spin representation with the
  standard module, and its odd half-spin representation with the dual standard module.
* The theorem
  `exists_spinPolarizationData_and_spinGroupEquivSpecialLinear_and_halfSpin_equiv_stdSLRep_and_dual`
  says that over a separably closed field of characteristic different from two, a nondegenerate
  six-dimensional quadratic space admits such a polarization and comparison.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* `TauCeti.RepresentationTheory.Spin.Exceptional.Six.Standard` supplies the split half-spin
  comparison generalized here.
* `TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear` supplies the polarized
  Spin-to-special-linear equivalence, and `HalfSpinDual` supplies the half-spin duality used below.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- Over a field with `2 ≠ 0`, a polarization of a six-dimensional
quadratic space identifies its Spin group with `SL₄` so that the even half-spin representation
is standard and the odd half-spin representation is its dual, along the same equivalence
`f : spinGroup Q ≃* SL₄`. -/
theorem
    exists_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_and_halfSpin_equiv_stdSLRep_and_dual
    [NeZero (2 : K)] (P : SpinPolarizationData Q) (hV : finrank K V = 6) :
    ∃ hline : P.line = ⊥, ∃ f : spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 4) K,
      Nonempty ((spinPlusSubrep P hline).toRepresentation.Equiv
        ((stdSLRep K 4).comp f.toMonoidHom)) ∧
      Nonempty ((spinMinusSubrep P hline).toRepresentation.Equiv
        (Representation.dual ((stdSLRep K 4).comp f.toMonoidHom))) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  have hline : P.line = ⊥ := P.line_eq_bot_of_even_finrank (hV ▸ by decide)
  let φ := spinGroupEquivSpecialLinearGroupOfFinrankEqSix P hV
  have h := nonempty_spinPlusSubrep_equiv_stdSLRep_of_matrix_action hline _ φ.toMonoidHom
    (coe_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_apply P hV)
  exact ⟨hline, φ, h, nonempty_spinMinusSubrep_equiv_dual_of_spinPlusSubrep_equiv P hV hline _ h⟩

/-- A nondegenerate six-dimensional quadratic space over a separably closed field with `2 ≠ 0`
admits a polarization and an equivalence from its Spin group to `SL₄` under which the half-spin
representations are the standard module and its dual. -/
theorem
    exists_spinPolarizationData_and_spinGroupEquivSpecialLinear_and_halfSpin_equiv_stdSLRep_and_dual
    [NeZero (2 : K)] [IsSepClosed K] (hQ : Q.Nondegenerate) (hV : finrank K V = 6) :
    ∃ P : SpinPolarizationData Q, ∃ hline : P.line = ⊥,
      ∃ f : spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 4) K,
        Nonempty ((spinPlusSubrep P hline).toRepresentation.Equiv
          ((stdSLRep K 4).comp f.toMonoidHom)) ∧
        Nonempty ((spinMinusSubrep P hline).toRepresentation.Equiv
          (Representation.dual ((stdSLRep K 4).comp f.toMonoidHom))) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let P := SpinPolarizationData.ofNondegenerate Q hQ
  obtain ⟨hline, f, hplus, hminus⟩ :=
    exists_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_and_halfSpin_equiv_stdSLRep_and_dual
      P hV
  exact ⟨P, hline, f, hplus, hminus⟩

end TauCeti

end
