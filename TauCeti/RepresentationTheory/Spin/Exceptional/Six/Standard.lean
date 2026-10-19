/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear
public import TauCeti.RepresentationTheory.Spin.HalfSpin.Standard
import TauCeti.RepresentationTheory.Spin.Exceptional.Six.HalfSpinDual
import TauCeti.RepresentationTheory.Intertwining

/-!
# The standard half-spin modules in dimension six

The matrix-product model of the even Clifford algebra of three hyperbolic planes reads its first
factor on the even half-spin module. Under the resulting equivalence `Spin₆ ≃ SL₄`, this
realizes the even half-spin representation as the standard four-dimensional representation. The
odd half-spin representation is its dual by reversal.

The comparison is stated over any field of characteristic different from two. It uses the
canonical split polarization of `splitEvenForm K 3`, so the chosen coordinates agree with the
existing matrix-product model.

## Main results

* `TauCeti.nonempty_hyperbolicSix_halfSpin_equiv_stdSLRep_and_dual`: the even half-spin module is
  the pulled-back standard `SL₄` module, and the odd half-spin module is its dual.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open _root_.CliffordAlgebra

namespace TauCeti

open Module

universe u v

variable (K : Type u) [Field K]

variable [NeZero (2 : K)]

/-- The invertibility witness used by the characteristic-not-two Clifford APIs. -/
local instance hyperbolicSixStandardInvertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (NeZero.ne (2 : K))

private theorem exists_hyperbolicSix_spinPlus_equiv_stdSLRep :
    Nonempty
      ((spinPlusSubrep (splitEvenPolarization K 3)
        (splitEvenPolarization_line K 3)).toRepresentation.Equiv
          ((stdSLRep K 4).comp (hyperbolicSixSpinEquivSpecialLinear K).toMonoidHom)) := by
  let P := splitEvenPolarization K 3
  let hline := splitEvenPolarization_line K 3
  let hW := splitEvenPolarization_W_ne_bot K (by norm_num : (3 : ℕ) ≠ 0)
  let hV := finrank_splitEvenSpace K 3
  let b := Module.finBasisOfFinrankEq K (spinPlus (splitEvenForm K 3) P)
    (finrank_hyperbolicSixSpinPlus K)
  let hWfin : finrank K P.W = 3 := by
    simp [P]
  have hmatrix := fun s ↦ coe_spinGroupMulEquivSpecialLinearGroup_apply P hline hWfin hW
    (finrank_hyperbolicSixSpinPlus K) hV b rfl s
  exact nonempty_spinPlusSubrep_equiv_stdSLRep_of_matrix_action hline b
    (hyperbolicSixSpinEquivSpecialLinear K).toMonoidHom (by
      exact hmatrix)

/-- For three hyperbolic planes, the even half-spin representation is the standard
four-dimensional representation pulled back along `hyperbolicSixSpinEquivSpecialLinear`, and the
odd half-spin representation is its dual. -/
theorem nonempty_hyperbolicSix_halfSpin_equiv_stdSLRep_and_dual :
    Nonempty
        ((spinPlusSubrep (splitEvenPolarization K 3)
          (splitEvenPolarization_line K 3)).toRepresentation.Equiv
            ((stdSLRep K 4).comp
              (hyperbolicSixSpinEquivSpecialLinear K).toMonoidHom)) ∧
      Nonempty
        ((spinMinusSubrep (splitEvenPolarization K 3)
          (splitEvenPolarization_line K 3)).toRepresentation.Equiv
            (Representation.dual
              ((stdSLRep K 4).comp
                (hyperbolicSixSpinEquivSpecialLinear K).toMonoidHom))) := by
  obtain ⟨eplus⟩ := exists_hyperbolicSix_spinPlus_equiv_stdSLRep K
  obtain ⟨hline, ⟨eminus⟩⟩ :=
    exists_spinMinusSubrep_equiv_dual_spinPlusSubrep_of_finrank_eq_six
      (splitEvenPolarization K 3)
        ((finrank_splitEvenSpace K 3).trans (by norm_num : (2 : ℕ) * 3 = 6))
  have hh : hline = splitEvenPolarization_line K 3 := Subsingleton.elim _ _
  cases hh
  exact ⟨⟨eplus⟩, ⟨eminus.trans eplus.dual⟩⟩

end TauCeti
