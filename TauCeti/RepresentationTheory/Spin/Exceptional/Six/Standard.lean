/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
import TauCeti.RepresentationTheory.Spin.Exceptional.Six.HalfSpinDual
import TauCeti.RepresentationTheory.Intertwining

/-!
# The standard half-spin modules in dimension six

The matrix-product model of the even Clifford algebra of three hyperbolic planes reads its first
factor on the even half-spin module. Under the resulting equivalence `Spin₆ ≃ SL₄`, this realizes
the even half-spin representation as the standard four-dimensional representation. The odd
half-spin representation is its dual by reversal.

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

universe u

variable (K : Type u) [Field K]

private theorem hyperbolicSix_spinPlus_finrank :
    finrank K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) = 4 := by
  rw [finrank_spinPlus _ (splitEvenPolarization_W_ne_bot K (by norm_num)),
    finrank_splitEvenPolarization_W K 3]
  norm_num

variable [NeZero (2 : K)]

/-- The invertibility witness used by the characteristic-not-two Clifford APIs. -/
local instance hyperbolicSixStandardInvertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (NeZero.ne (2 : K))

noncomputable local instance hyperbolicSixSpinPlusFinite :
    FiniteDimensional K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) :=
  Module.finite_of_finrank_pos (by rw [hyperbolicSix_spinPlus_finrank]; norm_num)

private theorem hyperbolicSixSpinEquivSpecialLinear_eq_toMatrix
    (g : spinGroup (splitEvenForm K 3)) :
    (hyperbolicSixSpinEquivSpecialLinear K g : Matrix (Fin 4) (Fin 4) K) =
      LinearMap.toMatrix
        (Module.finBasisOfFinrankEq K
          (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3))
          (hyperbolicSix_spinPlus_finrank K))
        (Module.finBasisOfFinrankEq K
          (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3))
          (hyperbolicSix_spinPlus_finrank K))
        (spinPlusAction (splitEvenForm K 3) (splitEvenPolarization K 3)
          (splitEvenPolarization_line K 3)
          (spinGroupToEven (splitEvenForm K 3) g)) := by
  let hW := splitEvenPolarization_W_ne_bot K (by norm_num : (3 : ℕ) ≠ 0)
  let hV := finrank_splitEvenSpace K 3
  let x := spinGroupToEven (splitEvenForm K 3) g
  calc
    (hyperbolicSixSpinEquivSpecialLinear K g : Matrix (Fin 4) (Fin 4) K) =
        hyperbolicSixEvenUnitaryEquivGeneralLinear K
          (spinGroupToEvenUnitary (splitEvenForm K 3) g) :=
      coe_hyperbolicSixSpinEquivSpecialLinear_apply K g
    _ = (hyperbolicSixEvenEquivMatrixProd K
          (evenUnitaryGroupEvenPart (splitEvenForm K 3)
            (spinGroupToEvenUnitary (splitEvenForm K 3) g))).1 :=
      coe_hyperbolicSixEvenUnitaryEquivGeneralLinear_apply K _
    _ = (hyperbolicSixEvenEquivMatrixProd K x).1 :=
      congrArg (fun y ↦ (hyperbolicSixEvenEquivMatrixProd K y).1)
        (evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply (splitEvenForm K 3) g)
    _ = ((splitEvenPolarization K 3).evenCliffordEquivProdMatrix hW hV x).1 :=
      congrArg Prod.fst (hyperbolicSixEvenEquivMatrixProd_apply K x)
    _ = Algebra.endAlgEquivMatrix K
        (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3))
        (hyperbolicSix_spinPlus_finrank K)
        (spinPlusAction (splitEvenForm K 3) (splitEvenPolarization K 3)
          (splitEvenPolarization_line K 3) x) :=
      congrArg Prod.fst
        ((splitEvenPolarization K 3).evenCliffordEquivProdMatrix_apply hW hV x)
    _ = _ := Algebra.endAlgEquivMatrix_apply K _ _ _

private theorem exists_hyperbolicSix_spinPlus_equiv_stdSLRep :
    Nonempty
      ((spinPlusSubrep (splitEvenPolarization K 3)
        (splitEvenPolarization_line K 3)).toRepresentation.Equiv
          ((stdSLRep K 4).comp (hyperbolicSixSpinEquivSpecialLinear K).toMonoidHom)) := by
  let P := splitEvenPolarization K 3
  let hline := splitEvenPolarization_line K 3
  let b := Module.finBasisOfFinrankEq K (spinPlus (splitEvenForm K 3) P)
    (hyperbolicSix_spinPlus_finrank K)
  let ep : spinPlus (splitEvenForm K 3) P ≃ₗ[K]
      (spinPlusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinPlusSubrep P hline).symm
  refine ⟨Representation.Equiv.ofBasisAction _
    ((stdSLRep K 4).comp (hyperbolicSixSpinEquivSpecialLinear K).toMonoidHom) ep.symm b
    (fun g ↦ spinPlusAction (splitEvenForm K 3) P hline
      (spinGroupToEven (splitEvenForm K 3) g)) ?_ ?_⟩
  · intro g s
    apply Subtype.ext
    simpa only [ep, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply] using
      (coe_spinPlusAction_spinGroupToEven_apply P hline g (ep.symm s)).symm
  · intro g s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, stdSLRep_apply_apply]
    rw [hyperbolicSixSpinEquivSpecialLinear_eq_toMatrix]
    exact LinearMap.toMatrix_mulVec_repr b b
      (spinPlusAction (splitEvenForm K 3) P hline
        (spinGroupToEven (splitEvenForm K 3) g)) s

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
