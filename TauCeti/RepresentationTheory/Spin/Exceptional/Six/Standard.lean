/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.GeneralLinear
public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
import TauCeti.RepresentationTheory.Spin.Exceptional.Six.HalfSpinDual
import TauCeti.RepresentationTheory.Intertwining

/-!
# The standard half-spin modules in dimension six

The matrix-product model of the even Clifford algebra of three hyperbolic planes reads its first
factor on the even half-spin module. Restricting the resulting equivalence with `GL₄` to the Spin
group therefore realizes the even half-spin representation as the standard four-dimensional
representation. The odd half-spin representation is its dual by reversal.

The comparison is stated over any field of characteristic different from two. It uses the
canonical split polarization of `splitEvenForm K 3`, so the chosen coordinates agree with the
existing matrix-product model.

## Main definitions

* `TauCeti.hyperbolicSixSpinToGeneralLinear`: the first half-spin matrix of a Spin element.

## Main results

* `TauCeti.exists_hyperbolicSix_halfSpin_equiv_stdRep_and_dual`: the even half-spin module is the
  pulled-back standard `GL₄` module, and the odd half-spin module is its dual.

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

private theorem hyperbolicSixSpinPlus_W_ne_bot :
    (splitEvenPolarization K 3).W ≠ ⊥ :=
  Submodule.finrank_eq_zero.not.1 <| by
    rw [(splitEvenPolarization K 3).finrank_W_eq_of_finrank_eq_two_mul
      (by simp [SplitEvenSpace] : finrank K (SplitEvenSpace K 3) = 2 * 3)]
    norm_num

private theorem hyperbolicSix_spinPlus_finrank :
    finrank K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) = 4 := by
  rw [finrank_spinPlus _ (hyperbolicSixSpinPlus_W_ne_bot K)]
  rw [(splitEvenPolarization K 3).finrank_W_eq_of_finrank_eq_two_mul
    (by simp [SplitEvenSpace] : finrank K (SplitEvenSpace K 3) = 2 * 3)]
  norm_num

variable [NeZero (2 : K)]

/-- The invertibility witness used by the characteristic-not-two Clifford APIs. -/
local instance hyperbolicSixStandardInvertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (NeZero.ne (2 : K))

/-- The first half-spin matrix of an element of the Spin group of three hyperbolic planes.

This is the restriction to Spin of the existing equivalence between the reverse-unitary group of
the even Clifford algebra and `GL₄`. -/
noncomputable def hyperbolicSixSpinToGeneralLinear :
    spinGroup (splitEvenForm K 3) →* Matrix.GeneralLinearGroup (Fin 4) K :=
  (hyperbolicSixEvenUnitaryEquivGeneralLinear K).toMonoidHom.comp
    (spinGroupToEvenUnitary (splitEvenForm K 3))

/-- The underlying matrix of `hyperbolicSixSpinToGeneralLinear` is the first factor of the
half-spin matrix-product model. -/
@[simp]
theorem coe_hyperbolicSixSpinToGeneralLinear_apply
    (g : spinGroup (splitEvenForm K 3)) :
    (hyperbolicSixSpinToGeneralLinear K g : Matrix (Fin 4) (Fin 4) K) =
      (hyperbolicSixEvenEquivMatrixProd K
        (spinGroupToEven (splitEvenForm K 3) g)).1 := by
  change (hyperbolicSixEvenUnitaryEquivGeneralLinear K
      (spinGroupToEvenUnitary (splitEvenForm K 3) g) : Matrix (Fin 4) (Fin 4) K) = _
  rw [coe_hyperbolicSixEvenUnitaryEquivGeneralLinear_apply]
  have heven : evenUnitaryGroupEvenPart (splitEvenForm K 3)
      (spinGroupToEvenUnitary (splitEvenForm K 3) g) =
        spinGroupToEven (splitEvenForm K 3) g := by
    apply Subtype.ext
    simp
  rw [heven]

noncomputable local instance hyperbolicSixSpinPlusFinite :
    FiniteDimensional K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) :=
  Module.finite_of_finrank_pos (by rw [hyperbolicSix_spinPlus_finrank]; norm_num)

private theorem hyperbolicSixSpinToGeneralLinear_eq_endAlgEquivMatrix
    (g : spinGroup (splitEvenForm K 3)) :
    (hyperbolicSixSpinToGeneralLinear K g : Matrix (Fin 4) (Fin 4) K) =
      Algebra.endAlgEquivMatrix K
        (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3))
        (hyperbolicSix_spinPlus_finrank K)
        (spinPlusAction (splitEvenForm K 3) (splitEvenPolarization K 3)
          (splitEvenPolarization_line K 3)
          (spinGroupToEven (splitEvenForm K 3) g)) := by
  let hW := hyperbolicSixSpinPlus_W_ne_bot K
  let hV : finrank K (SplitEvenSpace K 3) = 2 * 3 := by simp [SplitEvenSpace]
  let x := spinGroupToEven (splitEvenForm K 3) g
  calc
    (hyperbolicSixSpinToGeneralLinear K g : Matrix (Fin 4) (Fin 4) K) =
        (hyperbolicSixEvenEquivMatrixProd K x).1 :=
      coe_hyperbolicSixSpinToGeneralLinear_apply K g
    _ = ((splitEvenPolarization K 3).evenCliffordEquivProdMatrix hW hV x).1 :=
      congrArg Prod.fst (hyperbolicSixEvenEquivMatrixProd_apply K x)
    _ = _ := congrArg Prod.fst
      ((splitEvenPolarization K 3).evenCliffordEquivProdMatrix_apply hW hV x)

private theorem exists_hyperbolicSix_spinPlus_equiv_stdRep :
    Nonempty
      ((spinPlusSubrep (splitEvenPolarization K 3)
        (splitEvenPolarization_line K 3)).toRepresentation.Equiv
          ((stdRep K 4).comp (hyperbolicSixSpinToGeneralLinear K))) := by
  let P := splitEvenPolarization K 3
  let hline := splitEvenPolarization_line K 3
  let b := Module.finBasisOfFinrankEq K (spinPlus (splitEvenForm K 3) P)
    (hyperbolicSix_spinPlus_finrank K)
  let ep : spinPlus (splitEvenForm K 3) P ≃ₗ[K]
      (spinPlusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinPlusSubrep P hline).symm
  refine ⟨Representation.Equiv.mk (ep.symm.trans b.equivFun) ?_⟩
  intro g
  apply LinearMap.ext
  intro s
  have haction : ep.symm ((spinPlusSubrep P hline).toRepresentation g s) =
      spinPlusAction (splitEvenForm K 3) P hline
        (spinGroupToEven (splitEvenForm K 3) g) (ep.symm s) := by
    apply Subtype.ext
    have hsub :
        ((ep.symm ((spinPlusSubrep P hline).toRepresentation g s) :
            spinPlus (splitEvenForm K 3) P) : ExteriorAlgebra K P.W) =
          ((spinPlusAction (splitEvenForm K 3) P hline
            ⟨g, spinGroup.mem_even g.2⟩ (ep.symm s) :
              spinPlus (splitEvenForm K 3) P) : ExteriorAlgebra K P.W) := by
      simpa only [ep, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply] using
        (coe_spinPlusAction_spinGroup_apply P hline g (ep.symm s)).symm
    have heven : spinGroupToEven (splitEvenForm K 3) g =
        ⟨g, spinGroup.mem_even g.2⟩ :=
      Subtype.ext (coe_spinGroupToEven_apply (splitEvenForm K 3) g)
    exact hsub.trans (congrArg (fun x ↦
      ((spinPlusAction (splitEvenForm K 3) P hline x (ep.symm s) :
        spinPlus (splitEvenForm K 3) P) : ExteriorAlgebra K P.W)) heven.symm)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    MonoidHom.comp_apply, stdRep_apply_apply]
  rw [haction]
  have hmatrix :
      (hyperbolicSixSpinToGeneralLinear K g : Matrix (Fin 4) (Fin 4) K) =
        Algebra.endAlgEquivMatrix K (spinPlus (splitEvenForm K 3) P)
          (hyperbolicSix_spinPlus_finrank K)
          (spinPlusAction (splitEvenForm K 3) P hline
            (spinGroupToEven (splitEvenForm K 3) g)) := by
    simpa only [P, hline] using
      hyperbolicSixSpinToGeneralLinear_eq_endAlgEquivMatrix K g
  calc
    b.repr (spinPlusAction (splitEvenForm K 3) P hline
        (spinGroupToEven (splitEvenForm K 3) g) (ep.symm s)) =
        Matrix.mulVec
          (Algebra.endAlgEquivMatrix K (spinPlus (splitEvenForm K 3) P)
            (hyperbolicSix_spinPlus_finrank K)
            (spinPlusAction (splitEvenForm K 3) P hline
              (spinGroupToEven (splitEvenForm K 3) g)))
          (b.repr (ep.symm s)) := by
      simpa only [b] using
        (Algebra.endAlgEquivMatrix_mulVec_repr K (spinPlus (splitEvenForm K 3) P)
          (hyperbolicSix_spinPlus_finrank K)
          (spinPlusAction (splitEvenForm K 3) P hline
            (spinGroupToEven (splitEvenForm K 3) g)) (ep.symm s)).symm
    _ = Matrix.mulVec
        (hyperbolicSixSpinToGeneralLinear K g : Matrix (Fin 4) (Fin 4) K)
        (b.repr (ep.symm s)) := by
      exact congrArg (fun A ↦ Matrix.mulVec A (b.repr (ep.symm s))) hmatrix.symm

/-- For three hyperbolic planes, the even half-spin representation is the standard
four-dimensional representation pulled back along `hyperbolicSixSpinToGeneralLinear`, and the odd
half-spin representation is its dual. -/
theorem exists_hyperbolicSix_halfSpin_equiv_stdRep_and_dual :
    Nonempty
        ((spinPlusSubrep (splitEvenPolarization K 3)
          (splitEvenPolarization_line K 3)).toRepresentation.Equiv
            ((stdRep K 4).comp (hyperbolicSixSpinToGeneralLinear K))) ∧
      Nonempty
        ((spinMinusSubrep (splitEvenPolarization K 3)
          (splitEvenPolarization_line K 3)).toRepresentation.Equiv
            (Representation.dual
              ((stdRep K 4).comp (hyperbolicSixSpinToGeneralLinear K)))) := by
  obtain ⟨eplus⟩ := exists_hyperbolicSix_spinPlus_equiv_stdRep K
  obtain ⟨hline, ⟨eminus⟩⟩ :=
    exists_spinMinusSubrep_equiv_dual_spinPlusSubrep_of_finrank_eq_six
      (splitEvenPolarization K 3) (by simp [SplitEvenSpace])
  have hh : hline = splitEvenPolarization_line K 3 := Subsingleton.elim _ _
  cases hh
  exact ⟨⟨eplus⟩, ⟨eminus.trans eplus.dual⟩⟩

end TauCeti
