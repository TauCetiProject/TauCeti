/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
public import TauCeti.RepresentationTheory.Spin.Representation
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Symplectic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut
import TauCeti.RepresentationTheory.Spin.OddStructure

/-!
# The five-dimensional Spin group and its standard representation

For a five-dimensional quadratic space with polarization data over a field with `2 ≠ 0`, the
even Clifford algebra acts faithfully on the four-dimensional spinor module. Clifford reversal is
a symplectic involution, identifying the Spin group with `Sp₄`. The matrix model supplied by the
symplectic involution need not use the Fock basis, but Skolem–Noether conjugates it to that basis.
The inverse conjugating matrix then identifies the spin representation with the standard
representation of `Sp₄`.
Over a separably closed field with `2 ≠ 0`, every nondegenerate five-dimensional quadratic space
admits polarization data via `SpinPolarizationData.ofNondegenerate`, so its spin representation is
the standard representation of `Sp₄`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
* M.-A. Knus and M. Ojanguren, *Théorie de la descente et algèbres d'Azumaya*, Chapter IV.
-/

public section

open CliffordAlgebra Module QuadraticMap

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

private noncomputable def spinFiveIndexEquiv : Finset (Fin 2) ≃ Fin 2 ⊕ Fin 2 :=
  Fintype.equivOfCardEq (by simp)

private noncomputable def spinFiveExteriorBasis
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    Basis (Fin 2 ⊕ Fin 2) K (ExteriorAlgebra K P.W) :=
  b.ExteriorAlgebra.reindex spinFiveIndexEquiv

private noncomputable def spinFiveEquivMatrix
    [NeZero (2 : K)] [FiniteDimensional K V]
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W)
    (hV : finrank K V = 5) :
    ↥(CliffordAlgebra.even Q) ≃ₐ[K] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  (P.evenCliffordEquivEnd (hV ▸ by decide)).trans
    (LinearMap.toMatrixAlgEquiv (spinFiveExteriorBasis P b))

/-- In the Fock coordinates, the spin representation acts through the matrix model of the even
Clifford algebra. -/
private theorem equivFun_spinRep_apply [NeZero (2 : K)] [FiniteDimensional K V]
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) (hV : finrank K V = 5)
    (s : spinGroup Q) (x : ExteriorAlgebra K P.W) :
    (spinFiveExteriorBasis P b).equivFun ((spinRep Q P) s x) =
      Matrix.mulVec (spinFiveEquivMatrix P b hV (spinGroupToEven Q s))
        ((spinFiveExteriorBasis P b).equivFun x) := by
  have haction := LinearMap.congr_fun
    (P.evenCliffordEquivEnd_toMatrix_intertwines_spinRep
      (hV ▸ by decide) (spinFiveExteriorBasis P b) s) x
  simp only [LinearMap.comp_apply] at haction
  simpa only [spinFiveEquivMatrix, Matrix.mulVecLin_apply, LinearEquiv.coe_toLinearMap] using
    haction

/-- For a five-dimensional quadratic space with polarization data over a field with `2 ≠ 0`,
there is an equivalence from its Spin group to `Sp₄` under which the spin representation is the
standard four-dimensional representation. -/
theorem
    exists_spinGroup_mulEquiv_symplecticGroup_and_spinRep_equiv_stdSymplecticRep_of_finrank_eq_five
    [NeZero (2 : K)] (P : SpinPolarizationData Q) (hV : finrank K V = 5) :
    ∃ f : spinGroup Q ≃* Matrix.symplecticGroup (Fin 2) K,
      Nonempty ((spinRep Q P).Equiv ((stdSymplecticRep K 2).comp f.toMonoidHom)) := by
  let _ : FiniteDimensional K V := .of_finrank_eq_succ (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  have hW : finrank K P.W = 2 :=
    P.finrank_W_eq_of_finrank_eq_two_mul_add_one (l := 2) (by omega)
  let b := Module.finBasisOfFinrankEq K P.W hW
  let eFock := spinFiveEquivMatrix P b hV
  -- The involution theorem uses `Fin 4`; reindexing only supplies its input matrix model.
  let eFockFour := eFock.trans (Matrix.reindexAlgEquiv K K
    (Fintype.equivOfCardEq (by simp) : (Fin 2 ⊕ Fin 2) ≃ Fin 4))
  obtain ⟨e, he⟩ :=
    CliffordAlgebra.exists_algEquiv_reverseEven_eq_neg_J_mul_transpose_mul_J Q hV eFockFour
  let f := CliffordAlgebra.spinGroupEquivSymplecticGroup Q
    (P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K))
    (by omega) hV.le e he
  obtain ⟨g, hconj⟩ := e.exists_forall_eq_mul_mul_inv eFock
  refine ⟨f, ⟨Representation.Equiv.mk
    ((spinFiveExteriorBasis P b).equivFun.trans (Matrix.GeneralLinearGroup.toLin g⁻¹).toLinearEquiv)
    ?_⟩⟩
  intro s
  apply LinearMap.ext
  intro x
  have hfmatrix :
      (f s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        e (spinGroupToEven Q s) := by
    -- Expose the matrix carrier of the symplectic-group equivalence.
    change (CliffordAlgebra.spinGroupEquivSymplecticGroup Q
      (P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K))
      (by omega) hV.le e he s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
    rw [CliffordAlgebra.coe_spinGroupEquivSymplecticGroup_apply]
    congr 1
    apply Subtype.ext
    simp
  simp only [LinearMap.comp_apply, MonoidHom.comp_apply, stdSymplecticRep_apply]
  -- Unfold the chosen coordinate equivalence on both sides of equivariance.
  change (Matrix.GeneralLinearGroup.toLin g⁻¹).toLinearEquiv
      ((spinFiveExteriorBasis P b).equivFun ((spinRep Q P) s x)) =
    Matrix.mulVecLin (f s)
      ((Matrix.GeneralLinearGroup.toLin g⁻¹).toLinearEquiv
        ((spinFiveExteriorBasis P b).equivFun x))
  simp only [Matrix.mulVecLin_apply]
  rw [equivFun_spinRep_apply P b hV, hfmatrix]
  simp only [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply]
  exact Matrix.GeneralLinearGroup.inv_mulVec_mulVec_of_eq_mul_mul_inv g (hconj _) _

/-- A nondegenerate five-dimensional quadratic space over a separably closed field of
characteristic different from two admits polarization data identifying its Spin group with
`Sp₄`, under which the spin representation is standard. -/
theorem
    exists_spinGroup_mulEquiv_symplecticGroup_and_spinRep_equiv_stdSymplecticRep_of_isSepClosed
    [NeZero (2 : K)] [IsSepClosed K] (hQ : Q.Nondegenerate) (hV : finrank K V = 5) :
    ∃ P : SpinPolarizationData Q, ∃ f : spinGroup Q ≃* Matrix.symplecticGroup (Fin 2) K,
      Nonempty ((spinRep Q P).Equiv ((stdSymplecticRep K 2).comp f.toMonoidHom)) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let P := SpinPolarizationData.ofNondegenerate Q hQ
  obtain ⟨f, hf⟩ :=
    exists_spinGroup_mulEquiv_symplecticGroup_and_spinRep_equiv_stdSymplecticRep_of_finrank_eq_five
      P hV
  exact ⟨P, f, hf⟩

end TauCeti
