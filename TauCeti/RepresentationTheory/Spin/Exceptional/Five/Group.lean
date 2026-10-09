/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
public import TauCeti.RepresentationTheory.Spin.Representation
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Symplectic
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
  let σ := e.symm.trans eFock
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.innerAut_surjective K σ
  have hconj (x : CliffordAlgebra.even Q) :
      eFock x = (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * e x *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)⁻¹ := by
    simpa only [σ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
      Matrix.GeneralLinearGroup.innerAut_apply] using
      (congrArg (fun τ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K ≃ₐ[K]
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => τ (e x)) hg).symm
  let ψ := (spinFiveExteriorBasis P b).equivFun.trans
    (Matrix.GeneralLinearGroup.toLin g⁻¹).toLinearEquiv
  refine ⟨f, ⟨Representation.Equiv.mk ψ ?_⟩⟩
  intro s
  apply LinearMap.ext
  intro x
  have haction := LinearMap.congr_fun
    (P.evenCliffordEquivEnd_toMatrix_intertwines_spinRep
      (hV ▸ by decide) (spinFiveExteriorBasis P b) s) x
  simp only [LinearMap.comp_apply] at haction
  have haction' :
      (spinFiveExteriorBasis P b).equivFun ((spinRep Q P) s x) =
        Matrix.mulVec (eFock (spinGroupToEven Q s))
          ((spinFiveExteriorBasis P b).equivFun x) := by
    simpa only [eFock, spinFiveEquivMatrix, Matrix.mulVecLin_apply,
      LinearEquiv.coe_toLinearMap] using haction
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
  rw [haction', hfmatrix]
  -- Identify the general-linear action with multiplication by its matrix carrier.
  change Matrix.mulVec
      (↑(g⁻¹) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Matrix.mulVec (eFock (spinGroupToEven Q s))
        ((spinFiveExteriorBasis P b).equivFun x)) = _
  rw [hconj]
  -- The intertwining equation is now cancellation of the conjugating matrix.
  change Matrix.mulVec
      (↑(g⁻¹) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Matrix.mulVec
        ((↑g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          e (spinGroupToEven Q s) *
            (↑g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)⁻¹)
        ((spinFiveExteriorBasis P b).equivFun x)) =
    Matrix.mulVec (e (spinGroupToEven Q s))
      (Matrix.mulVec
        (↑(g⁻¹) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        ((spinFiveExteriorBasis P b).equivFun x))
  simp only [Matrix.mulVec_mulVec]
  apply congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K =>
    Matrix.mulVec M ((spinFiveExteriorBasis P b).equivFun x))
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul,
    Matrix.GeneralLinearGroup.coe_inv]

end TauCeti
