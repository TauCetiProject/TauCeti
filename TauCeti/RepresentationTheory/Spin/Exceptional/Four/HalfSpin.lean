/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.MatrixProd
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import TauCeti.RepresentationTheory.Spin.Structure
public import Mathlib.RepresentationTheory.Intertwining

/-!
# The half-spin representations of the four-dimensional Spin group

For a polarized four-dimensional quadratic space over a field of characteristic different from
two, the two half-spin modules have dimension two. Their paired action identifies the even
Clifford algebra with `M₂ × M₂`. Reversal becomes adjugation in each factor, and the exact
low-rank Spin/unitary comparison gives `Spin₄ ≅ SL₂ × SL₂` in this same model.

Under this group equivalence, `S⁺` is the standard representation of the first factor and `S⁻`
is the standard representation of the second. The result concerns the existing half-spin
subrepresentations of the Fock representation, rather than independently chosen two-dimensional
modules. It holds over any field admitting the given polarization, in particular over `ℂ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

namespace TauCeti

open Module CliffordAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- For a polarized quaternary quadratic space, there is an equivalence `Spin₄ ≅ SL₂ × SL₂`
under which its even and odd half-spin subrepresentations are the standard representations of
the first and second factors, respectively. The equivalence chooses bases of the half-spin spaces.

The witness `hline` records that the polarization has no residual line, as follows from dimension
four; it is also the proof used to define the existing half-spin subrepresentations. -/
theorem
    exists_spinGroup_mulEquiv_specialLinearGroup_prod_and_halfSpin_equiv_stdSLRep_of_finrank_eq_four
    [NeZero (2 : K)] (P : SpinPolarizationData Q) (hV : finrank K V = 4) :
    ∃ (hline : P.line = ⊥)
      (f : spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 2) K ×
        Matrix.SpecialLinearGroup (Fin 2) K),
      Nonempty ((spinPlusSubrep P hline).toRepresentation.Equiv
        ((stdSLRep K 2).comp ((MonoidHom.fst _ _).comp f.toMonoidHom))) ∧
      Nonempty ((spinMinusSubrep P hline).toRepresentation.Equiv
        ((stdSLRep K 2).comp ((MonoidHom.snd _ _).comp f.toMonoidHom))) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  have hline : P.line = ⊥ := P.line_eq_bot_of_even_finrank (hV ▸ by decide)
  have hWfin : finrank K P.W = 2 :=
    P.finrank_W_eq_of_finrank_eq_two_mul (l := 2) (by omega)
  have hW : P.W ≠ ⊥ := Submodule.finrank_eq_zero.not.1 (by omega)
  have hplus : finrank K (spinPlus Q P) = 2 := by simp [finrank_spinPlus P hW, hWfin]
  have hminus : finrank K (spinMinus Q P) = 2 := by simp [finrank_spinMinus P hW, hWfin]
  let bplus := Module.finBasisOfFinrankEq K (spinPlus Q P) hplus
  let bminus := Module.finBasisOfFinrankEq K (spinMinus Q P) hminus
  let e := (P.evenCliffordEquivProdEnd hline).trans
    ((LinearMap.toMatrixAlgEquiv bplus).prodCongr (LinearMap.toMatrixAlgEquiv bminus))
  let f := spinGroupEquivSpecialLinearProdOfAlgEquiv Q
    (P.nondegenerate_of_line_eq_bot hline) hV e
  -- Choose the group equivalence from the paired half-spin matrix model. Its two factors
  -- are therefore the matrices of the half-spin actions in these same bases.
  have hmatrix (g : spinGroup Q) :
      (((f g).1 : Matrix (Fin 2) (Fin 2) K), ((f g).2 : Matrix (Fin 2) (Fin 2) K)) =
        (LinearMap.toMatrix bplus bplus (spinPlusAction Q P hline (spinGroupToEven Q g)),
          LinearMap.toMatrix bminus bminus (spinMinusAction Q P hline (spinGroupToEven Q g))) := by
    have h := coe_spinGroupEquivSpecialLinearProdOfAlgEquiv_apply Q
      (P.nondegenerate_of_line_eq_bot hline) hV e g
    have heven : evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q g) =
        spinGroupToEven Q g := by
      apply Subtype.ext
      simp
    rw [heven] at h
    have he (x : even Q) : e x =
        (LinearMap.toMatrix bplus bplus (spinPlusAction Q P hline x),
          LinearMap.toMatrix bminus bminus (spinMinusAction Q P hline x)) := by
      simp only [e, AlgEquiv.trans_apply, AlgEquiv.prodCongr_apply,
        P.evenCliffordEquivProdEnd_apply, evenSpinActionProd_apply,
        LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply,
        Equiv.prodCongr_apply, Prod.map_apply, AlgEquiv.coe_toEquiv]
    rw [he] at h
    exact h
  let ep : spinPlus Q P ≃ₗ[K] (spinPlusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinPlusSubrep P hline).symm
  let em : spinMinus Q P ≃ₗ[K] (spinMinusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinMinusSubrep P hline).symm
  refine ⟨hline, f, ⟨?_, ?_⟩⟩
  · refine ⟨Representation.Equiv.mk (ep.symm.trans bplus.equivFun) ?_⟩
    intro g
    apply LinearMap.ext
    intro s
    have haction : ep.symm ((spinPlusSubrep P hline).toRepresentation g s) =
        spinPlusAction Q P hline (spinGroupToEven Q g) (ep.symm s) := by
      apply Subtype.ext
      have heven : spinGroupToEven Q g = ⟨g, spinGroup.mem_even g.2⟩ :=
        Subtype.ext (coe_spinGroupToEven_apply Q g)
      rw [heven]
      simpa only [ep, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply] using
        (coe_spinPlusAction_spinGroup_apply P hline g (ep.symm s)).symm
    -- Transport the actual subrepresentation to its parity submodule, then use Mathlib's
    -- coordinate formula for the matrix of an endomorphism.
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      MonoidHom.comp_apply, MonoidHom.coe_fst, MulEquiv.coe_toMonoidHom, stdSLRep_apply_apply]
    have hfactor : ((f g).1 : Matrix (Fin 2) (Fin 2) K) =
        LinearMap.toMatrix bplus bplus
          (spinPlusAction Q P hline (spinGroupToEven Q g)) := congrArg Prod.fst (hmatrix g)
    rw [haction, hfactor]
    exact (LinearMap.toMatrix_mulVec_repr bplus bplus
      (spinPlusAction Q P hline (spinGroupToEven Q g)) (ep.symm s)).symm
  · refine ⟨Representation.Equiv.mk (em.symm.trans bminus.equivFun) ?_⟩
    intro g
    apply LinearMap.ext
    intro s
    have haction : em.symm ((spinMinusSubrep P hline).toRepresentation g s) =
        spinMinusAction Q P hline (spinGroupToEven Q g) (em.symm s) := by
      apply Subtype.ext
      have heven : spinGroupToEven Q g = ⟨g, spinGroup.mem_even g.2⟩ :=
        Subtype.ext (coe_spinGroupToEven_apply Q g)
      rw [heven]
      simpa only [em, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply] using
        (coe_spinMinusAction_spinGroup_apply P hline g (em.symm s)).symm
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      MonoidHom.comp_apply, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom, stdSLRep_apply_apply]
    have hfactor : ((f g).2 : Matrix (Fin 2) (Fin 2) K) =
        LinearMap.toMatrix bminus bminus
          (spinMinusAction Q P hline (spinGroupToEven Q g)) := congrArg Prod.snd (hmatrix g)
    rw [haction, hfactor]
    exact (LinearMap.toMatrix_mulVec_repr bminus bminus
      (spinMinusAction Q P hline (spinGroupToEven Q g)) (em.symm s)).symm

end TauCeti
