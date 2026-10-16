/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import TauCeti.RepresentationTheory.Spin.Exceptional.Six.HalfSpinDual
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic

/-!
# The standard half-spin modules of a polarized six-dimensional space

Polarization identifies the even Clifford algebra of a six-dimensional quadratic space with a
product of two four-by-four matrix algebras. Its first factor gives an equivalence from the Spin
group to `SL₄`, under which the even half-spin module is the standard representation. The odd
half-spin module is its dual.

This packages the group equivalence and both representation equivalences together, ensuring that
all three use the same noncanonical choice of basis for the even half-spin module.

## Main result

* `exists_spinGroup_mulEquiv_specialLinearGroup_and_halfSpin_equiv_std_dual_of_finrank_eq_six`:
  a polarization of a six-dimensional quadratic space identifies its Spin group with `SL₄`, its
  even half-spin representation with the standard module, and its odd half-spin representation
  with the dual standard module.
* `exists_polarized_spinGroupEquivSL4_and_halfSpin_equiv_std_dual_of_finrank_eq_six`: over a
  separably closed field, a nondegenerate six-dimensional quadratic space admits such a
  polarization and comparison.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- A polarization of a six-dimensional quadratic space identifies its Spin group with `SL₄` so
that the even half-spin representation is standard and the odd half-spin representation is its
dual. The group and representation equivalences use the same noncanonical basis choice. -/
theorem exists_spinGroup_mulEquiv_specialLinearGroup_and_halfSpin_equiv_std_dual_of_finrank_eq_six
    [NeZero (2 : K)] (P : SpinPolarizationData Q) (hV : finrank K V = 6) :
    ∃ hline : P.line = ⊥, ∃ f : spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 4) K,
      Nonempty ((spinPlusSubrep P hline).toRepresentation.Equiv
        ((stdSLRep K 4).comp f.toMonoidHom)) ∧
      Nonempty ((spinMinusSubrep P hline).toRepresentation.Equiv
        (Representation.dual ((stdSLRep K 4).comp f.toMonoidHom))) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let hline : P.line = ⊥ := P.line_eq_bot_of_even_finrank (hV ▸ by decide)
  have hWfin : finrank K P.W = 3 :=
    P.finrank_W_eq_of_finrank_eq_two_mul (l := 3) (by omega)
  have hW : P.W ≠ ⊥ := Submodule.finrank_eq_zero.not.1 (by omega)
  have hplus : finrank K (spinPlus Q P) = 4 := by
    rw [finrank_spinPlus P hW, hWfin]
    norm_num
  let b := Module.finBasisOfFinrankEq K (spinPlus Q P) hplus
  let e := P.evenCliffordEquivProdMatrix (l := 3) hW (by omega)
  let u := e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
    (P.nondegenerate_of_line_eq_bot hline) hV
  have hu (s : spinGroup Q) :
      (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) =
        LinearMap.toMatrix b b
          (spinPlusAction Q P hline (spinGroupToEven Q s)) := by
    calc
      (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) =
          (e (spinGroupToEven Q s)).1 := by
        rw [AlgEquiv.coe_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_apply,
          CliffordAlgebra.evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply]
      _ = (Algebra.endAlgEquivMatrix K (spinPlus Q P) hplus
          (spinPlusAction Q P hline (spinGroupToEven Q s))) := by
        simpa only [e, hplus] using congrArg Prod.fst
          (P.evenCliffordEquivProdMatrix_apply (l := 3) hW (by omega)
            (spinGroupToEven Q s))
      _ = _ := by
        simpa only [b] using Algebra.endAlgEquivMatrix_apply K _ _ _
  let f : spinGroup Q →* Matrix.SpecialLinearGroup (Fin 4) K :=
    { toFun := fun s ↦ ⟨u (spinGroupToEvenUnitary Q s), by
          rw [hu, LinearMap.det_toMatrix]
          exact det_spinPlusAction_spinGroupToEven P hline hWfin s⟩
      map_one' := Subtype.ext (by
        -- Expose the underlying matrix hidden by the special-linear subtype and the local map.
        change (u (spinGroupToEvenUnitary Q 1) : Matrix (Fin 4) (Fin 4) K) = 1
        rw [map_one, map_one, Units.val_one])
      map_mul' := fun s t ↦ Subtype.ext (by
        -- Expose the underlying matrices so the homomorphism laws can rewrite this equality.
        change (u (spinGroupToEvenUnitary Q (s * t)) : Matrix (Fin 4) (Fin 4) K) =
          (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) *
            (u (spinGroupToEvenUnitary Q t) : Matrix (Fin 4) (Fin 4) K)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hf_bijective : Function.Bijective f := by
    constructor
    · intro s t h
      apply spinGroupToEvenUnitary_injective Q
      apply u.injective
      apply Units.ext
      exact congrArg Subtype.val h
    · intro A
      let a : Module.End K (spinPlus Q P) :=
        (LinearMap.toMatrix b b).symm (A : Matrix (Fin 4) (Fin 4) K)
      have hdet : LinearMap.det a = 1 := by
        rw [← LinearMap.det_toMatrix b, LinearEquiv.apply_symm_apply]
        exact A.property
      obtain ⟨s, hs⟩ :=
        exists_spinPlusAction_spinGroupToEven_eq_of_det_eq_one P hline hWfin a hdet
      refine ⟨s, Subtype.ext ?_⟩
      -- Expose the matrix equality hidden by the special-linear subtype and the local map.
      change (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) = A
      rw [hu, hs]
      exact LinearEquiv.apply_symm_apply (LinearMap.toMatrix b b)
        (A : Matrix (Fin 4) (Fin 4) K)
  let φ := MulEquiv.ofBijective f hf_bijective
  let ep : spinPlus Q P ≃ₗ[K] (spinPlusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinPlusSubrep P hline).symm
  let eplus :
      (spinPlusSubrep P hline).toRepresentation.Equiv
        ((stdSLRep K 4).comp φ.toMonoidHom) :=
    Representation.Equiv.ofBasisAction _ _ ep.symm b
      (fun s ↦ spinPlusAction Q P hline (spinGroupToEven Q s))
      (fun s x ↦ by
        apply Subtype.ext
        simpa only [ep, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply] using
          (coe_spinPlusAction_spinGroupToEven_apply P hline s (ep.symm x)).symm)
      (fun s x ↦ by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, stdSLRep_apply_apply]
        have hφ : (φ s : Matrix (Fin 4) (Fin 4) K) =
            LinearMap.toMatrix b b
              (spinPlusAction Q P hline (spinGroupToEven Q s)) := by
          rw [MulEquiv.ofBijective_apply]
          exact hu s
        rw [hφ]
        exact LinearMap.toMatrix_mulVec_repr b b
          (spinPlusAction Q P hline (spinGroupToEven Q s)) x)
  obtain ⟨hline', ⟨eminus⟩⟩ :=
    exists_spinMinusSubrep_equiv_dual_spinPlusSubrep_of_finrank_eq_six P hV
  have hh : hline' = hline := Subsingleton.elim _ _
  cases hh
  exact ⟨hline, φ, ⟨eplus⟩, ⟨eminus.trans eplus.dual⟩⟩

/-- A nondegenerate six-dimensional quadratic space over a separably closed field admits a
polarization and an equivalence from its Spin group to `SL₄` under which the half-spin
representations are the standard module and its dual. -/
theorem exists_polarized_spinGroupEquivSL4_and_halfSpin_equiv_std_dual_of_finrank_eq_six
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
    exists_spinGroup_mulEquiv_specialLinearGroup_and_halfSpin_equiv_std_dual_of_finrank_eq_six
      P hV
  exact ⟨P, hline, f, hplus, hminus⟩

end TauCeti

end
