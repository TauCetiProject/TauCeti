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
import TauCeti.RepresentationTheory.Spin.HalfSpin.Standard

/-!
# The standard half-spin modules of a polarized six-dimensional space

Over a field of characteristic different from two, polarization identifies the even Clifford
algebra of a six-dimensional quadratic space with a product of two four-by-four matrix algebras.
Its first factor gives an equivalence from the Spin group to `SL₄`, under which the even
half-spin module is the standard representation. The odd half-spin module is its dual.

This packages the group equivalence and both representation equivalences together, ensuring that
all three use the same noncanonical choice of basis for the even half-spin module.

## Main result

* `exists_spinGroup_mulEquiv_specialLinearGroup_and_halfSpin_equiv_stdSLRep_and_dual`:
  a polarization of a six-dimensional quadratic space over a field of characteristic different
  from two identifies its Spin group with `SL₄`, its even half-spin representation with the
  standard module, and its odd half-spin representation with the dual standard module.
* `exists_polarized_spinGroup_mulEquiv_specialLinearGroup_and_halfSpin_equiv_stdSLRep_and_dual`:
  over a separably closed field of characteristic different from two, a nondegenerate
  six-dimensional quadratic space admits such a polarization and comparison.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* `TauCeti.RepresentationTheory.Spin.Exceptional.Six.Standard` supplies the split half-spin
  comparison generalized here.
* `TauCeti.RepresentationTheory.Spin.Exceptional.Six.Group` supplies the arbitrary-form group
  endpoint; `SpecialLinear` and `HalfSpinDual` supply the group construction and half-spin
  duality used below.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

-- Formal lineage: the split comparison was introduced in Tau Ceti PR #16324, and the
-- arbitrary-form group endpoint in `Six.Group` was introduced in Tau Ceti PR #17008.

private theorem polarizedSpinGroupFirstFactor_matrix
    [Invertible (2 : K)] (P : SpinPolarizationData Q)
    [FiniteDimensional K V]
    [FiniteDimensional K (spinPlus Q P)]
    (hline : P.line = ⊥)
    (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) (s : spinGroup Q) :
    let e := P.evenCliffordEquivProdMatrix (l := 3) hW (by omega)
    let u := e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
      (P.nondegenerate_of_line_eq_bot hline) hV
    (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) =
      LinearMap.toMatrix b b (spinPlusAction Q P hline (spinGroupToEven Q s)) := by
  dsimp
  calc
    _ = (P.evenCliffordEquivProdMatrix (l := 3) hW (by omega)
        (spinGroupToEven Q s)).1 := by
      rw [AlgEquiv.coe_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_apply,
        CliffordAlgebra.evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply]
    _ = (Algebra.endAlgEquivMatrix K (spinPlus Q P) hplus
        (spinPlusAction Q P hline (spinGroupToEven Q s))) := by
      simpa using congrArg Prod.fst
        (P.evenCliffordEquivProdMatrix_apply (l := 3) hW (by omega)
          (spinGroupToEven Q s))
    _ = _ := by
      rw [Algebra.endAlgEquivMatrix_apply K _ _]
      rw [hb]

private noncomputable def polarizedSpinGroupMulHom
    [NeZero (2 : K)] (P : SpinPolarizationData Q) [FiniteDimensional K (spinPlus Q P)]
    (hline : P.line = ⊥)
    (hWfin : finrank K P.W = 3) (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) :
    spinGroup Q →* Matrix.SpecialLinearGroup (Fin 4) K := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : FiniteDimensional K (spinPlus Q P) := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let e := P.evenCliffordEquivProdMatrix (l := 3) hW (by omega)
  let u := e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
    (P.nondegenerate_of_line_eq_bot hline) hV
  exact
    { toFun := fun s ↦ ⟨u (spinGroupToEvenUnitary Q s), by
          have hm : (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) =
              LinearMap.toMatrix b b
                (spinPlusAction Q P hline (spinGroupToEven Q s)) := by
            simpa only [e, u] using
              polarizedSpinGroupFirstFactor_matrix P hline hW hplus hV b hb s
          rw [hm, LinearMap.det_toMatrix]
          exact det_spinPlusAction_spinGroupToEven P hline hWfin s⟩
      map_one' := Subtype.ext (by
        -- `Subtype.ext` leaves the special-linear carrier; expose its matrix projection so
        -- the homomorphism's `map_one` and the unit's value can rewrite the goal.
        change (u (spinGroupToEvenUnitary Q 1) : Matrix (Fin 4) (Fin 4) K) = 1
        rw [map_one, map_one, Units.val_one])
      map_mul' := fun s t ↦ Subtype.ext (by
        -- The multiplication law is available for the underlying unit-valued map, not for the
        -- special-linear subtype wrapper introduced by `Subtype.ext`; expose that projection.
        change (u (spinGroupToEvenUnitary Q (s * t)) : Matrix (Fin 4) (Fin 4) K) =
          (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) *
            (u (spinGroupToEvenUnitary Q t) : Matrix (Fin 4) (Fin 4) K)
        rw [map_mul, map_mul, Units.val_mul]) }

private theorem polarizedSpinGroupMulHom_matrix
    [NeZero (2 : K)] (P : SpinPolarizationData Q) [FiniteDimensional K (spinPlus Q P)]
    (hline : P.line = ⊥)
    (hWfin : finrank K P.W = 3) (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) (s : spinGroup Q) :
    (polarizedSpinGroupMulHom P hline hWfin hW hplus hV b hb s : Matrix (Fin 4) (Fin 4) K) =
      LinearMap.toMatrix b b (spinPlusAction Q P hline (spinGroupToEven Q s)) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : FiniteDimensional K (spinPlus Q P) := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let e := P.evenCliffordEquivProdMatrix (l := 3) hW (by omega)
  let u := e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
    (P.nondegenerate_of_line_eq_bot hline) hV
  -- The definition of the local homomorphism contains a special-linear subtype.  Its matrix
  -- projection is definitionally this first-factor value, which is the form of the helper above.
  change (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) = _
  exact polarizedSpinGroupFirstFactor_matrix P hline hW hplus hV b hb s

private theorem polarizedSpinGroupMulHom_bijective
    [NeZero (2 : K)] (P : SpinPolarizationData Q) [FiniteDimensional K (spinPlus Q P)]
    (hline : P.line = ⊥)
    (hWfin : finrank K P.W = 3) (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) :
    Function.Bijective (polarizedSpinGroupMulHom P hline hWfin hW hplus hV b hb) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : FiniteDimensional K (spinPlus Q P) := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let e := P.evenCliffordEquivProdMatrix (l := 3) hW (by omega)
  let u := e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
    (P.nondegenerate_of_line_eq_bot hline) hV
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
    -- The target still contains the special-linear subtype produced by the local homomorphism;
    -- expose its matrix projection so its matrix formula and `hs` can rewrite it.
    change (polarizedSpinGroupMulHom P hline hWfin hW hplus hV b hb s :
      Matrix (Fin 4) (Fin 4) K) = A
    rw [polarizedSpinGroupMulHom_matrix P hline hWfin hW hplus hV b hb s, hs]
    exact LinearEquiv.apply_symm_apply (LinearMap.toMatrix b b)
      (A : Matrix (Fin 4) (Fin 4) K)

/-- The first Clifford factor gives the polarized Spin-to-`SL₄` equivalence in the basis of the
even half-spin module. -/
private noncomputable def polarizedSpinGroupMulEquiv
    [NeZero (2 : K)] (P : SpinPolarizationData Q) [FiniteDimensional K (spinPlus Q P)]
    (hline : P.line = ⊥)
    (hWfin : finrank K P.W = 3) (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) :
    spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
  MulEquiv.ofBijective (polarizedSpinGroupMulHom P hline hWfin hW hplus hV b hb)
    (polarizedSpinGroupMulHom_bijective P hline hWfin hW hplus hV b hb)

private theorem polarizedSpinGroupMulEquiv_matrix
    [NeZero (2 : K)] (P : SpinPolarizationData Q) [FiniteDimensional K (spinPlus Q P)]
    (hline : P.line = ⊥)
    (hWfin : finrank K P.W = 3) (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) (s : spinGroup Q) :
    (polarizedSpinGroupMulEquiv P hline hWfin hW hplus hV b hb s : Matrix (Fin 4) (Fin 4) K) =
      LinearMap.toMatrix b b (spinPlusAction Q P hline (spinGroupToEven Q s)) := by
  rw [polarizedSpinGroupMulEquiv, MulEquiv.ofBijective_apply]
  exact polarizedSpinGroupMulHom_matrix P hline hWfin hW hplus hV b hb s

/-- Over a field of characteristic different from two, a polarization of a six-dimensional
quadratic space identifies its Spin group with `SL₄` so that the even half-spin representation
is standard and the odd half-spin representation is its dual. The group and representation
equivalences use the same noncanonical basis choice. -/
theorem
    exists_spinGroup_mulEquiv_specialLinearGroup_and_halfSpin_equiv_stdSLRep_and_dual
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
  let _ : FiniteDimensional K (spinPlus Q P) := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq K (spinPlus Q P) hplus
  have hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus := rfl
  let φ := polarizedSpinGroupMulEquiv P hline hWfin hW hplus hV b hb
  obtain ⟨eplus⟩ := nonempty_spinPlusSubrep_equiv_stdSLRep_of_matrix_action hline b φ
    (fun s ↦ polarizedSpinGroupMulEquiv_matrix P hline hWfin hW hplus hV b hb s)
  obtain ⟨hline', ⟨eminus⟩⟩ :=
    exists_spinMinusSubrep_equiv_dual_spinPlusSubrep_of_finrank_eq_six P hV
  have hh : hline' = hline := Subsingleton.elim _ _
  cases hh
  exact ⟨hline, φ, ⟨eplus⟩, ⟨eminus.trans eplus.dual⟩⟩

/-- A nondegenerate six-dimensional quadratic space over a separably closed field of
characteristic different from two admits a polarization and an equivalence from its Spin group to
`SL₄` under which the half-spin representations are the standard module and its dual. -/
theorem
    exists_polarized_spinGroup_mulEquiv_specialLinearGroup_and_halfSpin_equiv_stdSLRep_and_dual
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
    exists_spinGroup_mulEquiv_specialLinearGroup_and_halfSpin_equiv_stdSLRep_and_dual
      P hV
  exact ⟨P, hline, f, hplus, hminus⟩

end TauCeti

end
