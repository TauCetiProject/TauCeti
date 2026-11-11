/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Structure
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.Algebra.Algebra.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.GeneralLinear
import TauCeti.LinearAlgebra.Dual.End
import TauCeti.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

/-!
# Duality of the half-spin representations in dimension six

For a polarized six-dimensional quadratic space, reversal interchanges the two simple factors of
the even Clifford algebra. Consequently the action on one half-spin module is contragredient to
the action on the other. This file turns that observation into an equivalence between the odd
half-spin representation and the dual of the even half-spin representation.

The equivalence is not canonical. Reversal gives an anti-isomorphism between the two endomorphism
algebras, and Skolem--Noether identifies it, after linear duality, with conjugation by some linear
equivalence. Restriction to the Spin group then supplies the desired intertwiner.

## Main result

* `TauCeti.exists_spinMinusSubrep_equiv_dual_spinPlusSubrep_of_finrank_eq_six`: in dimension six,
  a polarization line vanishes and the odd half-spin representation is equivalent to the dual of
  the even half-spin representation.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v w z

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

variable {M : Type w} {N : Type z} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

private noncomputable def reverseEvenProdEquiv
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N) :
    (Module.End K M × Module.End K N)ᵐᵒᵖ ≃ₐ[K]
      Module.End K M × Module.End K N :=
  (AlgEquiv.op e.symm).trans ((CliffordAlgebra.reverseEvenOpEquiv Q).symm.trans e)

private theorem reverseEvenProdEquiv_apply
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (x : Module.End K M × Module.End K N) :
    reverseEvenProdEquiv e (MulOpposite.op x) = e (reverseEven Q (e.symm x)) :=
  by simp [reverseEvenProdEquiv]

private theorem evenCliffordEquivProdEnd_reverse_one_zero_of_finrank_eq_six
    [Invertible (2 : K)] [FiniteDimensional K V] (P : SpinPolarizationData Q)
    (hline : P.line = ⊥) (hV : finrank K V = 6) :
    P.evenCliffordEquivProdEnd hline
        (reverseEven Q ((P.evenCliffordEquivProdEnd hline).symm (1, 0))) =
      (0, 1) := by
  have hWfin : finrank K P.W = 3 :=
    P.finrank_W_eq_of_finrank_eq_two_mul (l := 3) (by omega)
  have hW : P.W ≠ ⊥ := Submodule.finrank_eq_zero.not.1 (by omega)
  have hplus : finrank K (spinPlus Q P) = 4 := by
    rw [finrank_spinPlus P hW, hWfin]
    norm_num
  have hminus : finrank K (spinMinus Q P) = 4 := by
    rw [finrank_spinMinus P hW, hWfin]
    norm_num
  let em : even Q ≃ₐ[K]
      Matrix (Fin 4) (Fin 4) K × Matrix (Fin 4) (Fin 4) K := by
    simpa using P.evenCliffordEquivProdMatrix (l := 3) hW (by omega)
  let ep := P.evenCliffordEquivProdEnd hline
  have hem (x : even Q) : em x =
      (Algebra.endAlgEquivMatrix K (spinPlus Q P) hplus
          (spinPlusAction Q P hline x),
        Algebra.endAlgEquivMatrix K (spinMinus Q P) hminus
          (spinMinusAction Q P hline x)) := by
    simpa [em] using P.evenCliffordEquivProdMatrix_apply (l := 3) hW (by omega) x
  have hep (x : even Q) : ep x =
      (spinPlusAction Q P hline x, spinMinusAction Q P hline x) := by
    simp [ep, evenSpinActionProd_apply]
  have hpreimage : ep.symm (1, 0) = em.symm (1, 0) := by
    apply em.injective
    rw [em.apply_symm_apply]
    rw [hem]
    have h := hep (ep.symm (1, 0))
    rw [ep.apply_symm_apply] at h
    rw [Prod.mk.injEq] at h
    rw [← h.1, ← h.2]
    simp
  have hmatrix := AlgEquiv.map_reverseEven_symm_one_zero_of_finrank_eq_six em
    (P.nondegenerate_of_line_eq_bot hline) hV
  rw [← hpreimage] at hmatrix
  rw [hep]
  have hplusMatrix := congrArg Prod.fst hmatrix
  have hminusMatrix := congrArg Prod.snd hmatrix
  apply Prod.ext
  · apply (Algebra.endAlgEquivMatrix K (spinPlus Q P) hplus).injective
    simpa [hem] using hplusMatrix
  · apply (Algebra.endAlgEquivMatrix K (spinMinus Q P) hminus).injective
    simpa [hem] using hminusMatrix

private def endProdMulOppositeEquiv :
    (Module.End K M × Module.End K N)ᵐᵒᵖ ≃ₐ[K]
      (Module.End K M)ᵐᵒᵖ × (Module.End K N)ᵐᵒᵖ where
  toFun x := (MulOpposite.op x.unop.1, MulOpposite.op x.unop.2)
  invFun x := MulOpposite.op (x.1.unop, x.2.unop)
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨x, y⟩; cases x; cases y; rfl
  map_mul' x y := by ext <;> simp
  map_add' x y := by ext <;> simp
  commutes' r := by ext <;> rfl

private noncomputable def reverseEvenToSecondAlgHom
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N) :
    (Module.End K M)ᵐᵒᵖ × (Module.End K N)ᵐᵒᵖ →ₐ[K] Module.End K N :=
  (AlgHom.snd K _ _).comp
    ((endProdMulOppositeEquiv (K := K) (M := M) (N := N)).symm.trans
      (reverseEvenProdEquiv e)).toAlgHom

private theorem reverseEvenToSecondAlgHom_apply
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (f : Module.End K M) (g : Module.End K N) :
    reverseEvenToSecondAlgHom e (MulOpposite.op f, MulOpposite.op g) =
      (reverseEvenProdEquiv e (MulOpposite.op (f, g))).2 :=
  rfl

private theorem reverseEvenToSecondAlgHom_one_zero
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1)) :
    reverseEvenToSecondAlgHom e (1, 0) = 1 := by
  have happ := reverseEvenToSecondAlgHom_apply e (1 : Module.End K M) (0 : Module.End K N)
  have hsnd := congrArg Prod.snd hswap
  exact happ.trans hsnd

private noncomputable def reverseEvenFirstToSecondAlgHom
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1)) :
    (Module.End K M)ᵐᵒᵖ →ₐ[K] Module.End K N :=
  AlgHom.prodFirst (reverseEvenToSecondAlgHom e) (reverseEvenToSecondAlgHom_one_zero e hswap)

private noncomputable def reverseEvenFirstToSecondAlgEquiv
    [FiniteDimensional K M] [FiniteDimensional K N]
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1))
    (hdim : finrank K M = finrank K N) :
    (Module.End K M)ᵐᵒᵖ ≃ₐ[K] Module.End K N := by
  let f := reverseEvenFirstToSecondAlgHom e hswap
  have hunit := reverseEvenToSecondAlgHom_one_zero e hswap
  have hsurj : Function.Surjective f := (AlgHom.prodFirst_surjective_iff _ hunit).2 <|
    Prod.snd_surjective.comp <|
      ((endProdMulOppositeEquiv (K := K) (M := M) (N := N)).symm.trans
        (reverseEvenProdEquiv e)).surjective
  refine AlgEquiv.ofBijective f ⟨?_, hsurj⟩
  have hrank : finrank K ((Module.End K M)ᵐᵒᵖ) =
      finrank K (Module.End K N) := by
    calc
      finrank K ((Module.End K M)ᵐᵒᵖ) = finrank K (Module.End K M) :=
        (MulOpposite.opLinearEquiv K).symm.finrank_eq
      _ = finrank K (Module.End K N) := by
        rw [Module.finrank_linearMap, Module.finrank_linearMap, hdim]
  have hsurj' : Function.Surjective f.toLinearMap := hsurj
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := K) (V := (Module.End K M)ᵐᵒᵖ)
      (V₂ := Module.End K N) (f := f.toLinearMap) hrank).mpr hsurj'

private theorem reverseEvenFirstToSecondAlgEquiv_apply
    [FiniteDimensional K M] [FiniteDimensional K N]
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1))
    (hdim : finrank K M = finrank K N) (f : (Module.End K M)ᵐᵒᵖ) :
    reverseEvenFirstToSecondAlgEquiv e hswap hdim f =
      reverseEvenFirstToSecondAlgHom e hswap f := by
  rw [reverseEvenFirstToSecondAlgEquiv]
  rfl

private theorem reverseEvenFirstToSecondAlgEquiv_action
    [FiniteDimensional K M] [FiniteDimensional K N]
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1))
    (hdim : finrank K M = finrank K N) (x : even Q) :
    reverseEvenFirstToSecondAlgEquiv e hswap hdim (MulOpposite.op (e x).1) =
      (e (reverseEven Q x)).2 := by
  rw [reverseEvenFirstToSecondAlgEquiv_apply]
  rw [reverseEvenFirstToSecondAlgHom, AlgHom.prodFirst_apply]
  have hfull : reverseEvenToSecondAlgHom e
      (MulOpposite.op (e x).1, MulOpposite.op (e x).2) =
        (e (reverseEven Q x)).2 := by
    rw [reverseEvenToSecondAlgHom_apply]
    simpa only [e.symm_apply_apply] using
      congrArg Prod.snd (reverseEvenProdEquiv_apply e (e x))
  rw [← hfull]
  exact (AlgHom.map_eq_map_fst
    (F := K) (A := (Module.End K M)ᵐᵒᵖ) (C := (Module.End K N)ᵐᵒᵖ)
    (B := Module.End K N) (reverseEvenToSecondAlgHom e)
    (reverseEvenToSecondAlgHom_one_zero e hswap)
    (MulOpposite.op (e x).1, MulOpposite.op (e x).2)).symm

/-- Reversal gives an anti-isomorphism between the endomorphism algebras of the two half-spin
modules in dimension six, intertwining the two actions of the even Clifford algebra. -/
private theorem exists_algEquiv_op_spinPlusAction_reverseEven [NeZero (2 : K)]
    (P : SpinPolarizationData Q) (hline : P.line = ⊥) (hV : finrank K V = 6) :
    ∃ a : (Module.End K (spinPlus Q P))ᵐᵒᵖ ≃ₐ[K] Module.End K (spinMinus Q P),
      ∀ x : even Q, a (MulOpposite.op (spinPlusAction Q P hline x)) =
        spinMinusAction Q P hline (reverseEven Q x) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  have hWfin : finrank K P.W = 3 :=
    P.finrank_W_eq_of_finrank_eq_two_mul (l := 3) (by omega)
  have hW : P.W ≠ ⊥ := Submodule.finrank_eq_zero.not.1 (by omega)
  have hplus : finrank K (spinPlus Q P) = 4 := by
    rw [finrank_spinPlus P hW, hWfin]
    norm_num
  have hminus : finrank K (spinMinus Q P) = 4 := by
    rw [finrank_spinMinus P hW, hWfin]
    norm_num
  let ep := P.evenCliffordEquivProdEnd hline
  have hswap : reverseEvenProdEquiv ep (MulOpposite.op (1, 0)) = (0, 1) := by
    rw [reverseEvenProdEquiv_apply]
    exact evenCliffordEquivProdEnd_reverse_one_zero_of_finrank_eq_six P hline hV
  have hep (x : even Q) : ep x =
      (spinPlusAction Q P hline x, spinMinusAction Q P hline x) := by
    simpa only [ep, evenSpinActionProd_apply] using
      P.evenCliffordEquivProdEnd_apply hline x
  refine ⟨reverseEvenFirstToSecondAlgEquiv ep hswap (hplus.trans hminus.symm), fun x ↦ ?_⟩
  simpa only [hep] using
    reverseEvenFirstToSecondAlgEquiv_action ep hswap (hplus.trans hminus.symm) x

/-- Scalar duality and Skolem--Noether realize reversal as a linear equivalence from the dual of
the even half-spin module to the odd half-spin module that intertwines the transposed even action
with the reversed odd action. -/
private theorem exists_linearEquiv_dual_spinPlus_conj [NeZero (2 : K)]
    (P : SpinPolarizationData Q) (hline : P.line = ⊥) (hV : finrank K V = 6) :
    ∃ T : Module.Dual K (spinPlus Q P) ≃ₗ[K] spinMinus Q P, ∀ (x : even Q)
      (φ : Module.Dual K (spinPlus Q P)),
      T ((spinPlusAction Q P hline x).dualMap φ) =
        spinMinusAction Q P hline (reverseEven Q x) (T φ) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨a, ha⟩ := exists_algEquiv_op_spinPlusAction_reverseEven P hline hV
  obtain ⟨T, hT⟩ :=
    ((Module.dualEndAlgEquiv K (spinPlus Q P)).symm.trans a).eq_linearEquivConjAlgEquiv
  refine ⟨T, fun x φ ↦ ?_⟩
  have h := LinearMap.congr_fun (AlgEquiv.congr_fun hT ((spinPlusAction Q P hline x).dualMap))
    (T φ)
  simp only [AlgEquiv.trans_apply, Module.dualEndAlgEquiv_symm_dualMap, ha,
    LinearEquiv.conjAlgEquiv_apply] at h
  simpa using h.symm

/-- In a polarized six-dimensional quadratic space, the odd half-spin representation is
equivalent to the dual of the even half-spin representation. The equivalence is noncanonical:
it is obtained from the anti-isomorphism between the two simple factors of the even Clifford
algebra induced by reversal. The vanishing of the polarization line is included in the result
because it follows from the dimension hypothesis. -/
theorem exists_spinMinusSubrep_equiv_dual_spinPlusSubrep_of_finrank_eq_six
    [NeZero (2 : K)] (P : SpinPolarizationData Q) (hV : finrank K V = 6) :
    ∃ hline : P.line = ⊥, Nonempty ((spinMinusSubrep P hline).toRepresentation.Equiv
      (spinPlusSubrep P hline).toRepresentation.dual) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  have hline : P.line = ⊥ := P.line_eq_bot_of_even_finrank (hV ▸ by decide)
  refine ⟨hline, ?_⟩
  obtain ⟨T, hT⟩ := exists_linearEquiv_dual_spinPlus_conj P hline hV
  let eplus : spinPlus Q P ≃ₗ[K] (spinPlusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinPlusSubrep P hline).symm
  let eminus : spinMinus Q P ≃ₗ[K] (spinMinusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinMinusSubrep P hline).symm
  let E : (spinMinusSubrep P hline).toSubmodule ≃ₗ[K]
      Module.Dual K (spinPlusSubrep P hline).toSubmodule :=
    eminus.symm.trans <| T.symm.trans eplus.symm.dualMap
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro g
  apply LinearMap.ext
  intro s
  apply eplus.dualMap.injective
  apply LinearMap.ext
  intro p
  -- Apply the conjugacy equation to the chosen odd spinor.
  have hintertwine :
      T.symm (spinMinusAction Q P hline (spinGroupToEven Q g) (eminus.symm s)) =
        (spinPlusAction Q P hline (spinGroupToEven Q g⁻¹)).dualMap
          (T.symm (eminus.symm s)) := by
    have h := hT (spinGroupToEven Q g⁻¹) (T.symm (eminus.symm s))
    rw [reverseEven_spinGroupToEven_inv, LinearEquiv.apply_symm_apply] at h
    exact T.symm_apply_eq.2 h.symm
  have hplusAction := spinPlusSubrep_toRepresentation_apply_eq_spinPlusAction P hline g⁻¹ p
  have hminusAction := spinMinusSubrep_toRepresentation_apply_eq_spinMinusAction P hline g s
  -- The remaining equality is the evaluation pairing for the transported dual action.
  simp only [E, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.dualMap_apply]
  rw [hminusAction, hintertwine]
  simp only [LinearMap.dualMap_apply]
  rw [eplus.symm_apply_apply]
  -- Expand the dual evaluation after transporting through the subtype equivalence.
  change (T.symm (eminus.symm s))
      (spinPlusAction Q P hline (spinGroupToEven Q g⁻¹) p) =
    (eplus.symm.dualMap (T.symm (eminus.symm s)))
      ((spinPlusSubrep P hline).toRepresentation g⁻¹ (eplus p))
  rw [LinearEquiv.dualMap_apply, hplusAction]

/-- Combine an equivalence of the even half-spin representation with the canonical duality of the
odd and even half-spin representations in dimension six. -/
theorem nonempty_spinMinusSubrep_equiv_dual_of_spinPlusSubrep_equiv
    [NeZero (2 : K)] (P : SpinPolarizationData Q) (hV : finrank K V = 6)
    (hline : P.line = ⊥) {M : Type w} [AddCommMonoid M] [Module K M]
    (ρ : Representation K (spinGroup Q) M)
    (eplus : Nonempty ((spinPlusSubrep P hline).toRepresentation.Equiv ρ)) :
    Nonempty ((spinMinusSubrep P hline).toRepresentation.Equiv (Representation.dual ρ)) := by
  obtain ⟨hline', ⟨eminus⟩⟩ :=
    exists_spinMinusSubrep_equiv_dual_spinPlusSubrep_of_finrank_eq_six P hV
  have hh : hline' = hline := Subsingleton.elim _ _
  cases hh
  exact ⟨eminus.trans eplus.some.dual⟩

end TauCeti
