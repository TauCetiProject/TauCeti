/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Structure
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.GeneralLinear
import TauCeti.LinearAlgebra.Dual.End
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

private theorem reverseEvenProdEquiv_first_fst_eq_zero
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1))
    (f : Module.End K M) :
    (reverseEvenProdEquiv e (MulOpposite.op (f, 0))).1 = 0 := by
  calc
    (reverseEvenProdEquiv e (MulOpposite.op (f, 0))).1 =
        (reverseEvenProdEquiv e
          (MulOpposite.op (f, 0) * MulOpposite.op (1, 0))).1 := by
            congr 2
    _ = ((reverseEvenProdEquiv e (MulOpposite.op (f, 0))) *
        reverseEvenProdEquiv e (MulOpposite.op (1, 0))).1 := by rw [map_mul]
    _ = 0 := by rw [hswap]; simp

private theorem reverseEvenProdEquiv_second_snd_eq_zero
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1))
    (g : Module.End K N) :
    (reverseEvenProdEquiv e (MulOpposite.op (0, g))).2 = 0 := by
  have hzeroOne : reverseEvenProdEquiv e (MulOpposite.op (0, 1)) = (1, 0) := by
    have hop : MulOpposite.op (0, (1 : Module.End K N)) =
        1 - MulOpposite.op ((1 : Module.End K M), 0) := by
      apply MulOpposite.unop_injective
      ext <;> simp
    rw [hop]
    rw [map_sub, map_one, hswap]
    ext <;> simp
  calc
    (reverseEvenProdEquiv e (MulOpposite.op (0, g))).2 =
        (reverseEvenProdEquiv e
          (MulOpposite.op (0, g) * MulOpposite.op (0, 1))).2 := by
            congr 2
    _ = ((reverseEvenProdEquiv e (MulOpposite.op (0, g))) *
        reverseEvenProdEquiv e (MulOpposite.op (0, 1))).2 := by rw [map_mul]
    _ = 0 := by rw [hzeroOne]; simp

private noncomputable def reverseEvenFirstToSecondAlgHom
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1)) :
    (Module.End K M)ᵐᵒᵖ →ₐ[K] Module.End K N where
  toFun f := (reverseEvenProdEquiv e (MulOpposite.op (f.unop, 0))).2
  map_one' := by simpa using congrArg Prod.snd hswap
  map_mul' f g := by
    have hsource : MulOpposite.op (g.unop * f.unop, (0 : Module.End K N)) =
        MulOpposite.op (f.unop, 0) * MulOpposite.op (g.unop, 0) := by
      apply MulOpposite.unop_injective
      simp
    -- Normalize multiplication in the opposite product algebra before applying multiplicativity.
    change (reverseEvenProdEquiv e
      (MulOpposite.op (g.unop * f.unop, 0))).2 = _
    rw [hsource, map_mul]
    rfl
  map_zero' := by
    have hsource : MulOpposite.op ((0 : Module.End K M), (0 : Module.End K N)) = 0 := rfl
    -- Normalize zero in the opposite product algebra before applying preservation of zero.
    change (reverseEvenProdEquiv e (MulOpposite.op (0, 0))).2 = 0
    rw [hsource, map_zero]
    rfl
  map_add' f g := by
    have hsource : MulOpposite.op (f.unop + g.unop, (0 : Module.End K N)) =
        MulOpposite.op (f.unop, 0) + MulOpposite.op (g.unop, 0) := by
      apply MulOpposite.unop_injective
      simp
    -- Normalize addition in the opposite product algebra before applying additivity.
    change (reverseEvenProdEquiv e
      (MulOpposite.op (f.unop + g.unop, 0))).2 = _
    rw [hsource, map_add]
    rfl
  commutes' r := by
    have hunop : MulOpposite.unop (algebraMap K (Module.End K M)ᵐᵒᵖ r) =
        algebraMap K (Module.End K M) r := by simp
    rw [hunop]
    have hop : MulOpposite.op (algebraMap K (Module.End K M) r, 0) =
        r • MulOpposite.op ((1 : Module.End K M), (0 : Module.End K N)) := by
      apply MulOpposite.unop_injective
      ext <;> simp [Algebra.smul_def]
    rw [hop]
    have h := congrArg Prod.snd <|
      (reverseEvenProdEquiv e).toLinearEquiv.map_smul r
        (MulOpposite.op ((1 : Module.End K M), (0 : Module.End K N)))
    simpa [hswap, Algebra.smul_def] using h

private theorem reverseEvenFirstToSecondAlgHom_injective
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1)) :
    Function.Injective (reverseEvenFirstToSecondAlgHom e hswap) := by
  intro f g hfg
  apply MulOpposite.unop_injective
  have hr : reverseEvenProdEquiv e (MulOpposite.op (f.unop, 0)) =
      reverseEvenProdEquiv e (MulOpposite.op (g.unop, 0)) := by
    apply Prod.ext
    · rw [reverseEvenProdEquiv_first_fst_eq_zero e hswap,
        reverseEvenProdEquiv_first_fst_eq_zero e hswap]
    · exact hfg
  have hpairs := MulOpposite.op_injective ((reverseEvenProdEquiv e).injective hr)
  exact congrArg Prod.fst hpairs

private noncomputable def reverseEvenFirstToSecondAlgEquiv
    [FiniteDimensional K M] [FiniteDimensional K N]
    (e : even Q ≃ₐ[K] Module.End K M × Module.End K N)
    (hswap : reverseEvenProdEquiv e (MulOpposite.op (1, 0)) = (0, 1))
    (hdim : finrank K M = finrank K N) :
    (Module.End K M)ᵐᵒᵖ ≃ₐ[K] Module.End K N := by
  let f := reverseEvenFirstToSecondAlgHom e hswap
  have hinj : Function.Injective f := reverseEvenFirstToSecondAlgHom_injective e hswap
  refine AlgEquiv.ofBijective f ⟨hinj, ?_⟩
  have hrank : finrank K ((Module.End K M)ᵐᵒᵖ) =
      finrank K (Module.End K N) := by
    calc
      finrank K ((Module.End K M)ᵐᵒᵖ) = finrank K (Module.End K M) :=
        (MulOpposite.opLinearEquiv K).symm.finrank_eq
      _ = finrank K (Module.End K N) := by
        rw [Module.finrank_linearMap, Module.finrank_linearMap, hdim]
  have hinj' : Function.Injective f.toLinearMap := hinj
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := K) (V := (Module.End K M)ᵐᵒᵖ)
      (V₂ := Module.End K N) (f := f.toLinearMap) hrank).mp hinj'

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
  -- Expose the product-algebra component selected by the restricted equivalence.
  change (reverseEvenProdEquiv e (MulOpposite.op ((e x).1, 0))).2 = _
  have hfull : reverseEvenProdEquiv e (MulOpposite.op (e x)) = e (reverseEven Q x) := by
    simpa using reverseEvenProdEquiv_apply e (e x)
  rw [← congrArg Prod.snd hfull]
  have hsource : MulOpposite.op (e x) =
      MulOpposite.op ((e x).1, 0) + MulOpposite.op (0, (e x).2) := by
    apply MulOpposite.unop_injective
    ext <;> simp
  rw [hsource, map_add]
  simp only [Prod.snd_add]
  rw [reverseEvenProdEquiv_second_snd_eq_zero e hswap, add_zero]

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
  let a : (Module.End K (spinPlus Q P))ᵐᵒᵖ ≃ₐ[K]
      Module.End K (spinMinus Q P) :=
    reverseEvenFirstToSecondAlgEquiv ep hswap (hplus.trans hminus.symm)
  let c : Module.End K (Module.Dual K (spinPlus Q P)) ≃ₐ[K]
      Module.End K (spinMinus Q P) :=
    (Module.dualEndAlgEquiv K (spinPlus Q P)).symm.trans a
  obtain ⟨T, hT⟩ := c.eq_linearEquivConjAlgEquiv
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
  have hactionInv := reverseEvenFirstToSecondAlgEquiv_action ep hswap
    (hplus.trans hminus.symm) (spinGroupToEven Q g⁻¹)
  have hcInv : c ((spinPlusAction Q P hline (spinGroupToEven Q g⁻¹)).dualMap) =
      spinMinusAction Q P hline (spinGroupToEven Q g) := by
    simp only [c, AlgEquiv.trans_apply, Module.dualEndAlgEquiv_symm_dualMap]
    have hrevInv : reverseEven Q (spinGroupToEven Q g⁻¹) = spinGroupToEven Q g := by
      apply Subtype.ext
      rw [coe_reverseEven_apply, coe_spinGroupToEven_apply, coe_spinGroupToEven_apply]
      calc
        reverse ((g⁻¹ : spinGroup Q) : CliffordAlgebra Q) =
            reverse (((spinGroupToEvenUnitary Q g⁻¹ : evenUnitaryGroup Q) :
              (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
                rw [coe_spinGroupToEvenUnitary_apply]
                rfl
        _ = ((((spinGroupToEvenUnitary Q g⁻¹ : evenUnitaryGroup Q) :
              (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
          evenUnitaryGroup.reverse_eq_inv Q (spinGroupToEvenUnitary Q g⁻¹)
        _ = (g : CliffordAlgebra Q) := by simp
    simpa [a, ep, P.evenCliffordEquivProdEnd_apply, evenSpinActionProd_apply, hrevInv]
      using hactionInv
  have hconjInv := AlgEquiv.congr_fun hT
    ((spinPlusAction Q P hline (spinGroupToEven Q g⁻¹)).dualMap)
  rw [hcInv] at hconjInv
  simp only [LinearEquiv.conjAlgEquiv_apply] at hconjInv
  have hintertwine :
      T.symm (spinMinusAction Q P hline (spinGroupToEven Q g) (eminus.symm s)) =
        (spinPlusAction Q P hline (spinGroupToEven Q g⁻¹)).dualMap
          (T.symm (eminus.symm s)) := by
    have h := congrArg T.symm <| LinearMap.congr_fun hconjInv (eminus.symm s)
    simpa using h
  have hplusAction :
      eplus.symm ((spinPlusSubrep P hline).toRepresentation g⁻¹ (eplus p)) =
        spinPlusAction Q P hline (spinGroupToEven Q g⁻¹) p := by
    apply Subtype.ext
    -- Expose the exterior-algebra carriers so the established Spin action formula applies.
    change (((spinPlusSubrep P hline).toRepresentation g⁻¹ (eplus p) :
      (spinPlusSubrep P hline).toSubmodule) : ExteriorAlgebra K P.W) =
        (spinPlusAction Q P hline (spinGroupToEven Q g⁻¹) p : ExteriorAlgebra K P.W)
    have heplus : eplus p = ⟨p, (mem_spinPlusSubrep P hline).2 p.2⟩ := by
      apply Subtype.ext
      rfl
    rw [heplus]
    have heven : spinGroupToEven Q g⁻¹ =
        ⟨(g⁻¹ : spinGroup Q), spinGroup.mem_even (g⁻¹ : spinGroup Q).2⟩ :=
      Subtype.ext (coe_spinGroupToEven_apply Q g⁻¹)
    rw [heven]
    exact (coe_spinPlusAction_spinGroup_apply P hline g⁻¹ p).symm
  have hminusAction : eminus.symm ((spinMinusSubrep P hline).toRepresentation g s) =
      spinMinusAction Q P hline (spinGroupToEven Q g) (eminus.symm s) := by
    apply Subtype.ext
    simpa [eminus] using
      (coe_spinMinusAction_spinGroup_apply P hline g (eminus.symm s)).symm
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

end TauCeti
