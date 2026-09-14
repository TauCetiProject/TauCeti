/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Hopf
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
public import TauCeti.Algebra.Bialgebra.GroupLike.ScalarAut
import TauCeti.Algebra.TensorProduct.Galois
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Reconstructing a group from its Galois module of characters

Let `H` be a commutative Hopf algebra over `k` which becomes spanned by group-like elements
over a finite Galois extension `L/k`. Its coordinate algebra is recovered from the invariants
of the group algebra on its characters over `L`, with the simultaneous Galois action on
coefficients and characters. In particular this applies to tori split by `L`.

The comparison is canonical: after extension to `L`, it is inverse to evaluation of formal
characters at their group-like values.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable (k L H : Type*) [Field k] [Field L] [Algebra k L]
variable [CommRing H] [HopfAlgebra k H]

/-- The characters over the chosen splitting field. -/
local notation "C" => GroupLike L (L ⊗[k] H)
/-- The Galois representation on the additive character group. -/
local notation "ρ" => Representation.ofMulDistribMulAction (L ≃ₐ[k] L) C
/-- The split coordinate algebra reconstructed from the characters. -/
local notation "D" => MonoidAlgebra L (Multiplicative (Additive C))

variable (hspan : Submodule.span L (Set.range (GroupLike.val (R := L) (A := L ⊗[k] H))) = ⊤)

/-- Evaluation identifies the group algebra on the tagged characters with the scalar extension. -/
private noncomputable def characterEvaluationEquiv : D ≃ₐc[L] L ⊗[k] H :=
  (MonoidAlgebra.domCongrBialgEquiv L L (MulEquiv.multiplicativeAdditive C)).trans
    (GroupLike.evaluationBialgEquiv L (L ⊗[k] H) hspan)

private theorem characterEvaluationEquiv_apply (x : D) :
    characterEvaluationEquiv k L H hspan x =
      GroupLike.evaluationBialgHom L (L ⊗[k] H)
        (MonoidAlgebra.domCongr L L (MulEquiv.multiplicativeAdditive C) x) :=
  -- The composite is defined above; evaluation's named equation identifies its second factor.
  GroupLike.evaluationBialgEquiv_apply L (L ⊗[k] H) hspan _

private theorem characterEvaluationEquiv_single (g : Multiplicative (Additive C)) (a : L) :
    characterEvaluationEquiv k L H hspan (MonoidAlgebra.single g a) = a • g.toAdd.toMul.val := by
  simp [characterEvaluationEquiv_apply]

private theorem characterEvaluationEquiv_action (σ : L ≃ₐ[k] L) (x : D) :
    characterEvaluationEquiv k L H hspan (groupAlgebraAction ρ σ x) =
      σ • characterEvaluationEquiv k L H hspan x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | single g a =>
      rw [groupAlgebraAction_single, characterEvaluationEquiv_single,
        characterEvaluationEquiv_single, ScalarAut.smul_smulₛₗ]
      simp only [Representation.ofMulDistribMulAction_apply_apply,
        toAdd_ofAdd, toMul_ofMul, ScalarAut.val_smul]

private theorem characterEvaluationEquiv_symm_mem (a : H) :
    (characterEvaluationEquiv k L H hspan).symm (1 ⊗ₜ[k] a) ∈ groupAlgebraInvariants ρ := by
  rw [mem_groupAlgebraInvariants_iff]
  intro σ
  apply EquivLike.injective (characterEvaluationEquiv k L H hspan)
  rw [characterEvaluationEquiv_action, BialgEquiv.apply_symm_apply]
  simp

/-- The invariant formal character expansion of an element of the original algebra. -/
private noncomputable def characterInvariantsAlgHom : H →ₐ[k] groupAlgebraInvariants ρ :=
  (((characterEvaluationEquiv k L H hspan).symm.toAlgEquiv.restrictScalars k).toAlgHom.comp
    Algebra.TensorProduct.includeRight).codRestrict _
      (characterEvaluationEquiv_symm_mem k L H hspan)

private theorem characterInvariantsAlgHom_val (a : H) :
    (characterInvariantsAlgHom k L H hspan a : D) =
      (characterEvaluationEquiv k L H hspan).symm (1 ⊗ₜ[k] a) := by
  -- Apply the codomain-restriction equation directly: its membership witness is stated
  -- using evaluation, definitionally equal to the composite algebra map's application.
  refine (AlgHom.coe_codRestrict _ _ _ a).trans ?_
  simp only [AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.restrictScalars_apply, BialgEquiv.coe_toAlgEquiv,
    Algebra.TensorProduct.includeRight_apply]

private theorem characterEvaluationEquiv_characterInvariantsAlgHom (a : H) :
    characterEvaluationEquiv k L H hspan (characterInvariantsAlgHom k L H hspan a : D) =
      1 ⊗ₜ[k] a := by
  rw [characterInvariantsAlgHom_val, BialgEquiv.apply_symm_apply]

variable [FiniteDimensional k L] [IsGalois k L]

private theorem characterInvariantsAlgHom_bijective :
    Function.Bijective (characterInvariantsAlgHom k L H hspan) := by
  constructor
  · intro a b hab
    apply Algebra.TensorProduct.includeRight_injective (R := k) (A := L)
      (RingHom.injective (algebraMap k L))
    have h := congrArg (fun x : groupAlgebraInvariants ρ ↦
      characterEvaluationEquiv k L H hspan (x : D)) hab
    simpa only [characterInvariantsAlgHom_val, BialgEquiv.apply_symm_apply,
      Algebra.TensorProduct.includeRight_apply] using h
  · intro x
    have hx : ∀ σ : L ≃ₐ[k] L,
        σ • characterEvaluationEquiv k L H hspan (x : D) =
          characterEvaluationEquiv k L H hspan (x : D) := by
      intro σ
      rw [← characterEvaluationEquiv_action,
        (mem_groupAlgebraInvariants_iff ρ x).mp x.property σ]
    obtain ⟨a, ha⟩ := (tensorProduct_forall_map_eq_self_iff_exists_one_tmul_eq _).mp hx
    refine ⟨a, Subtype.ext ?_⟩
    rw [characterInvariantsAlgHom_val, ha, BialgEquiv.symm_apply_apply]

private theorem characterInvariantsAlgHom_counit :
    (Bialgebra.counitAlgHom k (groupAlgebraInvariants ρ)).comp
        (characterInvariantsAlgHom k L H hspan) = Bialgebra.counitAlgHom k H := by
  ext a
  apply (algebraMap k L).injective
  simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
    counit_groupAlgebraInvariants, algebraMap_groupAlgebraInvariantsCounit]
  rw [← CoalgHomClass.counit_comp_apply (characterEvaluationEquiv k L H hspan),
    characterEvaluationEquiv_characterInvariantsAlgHom]
  simp [Algebra.algebraMap_eq_smul_one]

private theorem characterInvariantsAlgHom_comul :
    (Algebra.TensorProduct.map (characterInvariantsAlgHom k L H hspan)
        (characterInvariantsAlgHom k L H hspan)).comp (Bialgebra.comulAlgHom k H) =
      (Bialgebra.comulAlgHom k (groupAlgebraInvariants ρ)).comp
        (characterInvariantsAlgHom k L H hspan) := by
  let e := characterEvaluationEquiv k L H hspan
  let f := characterInvariantsAlgHom k L H hspan
  let E := Algebra.TensorProduct.congr e.toAlgEquiv e.toAlgEquiv
  have ht (t : H ⊗[k] H) :
      E (groupAlgebraInvariantsTensorEquiv ρ (Algebra.TensorProduct.map f f t) : D ⊗[L] D) =
        TensorProduct.AlgebraTensorModule.distribBaseChange k L H H (1 ⊗ₜ[k] t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy, TensorProduct.tmul_add]
    | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, groupAlgebraInvariantsTensorEquiv_tmul,
          E, Algebra.TensorProduct.congr_apply,
          AlgEquiv.coe_toAlgHom, BialgEquiv.coe_toAlgEquiv,
          e, f, characterEvaluationEquiv_characterInvariantsAlgHom,
          TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  ext a
  apply (groupAlgebraInvariantsTensorEquiv ρ).injective
  apply Subtype.val_injective
  apply E.injective
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    groupAlgebraInvariantsTensorEquiv_comul, groupAlgebraInvariantsComul_apply]
  rw [ht]
  have he := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom e)
    (characterInvariantsAlgHom k L H hspan a : D)
  have hE : E (Coalgebra.comul (R := L) (characterInvariantsAlgHom k L H hspan a : D)) =
      Coalgebra.comul (R := L) (1 ⊗ₜ[k] a) := by
    rw [Algebra.TensorProduct.congr_apply]
    convert he using 1
    · -- `congr_apply` and the coalgebra law use the two algebra-map coercions of `e`.
      rfl
    · exact congrArg (Coalgebra.comul (R := L))
        (characterEvaluationEquiv_characterInvariantsAlgHom k L H hspan a).symm
  rw [hE, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := k) a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x y => simp

/-- A commutative Hopf algebra split by a finite Galois extension is the invariant group
algebra of its characters, with their natural Galois action. The comparison preserves both
algebra and coalgebra structure, hence also the antipode. -/
noncomputable def characterGroupAlgebraInvariantsEquiv : H ≃ₐc[k] groupAlgebraInvariants ρ :=
  BialgEquiv.ofBijective
    (BialgHom.ofAlgHom (characterInvariantsAlgHom k L H hspan)
      (characterInvariantsAlgHom_counit k L H hspan)
      (characterInvariantsAlgHom_comul k L H hspan))
    (characterInvariantsAlgHom_bijective k L H hspan)

/-- Evaluation of the character expansion recovers the scalar extension of the original
element. This characterizes the reconstruction without choosing a basis of characters. -/
@[simp]
theorem characterGroupAlgebraInvariantsEquiv_evaluation (a : H) :
    GroupLike.evaluationBialgHom L (L ⊗[k] H)
      (MonoidAlgebra.domCongr L L (MulEquiv.multiplicativeAdditive C)
        (characterGroupAlgebraInvariantsEquiv k L H hspan a : D)) = 1 ⊗ₜ[k] a := by
  rw [← characterEvaluationEquiv_apply k L H hspan]
  exact characterEvaluationEquiv_characterInvariantsAlgHom k L H hspan a

/-- The inverse reconstruction evaluates an invariant formal character expansion in the
original Hopf algebra. Its scalar extension is ordinary evaluation. -/
@[simp]
theorem characterGroupAlgebraInvariantsEquiv_symm_evaluation (x : groupAlgebraInvariants ρ) :
    1 ⊗ₜ[k] (characterGroupAlgebraInvariantsEquiv k L H hspan).symm x =
      GroupLike.evaluationBialgHom L (L ⊗[k] H)
        (MonoidAlgebra.domCongr L L (MulEquiv.multiplicativeAdditive C) (x : D)) := by
  simpa only [BialgEquiv.apply_symm_apply] using
    (characterGroupAlgebraInvariantsEquiv_evaluation k L H hspan
      ((characterGroupAlgebraInvariantsEquiv k L H hspan).symm x)).symm

end TauCeti.GaloisDescent
