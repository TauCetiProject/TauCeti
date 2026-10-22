/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.OuterFactors
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Corner
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Basic

/-!
# Tensor factors of the zigzag vertex bimodule

The cyclic enveloping-algebra ideal used for `zigzagBraidBimodule` is
`Z e_i ⊗[k] e_i Z`. The right ideal is represented in `Zᵐᵒᵖ`.
We identify these presentations using `spanSingletonTensorProductEquiv` and
`LinearEquiv.ofEq`, and compute the two outer actions on the tensor factors.

This carrier identification is the input for extracting the middle corner from
balanced products of vertex bimodules. In particular it supplies a prerequisite
for the self-tensor decomposition used in the inverse braid homotopy equivalence.
The construction covers isolated vertices of the public componentwise algebra.
Balanced products extract the middle corner `e_i Z e_j`, leaving the two outer ideal factors.
-/

public section

noncomputable section

namespace TauCeti

open MulOpposite
open scoped TensorProduct

variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "E" => Z ⊗[k] Zᵐᵒᵖ
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
attribute [local instance] zigzagAlgebraIntegerGradedAlgebra
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "L" => fun i : V ↦ (Ideal.span {e i} : Ideal Z)
local notation "R" => fun i : V ↦ (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)

private theorem vertexBimodule_eq_span (i : V) :
    (Ideal.span {e i ⊗ₜ[k] op (e i)} : Ideal E) = zigzagBraidBimodule k G i := by
  ext u
  have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
  rw [mem_span_singleton_iff_mul_eq_self
    (he.tmul (k := k) (by rw [IsIdempotentElem, ← op_mul, he.eq])),
    mem_zigzagBraidBimodule_iff]

private def factorsEquivBase (i : V) :
    zigzagBraidBimodule k G i ≃ₗ[k] L i ⊗[k] R i :=
  ((LinearEquiv.ofEq _ _ (vertexBimodule_eq_span k G i)).restrictScalars k).symm.trans
    (spanSingletonTensorProductEquiv k (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
      (by rw [IsIdempotentElem, ← op_mul,
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i).eq])).symm

/-- Identify the actual graded vertex bimodule carrier with its two idempotent-ideal factors. -/
-- The graded carrier uses the same cyclic ideal, with inherited addition and scalar actions.
-- Specify these maps on that carrier so balanced products use its actual module instances.
def zigzagBraidBimoduleFactorsEquiv (i : V) : U i ≃ₗ[k] L i ⊗[k] R i where
  toFun u := factorsEquivBase k G i u
  invFun t := (factorsEquivBase k G i).symm t
  map_add' u v := (factorsEquivBase k G i).map_add u v
  map_smul' a u := (factorsEquivBase k G i).map_smul a u
  left_inv u := (factorsEquivBase k G i).symm_apply_apply u
  right_inv t := (factorsEquivBase k G i).apply_symm_apply t

/-- Including the tensor factors gives the enveloping-algebra representative of the bimodule. -/
theorem coe_zigzagBraidBimoduleFactorsEquiv_symm_apply (i : V) (t : L i ⊗[k] R i) :
    ((zigzagBraidBimoduleFactorsEquiv k G i).symm t : zigzagBraidBimodule k G i).val =
      TensorProduct.map ((L i).subtype.restrictScalars k)
        ((R i).subtype.restrictScalars k) t := by
  -- Compute the cyclic-ideal carrier map inside the graded equivalence.
  change ((factorsEquivBase k G i).symm t : E) = _
  simp only [factorsEquivBase, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.restrictScalars_apply,
    LinearEquiv.coe_ofEq_apply, coe_spanSingletonTensorProductEquiv_apply]

/-- The inverse identifies a pure tensor of the two ideals with the same ambient pure tensor. -/
@[simp]
theorem coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul (i : V) (x : L i) (y : R i) :
    ((zigzagBraidBimoduleFactorsEquiv k G i).symm (x ⊗ₜ[k] y) :
      zigzagBraidBimodule k G i).val =
      (x : Z) ⊗ₜ[k] (y : Zᵐᵒᵖ) := by
  rw [coe_zigzagBraidBimoduleFactorsEquiv_symm_apply, TensorProduct.map_tmul]
  rfl

/-- The inverse factor identification carries the two outer actions to the enveloping action. -/
@[simp]
theorem zigzagBraidBimoduleFactorsEquiv_symm_map_smul (i : V) (a b : Z)
    (t : L i ⊗[k] R i) :
    (zigzagBraidBimoduleFactorsEquiv k G i).symm
        (TensorProduct.map ((Algebra.lsmul k k (L i)) a)
          ((Algebra.lsmul k k (R i)) (op b)) t) =
      (a ⊗ₜ[k] op b) • (zigzagBraidBimoduleFactorsEquiv k G i).symm t := by
  -- Both enveloping actions are the inherited cyclic-ideal action.
  change (factorsEquivBase k G i).symm _ =
    (a ⊗ₜ[k] op b) • (factorsEquivBase k G i).symm t
  simp only [factorsEquivBase, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, spanSingletonTensorProductEquiv_map_smul,
    LinearEquiv.restrictScalars_apply, map_smul]

/-- The factor identification sends the enveloping action to the two factor actions. -/
-- This is an explicit action formula: the equivalence is `k`-linear, while the input uses
-- enveloping-algebra scalars. Global simp search for scalar-preserving equivs is unsuitable here.
theorem zigzagBraidBimoduleFactorsEquiv_tmul_smul (i : V) (a b : Z)
    (u : U i) :
    zigzagBraidBimoduleFactorsEquiv k G i ((a ⊗ₜ[k] op b) • u) =
      TensorProduct.map ((Algebra.lsmul k k (L i)) a)
        ((Algebra.lsmul k k (R i)) (op b)) (zigzagBraidBimoduleFactorsEquiv k G i u) := by
  apply (zigzagBraidBimoduleFactorsEquiv k G i).symm.injective
  rw [LinearEquiv.symm_apply_apply, zigzagBraidBimoduleFactorsEquiv_symm_map_smul,
    LinearEquiv.symm_apply_apply]

/-- On pure ideal tensors, the two factor actions are the enveloping-algebra action. -/
@[simp]
theorem zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul (i : V) (a : Z) (b : Zᵐᵒᵖ)
    (x : L i) (y : R i) :
    (a ⊗ₜ[k] b) • (zigzagBraidBimoduleFactorsEquiv k G i).symm (x ⊗ₜ[k] y) =
      (zigzagBraidBimoduleFactorsEquiv k G i).symm ((a • x) ⊗ₜ[k] (b • y)) := by
  simpa only [TensorProduct.map_tmul, Algebra.lsmul_apply, op_unop] using
    (zigzagBraidBimoduleFactorsEquiv_symm_map_smul k G i a (unop b) (x ⊗ₜ[k] y)).symm

/-- The generator `e_i ⊗ e_i` of the vertex bimodule, given by the generators of its two
idempotent-ideal factors. -/
def zigzagBraidBimoduleVertexGenerator (i : V) : U i :=
  (zigzagBraidBimoduleFactorsEquiv k G i).symm
    (spanSingletonGenerator (e i) ⊗ₜ[k] spanSingletonGenerator (op (e i)))

/-- The vertex generator is the inverse factor identification of the two ideal generators. -/
theorem zigzagBraidBimoduleVertexGenerator_def (i : V) :
    zigzagBraidBimoduleVertexGenerator k G i = (zigzagBraidBimoduleFactorsEquiv k G i).symm
      (spanSingletonGenerator (e i) ⊗ₜ[k] spanSingletonGenerator (op (e i))) := (rfl)

/-- The vertex generator has internal degree zero. -/
theorem zigzagBraidBimoduleVertexGenerator_mem (i : V) :
    zigzagBraidBimoduleVertexGenerator k G i ∈ (U i).grading.piece 0 := by
  have he := zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i
  refine mem_zigzagBraidBimoduleGrade_iff.mpr ?_
  rw [zigzagBraidBimoduleVertexGenerator_def, coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul]
  simpa using tmul_mem_zigzagEnvelopingGrading he he

private local instance tensorFactorsRightModule (i : V) : Module Zᵐᵒᵖ (U i) :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)
private local instance tensorFactorsLeftModule (i : V) : Module Z (U i) :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)

/-- Identify the vertex bimodule with its two idempotent-ideal factors in the opposite order,
the right ideal first. The right action of `Z` is then the action of `Zᵐᵒᵖ` on the first factor,
the form in which balanced tensor products over `Z` act. -/
def zigzagBraidBimoduleRightFactorsEquiv (i : V) : U i ≃ₗ[k] R i ⊗[k] L i :=
  (zigzagBraidBimoduleFactorsEquiv k G i).trans (TensorProduct.comm k _ _)

/-- The reversed factor identification is the factor identification followed by swapping the
two factors. -/
@[simp]
theorem zigzagBraidBimoduleRightFactorsEquiv_apply (i : V) (u : U i) :
    zigzagBraidBimoduleRightFactorsEquiv k G i u =
      TensorProduct.comm k (L i) (R i) (zigzagBraidBimoduleFactorsEquiv k G i u) := (rfl)

/-- The reversed factor identification carries the right action of `Z` on the vertex bimodule to
the action of `Zᵐᵒᵖ` on the right-ideal factor. It is stated with the restricted `Zᵐᵒᵖ` action,
the form `BalancedTensorProduct.congr` expects. -/
theorem zigzagBraidBimoduleRightFactorsEquiv_op_smul (i : V) (a : Z) (m : U i) :
    letI := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)
    zigzagBraidBimoduleRightFactorsEquiv k G i (op a • m) =
      op a • zigzagBraidBimoduleRightFactorsEquiv k G i m := by
  have key (t : L i ⊗[k] R i) :
      TensorProduct.comm k (L i) (R i)
        (TensorProduct.map ((Algebra.lsmul k k (L i)) (1 : Z))
          ((Algebra.lsmul k k (R i)) (op a)) t) =
        op a • TensorProduct.comm k (L i) (R i) t := by
    induction t using TensorProduct.inductionOn with
    | tmul l r => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  exact (congrArg (TensorProduct.comm k (L i) (R i))
    (zigzagBraidBimoduleFactorsEquiv_tmul_smul k G i 1 a m)).trans
      (key (zigzagBraidBimoduleFactorsEquiv k G i m))

private theorem leftFactors_equivariant (j : V) (a : Z) (n : U j) :
    zigzagBraidBimoduleFactorsEquiv k G j (a • n) =
      a • zigzagBraidBimoduleFactorsEquiv k G j n := by
  have key (t : L j ⊗[k] R j) :
      TensorProduct.map ((Algebra.lsmul k k (L j)) a)
        ((Algebra.lsmul k k (R j)) (op (1 : Z))) t = a • t := by
    induction t using TensorProduct.inductionOn with
    | tmul l r => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  exact (zigzagBraidBimoduleFactorsEquiv_tmul_smul k G j a 1 n).trans
    (key (zigzagBraidBimoduleFactorsEquiv k G j n))

/-- Extract the middle corner from the actual balanced product of two vertex bimodules. -/
def zigzagBraidTensorCornerEquiv (i j : V) :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U j) ≃ₗ[k]
      cornerSubmodule k (e i) (e j) ⊗[k] (L i ⊗[k] R j) :=
  (GradedModuleCat.bimoduleTensorUnderlyingEquiv Γ Γ Γ (U i) (U j)).trans
    ((BalancedTensorProduct.congr (zigzagBraidBimoduleRightFactorsEquiv k G i)
      (zigzagBraidBimoduleFactorsEquiv k G j)
      (zigzagBraidBimoduleRightFactorsEquiv_op_smul k G i) (leftFactors_equivariant k G j)).trans
    ((BalancedTensorProduct.outerFactors k Z (R i) (L j) (L i) (R j)).trans
      (TensorProduct.congr (spanSingletonBalancedTensorProductEquivCorner k
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (isIdempotentElem_zigzagAlgebraBasis_inl k G j)) (LinearEquiv.refl k _))))

/-- On pure vertex factors, middle-corner extraction multiplies the two inner factors. -/
@[simp]
theorem zigzagBraidTensorCornerEquiv_tmul (i j : V) (l : L i) (r : R i)
    (l' : L j) (r' : R j) :
    zigzagBraidTensorCornerEquiv k G i j
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U j)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r))
        ((zigzagBraidBimoduleFactorsEquiv k G j).symm (l' ⊗ₜ[k] r'))) =
    spanSingletonBalancedTensorProductEquivCorner k
      (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
      (isIdempotentElem_zigzagAlgebraBasis_inl k G j)
      (BalancedTensorProduct.tmul k Z r l') ⊗ₜ[k] (l ⊗ₜ[k] r') := by
  simp only [zigzagBraidTensorCornerEquiv, LinearEquiv.trans_apply]
  rw [GradedModuleCat.bimoduleTensorUnderlyingEquiv_tmul Γ Γ Γ (U i) (U j)]
  simp only [BalancedTensorProduct.congr_tmul, zigzagBraidBimoduleRightFactorsEquiv_apply,
    LinearEquiv.apply_symm_apply, TensorProduct.comm_tmul,
    BalancedTensorProduct.outerFactors_tmul, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply]

/-- The inverse middle-corner map inserts the right generator of the first vertex ideal. -/
@[simp]
theorem zigzagBraidTensorCornerEquiv_symm_tmul (i j : V)
    (x : cornerSubmodule k (e i) (e j)) (l : L i) (r : R j) :
    (zigzagBraidTensorCornerEquiv k G i j).symm (x ⊗ₜ[k] (l ⊗ₜ[k] r)) =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U j)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm
          (l ⊗ₜ[k] spanSingletonGenerator (op (e i))))
        ((zigzagBraidBimoduleFactorsEquiv k G j).symm
          (⟨(x : Z), mem_span_singleton_of_mem_cornerSubmodule
            (isIdempotentElem_zigzagAlgebraBasis_inl k G j) x.2⟩ ⊗ₜ[k] r)) := by
  apply (zigzagBraidTensorCornerEquiv k G i j).injective
  rw [LinearEquiv.apply_symm_apply, zigzagBraidTensorCornerEquiv_tmul]
  congr 1
  apply Subtype.ext
  simp only [coe_spanSingletonBalancedTensorProductEquivCorner_tmul,
    coe_spanSingletonGenerator, unop_op]
  exact (mul_eq_self_of_mem_cornerSubmodule
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i) x.2).symm

/-- Middle-corner extraction carries enveloping scalars to the two outer ideal factors. -/
theorem zigzagBraidTensorCornerEquiv_tmul_smul (i j : V) (a : Z) (b : Zᵐᵒᵖ)
    (t : GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U j)) :
    zigzagBraidTensorCornerEquiv k G i j ((a ⊗ₜ[k] b) • t) =
      TensorProduct.map (LinearMap.id : cornerSubmodule k (e i) (e j) →ₗ[k] _)
        (TensorProduct.map ((Algebra.lsmul k k (L i)) a)
          ((Algebra.lsmul k k (R j)) b)) (zigzagBraidTensorCornerEquiv k G i j t) := by
  induction t using GradedModuleCat.bimoduleTensor_induction_on Γ Γ Γ (U i) (U j) with
  | ht x y =>
    obtain ⟨tx, rfl⟩ := (zigzagBraidBimoduleFactorsEquiv k G i).symm.surjective x
    obtain ⟨ty, rfl⟩ := (zigzagBraidBimoduleFactorsEquiv k G j).symm.surjective y
    induction tx using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [map_add, GradedModuleCat.bimoduleTensorTmul_add_left, smul_add, hx, hy]
    | tmul l r =>
      induction ty using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [map_add, GradedModuleCat.bimoduleTensorTmul_add_right, smul_add, hx, hy]
      | tmul l' r' =>
        simp only [GradedModuleCat.tmul_smul_bimoduleTensorTmul,
          zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul, one_smul,
          zigzagBraidTensorCornerEquiv_tmul, TensorProduct.map_tmul,
          LinearMap.id_apply, Algebra.lsmul_apply]
  | ha x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Evaluation on the left and right vertex factors is multiplication.
The function type fixes the graded source and target module structures. -/
@[simp]
theorem zigzagBraidEvaluation_factors (i : V) (l : L i) (r : R i) :
    (Bimodule.of (AlgHom.id k Z)).symm
      (DFunLike.coe (F := U i →ₗ[E] zigzagGradedBimodule k G)
        (zigzagBraidEvaluation k G i)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r))) =
      (l : Z) * unop (r : Zᵐᵒᵖ) := by
  rw [← hom_zigzagBraidEvaluationHom]
  have heval :=
    (LinearMap.congr_fun (hom_zigzagBraidEvaluationHom (k := k) (G := G) i)
      ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r))).trans
        (zigzagBraidEvaluation_apply (k := k) (G := G) (i := i) _)
  simpa only [coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul, Bimodule.smul_of,
    AlgHom.id_apply, mul_one, LinearEquiv.symm_apply_apply] using
      congrArg (Bimodule.of (AlgHom.id k Z)).symm heval

end TauCeti
