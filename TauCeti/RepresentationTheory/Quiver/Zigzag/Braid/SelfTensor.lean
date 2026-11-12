/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Factors
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Tensor
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.TensorEvaluation
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The graded self-tensor of a zigzag vertex bimodule

The middle factor in the balanced self-tensor of `U_i = Z e_i ⊗[k] e_i Z` is
`e_i Z e_i`, with vertex and volume basis vectors in internal degrees zero and two.
Extracting that factor identifies the carrier with two copies of `U_i`.
The two insertions are enveloping-algebra linear and have the required degrees, so
reflection of isomorphisms by the existing graded-module forgetful functor upgrades
the carrier calculation to `U_i ⊗[Z] U_i ≅ U_i ⊞ U_i{2}`.

This is a prerequisite for the inverse braid homotopy equivalence. It does not
construct that homotopy. The calculation includes isolated vertices.

## References

* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*.
* B. Keller, *Deriving DG categories*, Section 6.1, for balanced tensor composition.
-/

public section

noncomputable section
namespace TauCeti
open MulOpposite CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct
variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]
local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "E" => Z ⊗[k] Zᵐᵒᵖ
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "L" => fun i : V ↦ (Ideal.span {e i} : Ideal Z)
local notation "R" => fun i : V ↦ (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)
-- Use the canonical signed path-length graded-algebra instance.
attribute [local instance] zigzagAlgebraIntegerGradedAlgebra
/-- Restrict the enveloping action to the right factor. -/
private local instance selfTensorRightModule (i : V) : Module Zᵐᵒᵖ (U i) :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)
/-- Restrict the enveloping action to the left factor. -/
private local instance selfTensorLeftModule (i : V) : Module Z (U i) :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)

private def selfTensorEquiv (i : V) :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i) ≃ₗ[k] (U i) × (U i) :=
  (zigzagBraidTensorCornerEquiv k G i i).trans
    ((TensorProduct.congr (zigzagAlgebraSelfCornerEquiv k G i)
      (LinearEquiv.refl k _)).trans
    ((TensorProduct.prodLeft k k k k (L i ⊗[k] R i)).trans
      (((TensorProduct.lid k (L i ⊗[k] R i)).trans
        (zigzagBraidBimoduleFactorsEquiv k G i).symm).prodCongr
       ((TensorProduct.lid k (L i ⊗[k] R i)).trans
        (zigzagBraidBimoduleFactorsEquiv k G i).symm))))

private theorem selfTensorEquiv_tmul (i : V) (l : L i) (r : R i)
    (l' : L i) (r' : R i) :
    selfTensorEquiv k G i
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r))
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l' ⊗ₜ[k] r'))) =
      (((zigzagAlgebraBasis k G).repr (unop (r : Zᵐᵒᵖ) * (l' : Z)) (.inl i)) •
          (zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r'),
       ((zigzagAlgebraBasis k G).repr (unop (r : Zᵐᵒᵖ) * (l' : Z)) (.inr (.inr i))) •
          (zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r')) := by
  simp only [selfTensorEquiv, LinearEquiv.trans_apply]
  rw [zigzagBraidTensorCornerEquiv_tmul]
  simp [TensorProduct.congr_tmul, LinearEquiv.prodCongr_apply]

private def vertexVolumeTensor (i : V) : U i :=
  ⟨zigzagAlgebraBasis k G (.inr (.inr i)) ⊗ₜ[k] op (e i), by
    simpa using tmul_mem_zigzagBraidBimodule i
      (zigzagAlgebraBasis k G (.inr (.inr i))) (1 : Z)⟩

private def selfTensorInsert (i : V) (z : GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i)) :
    U i →ₗ[E] GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i) :=
  (LinearMap.toSpanSingleton E _ z).comp (zigzagBraidBimodule k G i).subtype

@[simp] private theorem selfTensorInsert_apply (i : V)
    (z : GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i)) (u : U i) :
    selfTensorInsert k G i z u = (u : zigzagBraidBimodule k G i).val • z := (rfl)

private def selfTensorInsertZero (i : V) :
    U i →ₗ[E] GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i) :=
  selfTensorInsert k G i (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
    (zigzagBraidBimoduleVertexGenerator k G i) (zigzagBraidBimoduleVertexGenerator k G i))

private def selfTensorInsertTwo (i : V) :
    U i →ₗ[E] GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i) :=
  selfTensorInsert k G i (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
    (zigzagBraidBimoduleVertexGenerator k G i) (vertexVolumeTensor k G i))

private theorem vertexVolumeTensor_mem (i : V) :
    vertexVolumeTensor k G i ∈ (U i).grading.piece 2 := by
  have he : e i ∈ zigzagAlgebraIntegerGrade k G 0 :=
    (zigzagAlgebraIntegerGrade_ofNat k G 0).ge
      (zigzagAlgebraBasis_inl_mem_grade_zero k G i)
  have hx : zigzagAlgebraBasis k G (.inr (.inr i)) ∈ zigzagAlgebraIntegerGrade k G 2 :=
    (zigzagAlgebraIntegerGrade_ofNat k G 2).ge
      (zigzagAlgebraBasis_inr_inr_mem_grade_two k G i)
  exact mem_zigzagBraidBimoduleGrade_iff.mpr
    (tmul_mem_zigzagEnvelopingGrading hx he)

private def volumeInIdeal (i : V) : L i :=
  ⟨zigzagAlgebraBasis k G (.inr (.inr i)),
    (mem_span_singleton_iff_mul_eq_self
      (isIdempotentElem_zigzagAlgebraBasis_inl k G i)).mpr (by simp)⟩

private theorem vertexVolumeTensor_eq (i : V) :
    vertexVolumeTensor k G i = (zigzagBraidBimoduleFactorsEquiv k G i).symm
      ((volumeInIdeal k G i) ⊗ₜ[k] (spanSingletonGenerator (op (e i)))) := by
  apply Subtype.ext
  simpa only [coe_spanSingletonGenerator, vertexVolumeTensor,
    volumeInIdeal] using
    (coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul k G i
      (volumeInIdeal k G i) (spanSingletonGenerator (op (e i)))).symm

private theorem selfTensorInsertZero_factors (i : V) (l : L i) (r : R i) :
    selfTensorInsertZero k G i ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r)) =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] spanSingletonGenerator (op (e i))))
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (spanSingletonGenerator (e i) ⊗ₜ[k] r)) := by
  have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
  have heop : IsIdempotentElem (op (e i)) := by rw [IsIdempotentElem, ← op_mul, he.eq]
  rw [selfTensorInsertZero, selfTensorInsert_apply]
  have hu : ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r) :
      zigzagBraidBimodule k G i).val = (l : Z) ⊗ₜ[k] (r : Zᵐᵒᵖ) :=
    coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul k G i l r
  rw [hu, GradedModuleCat.tmul_smul_bimoduleTensorTmul Γ Γ Γ (U i) (U i),
    zigzagBraidBimoduleVertexGenerator_def]
  simp only [zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul,
    one_smul,
    smul_spanSingletonGenerator he, smul_spanSingletonGenerator heop]

private theorem selfTensorInsertTwo_factors (i : V) (l : L i) (r : R i) :
    selfTensorInsertTwo k G i ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r)) =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] spanSingletonGenerator (op (e i))))
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (volumeInIdeal k G i ⊗ₜ[k] r)) := by
  have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
  have heop : IsIdempotentElem (op (e i)) := by rw [IsIdempotentElem, ← op_mul, he.eq]
  rw [selfTensorInsertTwo, selfTensorInsert_apply]
  have hu : ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r) :
      zigzagBraidBimodule k G i).val = (l : Z) ⊗ₜ[k] (r : Zᵐᵒᵖ) :=
    coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul k G i l r
  rw [hu, GradedModuleCat.tmul_smul_bimoduleTensorTmul Γ Γ Γ (U i) (U i),
    zigzagBraidBimoduleVertexGenerator_def, vertexVolumeTensor_eq]
  simp only [zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul,
    one_smul,
    smul_spanSingletonGenerator he, smul_spanSingletonGenerator heop]

private theorem selfTensorEquiv_insertZero (i : V) (u : U i) :
    selfTensorEquiv k G i (selfTensorInsertZero k G i u) = (u, 0) := by
  classical
  have key (t : L i ⊗[k] R i) :
      selfTensorEquiv k G i (selfTensorInsertZero k G i
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm t)) =
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm t, 0) := by
    induction t using TensorProduct.inductionOn with
    | tmul l r =>
      rw [selfTensorInsertZero_factors, selfTensorEquiv_tmul]
      simp
    | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk, add_zero]
  simpa only [LinearEquiv.symm_apply_apply] using key (zigzagBraidBimoduleFactorsEquiv k G i u)

private theorem selfTensorEquiv_insertTwo (i : V) (u : U i) :
    selfTensorEquiv k G i (selfTensorInsertTwo k G i u) = (0, u) := by
  classical
  have key (t : L i ⊗[k] R i) :
      selfTensorEquiv k G i (selfTensorInsertTwo k G i
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm t)) =
        (0, (zigzagBraidBimoduleFactorsEquiv k G i).symm t) := by
    induction t using TensorProduct.inductionOn with
    | tmul l r =>
      rw [selfTensorInsertTwo_factors, selfTensorEquiv_tmul]
      simp [volumeInIdeal]
    | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk, add_zero]
  simpa only [LinearEquiv.symm_apply_apply] using key (zigzagBraidBimoduleFactorsEquiv k G i u)

/-- Insert the vertex component of the middle diagonal corner into the self-tensor. -/
def zigzagBraidSelfTensorInl (i : V) :
    U i ⟶ GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i) :=
  GradedModuleCat.ofHom (selfTensorInsertZero k G i) <|
    LinearMap.isHomogeneous_def.2 fun p u hu ↦ by
      have hz := GradedModuleCat.bimoduleTensorTmul_mem Γ Γ Γ (U i) (U i)
        (zigzagBraidBimoduleVertexGenerator_mem k G i)
        (zigzagBraidBimoduleVertexGenerator_mem k G i)
      simpa only [selfTensorInsertZero, selfTensorInsert_apply, vadd_eq_add, add_zero] using
        SetLike.GradedSMul.smul_mem (mem_zigzagBraidBimoduleGrade_iff.mp hu) hz

/-- Insert the volume component of the middle corner; its internal degree is two. -/
def zigzagBraidSelfTensorInr (i : V) :
    (U i).shiftObj 2 ⟶ GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i) :=
  GradedModuleCat.ofHom (selfTensorInsertTwo k G i) <|
    LinearMap.isHomogeneous_def.2 fun p u hu ↦ by
      have hu' := (GradedModuleCat.mem_shiftObj_piece_iff (U i) 2 p u).mp hu
      have hz := GradedModuleCat.bimoduleTensorTmul_mem Γ Γ Γ (U i) (U i)
        (zigzagBraidBimoduleVertexGenerator_mem k G i) (vertexVolumeTensor_mem k G i)
      have hdeg : (p - 2) + (0 + 2) = p + 0 := by omega
      simpa only [selfTensorInsertTwo, selfTensorInsert_apply, vadd_eq_add, hdeg] using
        SetLike.GradedSMul.smul_mem (mem_zigzagBraidBimoduleGrade_iff.mp hu') hz


private def insertPair (i : V) :
    (U i) × (U i) →ₗ[E] GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i) :=
  LinearMap.coprod (selfTensorInsertZero k G i) (selfTensorInsertTwo k G i)

private theorem selfTensorEquiv_insertPair (i : V) (uv : (U i) × (U i)) :
    selfTensorEquiv k G i (insertPair k G i uv) = uv := by
  simp [insertPair, selfTensorEquiv_insertZero, selfTensorEquiv_insertTwo]

private theorem bijective_insertPair (i : V) : Function.Bijective (insertPair k G i) :=
  ⟨fun x y h ↦ by
    simpa only [selfTensorEquiv_insertPair] using congrArg (selfTensorEquiv k G i) h,
    fun z ↦ ⟨selfTensorEquiv k G i z, by
      apply (selfTensorEquiv k G i).injective
      exact selfTensorEquiv_insertPair k G i _⟩⟩

private theorem isIso_insertDesc (i : V) :
    IsIso (biprod.desc (zigzagBraidSelfTensorInl k G i) (zigzagBraidSelfTensorInr k G i)) :=
  GradedModuleCat.isIso_biprod_desc_of_bijective _ _ (bijective_insertPair k G i)

/-- The graded vertex-bimodule self-tensor splits into the vertex and volume summands. -/
def zigzagBraidSelfTensorIso (i : V) :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i) ≅ (U i) ⊞ (U i).shiftObj 2 := by
  haveI := isIso_insertDesc k G i
  exact (asIso (biprod.desc (zigzagBraidSelfTensorInl k G i) (zigzagBraidSelfTensorInr k G i))).symm

/-- The inverse self-tensor isomorphism assembles the vertex and volume insertions. -/
@[simp]
theorem zigzagBraidSelfTensorIso_inv (i : V) :
    (zigzagBraidSelfTensorIso k G i).inv =
      biprod.desc (zigzagBraidSelfTensorInl k G i) (zigzagBraidSelfTensorInr k G i) := (rfl)

/-- The forward self-tensor isomorphism sends the vertex insertion to the first summand. -/
@[reassoc (attr := simp)]
theorem zigzagBraidSelfTensorInl_iso_hom (i : V) :
    zigzagBraidSelfTensorInl k G i ≫ (zigzagBraidSelfTensorIso k G i).hom = biprod.inl := by
  calc
    zigzagBraidSelfTensorInl k G i ≫ (zigzagBraidSelfTensorIso k G i).hom =
        (biprod.inl ≫ (zigzagBraidSelfTensorIso k G i).inv) ≫
          (zigzagBraidSelfTensorIso k G i).hom := by
      rw [zigzagBraidSelfTensorIso_inv, biprod.inl_desc]
    _ = biprod.inl := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The forward self-tensor isomorphism sends the volume insertion to the second summand. -/
@[reassoc (attr := simp)]
theorem zigzagBraidSelfTensorInr_iso_hom (i : V) :
    zigzagBraidSelfTensorInr k G i ≫ (zigzagBraidSelfTensorIso k G i).hom = biprod.inr := by
  calc
    zigzagBraidSelfTensorInr k G i ≫ (zigzagBraidSelfTensorIso k G i).hom =
        (biprod.inr ≫ (zigzagBraidSelfTensorIso k G i).inv) ≫
          (zigzagBraidSelfTensorIso k G i).hom := by
      rw [zigzagBraidSelfTensorIso_inv, biprod.inr_desc]
    _ = biprod.inr := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The vertex insertion separates the two outer ideal factors by the vertex idempotent. -/
@[simp]
theorem zigzagBraidSelfTensorInl_hom_factors (i : V) (l : L i) (r : R i) :
    (zigzagBraidSelfTensorInl k G i).hom
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r)) =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm
          (l ⊗ₜ[k] spanSingletonGenerator (op (e i))))
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm
          (spanSingletonGenerator (e i) ⊗ₜ[k] r)) := by
  simpa only [zigzagBraidSelfTensorInl, GradedModuleCat.hom_ofHom] using
    selfTensorInsertZero_factors k G i l r

private theorem volumeInIdeal_eq (i : V) : volumeInIdeal k G i =
    (zigzagAlgebraBasis k G (.inr (.inr i))) • spanSingletonGenerator (e i) := by
  apply Subtype.ext
  simp [volumeInIdeal]

/-- The volume insertion has the same outer factors and inserts the degree-two middle vector. -/
@[simp]
theorem zigzagBraidSelfTensorInr_hom_factors (i : V) (l : L i) (r : R i) :
    (zigzagBraidSelfTensorInr k G i).hom
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r)) =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm
          (l ⊗ₜ[k] spanSingletonGenerator (op (e i))))
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm
          (((zigzagAlgebraBasis k G (.inr (.inr i))) • spanSingletonGenerator (e i)) ⊗ₜ[k] r)) := by
  simpa only [zigzagBraidSelfTensorInr, GradedModuleCat.hom_ofHom,
    volumeInIdeal_eq] using selfTensorInsertTwo_factors k G i l r

/-- The degree-zero self-tensor insertion followed by right evaluation is the identity. -/
@[reassoc (attr := simp)]
theorem zigzagBraidSelfTensorInl_evaluationRight (i : V) :
    zigzagBraidSelfTensorInl k G i ≫ zigzagBraidTensorEvaluationRight k G i i =
      𝟙 (U i) := by
  apply GradedModuleCat.hom_ext
  apply LinearMap.ext
  intro u
  obtain ⟨t, rfl⟩ := (zigzagBraidBimoduleFactorsEquiv k G i).symm.surjective u
  induction t using TensorProduct.inductionOn with
  | tmul l r =>
    have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
    have heop : IsIdempotentElem (op (e i)) := by rw [IsIdempotentElem, ← op_mul, he.eq]
    have hr : e i * unop (r : Zᵐᵒᵖ) = unop (r : Zᵐᵒᵖ) := by
      simpa only [unop_mul, unop_op] using
        congrArg unop ((mem_span_singleton_iff_mul_eq_self heop).mp r.property)
    simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
      GradedModuleCat.hom_id, LinearMap.id_apply]
    rw [zigzagBraidSelfTensorInl_hom_factors k G i l r,
      zigzagBraidTensorEvaluationRight_tmul, hom_zigzagBraidEvaluationHom,
      zigzagBraidEvaluation_factors]
    simp only [coe_spanSingletonGenerator, hr, op_unop,
      zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul, one_smul,
      smul_spanSingletonGenerator heop]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The degree-zero self-tensor insertion followed by left evaluation is the identity. -/
@[reassoc (attr := simp)]
theorem zigzagBraidSelfTensorInl_evaluationLeft (i : V) :
    zigzagBraidSelfTensorInl k G i ≫ zigzagBraidTensorEvaluationLeft k G i i =
      𝟙 (U i) := by
  apply GradedModuleCat.hom_ext
  apply LinearMap.ext
  intro u
  obtain ⟨t, rfl⟩ := (zigzagBraidBimoduleFactorsEquiv k G i).symm.surjective u
  induction t using TensorProduct.inductionOn with
  | tmul l r =>
    have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
    have hl : (l : Z) * e i = (l : Z) :=
      (mem_span_singleton_iff_mul_eq_self he).mp l.property
    simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
      GradedModuleCat.hom_id, LinearMap.id_apply]
    rw [zigzagBraidSelfTensorInl_hom_factors k G i l r,
      zigzagBraidTensorEvaluationLeft_tmul, hom_zigzagBraidEvaluationHom,
      zigzagBraidEvaluation_factors]
    simp only [coe_spanSingletonGenerator, unop_op, hl,
      zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul, one_smul,
      smul_spanSingletonGenerator he]
  | add x y hx hy => simp only [map_add, hx, hy]

end TauCeti
