/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Graded bimodule tensor composition preserves coproducts

Balanced tensor composition preserves coproducts separately in both variables.
For each mapped direct-sum cofan, its universal map is the graded balanced lift
of the componentwise bilinear maps. Balancing and outer equivariance follow on
direct-sum generators, and the componentwise grading gives the required degree.

The resulting preservation instances provide the coproduct interchange needed
by Mathlib's associator for totalized cochain bifunctors. The direct-sum cofan,
graded tensor lift and categorical preservation machinery are reused throughout.
-/

public section

noncomputable section
open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct DirectSum
namespace TauCeti.GradedModuleCat
universe w v
variable {k A B C : Type*} [CommRing k] [Ring A] [Ring B] [Ring C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B) (Θ : InternalGrading k C)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece] [GradedAlgebra Θ.piece]

section Left

variable {J : Type w} [DecidableEq J]
  (M : J → GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece)
  (N : GradedModuleCat.{max w v} (Δ.tensorProduct Θ.opposite).piece)
  (s : Cofan fun j ↦ bimoduleTensorObj Γ Δ Θ (M j) N)

private def tensorLeftSummand (j : J) : M j →ₗ[k] N →ₗ[k] s.pt :=
  (((TensorProduct.mk k (M j) N).compr₂ (bimoduleTensorMkQ Γ Δ Θ (M j) N)).compr₂
    ((s.inj j).hom.restrictScalars k))

omit [DecidableEq J] in
private theorem tensorLeftSummand_apply (j : J) (m : M j) (n : N) :
    tensorLeftSummand Γ Δ Θ M N s j m n =
      (s.inj j).hom (bimoduleTensorTmul Γ Δ Θ (M j) N m n) := by
  simp only [tensorLeftSummand, LinearMap.compr₂_apply, LinearMap.restrictScalars_apply,
    TensorProduct.mk_apply, bimoduleTensorMkQ_tmul]

private def tensorLeftBilinear : (coproductCofan M).pt →ₗ[k] N →ₗ[k] s.pt := by
  classical
  exact DirectSum.toModule k J (N →ₗ[k] s.pt) (tensorLeftSummand Γ Δ Θ M N s)

private theorem tensorLeftBilinear_of (j : J) (m : M j) (n : N) :
    tensorLeftBilinear Γ Δ Θ M N s (DirectSum.of (fun j ↦ M j) j m) n =
      (s.inj j).hom (bimoduleTensorTmul Γ Δ Θ (M j) N m n) := by
  classical
  rw [tensorLeftBilinear, ← DirectSum.lof_eq_of k, DirectSum.toModule_lof,
    tensorLeftSummand_apply]

private theorem tensorLeftBilinear_inj (j : J) (m : M j) (n : N) :
    tensorLeftBilinear Γ Δ Θ M N s (((coproductCofan M).inj j).hom m) n =
      (s.inj j).hom (bimoduleTensorTmul Γ Δ Θ (M j) N m n) := by
  classical
  rw [hom_coproductCofan_inj, DirectSum.lof_eq_of]
  exact tensorLeftBilinear_of Γ Δ Θ M N s j m n

private theorem tensorLeftBilinear_balance (b : B) (m : (coproductCofan M).pt) (n : N) :
    tensorLeftBilinear Γ Δ Θ M N s (((1 : A) ⊗ₜ[k] op b) • m) n =
      tensorLeftBilinear Γ Δ Θ M N s m ((b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • n) := by
  classical
  induction m using DirectSum.induction_on with
  | zero =>
    have h : ((1 : A) ⊗ₜ[k] op b) • (0 : (coproductCofan M).pt) = 0 := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.zero_apply, smul_zero]
    rw [h]
    simp only [map_zero, LinearMap.zero_apply]
  | of j m =>
    rw [← DirectSum.of_smul (R := A ⊗[k] Bᵐᵒᵖ),
      tensorLeftBilinear_of, tensorLeftBilinear_of]
    rw [bimoduleTensorTmul_balance]
  | add x y hx hy =>
    have h : ((1 : A) ⊗ₜ[k] op b) • (x + y : (coproductCofan M).pt) =
        ((1 : A) ⊗ₜ[k] op b) • x + ((1 : A) ⊗ₜ[k] op b) • y := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.add_apply, smul_add]
    rw [h]
    simp only [map_add, LinearMap.add_apply, hx, hy]

private theorem tensorLeftBilinear_left (a : A) (m : (coproductCofan M).pt) (n : N) :
    tensorLeftBilinear Γ Δ Θ M N s ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n =
      (a ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • tensorLeftBilinear Γ Δ Θ M N s m n := by
  classical
  induction m using DirectSum.induction_on with
  | zero =>
    have h : (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (0 : (coproductCofan M).pt) = 0 := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.zero_apply, smul_zero]
    rw [h]
    simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | of j m =>
    rw [← DirectSum.of_smul (R := A ⊗[k] Bᵐᵒᵖ),
      tensorLeftBilinear_of, tensorLeftBilinear_of]
    have h := (s.inj j).hom.map_smul (a ⊗ₜ[k] (1 : Cᵐᵒᵖ))
      (bimoduleTensorTmul Γ Δ Θ (M j) N m n)
    rw [tmul_smul_bimoduleTensorTmul] at h
    simpa only [← Algebra.TensorProduct.one_def, one_smul] using h
  | add x y hx hy =>
    have h : (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (x + y : (coproductCofan M).pt) =
        (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • x + (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • y := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.add_apply, smul_add]
    rw [h]
    simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]

private theorem tensorLeftBilinear_right (c : Cᵐᵒᵖ) (m : (coproductCofan M).pt) (n : N) :
    tensorLeftBilinear Γ Δ Θ M N s m (((1 : B) ⊗ₜ[k] c) • n) =
      ((1 : A) ⊗ₜ[k] c) • tensorLeftBilinear Γ Δ Θ M N s m n := by
  classical
  induction m using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | of j m =>
    rw [tensorLeftBilinear_of, tensorLeftBilinear_of]
    have h := (s.inj j).hom.map_smul ((1 : A) ⊗ₜ[k] c)
      (bimoduleTensorTmul Γ Δ Θ (M j) N m n)
    rw [tmul_smul_bimoduleTensorTmul] at h
    simpa only [← Algebra.TensorProduct.one_def, one_smul] using h
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]

private theorem tensorLeftBilinear_degree {p q : ℤ}
    {m : (coproductCofan M).pt} {n : N}
    (hm : m ∈ (coproductCofan M).pt.grading.piece p) (hn : n ∈ N.grading.piece q) :
    tensorLeftBilinear Γ Δ Θ M N s m n ∈ s.pt.grading.piece (p + q) := by
  classical
  have hm' := (mem_coproductCofan_pt_piece_iff M).1 hm
  rw [← DFinsupp.sum_single (f := m), DFinsupp.sum, map_sum, LinearMap.sum_apply]
  refine (s.pt.grading.piece (p + q)).sum_mem fun j _ ↦ ?_
  rw [DirectSum.single_eq_lof k, DirectSum.lof_eq_of, tensorLeftBilinear_of]
  exact map_mem (s.inj j) (bimoduleTensorTmul_mem Γ Δ Θ (M j) N (hm' j) hn)

private def tensorLeftDesc :
    bimoduleTensorObj Γ Δ Θ (coproductCofan M).pt N ⟶ s.pt :=
  bimoduleTensorLift Γ Δ Θ (tensorLeftBilinear Γ Δ Θ M N s)
    (tensorLeftBilinear_balance Γ Δ Θ M N s)
    (tensorLeftBilinear_left Γ Δ Θ M N s)
    (tensorLeftBilinear_right Γ Δ Θ M N s)
    (fun hm hn ↦ tensorLeftBilinear_degree Γ Δ Θ M N s hm hn)

private abbrev tensorLeftCofan : Cofan fun j ↦ bimoduleTensorObj Γ Δ Θ (M j) N :=
  Cofan.mk (bimoduleTensorObj Γ Δ Θ (coproductCofan M).pt N)
    (fun j ↦ bimoduleTensorMap Γ Δ Θ ((coproductCofan M).inj j) (𝟙 N))

omit [DecidableEq J] in
private theorem tensorLeftCofan_inj (j : J) :
    (tensorLeftCofan Γ Δ Θ M N).inj j =
      bimoduleTensorMap Γ Δ Θ ((coproductCofan M).inj j) (𝟙 N) := rfl

private theorem tensorLeftDesc_tmul (m : (coproductCofan M).pt) (n : N) :
    (tensorLeftDesc Γ Δ Θ M N s).hom
      (bimoduleTensorTmul Γ Δ Θ (coproductCofan M).pt N m n) =
        tensorLeftBilinear Γ Δ Θ M N s m n := by
  rw [tensorLeftDesc, bimoduleTensorLift_tmul]

private theorem tensorLeft_inj_desc (j : J) :
    (tensorLeftCofan Γ Δ Θ M N).inj j ≫ tensorLeftDesc Γ Δ Θ M N s = s.inj j := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  rw [tensorLeftCofan_inj, GradedModuleCat.hom_comp, LinearMap.comp_apply]
  rw [bimoduleTensorMap_tmul Γ Δ Θ ((coproductCofan M).inj j) (𝟙 N) m n,
    GradedModuleCat.hom_id, LinearMap.id_apply, tensorLeftDesc_tmul,
    tensorLeftBilinear_inj]

private def tensorLeftCofanIsColimit : IsColimit (tensorLeftCofan Γ Δ Θ M N) := by
  classical
  refine Cofan.IsColimit.mk _ (tensorLeftDesc Γ Δ Θ M N)
    (tensorLeft_inj_desc Γ Δ Θ M N) ?_
  intro s f hf
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  induction m using DirectSum.induction_on with
  | zero => simp only [bimoduleTensorTmul_zero_left, map_zero]
  | of j m =>
    have h := LinearMap.congr_fun (congrArg Hom.hom (hf j))
      (bimoduleTensorTmul Γ Δ Θ (M j) N m n)
    rw [tensorLeftCofan_inj] at h
    rw [GradedModuleCat.hom_comp, LinearMap.comp_apply,
      bimoduleTensorMap_tmul Γ Δ Θ ((coproductCofan M).inj j) (𝟙 N) m n,
      GradedModuleCat.hom_id, LinearMap.id_apply] at h
    rw [tensorLeftDesc_tmul, tensorLeftBilinear_of]
    rw [hom_coproductCofan_inj M j, DirectSum.lof_eq_of] at h
    exact h
  | add x y hx hy =>
    rw [bimoduleTensorTmul_add_left Γ Δ Θ (coproductCofan M).pt N x y n, map_add, map_add]
    rw [hx, hy]

omit [DecidableEq J] in
/-- Balanced tensor composition preserves coproducts in its left variable. -/
instance : PreservesColimit (Discrete.functor M) ((bimoduleTensor Γ Δ Θ).flip.obj N) := by
  have : DecidableEq J := Classical.decEq J
  exact preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit M)
    ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
      (tensorLeftCofanIsColimit Γ Δ Θ M N))

end Left

section Right

variable {J : Type w} [DecidableEq J]
  (M : GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece)
  (N : J → GradedModuleCat.{max w v} (Δ.tensorProduct Θ.opposite).piece)
  (s : Cofan fun j ↦ bimoduleTensorObj Γ Δ Θ M (N j))

private def tensorRightSummand (j : J) : N j →ₗ[k] M →ₗ[k] s.pt :=
  ((((TensorProduct.mk k M (N j)).compr₂ (bimoduleTensorMkQ Γ Δ Θ M (N j))).compr₂
    ((s.inj j).hom.restrictScalars k))).flip

omit [DecidableEq J] in
private theorem tensorRightSummand_apply (j : J) (n : N j) (m : M) :
    tensorRightSummand Γ Δ Θ M N s j n m =
      (s.inj j).hom (bimoduleTensorTmul Γ Δ Θ M (N j) m n) := by
  simp only [tensorRightSummand, LinearMap.flip_apply, LinearMap.compr₂_apply,
    LinearMap.restrictScalars_apply, TensorProduct.mk_apply, bimoduleTensorMkQ_tmul]

private def tensorRightBilinear : M →ₗ[k] (coproductCofan N).pt →ₗ[k] s.pt := by
  classical
  exact (DirectSum.toModule k J (M →ₗ[k] s.pt) (tensorRightSummand Γ Δ Θ M N s)).flip

private theorem tensorRightBilinear_of (m : M) (j : J) (n : N j) :
    tensorRightBilinear Γ Δ Θ M N s m (DirectSum.of (fun j ↦ N j) j n) =
      (s.inj j).hom (bimoduleTensorTmul Γ Δ Θ M (N j) m n) := by
  classical
  rw [tensorRightBilinear, LinearMap.flip_apply, ← DirectSum.lof_eq_of k,
    DirectSum.toModule_lof, tensorRightSummand_apply]

private theorem tensorRightBilinear_inj (m : M) (j : J) (n : N j) :
    tensorRightBilinear Γ Δ Θ M N s m (((coproductCofan N).inj j).hom n) =
      (s.inj j).hom (bimoduleTensorTmul Γ Δ Θ M (N j) m n) := by
  classical
  rw [hom_coproductCofan_inj, DirectSum.lof_eq_of]
  exact tensorRightBilinear_of Γ Δ Θ M N s m j n

private theorem tensorRightBilinear_balance (b : B) (m : M) (n : (coproductCofan N).pt) :
    tensorRightBilinear Γ Δ Θ M N s (((1 : A) ⊗ₜ[k] op b) • m) n =
      tensorRightBilinear Γ Δ Θ M N s m ((b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • n) := by
  classical
  induction n using DirectSum.induction_on with
  | zero =>
    have h : (b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • (0 : (coproductCofan N).pt) = 0 := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.zero_apply, smul_zero]
    rw [h]
    simp only [map_zero]
  | of j n =>
    rw [← DirectSum.of_smul (R := B ⊗[k] Cᵐᵒᵖ),
      tensorRightBilinear_of, tensorRightBilinear_of]
    rw [bimoduleTensorTmul_balance]
  | add x y hx hy =>
    have h : (b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • (x + y : (coproductCofan N).pt) =
        (b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • x + (b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • y := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.add_apply, smul_add]
    rw [h]
    simp only [map_add, hx, hy]

private theorem tensorRightBilinear_left (a : A) (m : M) (n : (coproductCofan N).pt) :
    tensorRightBilinear Γ Δ Θ M N s ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n =
      (a ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • tensorRightBilinear Γ Δ Θ M N s m n := by
  classical
  induction n using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | of j n =>
    rw [tensorRightBilinear_of, tensorRightBilinear_of]
    have h := (s.inj j).hom.map_smul (a ⊗ₜ[k] (1 : Cᵐᵒᵖ))
      (bimoduleTensorTmul Γ Δ Θ M (N j) m n)
    rw [tmul_smul_bimoduleTensorTmul] at h
    simpa only [← Algebra.TensorProduct.one_def, one_smul] using h
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

private theorem tensorRightBilinear_right (c : Cᵐᵒᵖ) (m : M) (n : (coproductCofan N).pt) :
    tensorRightBilinear Γ Δ Θ M N s m (((1 : B) ⊗ₜ[k] c) • n) =
      ((1 : A) ⊗ₜ[k] c) • tensorRightBilinear Γ Δ Θ M N s m n := by
  classical
  induction n using DirectSum.induction_on with
  | zero =>
    have h : ((1 : B) ⊗ₜ[k] c) • (0 : (coproductCofan N).pt) = 0 := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.zero_apply, smul_zero]
    rw [h]
    simp only [map_zero, smul_zero]
  | of j n =>
    rw [← DirectSum.of_smul (R := B ⊗[k] Cᵐᵒᵖ),
      tensorRightBilinear_of, tensorRightBilinear_of]
    have h := (s.inj j).hom.map_smul ((1 : A) ⊗ₜ[k] c)
      (bimoduleTensorTmul Γ Δ Θ M (N j) m n)
    rw [tmul_smul_bimoduleTensorTmul] at h
    simpa only [← Algebra.TensorProduct.one_def, one_smul] using h
  | add x y hx hy =>
    have h : ((1 : B) ⊗ₜ[k] c) • (x + y : (coproductCofan N).pt) =
        ((1 : B) ⊗ₜ[k] c) • x + ((1 : B) ⊗ₜ[k] c) • y := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.add_apply, smul_add]
    rw [h]
    simp only [map_add, hx, hy, smul_add]

private theorem tensorRightBilinear_degree {p q : ℤ} {m : M} {n : (coproductCofan N).pt}
    (hm : m ∈ M.grading.piece p) (hn : n ∈ (coproductCofan N).pt.grading.piece q) :
    tensorRightBilinear Γ Δ Θ M N s m n ∈ s.pt.grading.piece (p + q) := by
  classical
  have hn' := (mem_coproductCofan_pt_piece_iff N).1 hn
  rw [← DFinsupp.sum_single (f := n), DFinsupp.sum, map_sum]
  refine (s.pt.grading.piece (p + q)).sum_mem fun j _ ↦ ?_
  rw [DirectSum.single_eq_lof k, DirectSum.lof_eq_of, tensorRightBilinear_of]
  exact map_mem (s.inj j) (bimoduleTensorTmul_mem Γ Δ Θ M (N j) hm (hn' j))

private def tensorRightDesc :
    bimoduleTensorObj Γ Δ Θ M (coproductCofan N).pt ⟶ s.pt :=
  bimoduleTensorLift Γ Δ Θ (tensorRightBilinear Γ Δ Θ M N s)
    (tensorRightBilinear_balance Γ Δ Θ M N s)
    (tensorRightBilinear_left Γ Δ Θ M N s)
    (tensorRightBilinear_right Γ Δ Θ M N s)
    (fun hm hn ↦ tensorRightBilinear_degree Γ Δ Θ M N s hm hn)

private abbrev tensorRightCofan : Cofan fun j ↦ bimoduleTensorObj Γ Δ Θ M (N j) :=
  Cofan.mk (bimoduleTensorObj Γ Δ Θ M (coproductCofan N).pt)
    (fun j ↦ bimoduleTensorMap Γ Δ Θ (𝟙 M) ((coproductCofan N).inj j))

omit [DecidableEq J] in
private theorem tensorRightCofan_inj (j : J) :
    (tensorRightCofan Γ Δ Θ M N).inj j =
      bimoduleTensorMap Γ Δ Θ (𝟙 M) ((coproductCofan N).inj j) := rfl

private theorem tensorRightDesc_tmul (m : M) (n : (coproductCofan N).pt) :
    (tensorRightDesc Γ Δ Θ M N s).hom
      (bimoduleTensorTmul Γ Δ Θ M (coproductCofan N).pt m n) =
        tensorRightBilinear Γ Δ Θ M N s m n := by
  rw [tensorRightDesc, bimoduleTensorLift_tmul]

private theorem tensorRight_inj_desc (j : J) :
    (tensorRightCofan Γ Δ Θ M N).inj j ≫ tensorRightDesc Γ Δ Θ M N s = s.inj j := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  rw [tensorRightCofan_inj, GradedModuleCat.hom_comp, LinearMap.comp_apply]
  rw [bimoduleTensorMap_tmul Γ Δ Θ (𝟙 M) ((coproductCofan N).inj j) m n,
    GradedModuleCat.hom_id, LinearMap.id_apply, tensorRightDesc_tmul, tensorRightBilinear_inj]

private def tensorRightCofanIsColimit : IsColimit (tensorRightCofan Γ Δ Θ M N) := by
  classical
  refine Cofan.IsColimit.mk _ (tensorRightDesc Γ Δ Θ M N)
    (tensorRight_inj_desc Γ Δ Θ M N) ?_
  intro s f hf
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro m n
  induction n using DirectSum.induction_on with
  | zero => simp only [bimoduleTensorTmul_zero_right, map_zero]
  | of j n =>
    have h := LinearMap.congr_fun (congrArg Hom.hom (hf j))
      (bimoduleTensorTmul Γ Δ Θ M (N j) m n)
    rw [tensorRightCofan_inj] at h
    rw [GradedModuleCat.hom_comp, LinearMap.comp_apply,
      bimoduleTensorMap_tmul Γ Δ Θ (𝟙 M) ((coproductCofan N).inj j) m n,
      GradedModuleCat.hom_id, LinearMap.id_apply] at h
    rw [tensorRightDesc_tmul, tensorRightBilinear_of]
    rw [hom_coproductCofan_inj N j, DirectSum.lof_eq_of] at h
    exact h
  | add x y hx hy =>
    rw [bimoduleTensorTmul_add_right Γ Δ Θ M (coproductCofan N).pt m x y, map_add, map_add]
    rw [hx, hy]

omit [DecidableEq J] in
/-- Balanced tensor composition preserves coproducts in its right variable. -/
instance : PreservesColimit (Discrete.functor N) ((bimoduleTensor Γ Δ Θ).obj M) := by
  have : DecidableEq J := Classical.decEq J
  exact preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit N)
    ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
      (tensorRightCofanIsColimit Γ Δ Θ M N))

end Right

variable {J : Type w}

/-- Tensoring with a fixed right bimodule preserves all coproducts of the given shape. -/
instance (N : GradedModuleCat.{max w v} (Δ.tensorProduct Θ.opposite).piece) :
    PreservesColimitsOfShape (Discrete J)
      ((bimoduleTensor.{max w v, max w v} Γ Δ Θ).flip.obj N) :=
  preservesColimitsOfShape_of_discrete _

/-- Tensoring with a fixed left bimodule preserves all coproducts of the given shape. -/
instance (M : GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece) :
    PreservesColimitsOfShape (Discrete J)
      ((bimoduleTensor.{max w v, max w v} Γ Δ Θ).obj M) :=
  preservesColimitsOfShape_of_discrete _

end TauCeti.GradedModuleCat
