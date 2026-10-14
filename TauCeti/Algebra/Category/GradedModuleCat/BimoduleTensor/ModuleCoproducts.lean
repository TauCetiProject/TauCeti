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
# Graded bimodule action preserves coproducts

Tensoring a graded bimodule with a graded left module preserves coproducts in each
variable. The direct-sum universal property constructs balanced bilinear maps, and
the existing graded tensor lift makes their universal maps homogeneous and left-linear.

These instances provide the coproduct interchange required by Mathlib's associator
for the totalized action on cochain complexes. They retain the opaque tensor bifunctor
and use its public object and transported map computations.
-/

public section

noncomputable section
open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct DirectSum
namespace TauCeti.GradedModuleCat
universe w v
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece]

section Left

variable {J : Type w} [DecidableEq J]
  (M : J → GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece)
  (N : GradedModuleCat.{max w v} Δ.piece)
  (s : Cofan fun j ↦ bimoduleModuleTensorObj Γ Δ (M j) N)

private def moduleTensorLeftSummand (j : J) : M j →ₗ[k] N →ₗ[k] s.pt :=
  (bimoduleModuleTensorMk Γ Δ (M j) N).compr₂ ((s.inj j).hom.restrictScalars k)

omit [DecidableEq J] in
private theorem moduleTensorLeftSummand_apply (j : J) (m : M j) (n : N) :
    moduleTensorLeftSummand Γ Δ M N s j m n =
      (s.inj j).hom (bimoduleModuleTensorTmul Γ Δ (M j) N m n) := by
  simp only [moduleTensorLeftSummand, LinearMap.compr₂_apply,
    LinearMap.restrictScalars_apply, bimoduleModuleTensorMk_apply]

private def moduleTensorLeftBilinear : (coproductCofan M).pt →ₗ[k] N →ₗ[k] s.pt := by
  classical
  exact DirectSum.toModule k J (N →ₗ[k] s.pt) (moduleTensorLeftSummand Γ Δ M N s)

private theorem moduleTensorLeftBilinear_of (j : J) (m : M j) (n : N) :
    moduleTensorLeftBilinear Γ Δ M N s (DirectSum.of (fun j ↦ M j) j m) n =
      (s.inj j).hom (bimoduleModuleTensorTmul Γ Δ (M j) N m n) := by
  classical
  rw [moduleTensorLeftBilinear, ← DirectSum.lof_eq_of k, DirectSum.toModule_lof,
    moduleTensorLeftSummand_apply]

private theorem moduleTensorLeftBilinear_inj (j : J) (m : M j) (n : N) :
    moduleTensorLeftBilinear Γ Δ M N s (((coproductCofan M).inj j).hom m) n =
      (s.inj j).hom (bimoduleModuleTensorTmul Γ Δ (M j) N m n) := by
  classical
  rw [hom_coproductCofan_inj, DirectSum.lof_eq_of]
  exact moduleTensorLeftBilinear_of Γ Δ M N s j m n

private theorem moduleTensorLeftBilinear_balance (b : B) (m : (coproductCofan M).pt) (n : N) :
    moduleTensorLeftBilinear Γ Δ M N s (((1 : A) ⊗ₜ[k] op b) • m) n =
      moduleTensorLeftBilinear Γ Δ M N s m (b • n) := by
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
      moduleTensorLeftBilinear_of, moduleTensorLeftBilinear_of]
    rw [bimoduleModuleTensorTmul_balance]
  | add x y hx hy =>
    have h : ((1 : A) ⊗ₜ[k] op b) • (x + y : (coproductCofan M).pt) =
        ((1 : A) ⊗ₜ[k] op b) • x + ((1 : A) ⊗ₜ[k] op b) • y := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.add_apply, smul_add]
    rw [h]
    simp only [map_add, LinearMap.add_apply, hx, hy]

private theorem moduleTensorLeftBilinear_left (a : A) (m : (coproductCofan M).pt) (n : N) :
    moduleTensorLeftBilinear Γ Δ M N s ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n =
      a • moduleTensorLeftBilinear Γ Δ M N s m n := by
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
      moduleTensorLeftBilinear_of, moduleTensorLeftBilinear_of]
    have h := (s.inj j).hom.map_smul a
      (bimoduleModuleTensorTmul Γ Δ (M j) N m n)
    rw [smul_bimoduleModuleTensorTmul] at h
    exact h
  | add x y hx hy =>
    have h : (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (x + y : (coproductCofan M).pt) =
        (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • x + (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • y := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.add_apply, smul_add]
    rw [h]
    simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]

private theorem moduleTensorLeftBilinear_degree {p q : ℤ}
    {m : (coproductCofan M).pt} {n : N}
    (hm : m ∈ (coproductCofan M).pt.grading.piece p) (hn : n ∈ N.grading.piece q) :
    moduleTensorLeftBilinear Γ Δ M N s m n ∈ s.pt.grading.piece (p + q) := by
  classical
  have hm' := (mem_coproductCofan_pt_piece_iff M).1 hm
  rw [← DFinsupp.sum_single (f := m), DFinsupp.sum, map_sum, LinearMap.sum_apply]
  refine (s.pt.grading.piece (p + q)).sum_mem fun j _ ↦ ?_
  rw [DirectSum.single_eq_lof k, DirectSum.lof_eq_of, moduleTensorLeftBilinear_of]
  exact map_mem (s.inj j) (bimoduleModuleTensorTmul_mem Γ Δ (M j) N (hm' j) hn)

private def moduleTensorLeftDesc :
    bimoduleModuleTensorObj Γ Δ (coproductCofan M).pt N ⟶ s.pt :=
  bimoduleModuleTensorLift Γ Δ (moduleTensorLeftBilinear Γ Δ M N s)
    (moduleTensorLeftBilinear_balance Γ Δ M N s)
    (moduleTensorLeftBilinear_left Γ Δ M N s)
    (fun hm hn ↦ moduleTensorLeftBilinear_degree Γ Δ M N s hm hn)

private abbrev moduleTensorLeftCofan : Cofan fun j ↦ bimoduleModuleTensorObj Γ Δ (M j) N :=
  Cofan.mk (bimoduleModuleTensorObj Γ Δ (coproductCofan M).pt N)
    (fun j ↦ bimoduleModuleTensorMap Γ Δ ((coproductCofan M).inj j) (𝟙 N))

omit [DecidableEq J] in
private theorem moduleTensorLeftCofan_inj (j : J) :
    (moduleTensorLeftCofan Γ Δ M N).inj j =
      bimoduleModuleTensorMap Γ Δ ((coproductCofan M).inj j) (𝟙 N) := rfl

private theorem moduleTensorLeftDesc_tmul (m : (coproductCofan M).pt) (n : N) :
    (moduleTensorLeftDesc Γ Δ M N s).hom
      (bimoduleModuleTensorTmul Γ Δ (coproductCofan M).pt N m n) =
        moduleTensorLeftBilinear Γ Δ M N s m n := by
  rw [moduleTensorLeftDesc, bimoduleModuleTensorLift_tmul]

private theorem moduleTensorLeft_inj_desc (j : J) :
    (moduleTensorLeftCofan Γ Δ M N).inj j ≫ moduleTensorLeftDesc Γ Δ M N s = s.inj j := by
  apply bimoduleModuleTensor_hom_ext Γ Δ
  intro m n
  rw [moduleTensorLeftCofan_inj, GradedModuleCat.hom_comp, LinearMap.comp_apply]
  rw [bimoduleModuleTensorMap_tmul Γ Δ ((coproductCofan M).inj j) (𝟙 N) m n,
    GradedModuleCat.hom_id, LinearMap.id_apply, moduleTensorLeftDesc_tmul,
    moduleTensorLeftBilinear_inj]

private def moduleTensorLeftCofanIsColimit : IsColimit (moduleTensorLeftCofan Γ Δ M N) := by
  classical
  refine Cofan.IsColimit.mk _ (moduleTensorLeftDesc Γ Δ M N)
    (moduleTensorLeft_inj_desc Γ Δ M N) ?_
  intro s f hf
  apply bimoduleModuleTensor_hom_ext Γ Δ
  intro m n
  induction m using DirectSum.induction_on with
  | zero => simp only [← bimoduleModuleTensorMk_apply, map_zero, LinearMap.zero_apply]
  | of j m =>
    have h := LinearMap.congr_fun (congrArg Hom.hom (hf j))
      (bimoduleModuleTensorTmul Γ Δ (M j) N m n)
    rw [moduleTensorLeftCofan_inj] at h
    rw [GradedModuleCat.hom_comp, LinearMap.comp_apply,
      bimoduleModuleTensorMap_tmul Γ Δ ((coproductCofan M).inj j) (𝟙 N) m n,
      GradedModuleCat.hom_id, LinearMap.id_apply] at h
    rw [moduleTensorLeftDesc_tmul, moduleTensorLeftBilinear_of]
    rw [hom_coproductCofan_inj M j, DirectSum.lof_eq_of] at h
    exact h
  | add x y hx hy =>
    simpa only [← bimoduleModuleTensorMk_apply, map_add, LinearMap.add_apply]
      using congrArg₂ (· + ·) hx hy

private def moduleTensorLeftFunctor (N : GradedModuleCat.{v} Δ.piece) :
    GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece ⥤
      GradedModuleCat.{v} Γ.piece where
  obj M := bimoduleModuleTensorObj Γ Δ M N
  map f := bimoduleModuleTensorMap Γ Δ f (𝟙 N)
  map_id _ := bimoduleModuleTensorMap_id Γ Δ
  map_comp _ _ := by rw [← bimoduleModuleTensorMap_comp, Category.id_comp]

private def moduleTensorLeftFunctorIso (N : GradedModuleCat.{v} Δ.piece) :
    (bimoduleModuleTensor.{v, v} Γ Δ).flip.obj N ≅ moduleTensorLeftFunctor Γ Δ N :=
  NatIso.ofComponents (fun M ↦
    eqToIso (bimoduleModuleTensor_obj_obj Γ Δ (M := M) (N := N))) (by
    intro M M' f
    dsimp only [Functor.flip_obj_map, moduleTensorLeftFunctor]
    simp only [eqToIso.hom, bimoduleModuleTensor_map_app, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id])

omit [DecidableEq J] in
/-- Tensoring with a graded left module preserves coproducts of bimodules. -/
instance : PreservesColimit (Discrete.functor M) ((bimoduleModuleTensor Γ Δ).flip.obj N) := by
  have : DecidableEq J := Classical.decEq J
  let : PreservesColimit (Discrete.functor M) (moduleTensorLeftFunctor.{max w v} Γ Δ N) :=
    preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit M)
      ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
        (moduleTensorLeftCofanIsColimit Γ Δ M N))
  exact preservesColimit_of_natIso _ (moduleTensorLeftFunctorIso.{max w v} Γ Δ N).symm

end Left

section Right

variable {J : Type w} [DecidableEq J]
  (M : GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece)
  (N : J → GradedModuleCat.{max w v} Δ.piece)
  (s : Cofan fun j ↦ bimoduleModuleTensorObj Γ Δ M (N j))

private def moduleTensorRightSummand (j : J) : N j →ₗ[k] M →ₗ[k] s.pt :=
  ((bimoduleModuleTensorMk Γ Δ M (N j)).compr₂
    ((s.inj j).hom.restrictScalars k)).flip

omit [DecidableEq J] in
private theorem moduleTensorRightSummand_apply (j : J) (n : N j) (m : M) :
    moduleTensorRightSummand Γ Δ M N s j n m =
      (s.inj j).hom (bimoduleModuleTensorTmul Γ Δ M (N j) m n) := by
  simp only [moduleTensorRightSummand, LinearMap.flip_apply, LinearMap.compr₂_apply,
    LinearMap.restrictScalars_apply, bimoduleModuleTensorMk_apply]

private def moduleTensorRightBilinear : M →ₗ[k] (coproductCofan N).pt →ₗ[k] s.pt := by
  classical
  exact (DirectSum.toModule k J (M →ₗ[k] s.pt) (moduleTensorRightSummand Γ Δ M N s)).flip

private theorem moduleTensorRightBilinear_of (m : M) (j : J) (n : N j) :
    moduleTensorRightBilinear Γ Δ M N s m (DirectSum.of (fun j ↦ N j) j n) =
      (s.inj j).hom (bimoduleModuleTensorTmul Γ Δ M (N j) m n) := by
  classical
  rw [moduleTensorRightBilinear, LinearMap.flip_apply, ← DirectSum.lof_eq_of k,
    DirectSum.toModule_lof, moduleTensorRightSummand_apply]

private theorem moduleTensorRightBilinear_inj (m : M) (j : J) (n : N j) :
    moduleTensorRightBilinear Γ Δ M N s m (((coproductCofan N).inj j).hom n) =
      (s.inj j).hom (bimoduleModuleTensorTmul Γ Δ M (N j) m n) := by
  classical
  rw [hom_coproductCofan_inj, DirectSum.lof_eq_of]
  exact moduleTensorRightBilinear_of Γ Δ M N s m j n

private theorem moduleTensorRightBilinear_balance (b : B) (m : M) (n : (coproductCofan N).pt) :
    moduleTensorRightBilinear Γ Δ M N s (((1 : A) ⊗ₜ[k] op b) • m) n =
      moduleTensorRightBilinear Γ Δ M N s m (b • n) := by
  classical
  induction n using DirectSum.induction_on with
  | zero =>
    have h : b • (0 : (coproductCofan N).pt) = 0 := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.zero_apply, smul_zero]
    rw [h]
    simp only [map_zero]
  | of j n =>
    rw [← DirectSum.of_smul (R := B),
      moduleTensorRightBilinear_of, moduleTensorRightBilinear_of]
    rw [bimoduleModuleTensorTmul_balance]
  | add x y hx hy =>
    have h : b • (x + y : (coproductCofan N).pt) =
        b • x + b • y := by
      apply DirectSum.ext
      intro j
      simp only [DirectSum.smul_apply, DirectSum.add_apply, smul_add]
    rw [h]
    simp only [map_add, hx, hy]

private theorem moduleTensorRightBilinear_left (a : A) (m : M) (n : (coproductCofan N).pt) :
    moduleTensorRightBilinear Γ Δ M N s ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n =
      a • moduleTensorRightBilinear Γ Δ M N s m n := by
  classical
  induction n using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | of j n =>
    rw [moduleTensorRightBilinear_of, moduleTensorRightBilinear_of]
    have h := (s.inj j).hom.map_smul a
      (bimoduleModuleTensorTmul Γ Δ M (N j) m n)
    rw [smul_bimoduleModuleTensorTmul] at h
    exact h
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

private theorem moduleTensorRightBilinear_degree {p q : ℤ} {m : M} {n : (coproductCofan N).pt}
    (hm : m ∈ M.grading.piece p) (hn : n ∈ (coproductCofan N).pt.grading.piece q) :
    moduleTensorRightBilinear Γ Δ M N s m n ∈ s.pt.grading.piece (p + q) := by
  classical
  have hn' := (mem_coproductCofan_pt_piece_iff N).1 hn
  rw [← DFinsupp.sum_single (f := n), DFinsupp.sum, map_sum]
  refine (s.pt.grading.piece (p + q)).sum_mem fun j _ ↦ ?_
  rw [DirectSum.single_eq_lof k, DirectSum.lof_eq_of, moduleTensorRightBilinear_of]
  exact map_mem (s.inj j) (bimoduleModuleTensorTmul_mem Γ Δ M (N j) hm (hn' j))

private def moduleTensorRightDesc :
    bimoduleModuleTensorObj Γ Δ M (coproductCofan N).pt ⟶ s.pt :=
  bimoduleModuleTensorLift Γ Δ (moduleTensorRightBilinear Γ Δ M N s)
    (moduleTensorRightBilinear_balance Γ Δ M N s)
    (moduleTensorRightBilinear_left Γ Δ M N s)
    (fun hm hn ↦ moduleTensorRightBilinear_degree Γ Δ M N s hm hn)

private abbrev moduleTensorRightCofan : Cofan fun j ↦ bimoduleModuleTensorObj Γ Δ M (N j) :=
  Cofan.mk (bimoduleModuleTensorObj Γ Δ M (coproductCofan N).pt)
    (fun j ↦ bimoduleModuleTensorMap Γ Δ (𝟙 M) ((coproductCofan N).inj j))

omit [DecidableEq J] in
private theorem moduleTensorRightCofan_inj (j : J) :
    (moduleTensorRightCofan Γ Δ M N).inj j =
      bimoduleModuleTensorMap Γ Δ (𝟙 M) ((coproductCofan N).inj j) := rfl

private theorem moduleTensorRightDesc_tmul (m : M) (n : (coproductCofan N).pt) :
    (moduleTensorRightDesc Γ Δ M N s).hom
      (bimoduleModuleTensorTmul Γ Δ M (coproductCofan N).pt m n) =
        moduleTensorRightBilinear Γ Δ M N s m n := by
  rw [moduleTensorRightDesc, bimoduleModuleTensorLift_tmul]

private theorem moduleTensorRight_inj_desc (j : J) :
    (moduleTensorRightCofan Γ Δ M N).inj j ≫ moduleTensorRightDesc Γ Δ M N s = s.inj j := by
  apply bimoduleModuleTensor_hom_ext Γ Δ
  intro m n
  rw [moduleTensorRightCofan_inj, GradedModuleCat.hom_comp, LinearMap.comp_apply]
  rw [bimoduleModuleTensorMap_tmul Γ Δ (𝟙 M) ((coproductCofan N).inj j) m n,
    GradedModuleCat.hom_id, LinearMap.id_apply, moduleTensorRightDesc_tmul,
    moduleTensorRightBilinear_inj]

private def moduleTensorRightCofanIsColimit : IsColimit (moduleTensorRightCofan Γ Δ M N) := by
  classical
  refine Cofan.IsColimit.mk _ (moduleTensorRightDesc Γ Δ M N)
    (moduleTensorRight_inj_desc Γ Δ M N) ?_
  intro s f hf
  apply bimoduleModuleTensor_hom_ext Γ Δ
  intro m n
  induction n using DirectSum.induction_on with
  | zero => simp only [← bimoduleModuleTensorMk_apply, map_zero]
  | of j n =>
    have h := LinearMap.congr_fun (congrArg Hom.hom (hf j))
      (bimoduleModuleTensorTmul Γ Δ M (N j) m n)
    rw [moduleTensorRightCofan_inj] at h
    rw [GradedModuleCat.hom_comp, LinearMap.comp_apply,
      bimoduleModuleTensorMap_tmul Γ Δ (𝟙 M) ((coproductCofan N).inj j) m n,
      GradedModuleCat.hom_id, LinearMap.id_apply] at h
    rw [moduleTensorRightDesc_tmul, moduleTensorRightBilinear_of]
    rw [hom_coproductCofan_inj N j, DirectSum.lof_eq_of] at h
    exact h
  | add x y hx hy =>
    simpa only [← bimoduleModuleTensorMk_apply, map_add, LinearMap.add_apply]
      using congrArg₂ (· + ·) hx hy

private def moduleTensorRightFunctor
    (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    GradedModuleCat.{v} Δ.piece ⥤ GradedModuleCat.{v} Γ.piece where
  obj N := bimoduleModuleTensorObj Γ Δ M N
  map g := bimoduleModuleTensorMap Γ Δ (𝟙 M) g
  map_id _ := bimoduleModuleTensorMap_id Γ Δ
  map_comp _ _ := by rw [← bimoduleModuleTensorMap_comp, Category.id_comp]

private def moduleTensorRightFunctorIso
    (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    (bimoduleModuleTensor.{v, v} Γ Δ).obj M ≅ moduleTensorRightFunctor Γ Δ M :=
  NatIso.ofComponents (fun N ↦
    eqToIso (bimoduleModuleTensor_obj_obj Γ Δ (M := M) (N := N))) (by
    intro N N' g
    dsimp only [moduleTensorRightFunctor]
    simp only [eqToIso.hom, bimoduleModuleTensor_obj_map, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id])

omit [DecidableEq J] in
/-- Tensoring with a graded bimodule preserves coproducts of left modules. -/
instance : PreservesColimit (Discrete.functor N) ((bimoduleModuleTensor Γ Δ).obj M) := by
  have : DecidableEq J := Classical.decEq J
  let : PreservesColimit (Discrete.functor N) (moduleTensorRightFunctor.{max w v} Γ Δ M) :=
    preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit N)
      ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
        (moduleTensorRightCofanIsColimit Γ Δ M N))
  exact preservesColimit_of_natIso _ (moduleTensorRightFunctorIso.{max w v} Γ Δ M).symm

end Right

variable {J : Type w}

/-- Tensoring with a fixed graded left module preserves all coproducts of the given shape. -/
instance (N : GradedModuleCat.{max w v} Δ.piece) :
    PreservesColimitsOfShape (Discrete J)
      ((bimoduleModuleTensor.{max w v, max w v} Γ Δ).flip.obj N) :=
  preservesColimitsOfShape_of_discrete _

/-- Tensoring with a fixed graded bimodule preserves all coproducts of the given shape. -/
instance (M : GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece) :
    PreservesColimitsOfShape (Discrete J)
      ((bimoduleModuleTensor.{max w v, max w v} Γ Δ).obj M) :=
  preservesColimitsOfShape_of_discrete _

end TauCeti.GradedModuleCat
