/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Bilinear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Graded bimodule action preserves coproducts

Tensoring a graded bimodule with a graded left module preserves discrete coproducts in
both variables. These instances supply the coproduct interchange for the totalized action
on cochain complexes.

The construction adapts `TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Coproducts`,
contributed by Wentao Li and the Tau Ceti contributors in PR #14604, and shares its bilinear
cofan machinery.
-/

public section

noncomputable section
open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct
namespace TauCeti.GradedModuleCat
universe w v
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece]

section Left

variable {J : Type w}
  (M : J → GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece)
  (N : GradedModuleCat.{max w v} Δ.piece)
  (s : Cofan fun j ↦ bimoduleModuleTensorObj Γ Δ (M j) N)

private def moduleTensorLeftSummand (j : J) : M j →ₗ[k] N →ₗ[k] s.pt :=
  (bimoduleModuleTensorMk Γ Δ (M j) N).compr₂ ((s.inj j).hom.restrictScalars k)

private theorem moduleTensorLeftSummand_apply (j : J) (m : M j) (n : N) :
    moduleTensorLeftSummand Γ Δ M N s j m n =
      (s.inj j).hom (bimoduleModuleTensorTmul Γ Δ (M j) N m n) := by
  rw [moduleTensorLeftSummand, LinearMap.compr₂_apply, LinearMap.restrictScalars_apply,
    bimoduleModuleTensorMk_apply]

private def moduleTensorLeftBilinear : (coproductCofan M).pt →ₗ[k] N →ₗ[k] s.pt :=
  coproductBilinear M (moduleTensorLeftSummand Γ Δ M N s)

private theorem moduleTensorLeftBilinear_balance (b : B) (m : (coproductCofan M).pt) (n : N) :
    moduleTensorLeftBilinear Γ Δ M N s (((1 : A) ⊗ₜ[k] op b) • m) n =
      moduleTensorLeftBilinear Γ Δ M N s m (b • n) := by
  apply coproductBilinear_equivariant M (moduleTensorLeftSummand Γ Δ M N s)
    ((1 : A) ⊗ₜ[k] op b) LinearMap.id (Algebra.lsmul k k N b)
    LinearMap.id
  intro j m n
  simp only [LinearMap.id_apply, Algebra.lsmul_apply, moduleTensorLeftSummand_apply]
  rw [bimoduleModuleTensorTmul_balance]

private theorem moduleTensorLeftBilinear_left (a : A) (m : (coproductCofan M).pt) (n : N) :
    moduleTensorLeftBilinear Γ Δ M N s ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n =
      a • moduleTensorLeftBilinear Γ Δ M N s m n := by
  apply coproductBilinear_equivariant M (moduleTensorLeftSummand Γ Δ M N s)
    (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) LinearMap.id LinearMap.id
    (Algebra.lsmul k k s.pt a)
  intro j m n
  have h := (s.inj j).hom.map_smul a
    (bimoduleModuleTensorTmul Γ Δ (M j) N m n)
  rw [smul_bimoduleModuleTensorTmul] at h
  simpa only [LinearMap.id_apply, Algebra.lsmul_apply, moduleTensorLeftSummand_apply] using h

private theorem moduleTensorLeftBilinear_degree {p q : ℤ}
    {m : (coproductCofan M).pt} {n : N}
    (hm : m ∈ (coproductCofan M).pt.grading.piece p) (hn : n ∈ N.grading.piece q) :
    moduleTensorLeftBilinear Γ Δ M N s m n ∈ s.pt.grading.piece (p + q) :=
  coproductBilinear_mem M (moduleTensorLeftSummand Γ Δ M N s)
    (fun j {p q} {m n} hm hn ↦ by
      rw [moduleTensorLeftSummand_apply]
      exact map_mem (s.inj j) (bimoduleModuleTensorTmul_mem Γ Δ (M j) N hm hn)) hm hn

private def moduleTensorLeftDesc :
    bimoduleModuleTensorObj Γ Δ (coproductCofan M).pt N ⟶ s.pt :=
  bimoduleModuleTensorLift Γ Δ (moduleTensorLeftBilinear Γ Δ M N s)
    (moduleTensorLeftBilinear_balance Γ Δ M N s)
    (moduleTensorLeftBilinear_left Γ Δ M N s)
    (fun hm hn ↦ moduleTensorLeftBilinear_degree Γ Δ M N s hm hn)

private theorem moduleTensorLeftDesc_tmul (m : (coproductCofan M).pt) (n : N) :
    (moduleTensorLeftDesc Γ Δ M N s).hom
      (bimoduleModuleTensorTmul Γ Δ (coproductCofan M).pt N m n) =
        moduleTensorLeftBilinear Γ Δ M N s m n :=
  bimoduleModuleTensorLift_tmul Γ Δ (moduleTensorLeftBilinear Γ Δ M N s)
    (moduleTensorLeftBilinear_balance Γ Δ M N s)
    (moduleTensorLeftBilinear_left Γ Δ M N s)
    (fun hm hn ↦ moduleTensorLeftBilinear_degree Γ Δ M N s hm hn) m n

private abbrev moduleTensorLeftCofan : Cofan fun j ↦ bimoduleModuleTensorObj Γ Δ (M j) N :=
  Cofan.mk (bimoduleModuleTensorObj Γ Δ (coproductCofan M).pt N)
    (fun j ↦ bimoduleModuleTensorMap Γ Δ ((coproductCofan M).inj j) (𝟙 N))

private def moduleTensorLeftCofanIsColimit : IsColimit (moduleTensorLeftCofan Γ Δ M N) :=
  (moduleTensorLeftCofan Γ Δ M N).bilinearIsColimit.{w, v} M
    (fun j ↦ bimoduleModuleTensorMk Γ Δ (M j) N)
    (bimoduleModuleTensorMk Γ Δ (coproductCofan M).pt N)
    (fun j m n ↦ by
      -- Reduce the cofan injection together with its dependent tensor-object carrier.
      -- The cofan abbreviation has no equation theorem for `rw`, and `cofan_mk_inj`
      -- does not match until those carrier reductions are exposed.
      change (bimoduleModuleTensorMap Γ Δ ((coproductCofan M).inj j) (𝟙 N)).hom _ = _
      rw [bimoduleModuleTensorMk_apply, bimoduleModuleTensorMk_apply, bimoduleModuleTensorMap_tmul,
        hom_id, LinearMap.id_apply])
    (fun j {P} {f g} h ↦ bimoduleModuleTensor_hom_ext Γ Δ
      (fun m n ↦ by simpa only [bimoduleModuleTensorMk_apply] using h m n))
    (fun {P} {f g} h ↦ bimoduleModuleTensor_hom_ext Γ Δ
      (fun m n ↦ by
        simpa only [bimoduleModuleTensorMk_apply Γ Δ (coproductCofan M).pt N] using h m n))
    (moduleTensorLeftDesc Γ Δ M N)
    (fun s m n ↦ by
      rw [bimoduleModuleTensorMk_apply Γ Δ (coproductCofan M).pt N, moduleTensorLeftDesc_tmul]
      rfl)

/-- Tensoring with a graded left module preserves coproducts of bimodules. -/
instance : PreservesColimit (Discrete.functor M) ((bimoduleModuleTensor Γ Δ).flip.obj N) :=
  preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit M)
    ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
      (moduleTensorLeftCofanIsColimit Γ Δ M N))

end Left

section Right

variable {J : Type w}
  (M : GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece)
  (N : J → GradedModuleCat.{max w v} Δ.piece)
  (s : Cofan fun j ↦ bimoduleModuleTensorObj Γ Δ M (N j))

private def moduleTensorRightSummand (j : J) : N j →ₗ[k] M →ₗ[k] s.pt :=
  ((bimoduleModuleTensorMk Γ Δ M (N j)).compr₂ ((s.inj j).hom.restrictScalars k)).flip

private theorem moduleTensorRightSummand_apply (j : J) (n : N j) (m : M) :
    moduleTensorRightSummand Γ Δ M N s j n m =
      (s.inj j).hom (bimoduleModuleTensorTmul Γ Δ M (N j) m n) := by
  rw [moduleTensorRightSummand, LinearMap.flip_apply, LinearMap.compr₂_apply,
    LinearMap.restrictScalars_apply, bimoduleModuleTensorMk_apply]

private def moduleTensorRightBilinear : M →ₗ[k] (coproductCofan N).pt →ₗ[k] s.pt :=
  (coproductBilinear N (moduleTensorRightSummand Γ Δ M N s)).flip

private theorem moduleTensorRightBilinear_balance (b : B) (m : M) (n : (coproductCofan N).pt) :
    moduleTensorRightBilinear Γ Δ M N s (((1 : A) ⊗ₜ[k] op b) • m) n =
      moduleTensorRightBilinear Γ Δ M N s m (b • n) := by
  symm
  apply coproductBilinear_equivariant N (moduleTensorRightSummand Γ Δ M N s)
    b LinearMap.id
    (Algebra.lsmul k k M ((1 : A) ⊗ₜ[k] op b)) LinearMap.id
  intro j n m
  simp only [LinearMap.id_apply, Algebra.lsmul_apply, moduleTensorRightSummand_apply]
  rw [bimoduleModuleTensorTmul_balance]

private theorem moduleTensorRightBilinear_left (a : A) (m : M) (n : (coproductCofan N).pt) :
    moduleTensorRightBilinear Γ Δ M N s ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n =
      a • moduleTensorRightBilinear Γ Δ M N s m n := by
  have h := coproductBilinear_equivariant N (moduleTensorRightSummand Γ Δ M N s) 1
    (Algebra.lsmul k k M (a ⊗ₜ[k] (1 : Bᵐᵒᵖ))) LinearMap.id
    (Algebra.lsmul k k s.pt a) (fun j n m ↦ by
      have h := (s.inj j).hom.map_smul a
        (bimoduleModuleTensorTmul Γ Δ M (N j) m n)
      rw [smul_bimoduleModuleTensorTmul] at h
      simpa only [one_smul, LinearMap.id_apply, Algebra.lsmul_apply,
        moduleTensorRightSummand_apply] using h) n m
  simpa only [moduleTensorRightBilinear, LinearMap.flip_apply, LinearMap.id_apply,
    Algebra.lsmul_apply, one_smul] using h

private theorem moduleTensorRightBilinear_degree {p q : ℤ} {m : M} {n : (coproductCofan N).pt}
    (hm : m ∈ M.grading.piece p) (hn : n ∈ (coproductCofan N).pt.grading.piece q) :
    moduleTensorRightBilinear Γ Δ M N s m n ∈ s.pt.grading.piece (p + q) := by
  rw [moduleTensorRightBilinear,
    LinearMap.flip_apply (coproductBilinear N (moduleTensorRightSummand Γ Δ M N s))]
  simpa only [add_comm] using
    coproductBilinear_mem N (moduleTensorRightSummand Γ Δ M N s)
      (fun j {p q} {n m} hn hm ↦ by
        rw [moduleTensorRightSummand_apply]
        simpa only [add_comm] using map_mem (s.inj j)
          (bimoduleModuleTensorTmul_mem Γ Δ M (N j) (p := q) (q := p) hm hn)) hn hm

private def moduleTensorRightDesc :
    bimoduleModuleTensorObj Γ Δ M (coproductCofan N).pt ⟶ s.pt :=
  bimoduleModuleTensorLift Γ Δ (moduleTensorRightBilinear Γ Δ M N s)
    (moduleTensorRightBilinear_balance Γ Δ M N s)
    (moduleTensorRightBilinear_left Γ Δ M N s)
    (fun hm hn ↦ moduleTensorRightBilinear_degree Γ Δ M N s hm hn)

private theorem moduleTensorRightDesc_tmul (m : M) (n : (coproductCofan N).pt) :
    (moduleTensorRightDesc Γ Δ M N s).hom
      (bimoduleModuleTensorTmul Γ Δ M (coproductCofan N).pt m n) =
        moduleTensorRightBilinear Γ Δ M N s m n :=
  bimoduleModuleTensorLift_tmul Γ Δ (moduleTensorRightBilinear Γ Δ M N s)
    (moduleTensorRightBilinear_balance Γ Δ M N s)
    (moduleTensorRightBilinear_left Γ Δ M N s)
    (fun hm hn ↦ moduleTensorRightBilinear_degree Γ Δ M N s hm hn) m n

private abbrev moduleTensorRightCofan : Cofan fun j ↦ bimoduleModuleTensorObj Γ Δ M (N j) :=
  Cofan.mk (bimoduleModuleTensorObj Γ Δ M (coproductCofan N).pt)
    (fun j ↦ bimoduleModuleTensorMap Γ Δ (𝟙 M) ((coproductCofan N).inj j))

private def moduleTensorRightCofanIsColimit : IsColimit (moduleTensorRightCofan Γ Δ M N) :=
  (moduleTensorRightCofan Γ Δ M N).bilinearIsColimit.{w, v} N
    (fun j ↦ (bimoduleModuleTensorMk Γ Δ M (N j)).flip)
    (bimoduleModuleTensorMk Γ Δ M (coproductCofan N).pt).flip
    (fun j n m ↦ by
      -- Reduce the cofan injection together with its dependent tensor-object carrier.
      -- The cofan abbreviation has no equation theorem for `rw`, and `cofan_mk_inj`
      -- does not match until those carrier reductions are exposed.
      change (bimoduleModuleTensorMap Γ Δ (𝟙 M) ((coproductCofan N).inj j)).hom _ = _
      rw [LinearMap.flip_apply, LinearMap.flip_apply, bimoduleModuleTensorMk_apply,
        bimoduleModuleTensorMk_apply, bimoduleModuleTensorMap_tmul, hom_id, LinearMap.id_apply])
    (fun j {P} {f g} h ↦ bimoduleModuleTensor_hom_ext Γ Δ
      (fun m n ↦ by simpa only [LinearMap.flip_apply, bimoduleModuleTensorMk_apply] using h n m))
    (fun {P} {f g} h ↦ bimoduleModuleTensor_hom_ext Γ Δ
      (fun m n ↦ by
        simpa only [LinearMap.flip_apply,
          bimoduleModuleTensorMk_apply Γ Δ M (coproductCofan N).pt] using h n m))
    (moduleTensorRightDesc Γ Δ M N)
    (fun s n m ↦ by
      rw [LinearMap.flip_apply, bimoduleModuleTensorMk_apply Γ Δ M (coproductCofan N).pt,
        moduleTensorRightDesc_tmul]
      rfl)

/-- Tensoring with a graded bimodule preserves coproducts of left modules. -/
instance : PreservesColimit (Discrete.functor N) ((bimoduleModuleTensor Γ Δ).obj M) :=
  preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit N)
    ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
      (moduleTensorRightCofanIsColimit Γ Δ M N))

end Right

variable {J : Type w}

/-- A fixed graded left module preserves coproducts of bimodules of the given shape. -/
instance (N : GradedModuleCat.{max w v} Δ.piece) :
    PreservesColimitsOfShape (Discrete J)
      ((bimoduleModuleTensor.{max w v, max w v} Γ Δ).flip.obj N) :=
  preservesColimitsOfShape_of_discrete _

/-- A fixed graded bimodule preserves coproducts of left modules of the given shape. -/
instance (M : GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece) :
    PreservesColimitsOfShape (Discrete J)
      ((bimoduleModuleTensor.{max w v, max w v} Γ Δ).obj M) :=
  preservesColimitsOfShape_of_discrete _

end TauCeti.GradedModuleCat
