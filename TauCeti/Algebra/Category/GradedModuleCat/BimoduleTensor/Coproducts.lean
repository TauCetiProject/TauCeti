/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Bilinear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Graded bimodule tensor composition preserves coproducts

Balanced tensor composition of graded bimodules preserves discrete coproducts separately
in both variables. These preservation instances provide the coproduct interchange needed
by Mathlib's associator for totalized cochain bifunctors.
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

private def tensorBilinear
    (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece)
    (N : GradedModuleCat.{v} (Δ.tensorProduct Θ.opposite).piece) :
    M →ₗ[k] N →ₗ[k] bimoduleTensorObj Γ Δ Θ M N :=
  (TensorProduct.mk k M N).compr₂ (bimoduleTensorMkQ Γ Δ Θ M N)

private theorem tensorBilinear_apply
    (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece)
    (N : GradedModuleCat.{v} (Δ.tensorProduct Θ.opposite).piece) (m : M) (n : N) :
    tensorBilinear Γ Δ Θ M N m n = bimoduleTensorTmul Γ Δ Θ M N m n := by
  simp only [tensorBilinear, LinearMap.compr₂_apply, TensorProduct.mk_apply,
    bimoduleTensorMkQ_tmul]

section Left

variable {J : Type w}
  (M : J → GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece)
  (N : GradedModuleCat.{max w v} (Δ.tensorProduct Θ.opposite).piece)
  (s : Cofan fun j ↦ bimoduleTensorObj Γ Δ Θ (M j) N)

private def tensorLeftSummand (j : J) : M j →ₗ[k] N →ₗ[k] s.pt :=
  (tensorBilinear Γ Δ Θ (M j) N).compr₂ ((s.inj j).hom.restrictScalars k)

private theorem tensorLeftSummand_apply (j : J) (m : M j) (n : N) :
    tensorLeftSummand Γ Δ Θ M N s j m n =
      (s.inj j).hom (bimoduleTensorTmul Γ Δ Θ (M j) N m n) := by
  rw [tensorLeftSummand, LinearMap.compr₂_apply, LinearMap.restrictScalars_apply,
    tensorBilinear_apply]

private def tensorLeftBilinear : (coproductCofan M).pt →ₗ[k] N →ₗ[k] s.pt :=
  coproductBilinear M (tensorLeftSummand Γ Δ Θ M N s)

private theorem tensorLeftBilinear_balance (b : B) (m : (coproductCofan M).pt) (n : N) :
    tensorLeftBilinear Γ Δ Θ M N s (((1 : A) ⊗ₜ[k] op b) • m) n =
      tensorLeftBilinear Γ Δ Θ M N s m ((b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • n) := by
  apply coproductBilinear_equivariant M (tensorLeftSummand Γ Δ Θ M N s)
    ((1 : A) ⊗ₜ[k] op b) LinearMap.id (Algebra.lsmul k k N (b ⊗ₜ[k] (1 : Cᵐᵒᵖ)))
    LinearMap.id
  intro j m n
  simp only [LinearMap.id_apply, Algebra.lsmul_apply, tensorLeftSummand_apply]
  rw [bimoduleTensorTmul_balance]

private theorem tensorLeftBilinear_left (a : A) (m : (coproductCofan M).pt) (n : N) :
    tensorLeftBilinear Γ Δ Θ M N s ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n =
      (a ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • tensorLeftBilinear Γ Δ Θ M N s m n := by
  apply coproductBilinear_equivariant M (tensorLeftSummand Γ Δ Θ M N s)
    (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) LinearMap.id LinearMap.id
    (Algebra.lsmul k k s.pt (a ⊗ₜ[k] (1 : Cᵐᵒᵖ)))
  intro j m n
  have h := (s.inj j).hom.map_smul (a ⊗ₜ[k] (1 : Cᵐᵒᵖ))
    (bimoduleTensorTmul Γ Δ Θ (M j) N m n)
  rw [tmul_smul_bimoduleTensorTmul] at h
  simpa only [LinearMap.id_apply, Algebra.lsmul_apply, tensorLeftSummand_apply,
    ← Algebra.TensorProduct.one_def, one_smul] using h

private theorem tensorLeftBilinear_right (c : Cᵐᵒᵖ) (m : (coproductCofan M).pt) (n : N) :
    tensorLeftBilinear Γ Δ Θ M N s m (((1 : B) ⊗ₜ[k] c) • n) =
      ((1 : A) ⊗ₜ[k] c) • tensorLeftBilinear Γ Δ Θ M N s m n := by
  have h := coproductBilinear_equivariant M (tensorLeftSummand Γ Δ Θ M N s) 1
    (Algebra.lsmul k k N ((1 : B) ⊗ₜ[k] c)) LinearMap.id
    (Algebra.lsmul k k s.pt ((1 : A) ⊗ₜ[k] c)) (fun j m n ↦ by
      have h := (s.inj j).hom.map_smul ((1 : A) ⊗ₜ[k] c)
        (bimoduleTensorTmul Γ Δ Θ (M j) N m n)
      rw [tmul_smul_bimoduleTensorTmul] at h
      simpa only [one_smul, LinearMap.id_apply, Algebra.lsmul_apply,
        tensorLeftSummand_apply, ← Algebra.TensorProduct.one_def] using h) m n
  rw [Algebra.lsmul_apply k k N ((1 : B) ⊗ₜ[k] c) n,
    Algebra.lsmul_apply k k s.pt ((1 : A) ⊗ₜ[k] c), LinearMap.id_apply] at h
  rw [one_smul (A ⊗[k] Bᵐᵒᵖ) m] at h
  exact h

private theorem tensorLeftBilinear_degree {p q : ℤ}
    {m : (coproductCofan M).pt} {n : N}
    (hm : m ∈ (coproductCofan M).pt.grading.piece p) (hn : n ∈ N.grading.piece q) :
    tensorLeftBilinear Γ Δ Θ M N s m n ∈ s.pt.grading.piece (p + q) :=
  coproductBilinear_mem M (tensorLeftSummand Γ Δ Θ M N s)
    (fun j {p q} {m n} hm hn ↦ by
      rw [tensorLeftSummand_apply]
      exact map_mem (s.inj j) (bimoduleTensorTmul_mem Γ Δ Θ (M j) N hm hn)) hm hn

private def tensorLeftDesc :
    bimoduleTensorObj Γ Δ Θ (coproductCofan M).pt N ⟶ s.pt :=
  bimoduleTensorLift Γ Δ Θ (tensorLeftBilinear Γ Δ Θ M N s)
    (tensorLeftBilinear_balance Γ Δ Θ M N s)
    (tensorLeftBilinear_left Γ Δ Θ M N s)
    (tensorLeftBilinear_right Γ Δ Θ M N s)
    (fun hm hn ↦ tensorLeftBilinear_degree Γ Δ Θ M N s hm hn)

private theorem tensorLeftDesc_tmul (m : (coproductCofan M).pt) (n : N) :
    (tensorLeftDesc Γ Δ Θ M N s).hom
      (bimoduleTensorTmul Γ Δ Θ (coproductCofan M).pt N m n) =
        tensorLeftBilinear Γ Δ Θ M N s m n :=
  bimoduleTensorLift_tmul Γ Δ Θ (tensorLeftBilinear Γ Δ Θ M N s)
    (tensorLeftBilinear_balance Γ Δ Θ M N s)
    (tensorLeftBilinear_left Γ Δ Θ M N s)
    (tensorLeftBilinear_right Γ Δ Θ M N s)
    (fun hm hn ↦ tensorLeftBilinear_degree Γ Δ Θ M N s hm hn) m n

private abbrev tensorLeftCofan : Cofan fun j ↦ bimoduleTensorObj Γ Δ Θ (M j) N :=
  Cofan.mk (bimoduleTensorObj Γ Δ Θ (coproductCofan M).pt N)
    (fun j ↦ bimoduleTensorMap Γ Δ Θ ((coproductCofan M).inj j) (𝟙 N))

private theorem tensorLeftCofan_inj (j : J) :
    (tensorLeftCofan Γ Δ Θ M N).inj j =
      bimoduleTensorMap Γ Δ Θ ((coproductCofan M).inj j) (𝟙 N) := rfl

private def tensorLeftCofanIsColimit : IsColimit (tensorLeftCofan Γ Δ Θ M N) :=
  (tensorLeftCofan Γ Δ Θ M N).bilinearIsColimit.{w, v} M
    (fun j ↦ tensorBilinear Γ Δ Θ (M j) N)
    (tensorBilinear Γ Δ Θ (coproductCofan M).pt N)
    (fun j m n ↦ by
      rw [tensorLeftCofan_inj, tensorBilinear_apply, tensorBilinear_apply, bimoduleTensorMap_tmul,
        hom_id, LinearMap.id_apply])
    (fun j {P} {f g} h ↦ bimoduleTensor_hom_ext Γ Δ Θ
      (fun m n ↦ by simpa only [tensorBilinear_apply] using h m n))
    (fun {P} {f g} h ↦ bimoduleTensor_hom_ext Γ Δ Θ
      (fun m n ↦ by
        simpa only [tensorBilinear_apply Γ Δ Θ (coproductCofan M).pt N] using h m n))
    (tensorLeftDesc Γ Δ Θ M N)
    (fun s m n ↦ by
      rw [tensorBilinear_apply Γ Δ Θ (coproductCofan M).pt N, tensorLeftDesc_tmul]
      rfl)

/-- Balanced tensor composition preserves coproducts in its left variable. -/
instance : PreservesColimit (Discrete.functor M) ((bimoduleTensor Γ Δ Θ).flip.obj N) :=
  preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit M)
    ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
      (tensorLeftCofanIsColimit Γ Δ Θ M N))

end Left

section Right

variable {J : Type w}
  (M : GradedModuleCat.{max w v} (Γ.tensorProduct Δ.opposite).piece)
  (N : J → GradedModuleCat.{max w v} (Δ.tensorProduct Θ.opposite).piece)
  (s : Cofan fun j ↦ bimoduleTensorObj Γ Δ Θ M (N j))

private def tensorRightSummand (j : J) : N j →ₗ[k] M →ₗ[k] s.pt :=
  ((tensorBilinear Γ Δ Θ M (N j)).compr₂ ((s.inj j).hom.restrictScalars k)).flip

private theorem tensorRightSummand_apply (j : J) (n : N j) (m : M) :
    tensorRightSummand Γ Δ Θ M N s j n m =
      (s.inj j).hom (bimoduleTensorTmul Γ Δ Θ M (N j) m n) := by
  rw [tensorRightSummand, LinearMap.flip_apply, LinearMap.compr₂_apply,
    LinearMap.restrictScalars_apply, tensorBilinear_apply]

private def tensorRightBilinear : M →ₗ[k] (coproductCofan N).pt →ₗ[k] s.pt :=
  (coproductBilinear N (tensorRightSummand Γ Δ Θ M N s)).flip

private theorem tensorRightBilinear_balance (b : B) (m : M) (n : (coproductCofan N).pt) :
    tensorRightBilinear Γ Δ Θ M N s (((1 : A) ⊗ₜ[k] op b) • m) n =
      tensorRightBilinear Γ Δ Θ M N s m ((b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • n) := by
  symm
  apply coproductBilinear_equivariant N (tensorRightSummand Γ Δ Θ M N s)
    (b ⊗ₜ[k] (1 : Cᵐᵒᵖ)) LinearMap.id
    (Algebra.lsmul k k M ((1 : A) ⊗ₜ[k] op b)) LinearMap.id
  intro j n m
  simp only [LinearMap.id_apply, Algebra.lsmul_apply, tensorRightSummand_apply]
  rw [bimoduleTensorTmul_balance]

private theorem tensorRightBilinear_left (a : A) (m : M) (n : (coproductCofan N).pt) :
    tensorRightBilinear Γ Δ Θ M N s ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n =
      (a ⊗ₜ[k] (1 : Cᵐᵒᵖ)) • tensorRightBilinear Γ Δ Θ M N s m n := by
  have h := coproductBilinear_equivariant N (tensorRightSummand Γ Δ Θ M N s) 1
    (Algebra.lsmul k k M (a ⊗ₜ[k] (1 : Bᵐᵒᵖ))) LinearMap.id
    (Algebra.lsmul k k s.pt (a ⊗ₜ[k] (1 : Cᵐᵒᵖ))) (fun j n m ↦ by
      have h := (s.inj j).hom.map_smul (a ⊗ₜ[k] (1 : Cᵐᵒᵖ))
        (bimoduleTensorTmul Γ Δ Θ M (N j) m n)
      rw [tmul_smul_bimoduleTensorTmul] at h
      simpa only [one_smul, LinearMap.id_apply, Algebra.lsmul_apply,
        tensorRightSummand_apply, ← Algebra.TensorProduct.one_def] using h) n m
  rw [Algebra.lsmul_apply k k M (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) m,
    Algebra.lsmul_apply k k s.pt (a ⊗ₜ[k] (1 : Cᵐᵒᵖ)), LinearMap.id_apply] at h
  rw [one_smul (B ⊗[k] Cᵐᵒᵖ) n] at h
  exact h

private theorem tensorRightBilinear_right (c : Cᵐᵒᵖ) (m : M) (n : (coproductCofan N).pt) :
    tensorRightBilinear Γ Δ Θ M N s m (((1 : B) ⊗ₜ[k] c) • n) =
      ((1 : A) ⊗ₜ[k] c) • tensorRightBilinear Γ Δ Θ M N s m n := by
  apply coproductBilinear_equivariant N (tensorRightSummand Γ Δ Θ M N s)
    ((1 : B) ⊗ₜ[k] c) LinearMap.id LinearMap.id
    (Algebra.lsmul k k s.pt ((1 : A) ⊗ₜ[k] c))
  intro j n m
  have h := (s.inj j).hom.map_smul ((1 : A) ⊗ₜ[k] c)
    (bimoduleTensorTmul Γ Δ Θ M (N j) m n)
  rw [tmul_smul_bimoduleTensorTmul] at h
  simpa only [LinearMap.id_apply, Algebra.lsmul_apply, tensorRightSummand_apply,
    ← Algebra.TensorProduct.one_def, one_smul] using h

private theorem tensorRightBilinear_degree {p q : ℤ} {m : M} {n : (coproductCofan N).pt}
    (hm : m ∈ M.grading.piece p) (hn : n ∈ (coproductCofan N).pt.grading.piece q) :
    tensorRightBilinear Γ Δ Θ M N s m n ∈ s.pt.grading.piece (p + q) := by
  rw [tensorRightBilinear,
    LinearMap.flip_apply (coproductBilinear N (tensorRightSummand Γ Δ Θ M N s))]
  simpa only [add_comm] using
    coproductBilinear_mem N (tensorRightSummand Γ Δ Θ M N s)
      (fun j {p q} {n m} hn hm ↦ by
        rw [tensorRightSummand_apply]
        simpa only [add_comm] using map_mem (s.inj j)
          (bimoduleTensorTmul_mem Γ Δ Θ M (N j) (p := q) (q := p) hm hn)) hn hm

private def tensorRightDesc :
    bimoduleTensorObj Γ Δ Θ M (coproductCofan N).pt ⟶ s.pt :=
  bimoduleTensorLift Γ Δ Θ (tensorRightBilinear Γ Δ Θ M N s)
    (tensorRightBilinear_balance Γ Δ Θ M N s)
    (tensorRightBilinear_left Γ Δ Θ M N s)
    (tensorRightBilinear_right Γ Δ Θ M N s)
    (fun hm hn ↦ tensorRightBilinear_degree Γ Δ Θ M N s hm hn)

private theorem tensorRightDesc_tmul (m : M) (n : (coproductCofan N).pt) :
    (tensorRightDesc Γ Δ Θ M N s).hom
      (bimoduleTensorTmul Γ Δ Θ M (coproductCofan N).pt m n) =
        tensorRightBilinear Γ Δ Θ M N s m n :=
  bimoduleTensorLift_tmul Γ Δ Θ (tensorRightBilinear Γ Δ Θ M N s)
    (tensorRightBilinear_balance Γ Δ Θ M N s)
    (tensorRightBilinear_left Γ Δ Θ M N s)
    (tensorRightBilinear_right Γ Δ Θ M N s)
    (fun hm hn ↦ tensorRightBilinear_degree Γ Δ Θ M N s hm hn) m n

private abbrev tensorRightCofan : Cofan fun j ↦ bimoduleTensorObj Γ Δ Θ M (N j) :=
  Cofan.mk (bimoduleTensorObj Γ Δ Θ M (coproductCofan N).pt)
    (fun j ↦ bimoduleTensorMap Γ Δ Θ (𝟙 M) ((coproductCofan N).inj j))

private theorem tensorRightCofan_inj (j : J) :
    (tensorRightCofan Γ Δ Θ M N).inj j =
      bimoduleTensorMap Γ Δ Θ (𝟙 M) ((coproductCofan N).inj j) := rfl

private def tensorRightCofanIsColimit : IsColimit (tensorRightCofan Γ Δ Θ M N) :=
  (tensorRightCofan Γ Δ Θ M N).bilinearIsColimit.{w, v} N
    (fun j ↦ (tensorBilinear Γ Δ Θ M (N j)).flip)
    (tensorBilinear Γ Δ Θ M (coproductCofan N).pt).flip
    (fun j n m ↦ by
      rw [tensorRightCofan_inj, LinearMap.flip_apply, LinearMap.flip_apply, tensorBilinear_apply,
        tensorBilinear_apply, bimoduleTensorMap_tmul, hom_id, LinearMap.id_apply])
    (fun j {P} {f g} h ↦ bimoduleTensor_hom_ext Γ Δ Θ
      (fun m n ↦ by simpa only [LinearMap.flip_apply, tensorBilinear_apply] using h n m))
    (fun {P} {f g} h ↦ bimoduleTensor_hom_ext Γ Δ Θ
      (fun m n ↦ by
        simpa only [LinearMap.flip_apply,
          tensorBilinear_apply Γ Δ Θ M (coproductCofan N).pt] using h n m))
    (tensorRightDesc Γ Δ Θ M N)
    (fun s n m ↦ by
      rw [LinearMap.flip_apply, tensorBilinear_apply Γ Δ Θ M (coproductCofan N).pt,
        tensorRightDesc_tmul]
      rfl)

/-- Balanced tensor composition preserves coproducts in its right variable. -/
instance : PreservesColimit (Discrete.functor N) ((bimoduleTensor Γ Δ Θ).obj M) :=
  preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit N)
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
