/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import TauCeti.Algebra.Homology.DG.Bimodule.Category
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Basic

/-!
# Functorial tensor products of DG bimodules

The balanced tensor product defines a bifunctor from DG `(A, B)`-bimodules and DG
`(B, C)`-bimodules to DG `(A, C)`-bimodules. On morphisms it sends a pure tensor
`m ⊗ n` to `f(m) ⊗ g(n)`, retaining both outer actions and the signed differential.
It is linear separately in each variable. This is the tensor operation used to
iterate bimodules and to compose their actions on modules.

The carrier, grading, outer actions and differential are the existing balanced tensor
constructions. These are ordinary tensor products; derived tensor products additionally
require suitable resolutions. The module carriers may live in independent universes.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGBimoduleCat

universe uR uA uB uC uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}

open BalancedTensorProduct

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
  outerSMulCommClass

attribute [local instance] tensorGradedOuterLeft tensorGradedOuterRight

/-- The ordinary tensor product of two DG bimodules. The abbreviation retains the
balanced tensor carrier and its outer actions. -/
abbrev tensorObj (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    DGBimoduleCat.{uR, uA, uC, max uM uN} hA hC :=
  of (isDGBimodule_tensorProduct M.isDGBimodule N.isDGBimodule)

variable {M M' M'' : DGBimoduleCat.{uR, uA, uB, uM} hA hB}
  {N N' N'' : DGBimoduleCat.{uR, uB, uC, uN} hB hC}

/-- The differential on a homogeneous pure tensor has the usual Koszul sign. -/
theorem tensorObj_differential_tmul {p : ℤ} {m : M} (hm : m ∈ M.grading p) (n : N) :
    (tensorObj M N).differential (tmul R B m n) =
      tmul R B (M.differential m) n + p.negOnePow • tmul R B m (N.differential n) := by
  simpa only [Units.smul_def, Int.cast_smul_eq_zsmul] using
    differential_tmul_of_mem M.isDGRightModule N.isDGLeftModule hm n

/-- Morphisms out of a tensor product are determined by their values on pure tensors. -/
@[ext]
theorem tensorObj_hom_ext {P : DGBimoduleCat hA hC} {f g : tensorObj M N ⟶ P}
    (h : ∀ m n, f (tmul R B m n) = g (tmul R B m n)) : f = g := by
  apply hom_ext
  intro z
  induction z using BalancedTensorProduct.induction_on with
  | ht m n => exact h m n
  | ha x y hx hy => simp only [map_add, hx, hy]

-- Transport the graded actions to the internal gradings used by balanced tensors.
local instance (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece
      (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    SetLike.GradedSMul ℬ (InternalGrading.ofDecomposition N.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- A pure tensor of homogeneous elements has the sum of their degrees. -/
theorem tmul_mem_tensorObj_grading {p q : ℤ} {m : M} {n : N}
    (hm : m ∈ M.grading p) (hn : n ∈ N.grading q) :
    tmul R B m n ∈ (tensorObj M N).grading (p + q) :=
  tmul_mem_grading (𝒜 := ℬ) (InternalGrading.ofDecomposition M.grading)
    (InternalGrading.ofDecomposition N.grading)
    (by simpa only [InternalGrading.ofDecomposition_piece] using hm)
    (by simpa only [InternalGrading.ofDecomposition_piece] using hn)

/-- Tensoring degree-zero closed bimodule morphisms preserves both outer actions,
the grading and the differential. -/
def tensorMap (f : M ⟶ M') (g : N ⟶ N') : tensorObj M N ⟶ tensorObj M' N' := by
  -- Retain the existing balanced map, adding its two outer equivariance laws.
  let F := f.val.toLinearMap.restrictScalars R
  let G := g.val.toLinearMap.restrictScalars R
  have hf : ∀ (b : B) m, F (op b • m) = op b • F m := by
    intro b m
    simpa only [F, LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
      DGBimoduleHom.coe_val] using map_smul f (op b) m
  have hg : ∀ (b : B) n, G (b • n) = b • G n := by
    intro b n
    simpa only [G, LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
      DGBimoduleHom.coe_val] using map_smul_left g b n
  have hf₀ : LinearMap.IsHomogeneous F M.grading M'.grading 0 :=
    LinearMap.isHomogeneous_def.mpr fun _ _ hx => by
      simpa only [F, LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
        DGBimoduleHom.coe_val, add_zero] using Graded.map_mem f hx
  have hg₀ : LinearMap.IsHomogeneous G N.grading N'.grading 0 :=
    LinearMap.isHomogeneous_def.mpr fun _ _ hx => by
      simpa only [G, LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
        DGBimoduleHom.coe_val, add_zero] using Graded.map_mem g hx
  let T : tensorObj M N →ₗ[Cᵐᵒᵖ] tensorObj M' N' := {
    toFun := BalancedTensorProduct.map F G hf hg
    map_add' := map_add _
    map_smul' := fun c z =>
      map_smul_right Cᵐᵒᵖ F G hf hg (fun c n => map_smul g c n) c z }
  have hT (z) : T z = BalancedTensorProduct.map F G hf hg z := rfl
  -- Grade preservation and differential compatibility come from the carrier-level API.
  refine ⟨{ toLinearMap := T, map_mem' := ?_, map_d' := ?_ }, ?_⟩
  · intro p z hz
    rw [hT]
    have hf' : LinearMap.IsHomogeneous F
        (InternalGrading.ofDecomposition M.grading).piece
        (InternalGrading.ofDecomposition M'.grading).piece 0 := by
      simpa only [InternalGrading.ofDecomposition_piece] using hf₀
    have hg' : LinearMap.IsHomogeneous G
        (InternalGrading.ofDecomposition N.grading).piece
        (InternalGrading.ofDecomposition N'.grading).piece 0 := by
      simpa only [InternalGrading.ofDecomposition_piece] using hg₀
    simpa only [add_zero] using
      (isHomogeneous_map (𝒜 := ℬ) _ _ _ _ F G hf hg hf' hg').map_mem hz
  · intro z
    rw [hT, hT]
    exact LinearMap.congr_fun
      (differential_naturality M.isDGRightModule N.isDGLeftModule
        M'.isDGRightModule N'.isDGLeftModule F G hf hg hf₀
        (LinearMap.ext fun x => map_d f x) (LinearMap.ext fun x => map_d g x)) z
  · rw [mem_dgBimoduleHomSubmodule]
    intro a z
    rw [DGRightModuleHom.coe_mk, hT, hT]
    exact BalancedTensorProduct.map_smul_left A F G hf hg (fun a m => map_smul_left f a m) a z

/-- Tensor morphisms act factor by factor, with no sign since both maps have degree zero.
This runs before simplification of the bundled carriers, which would prevent matching. -/
@[simp↓]
theorem tensorMap_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    tensorMap f g (tmul R B m n) = tmul R B (f m) (g n) := by
  rw [← DGBimoduleHom.coe_val]
  simp only [tensorMap, DGRightModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    BalancedTensorProduct.map_tmul, LinearMap.restrictScalars_apply,
    DGRightModuleHom.coe_toLinearMap, DGBimoduleHom.coe_val]

/-- Tensoring identity morphisms gives the identity. -/
@[simp]
theorem tensorMap_id (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    tensorMap (𝟙 M) (𝟙 N) = 𝟙 (tensorObj M N) := by
  apply tensorObj_hom_ext
  intro m n
  rw [id_apply]
  simp

/-- Tensoring preserves simultaneous composition in the two factors. -/
@[simp]
theorem tensorMap_comp (f : M ⟶ M') (g : N ⟶ N') (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    tensorMap (f ≫ f') (g ≫ g') = tensorMap f g ≫ tensorMap f' g' := by
  apply tensorObj_hom_ext
  intro m n
  rw [comp_apply, tensorMap_tmul, tensorMap_tmul, tensorMap_tmul,
    comp_apply, comp_apply]

/-- Tensor morphisms are additive in the first factor. -/
@[simp]
theorem tensorMap_add_left (f f' : M ⟶ M') (g : N ⟶ N') :
    tensorMap (f + f') g = tensorMap f g + tensorMap f' g := by
  apply tensorObj_hom_ext
  intro m n
  rw [add_apply]
  simp [add_tmul]

/-- Tensor morphisms are additive in the second factor. -/
@[simp]
theorem tensorMap_add_right (f : M ⟶ M') (g g' : N ⟶ N') :
    tensorMap f (g + g') = tensorMap f g + tensorMap f g' := by
  apply tensorObj_hom_ext
  intro m n
  rw [add_apply]
  simp [tmul_add]

/-- Tensor morphisms respect ground-ring scaling in the first factor. -/
@[simp]
theorem tensorMap_smul_left (r : R) (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap (r • f) g = r • tensorMap f g := by
  apply tensorObj_hom_ext
  intro m n
  rw [smul_apply]
  simp [smul_tmul]

/-- Tensor morphisms respect ground-ring scaling in the second factor. -/
@[simp]
theorem tensorMap_smul_right (r : R) (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap f (r • g) = r • tensorMap f g := by
  apply tensorObj_hom_ext
  intro m n
  rw [smul_apply]
  simp [tmul_smul]

/-- Tensoring a zero map in the first factor gives zero. -/
@[simp]
theorem tensorMap_zero_left (g : N ⟶ N') : tensorMap (0 : M ⟶ M') g = 0 := by
  simpa only [zero_smul] using tensorMap_smul_left (0 : R) (0 : M ⟶ M') g

/-- Tensoring a zero map in the second factor gives zero. -/
@[simp]
theorem tensorMap_zero_right (f : M ⟶ M') : tensorMap f (0 : N ⟶ N') = 0 := by
  simpa only [zero_smul] using tensorMap_smul_right (0 : R) f (0 : N ⟶ N')

/-- The ordinary balanced tensor product as a bifunctor on DG bimodules.
The abbreviation keeps its object maps definitionally equal to `tensorObj`, so that
its morphisms act on the balanced carriers without transports. -/
abbrev tensorFunctor :
    DGBimoduleCat.{uR, uA, uB, uM} hA hB ⥤
      DGBimoduleCat.{uR, uB, uC, uN} hB hC ⥤
        DGBimoduleCat.{uR, uA, uC, max uM uN} hA hC where
  obj M :=
    { obj := tensorObj M
      map := fun g => tensorMap (𝟙 M) g
      map_id := fun N => tensorMap_id M N
      map_comp := fun g g' => by simpa using tensorMap_comp (𝟙 M) g (𝟙 M) g' }
  map f :=
    { app := fun N => tensorMap f (𝟙 N)
      naturality := fun N N' g => by
        rw [← tensorMap_comp, ← tensorMap_comp]
        simp }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact tensorMap_id M N
  map_comp f f' := by
    apply NatTrans.ext
    funext N
    simpa using tensorMap_comp f (𝟙 N) f' (𝟙 N)

@[simp]
theorem tensorFunctor_obj_obj (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    (tensorFunctor.obj M).obj N = tensorObj M N := (rfl)

@[simp]
theorem tensorFunctor_obj_map (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (g : N ⟶ N') :
    (tensorFunctor.obj M).map g = tensorMap (𝟙 M) g := (rfl)

@[simp]
theorem tensorFunctor_map_app (f : M ⟶ M') (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    (tensorFunctor.map f).app N = tensorMap f (𝟙 N) := (rfl)

instance (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    ((tensorFunctor (hC := hC)).obj M).Additive where
  map_add := by intros; unfold tensorFunctor; exact tensorMap_add_right _ _ _

instance (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    ((tensorFunctor (hC := hC)).obj M).Linear R where
  map_smul := by intros; unfold tensorFunctor; exact tensorMap_smul_right _ _ _

instance : (tensorFunctor.{uR, uA, uB, uC, uM, uN}
    (hA := hA) (hB := hB) (hC := hC)).Additive where
  map_add := by
    intros
    apply NatTrans.ext
    funext N
    unfold tensorFunctor
    exact tensorMap_add_left _ _ _

instance : (tensorFunctor.{uR, uA, uB, uC, uM, uN}
    (hA := hA) (hB := hB) (hC := hC)).Linear R where
  map_smul := by
    intros
    apply NatTrans.ext
    funext N
    unfold tensorFunctor
    exact tensorMap_smul_left _ _ _

end TauCeti.DGBimoduleCat
