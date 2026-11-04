/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Category
public import TauCeti.Algebra.Module.GradedModule.DirectSum
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Coproducts of differential graded bimodules

The direct sum of DG `(A, B)`-bimodules has componentwise actions and differential.
An element is homogeneous precisely when every coordinate has the same degree. The
inclusions and the map induced by a family of closed degree-zero bimodule maps make this
sum a coproduct in `DGBimoduleCat`.

In particular, countable sums can assemble tensor powers of a DG bimodule without
replacing their finite-support sum by a product or a completion. No flatness assumptions
are required for this construction; it does not compute derived tensor products.

The grading reuses `InternalGrading.directSum`, and the underlying module maps are
Mathlib's `DirectSum.lof`, `DirectSum.lmap`, and `DirectSum.toModule`.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1, for DG modules and bimodules.
* B. Keller, *Deformed Calabi--Yau completions*, Section 4, for tensor-length sums.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped DirectSum

namespace TauCeti.DGBimoduleCat

universe uR uA uB uM uI

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {ι : Type uI} (M : ι → DGBimoduleCat.{uR, uA, uB, uM} hA hB)

local notation "G" => InternalGrading.directSum
  (fun i ↦ InternalGrading.ofDecomposition
    (DGRightModuleCat.grading (DGBimoduleCat.toDGRightModuleCat (M i))))

private theorem mem_sum_grading (p : ℤ) (x : ⨁ i, M i) :
    x ∈ (G).piece p ↔ ∀ i, x i ∈ (M i).grading p := by
  simp only [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff,
    InternalGrading.ofDecomposition_piece]

/-- The componentwise left action adds degrees in a direct sum of DG bimodules. -/
instance directSumGradedSMulLeft : SetLike.GradedSMul 𝒜 (G).piece where
  smul_mem := by
    intro p q a x ha hx
    exact (mem_sum_grading M _ _).mpr fun i ↦
      SetLike.GradedSMul.smul_mem ha ((mem_sum_grading M _ _).mp hx i)

/-- The componentwise right action adds degrees in a direct sum of DG bimodules. -/
instance directSumGradedSMulRight : SetLike.GradedSMul
    (InternalGrading.ofDecomposition ℬ).opposite.piece (G).piece where
  smul_mem := by
    intro p q b x hb hx
    exact (mem_sum_grading M _ _).mpr fun i ↦
      SetLike.GradedSMul.smul_mem hb ((mem_sum_grading M _ _).mp hx i)

private theorem directSum_isDGBimodule :
    IsDGBimodule hA hB (G).piece (DirectSum.lmap fun i ↦ (M i).differential) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun p x hx ↦
    (mem_sum_grading M _ _).mpr fun i ↦
      (M i).isDGLeftModule.isHomogeneous.map_mem ((mem_sum_grading M _ _).mp hx i)
  sq_zero x := by
    ext i
    simp only [DirectSum.lmap_apply, DirectSum.zero_apply]
    exact (M i).isDGLeftModule.sq_zero (x i)
  leibniz ha x := by
    ext i
    simp only [DirectSum.lmap_apply, DirectSum.add_apply, DirectSum.smul_apply]
    exact (M i).isDGLeftModule.leibniz ha (x i)
  leibniz_right hx b := by
    ext i
    simp only [DirectSum.lmap_apply, DirectSum.add_apply, DirectSum.smul_apply]
    exact (M i).isDGRightModule.leibniz ((mem_sum_grading M _ _).mp hx i) b

/-- The direct sum of DG bimodules, with componentwise actions and differential and
with the direct-sum internal grading. -/
abbrev directSumObj : DGBimoduleCat.{uR, uA, uB, max uI uM} hA hB :=
  of (ℳ := (G).piece) (dM := DirectSum.lmap fun i ↦ (M i).differential)
    (by exact directSum_isDGBimodule M)

/-- The grading of the direct sum is the direct sum of the internal gradings. -/
theorem directSumObj_grading : (directSumObj M).grading = (G).piece := (rfl)

/-- The differential of a direct sum is the componentwise differential. -/
@[simp]
theorem directSumObj_differential_apply (x : directSumObj M) (i : ι) :
    (directSumObj M).differential x i = (M i).differential (x i) := (rfl)

/-- The inclusion of one DG bimodule into their direct sum. -/
def directSumι (i : ι) : DGBimoduleHom (M i).isDGBimodule (directSumObj M).isDGBimodule := by
  letI := Classical.decEq ι
  refine ⟨{ toLinearMap := DirectSum.lof Bᵐᵒᵖ ι (fun i ↦ M i) i
            map_mem' := ?_
            map_d' := ?_ }, ?_⟩
  · intro p x hx
    rw [directSumObj_grading, InternalGrading.directSum_piece]
    exact InternalGrading.lof_mem_directSumPiece
      (fun i ↦ InternalGrading.ofDecomposition (M i).grading) p i
      ⟨x, by simpa only [InternalGrading.ofDecomposition_piece] using hx⟩
  · intro x
    exact DirectSum.lmap_lof (fun i ↦ (M i).differential) i x
  · rw [mem_dgBimoduleHomSubmodule]
    intro a x
    -- `lof` over either scalar ring is definitionally the same single-coordinate map.
    exact map_smul (DirectSum.lof A ι (fun i ↦ M i) i) a x

/-- On elements, the inclusion is the usual finitely supported single-coordinate map. -/
@[simp]
theorem directSumι_apply [inst : DecidableEq ι] (i : ι) (x : M i) :
    directSumι M i x = DirectSum.of (fun i ↦ M i) i x := by
  -- The inclusion stores `lof` with the classical instance; `lof_eq_of` is definitional.
  -- Subsingleton elimination replaces that instance with the caller's instance.
  exact congrArg (fun decEq ↦ @DirectSum.of ι (fun i ↦ M i) _ decEq i x)
    (Subsingleton.elim (Classical.decEq ι) inst)

variable {M}

private def directSumDescLinearMap {N : DGBimoduleCat hA hB}
    (f : ∀ i, DGBimoduleHom (M i).isDGBimodule N.isDGBimodule) :
    (⨁ i, M i) →ₗ[Bᵐᵒᵖ] N := by
  letI := Classical.decEq ι
  exact DirectSum.toModule Bᵐᵒᵖ ι N (fun i ↦ (f i).val.toLinearMap)

private theorem directSumDescLinearMap_of {N : DGBimoduleCat hA hB}
    (f : ∀ i, DGBimoduleHom (M i).isDGBimodule N.isDGBimodule) (i : ι) (x : M i) :
    directSumDescLinearMap f
      (@DirectSum.of ι (fun i ↦ M i) _ (Classical.decEq ι) i x) = f i x := by
  let := Classical.decEq ι
  simpa only [directSumDescLinearMap, DirectSum.lof_eq_of,
    DGRightModuleHom.coe_toLinearMap, DGBimoduleHom.coe_val] using
    (DirectSum.toModule_lof Bᵐᵒᵖ (φ := fun i ↦ (f i).val.toLinearMap) i x)

/-- The closed degree-zero bimodule map induced by maps out of every summand.
The target carrier universe is independent of the summands and the index type. -/
def directSumDesc {N : DGBimoduleCat hA hB}
    (f : ∀ i, DGBimoduleHom (M i).isDGBimodule N.isDGBimodule) :
    DGBimoduleHom (directSumObj M).isDGBimodule N.isDGBimodule := by
  classical
  let F := directSumDescLinearMap f
  refine ⟨{ toLinearMap := F, map_mem' := ?_, map_d' := ?_ }, ?_⟩
  · intro p x hx
    rw [directSumObj_grading, InternalGrading.directSum_piece] at hx
    exact InternalGrading.toModule_mem_of_mem_directSumPiece
      (fun i ↦ InternalGrading.ofDecomposition (M i).grading) N.grading _
      (fun i y hy ↦ Graded.map_mem (f i)
        (by simpa only [InternalGrading.ofDecomposition_piece] using hy)) hx
  · intro x
    have h := DirectSum.addHom_ext
      (f := N.differential.toAddMonoidHom.comp F.toAddMonoidHom)
      (g := F.toAddMonoidHom.comp
        (DirectSum.lmap fun i ↦ (M i).differential).toAddMonoidHom) (fun i y ↦ by
          simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, F,
            DirectSum.lmap_of, directSumDescLinearMap_of]
          exact (f i).map_d y)
    exact DFunLike.congr_fun h x
  · rw [mem_dgBimoduleHomSubmodule]
    intro a x
    have h := DirectSum.addHom_ext
      (f := F.toAddMonoidHom.comp (DistribSMul.toAddMonoidHom (⨁ i, M i) a))
      (g := (DistribSMul.toAddMonoidHom N a).comp F.toAddMonoidHom) (fun i y ↦ by
        simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
          DistribSMul.toAddMonoidHom_apply, ← DirectSum.of_smul, F,
          directSumDescLinearMap_of]
        exact (f i).map_smul_left a y)
    exact DFunLike.congr_fun h x

/-- The induced map evaluates a single-coordinate element using the given component map. -/
@[simp]
theorem directSumDesc_of [inst : DecidableEq ι] {N : DGBimoduleCat hA hB}
    (f : ∀ i, DGBimoduleHom (M i).isDGBimodule N.isDGBimodule) (i : ι) (x : M i) :
    directSumDesc f (DirectSum.of (fun i ↦ M i) i x) = f i x := by
  cases Subsingleton.elim inst (Classical.decEq ι)
  -- The DG morphism stores `directSumDescLinearMap f` as its underlying linear map.
  exact directSumDescLinearMap_of f i x

/-- The induced map has the prescribed value on each summand. -/
@[simp]
theorem directSumDesc_ι {N : DGBimoduleCat hA hB}
    (f : ∀ i, DGBimoduleHom (M i).isDGBimodule N.isDGBimodule) (i : ι) (x : M i) :
    directSumDesc f (directSumι M i x) = f i x := by
  classical
  rw [directSumι_apply, directSumDesc_of]

/-- Maps out of a direct sum are determined by their restrictions to the summands. -/
@[ext]
theorem directSum_hom_ext {N : DGBimoduleCat hA hB}
    {f g : DGBimoduleHom (directSumObj M).isDGBimodule N.isDGBimodule}
    (h : ∀ i x, f (directSumι M i x) = g (directSumι M i x)) : f = g := by
  classical
  have hfg : f.val.toLinearMap = g.val.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    exact h i x
  exact DGBimoduleHom.ext (fun x ↦ DFunLike.congr_fun hfg x)

section Coproduct

variable {κ : Type uM} (N : κ → DGBimoduleCat.{uR, uA, uB, uM} hA hB)

/-- The direct-sum inclusions as a categorical coproduct cocone. The index and carrier
universes agree so the sum stays in the same category of bimodules. The abbreviation
retains the direct-sum carrier as the cocone point. -/
abbrev directSumCofan : Cofan N :=
  Cofan.mk (directSumObj N) (directSumι N)

/-- The coproduct cocone has the componentwise direct sum as its point. -/
@[simp]
theorem directSumCofan_pt : (directSumCofan N).pt = directSumObj N := (rfl)

/-- The legs of the coproduct cocone are the direct-sum inclusions. -/
@[simp]
theorem directSumCofan_inj_apply (i : κ) (x : N i) :
    (directSumCofan N).inj i x = directSumι N i x := (rfl)

/-- The componentwise direct sum is a coproduct of DG bimodules. -/
def directSumCofanIsColimit : IsColimit (directSumCofan N) := by
  refine Cofan.IsColimit.mk _ (fun s ↦ directSumDesc s.inj) ?_ ?_
  · intro s i
    apply hom_ext
    intro x
    simpa only [comp_apply, directSumCofan, cofan_mk_inj] using directSumDesc_ι s.inj i x
  · intro s f hf
    dsimp only [directSumCofan] at f hf ⊢
    apply directSum_hom_ext
    intro i x
    have h := congrArg (fun g : N i ⟶ s.pt ↦ g x) (hf i)
    rw [cofan_mk_inj, comp_apply] at h
    rw [directSumDesc_ι]
    exact h

/-- DG bimodules have coproducts indexed in their carrier universe. -/
instance : HasCoproducts.{uM} (DGBimoduleCat.{uR, uA, uB, uM} hA hB) :=
  hasCoproducts_of_colimit_cofans directSumCofan directSumCofanIsColimit

end Coproduct

end TauCeti.DGBimoduleCat
