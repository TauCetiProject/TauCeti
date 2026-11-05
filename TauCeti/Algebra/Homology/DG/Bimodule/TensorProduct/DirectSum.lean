/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.DirectSum
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Lift

/-!
# Tensor products distribute over direct sums of DG bimodules

Ordinary balanced tensor product commutes with arbitrary direct sums in either variable.
The comparison maps preserve the cohomological grading, both outer actions, and the signed
differential. On a tensor supported in one summand, they simply insert the tensor into that
summand. No flatness is needed, and the sum retains finite support.

These comparisons allow maps on pairs of tensor-length pieces to assemble into multiplication
on a direct sum of tensor powers. They concern ordinary tensor products; computing a derived
tensor algebra additionally requires suitable resolutions.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
* B. Keller, *Deformed Calabi--Yau completions*, Section 4.
-/

public section
noncomputable section

open CategoryTheory MulOpposite
open scoped DirectSum

namespace TauCeti.DGBimoduleCat

universe uR uA uB uC u

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
  {ι : Type u}

open BalancedTensorProduct

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
  outerSMulCommClass
attribute [local instance] tensorGradedOuterLeft tensorGradedOuterRight

section Left

variable (M : ι → DGBimoduleCat.{uR, uA, uB, u} hA hB)
  (N : DGBimoduleCat.{uR, uB, uC, u} hB hC)

private def distributeLeftBilinear :
    directSumObj M →ₗ[R] N →ₗ[R] directSumObj (fun i ↦ tensorObj (M i) N) := by
  classical
  exact DirectSum.toModule R ι _ fun i ↦
    (BalancedTensorProduct.mk R B).compr₂
      ((directSumι (fun i ↦ tensorObj (M i) N) i).val.toLinearMap.restrictScalars R)

@[simp]
private theorem distributeLeftBilinear_ι (i : ι) (m : M i) (n : N) :
    distributeLeftBilinear M N (directSumι M i m) n =
      directSumι (fun i ↦ tensorObj (M i) N) i (tmul R B m n) := by
  classical
  rw [directSumι_apply, ← DirectSum.lof_eq_of R, distributeLeftBilinear,
    DirectSum.toModule_lof]
  simp only [LinearMap.compr₂_apply, BalancedTensorProduct.mk_apply,
    LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap, DGBimoduleHom.coe_val]

private theorem distributeLeftBilinear_mem {p q : ℤ} {m : directSumObj M} {n : N}
    (hm : m ∈ (directSumObj M).grading p) (hn : n ∈ N.grading q) :
    distributeLeftBilinear M N m n ∈
      (directSumObj (fun i ↦ tensorObj (M i) N)).grading (p + q) := by
  classical
  have he : (distributeLeftBilinear M N).flip n = DirectSum.toModule R ι _
      (fun i ↦ ((directSumι (fun i ↦ tensorObj (M i) N) i).val.toLinearMap.restrictScalars R).comp
        ((BalancedTensorProduct.mk R B).flip n)) := by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    simp [distributeLeftBilinear, LinearMap.compr₂_apply]
  rw [← LinearMap.flip_apply, he]
  rw [directSumObj_grading, InternalGrading.directSum_piece] at hm
  exact InternalGrading.toModule_mem_of_mem_directSumPiece
    (fun i ↦ InternalGrading.ofDecomposition (M i).grading) _ _
    (fun i x hx ↦ by
      simpa only [LinearMap.comp_apply, LinearMap.flip_apply, BalancedTensorProduct.mk_apply,
        LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
        DGBimoduleHom.coe_val] using
        Graded.map_mem (directSumι (fun i ↦ tensorObj (M i) N) i)
          (tmul_mem_tensorObj_grading
            (by simpa only [InternalGrading.ofDecomposition_piece] using hx) hn)) hm

private def distributeLeftHom :
    tensorObj (directSumObj M) N ⟶ directSumObj (fun i ↦ tensorObj (M i) N) := by
  classical
  refine tensorLift (distributeLeftBilinear M N) ?_ ?_ ?_
    (fun hm hn ↦ distributeLeftBilinear_mem M N hm hn) ?_
  · intro b m n
    induction m using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [← directSumι_apply, ← map_smul, distributeLeftBilinear_ι,
        distributeLeftBilinear_ι, balance]
    | add x y hx hy => simp only [smul_add, map_add, LinearMap.add_apply, hx, hy]
  · intro a m n
    induction m using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [← directSumι_apply, ← DGBimoduleHom.map_smul_left, distributeLeftBilinear_ι,
        distributeLeftBilinear_ι, ← smul_tmul_left, DGBimoduleHom.map_smul_left]
    | add x y hx hy => simp only [smul_add, map_add, LinearMap.add_apply, hx, hy]
  · intro c m n
    induction m using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [← directSumι_apply, distributeLeftBilinear_ι, distributeLeftBilinear_ι,
        ← smul_tmul_right, map_smul]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]
  · intro p m hm n
    -- Expand only homogeneous coordinates, so each summand has the same Koszul sign.
    have hx : ∀ i, m i ∈ (M i).grading p := by
      simpa only [directSumObj_grading, InternalGrading.directSum_piece,
        InternalGrading.mem_directSumPiece_iff, InternalGrading.ofDecomposition_piece] using hm
    rw [← DFinsupp.sum_single (f := m)]
    simp only [DFinsupp.sum, map_sum, LinearMap.sum_apply, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [DirectSum.single_eq_lof R, DirectSum.lof_eq_of, ← directSumι_apply,
      distributeLeftBilinear_ι, DGBimoduleHom.map_d,
      tensorObj_differential_tmul (hx i), map_add, map_zsmul_unit,
      DGBimoduleHom.map_d (directSumι M i), distributeLeftBilinear_ι,
      distributeLeftBilinear_ι]

/-- Tensoring a direct sum in the first variable distributes over its summands. -/
def tensorDirectSumLeft :
    tensorObj (directSumObj M) N ≅ directSumObj (fun i ↦ tensorObj (M i) N) where
  hom := distributeLeftHom M N
  inv := directSumDesc fun i ↦ tensorMap (directSumι M i) (𝟙 N)
  hom_inv_id := by
    classical
    apply tensorObj_hom_ext
    intro m n
    rw [comp_apply (M := tensorObj (directSumObj M) N)
      (N := directSumObj (fun i ↦ tensorObj (M i) N))
      (P := tensorObj (directSumObj M) N), id_apply]
    induction m using DirectSum.induction_on with
    | zero =>
      rw [zero_tmul]
      exact (congrArg (directSumDesc fun i ↦ tensorMap (directSumι M i) (𝟙 N))
        ((distributeLeftHom M N).val.toLinearMap.map_zero)).trans
          ((directSumDesc fun i ↦ tensorMap (directSumι M i) (𝟙 N)).val.toLinearMap.map_zero)
    | of i x =>
      rw [← directSumι_apply, distributeLeftHom, tensorLift_tmul,
        distributeLeftBilinear_ι, directSumDesc_ι, tensorMap_tmul, id_apply]
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  inv_hom_id := by
    apply directSum_hom_ext
    intro i z
    rw [comp_apply (M := directSumObj (fun i ↦ tensorObj (M i) N))
      (N := tensorObj (directSumObj M) N)
      (P := directSumObj (fun i ↦ tensorObj (M i) N)), id_apply]
    induction z using BalancedTensorProduct.induction_on with
    | ht m n =>
      rw [directSumDesc_ι, tensorMap_tmul, id_apply,
        distributeLeftHom, tensorLift_tmul, distributeLeftBilinear_ι]
    | ha x y hx hy => simp only [map_add, hx, hy]

/-- The forward comparison places a pure tensor in the same summand. -/
@[simp↓]
theorem tensorDirectSumLeft_hom_tmul_ι (i : ι) (m : M i) (n : N) :
    (tensorDirectSumLeft M N).hom (tmul R B (directSumι M i m) n) =
      directSumι (fun i ↦ tensorObj (M i) N) i (tmul R B m n) := by
  dsimp only [tensorDirectSumLeft]
  rw [distributeLeftHom, tensorLift_tmul, distributeLeftBilinear_ι]

/-- The inverse comparison tensors the summand inclusion with the identity. -/
@[simp↓]
theorem tensorDirectSumLeft_inv_ι (i : ι) (z : tensorObj (M i) N) :
    (tensorDirectSumLeft M N).inv (directSumι (fun i ↦ tensorObj (M i) N) i z) =
      tensorMap (directSumι M i) (𝟙 N) z := by
  exact directSumDesc_ι (fun i ↦ tensorMap (directSumι M i) (𝟙 N)) i z

end Left

section Right

variable (M : DGBimoduleCat.{uR, uA, uB, u} hA hB)
  (N : ι → DGBimoduleCat.{uR, uB, uC, u} hB hC)

private def distributeRightBilinear :
    M →ₗ[R] directSumObj N →ₗ[R] directSumObj (fun i ↦ tensorObj M (N i)) := by
  classical
  exact (DirectSum.toModule R ι _ fun i ↦
    (BalancedTensorProduct.mk R B).flip.compr₂
      ((directSumι (fun i ↦ tensorObj M (N i)) i).val.toLinearMap.restrictScalars R)).flip

@[simp]
private theorem distributeRightBilinear_ι (i : ι) (m : M) (n : N i) :
    distributeRightBilinear M N m (directSumι N i n) =
      directSumι (fun i ↦ tensorObj M (N i)) i (tmul R B m n) := by
  classical
  rw [directSumι_apply, ← DirectSum.lof_eq_of R, distributeRightBilinear,
    LinearMap.flip_apply, DirectSum.toModule_lof]
  simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, BalancedTensorProduct.mk_apply,
    LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap, DGBimoduleHom.coe_val]

private theorem distributeRightBilinear_mem {p q : ℤ} {m : M} {n : directSumObj N}
    (hm : m ∈ M.grading p) (hn : n ∈ (directSumObj N).grading q) :
    distributeRightBilinear M N m n ∈
      (directSumObj (fun i ↦ tensorObj M (N i))).grading (p + q) := by
  classical
  have he : distributeRightBilinear M N m = DirectSum.toModule R ι _
      (fun i ↦ ((directSumι (fun i ↦ tensorObj M (N i)) i).val.toLinearMap.restrictScalars R).comp
        (BalancedTensorProduct.mk R B m)) := by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    simp [distributeRightBilinear, LinearMap.compr₂_apply]
  rw [he]
  rw [directSumObj_grading, InternalGrading.directSum_piece] at hn
  exact InternalGrading.toModule_mem_of_mem_directSumPiece
    (fun i ↦ InternalGrading.ofDecomposition (N i).grading) _ _
    (fun i x hx ↦ by
      simpa only [LinearMap.comp_apply, BalancedTensorProduct.mk_apply,
        LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
        DGBimoduleHom.coe_val] using
        Graded.map_mem (directSumι (fun i ↦ tensorObj M (N i)) i)
          (tmul_mem_tensorObj_grading hm
            (by simpa only [InternalGrading.ofDecomposition_piece] using hx))) hn

private def distributeRightHom :
    tensorObj M (directSumObj N) ⟶ directSumObj (fun i ↦ tensorObj M (N i)) := by
  classical
  refine tensorLift (distributeRightBilinear M N) ?_ ?_ ?_
    (fun hm hn ↦ distributeRightBilinear_mem M N hm hn) ?_
  · intro b m n
    induction n using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [← directSumι_apply, ← DGBimoduleHom.map_smul_left, distributeRightBilinear_ι,
        distributeRightBilinear_ι, balance]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  · intro a m n
    induction n using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [← directSumι_apply, distributeRightBilinear_ι, distributeRightBilinear_ι,
        ← smul_tmul_left, DGBimoduleHom.map_smul_left]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  · intro c m n
    induction n using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [← directSumι_apply, ← map_smul, distributeRightBilinear_ι,
        distributeRightBilinear_ι, ← smul_tmul_right, map_smul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  · intro p m hm n
    induction n using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [← directSumι_apply, distributeRightBilinear_ι, DGBimoduleHom.map_d,
        tensorObj_differential_tmul hm, map_add, map_zsmul_unit,
        DGBimoduleHom.map_d (directSumι N i), distributeRightBilinear_ι,
        distributeRightBilinear_ι]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]; abel

/-- Tensoring a direct sum in the second variable distributes over its summands. -/
def tensorDirectSumRight :
    tensorObj M (directSumObj N) ≅ directSumObj (fun i ↦ tensorObj M (N i)) where
  hom := distributeRightHom M N
  inv := directSumDesc fun i ↦ tensorMap (𝟙 M) (directSumι N i)
  hom_inv_id := by
    classical
    apply tensorObj_hom_ext
    intro m n
    rw [comp_apply (M := tensorObj M (directSumObj N))
      (N := directSumObj (fun i ↦ tensorObj M (N i)))
      (P := tensorObj M (directSumObj N)), id_apply]
    induction n using DirectSum.induction_on with
    | zero =>
      rw [tmul_zero]
      exact (congrArg (directSumDesc fun i ↦ tensorMap (𝟙 M) (directSumι N i))
        ((distributeRightHom M N).val.toLinearMap.map_zero)).trans
          ((directSumDesc fun i ↦ tensorMap (𝟙 M) (directSumι N i)).val.toLinearMap.map_zero)
    | of i x =>
      rw [← directSumι_apply, distributeRightHom, tensorLift_tmul,
        distributeRightBilinear_ι, directSumDesc_ι, tensorMap_tmul, id_apply]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  inv_hom_id := by
    apply directSum_hom_ext
    intro i z
    rw [comp_apply (M := directSumObj (fun i ↦ tensorObj M (N i)))
      (N := tensorObj M (directSumObj N))
      (P := directSumObj (fun i ↦ tensorObj M (N i))), id_apply]
    induction z using BalancedTensorProduct.induction_on with
    | ht m n =>
      rw [directSumDesc_ι, tensorMap_tmul, id_apply,
        distributeRightHom, tensorLift_tmul, distributeRightBilinear_ι]
    | ha x y hx hy => simp only [map_add, hx, hy]

/-- The forward comparison places a pure tensor in the same summand. -/
@[simp↓]
theorem tensorDirectSumRight_hom_tmul_ι (i : ι) (m : M) (n : N i) :
    (tensorDirectSumRight M N).hom (tmul R B m (directSumι N i n)) =
      directSumι (fun i ↦ tensorObj M (N i)) i (tmul R B m n) := by
  dsimp only [tensorDirectSumRight]
  rw [distributeRightHom, tensorLift_tmul, distributeRightBilinear_ι]

/-- The inverse comparison tensors the identity with the summand inclusion. -/
@[simp↓]
theorem tensorDirectSumRight_inv_ι (i : ι) (z : tensorObj M (N i)) :
    (tensorDirectSumRight M N).inv (directSumι (fun i ↦ tensorObj M (N i)) i z) =
      tensorMap (𝟙 M) (directSumι N i) z := by
  exact directSumDesc_ι (fun i ↦ tensorMap (𝟙 M) (directSumι N i)) i z

end Right

end TauCeti.DGBimoduleCat
