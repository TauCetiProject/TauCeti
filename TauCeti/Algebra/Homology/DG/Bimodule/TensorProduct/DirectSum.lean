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
summand. No flatness is needed, and the sum retains finite support. The two factor universes
are independent; the index universe is bounded by the carrier universe of the summed factor,
as required by `tensorMap` on the summand inclusions. In particular, a sum indexed by `ℕ`
can have summands in any carrier universe.

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

universe uR uA uB uC uI uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
  {ι : Type uI}

open BalancedTensorProduct

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
  outerSMulCommClass
attribute [local instance] tensorGradedOuterLeft tensorGradedOuterRight

-- Bundling the additive maps avoids repeating zero and addition cases for each action.
private theorem directSum_ext_on_summands
    (M : ι → DGBimoduleCat.{uR, uA, uB, uM} hA hB)
    {X : Type*} [AddCommGroup X] {f g : directSumObj M → X}
    (hf : ∀ x y, f (x + y) = f x + f y)
    (hg : ∀ x y, g (x + y) = g x + g y)
    (h : ∀ i x, f (directSumι M i x) = g (directSumι M i x))
    (m : directSumObj M) : f m = g m := by
  classical
  apply DFunLike.congr_fun (DirectSum.addHom_ext (f := AddMonoidHom.mk' f hf)
    (g := AddMonoidHom.mk' g hg) ?_) m
  intro i x
  simpa only [AddMonoidHom.mk'_apply, directSumι_apply M] using h i x

section Left

-- `tensorMap` requires each inclusion to stay in one carrier universe.
variable (M : ι → DGBimoduleCat.{uR, uA, uB, max uI uM} hA hB)
  (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC)

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
    refine directSum_ext_on_summands M
      (f := fun m ↦ distributeLeftBilinear M N (op b • m) n)
      (g := fun m ↦ distributeLeftBilinear M N m (b • n))
      (fun x y ↦ ?_) (fun x y ↦ ?_) ?_ m
    · simp [smul_add]
    · simp
    · intro i x
      rw [← map_smul, distributeLeftBilinear_ι, distributeLeftBilinear_ι, balance]
  · intro a m n
    refine directSum_ext_on_summands M
      (f := fun m ↦ distributeLeftBilinear M N (a • m) n)
      (g := fun m ↦ a • distributeLeftBilinear M N m n)
      (fun x y ↦ ?_) (fun x y ↦ ?_) ?_ m
    · simp [smul_add]
    · simp [smul_add]
    · intro i x
      rw [← DGBimoduleHom.map_smul_left, distributeLeftBilinear_ι,
        distributeLeftBilinear_ι, ← smul_tmul_left, DGBimoduleHom.map_smul_left]
  · intro c m n
    refine directSum_ext_on_summands M
      (f := fun m ↦ distributeLeftBilinear M N m (op c • n))
      (g := fun m ↦ op c • distributeLeftBilinear M N m n)
      (fun x y ↦ ?_) (fun x y ↦ ?_) ?_ m
    · simp
    · simp [smul_add]
    · intro i x
      rw [distributeLeftBilinear_ι, distributeLeftBilinear_ι, ← smul_tmul_right, map_smul]
  · intro p m hm n
    -- Expand only homogeneous coordinates, so each summand has the same Koszul sign.
    have hx : ∀ i, m i ∈ (M i).grading p := by
      simpa only [directSumObj_grading, InternalGrading.directSum_piece,
        InternalGrading.mem_directSumPiece_iff, InternalGrading.ofDecomposition_piece] using hm
    rw [← DirectSum.sum_support_of m]
    simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← directSumι_apply]
    simp only [distributeLeftBilinear_ι M N, DGBimoduleHom.map_d,
      tensorObj_differential_tmul (hx i), map_add, map_zsmul_unit]

/-- Tensoring a direct sum in the first variable distributes over its summands. -/
def tensorDirectSumLeft :
    tensorObj (directSumObj M) N ≅ directSumObj (fun i ↦ tensorObj (M i) N) where
  hom := distributeLeftHom M N
  inv := directSumDesc fun i ↦ tensorMap (directSumι M i) (𝟙 N)
  hom_inv_id := by
    classical
    apply tensorObj_hom_ext
    intro m n
    rw [comp_apply, id_apply]
    induction m using DirectSum.induction_on with
    | zero =>
      -- ZeroHomClass is not synthesized here; name the linear map's zero rule
      -- at the morphism level so rewriting need not unfold its function coercion.
      have hz : distributeLeftHom M N 0 = 0 :=
        (distributeLeftHom M N).val.toLinearMap.map_zero
      rw [zero_tmul, hz]
      exact (directSumDesc fun i ↦ tensorMap (directSumι M i) (𝟙 N)).val.toLinearMap.map_zero
    | of i x =>
      rw [← directSumι_apply, distributeLeftHom, tensorLift_tmul,
        distributeLeftBilinear_ι, directSumDesc_ι, tensorMap_tmul, id_apply]
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  inv_hom_id := by
    apply directSum_hom_ext
    intro i z
    rw [comp_apply, id_apply]
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

/-- The forward comparison on a single-coordinate element of the first factor. -/
@[simp↓]
theorem tensorDirectSumLeft_hom_tmul_of [DecidableEq ι] (i : ι) (m : M i) (n : N) :
    (tensorDirectSumLeft M N).hom (tmul R B (DirectSum.of (fun i ↦ M i) i m) n) =
      DirectSum.of (fun i ↦ tensorObj (M i) N) i (tmul R B m n) := by
  rw [← directSumι_apply M, ← directSumι_apply (fun i ↦ tensorObj (M i) N)]
  exact tensorDirectSumLeft_hom_tmul_ι M N i m n

/-- The inverse comparison on a single-coordinate element of the sum of tensors. -/
@[simp↓]
theorem tensorDirectSumLeft_inv_of [DecidableEq ι] (i : ι) (z : tensorObj (M i) N) :
    (tensorDirectSumLeft M N).inv (DirectSum.of (fun i ↦ tensorObj (M i) N) i z) =
      tensorMap (directSumι M i) (𝟙 N) z := by
  rw [← directSumι_apply (fun i ↦ tensorObj (M i) N)]
  exact tensorDirectSumLeft_inv_ι M N i z

end Left

section Right

-- `tensorMap` requires each inclusion to stay in one carrier universe.
variable (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
  (N : ι → DGBimoduleCat.{uR, uB, uC, max uI uN} hB hC)

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

private theorem distributeRightBilinear_balance (b : B) (m : M) (n : directSumObj N) :
    distributeRightBilinear M N (op b • m) n = distributeRightBilinear M N m (b • n) := by
  refine directSum_ext_on_summands N
    (f := fun n ↦ distributeRightBilinear M N (op b • m) n)
    (g := fun n ↦ distributeRightBilinear M N m (b • n))
    (fun x y ↦ ?_) (fun x y ↦ ?_) ?_ n
  · simp only [map_add]
  · simp only [smul_add, map_add]
  · intro i x
    rw [← DGBimoduleHom.map_smul_left, distributeRightBilinear_ι,
      distributeRightBilinear_ι, balance]

private theorem distributeRightBilinear_smul_left (a : A) (m : M) (n : directSumObj N) :
    distributeRightBilinear M N (a • m) n = a • distributeRightBilinear M N m n := by
  refine directSum_ext_on_summands N
    (f := fun n ↦ distributeRightBilinear M N (a • m) n)
    (g := fun n ↦ a • distributeRightBilinear M N m n)
    (fun x y ↦ ?_) (fun x y ↦ ?_) ?_ n
  · simp only [map_add]
  · simp only [map_add, smul_add]
  · intro i x
    rw [distributeRightBilinear_ι, distributeRightBilinear_ι,
      ← smul_tmul_left, DGBimoduleHom.map_smul_left]

private theorem distributeRightBilinear_smul_right (c : C) (m : M) (n : directSumObj N) :
    distributeRightBilinear M N m (op c • n) = op c • distributeRightBilinear M N m n := by
  refine directSum_ext_on_summands N
    (f := fun n ↦ distributeRightBilinear M N m (op c • n))
    (g := fun n ↦ op c • distributeRightBilinear M N m n)
    (fun x y ↦ ?_) (fun x y ↦ ?_) ?_ n
  · simp only [smul_add, map_add]
  · simp only [map_add, smul_add]
  · intro i x
    rw [← map_smul, distributeRightBilinear_ι, distributeRightBilinear_ι,
      ← smul_tmul_right, map_smul]

private def distributeRightHom :
    tensorObj M (directSumObj N) ⟶ directSumObj (fun i ↦ tensorObj M (N i)) := by
  classical
  let f := distributeRightBilinear M N
  refine tensorLift (M := M) (N := directSumObj N)
    (P := directSumObj (fun i ↦ tensorObj M (N i))) f
    (distributeRightBilinear_balance M N) (distributeRightBilinear_smul_left M N)
    (distributeRightBilinear_smul_right M N) (distributeRightBilinear_mem M N) ?_
  intro p m hm n
  induction n using DirectSum.induction_on with
  | zero => simp [f]
  | of i x =>
    rw [← directSumι_apply]
    simp only [f, distributeRightBilinear_ι M N, DGBimoduleHom.map_d,
      tensorObj_differential_tmul hm, map_add, map_zsmul_unit]
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
    rw [comp_apply, id_apply]
    induction n using DirectSum.induction_on with
    | zero =>
      -- ZeroHomClass is not synthesized here; name the linear map's zero rule
      -- at the morphism level so rewriting need not unfold its function coercion.
      have hz : distributeRightHom M N 0 = 0 :=
        (distributeRightHom M N).val.toLinearMap.map_zero
      rw [tmul_zero, hz]
      exact (directSumDesc fun i ↦ tensorMap (𝟙 M) (directSumι N i)).val.toLinearMap.map_zero
    | of i x =>
      rw [← directSumι_apply, distributeRightHom, tensorLift_tmul,
        distributeRightBilinear_ι, directSumDesc_ι, tensorMap_tmul, id_apply]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  inv_hom_id := by
    apply directSum_hom_ext
    intro i z
    rw [comp_apply, id_apply]
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

/-- The forward comparison on a single-coordinate element of the second factor. -/
@[simp↓]
theorem tensorDirectSumRight_hom_tmul_of [DecidableEq ι] (i : ι) (m : M) (n : N i) :
    (tensorDirectSumRight M N).hom (tmul R B m (DirectSum.of (fun i ↦ N i) i n)) =
      DirectSum.of (fun i ↦ tensorObj M (N i)) i (tmul R B m n) := by
  rw [← directSumι_apply N, ← directSumι_apply (fun i ↦ tensorObj M (N i))]
  exact tensorDirectSumRight_hom_tmul_ι M N i m n

/-- The inverse comparison on a single-coordinate element of the sum of tensors. -/
@[simp↓]
theorem tensorDirectSumRight_inv_of [DecidableEq ι] (i : ι) (z : tensorObj M (N i)) :
    (tensorDirectSumRight M N).inv (DirectSum.of (fun i ↦ tensorObj M (N i)) i z) =
      tensorMap (𝟙 M) (directSumι N i) z := by
  rw [← directSumι_apply (fun i ↦ tensorObj M (N i))]
  exact tensorDirectSumRight_inv_ι M N i z

end Right

end TauCeti.DGBimoduleCat
