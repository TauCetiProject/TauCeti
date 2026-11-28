/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic

/-!
# Balanced tensor products over a commutative semiring

If `A` is commutative and its right action on `M` agrees with its left action, then under
compatible ground-ring actions `BalancedTensorProduct.tensorProductEquiv` identifies the
balanced tensor product with Mathlib's `M ⊗[A] N` by an `R`-linear equivalence natural in both
factors. Taking `A = R` compares the two constructions of the tensor product over the same ring.

The comparison uses Mathlib's `TensorProduct.mapOfCompatibleSMul` and `TensorProduct.liftAddHom`.
The description of the ring tensor product by the balancing relations is in Mac Lane,
*Categories for the Working Mathematician*, §IX.6.
-/

public section

namespace TauCeti.BalancedTensorProduct

open scoped TensorProduct

attribute [local instance] SMulCommClass.symm

variable {R A M N : Type*} [CommRing R] [CommSemiring A]
  [AddCommGroup M] [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsCentralScalar A M]
  [SMulCommClass A R M] [AddCommGroup N] [Module R N] [Module A N]
  [TensorProduct.CompatibleSMul A R M N]

private theorem relations_le_ker :
    balancedTensorRelations R A M N ≤ (TensorProduct.mapOfCompatibleSMul A R R M N).ker := by
  rw [balancedTensorRelations_def, Submodule.span_le]
  rintro _ ⟨a, m, n, rfl⟩
  simp [LinearMap.mem_ker, TensorProduct.smul_tmul]

private def fromTensorProduct : M ⊗[A] N →ₗ[R] BalancedTensorProduct R A M N where
  __ := TensorProduct.liftAddHom
    (LinearMap.toAddMonoidHom'.comp (mk R A (M := M) (N := N)).toAddMonoidHom)
    (fun a m n ↦ by simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom'_apply,
      LinearMap.toAddMonoidHom_coe, mk_apply, op_smul_eq_smul] using balance R A a m n)
  map_smul' r z := by
    refine z.inductionOn (fun m n ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [TensorProduct.smul_tmul']
    · simp_all [smul_add]

omit [TensorProduct.CompatibleSMul A R M N] in
private theorem fromTensorProduct_tmul (m : M) (n : N) :
    fromTensorProduct (R := R) (m ⊗ₜ[A] n) = tmul R A m n := by
  simp [fromTensorProduct]

variable (R A M N) in
/-- The balanced tensor product over a commutative semiring is the ordinary tensor product
over that semiring, with its compatible ground-ring action on the first factor. -/
def tensorProductEquiv : BalancedTensorProduct R A M N ≃ₗ[R] M ⊗[A] N := by
  let f := TensorProduct.mapOfCompatibleSMul A R R M N
  let q : BalancedTensorProduct R A M N →ₗ[R] M ⊗[A] N :=
    (balancedTensorRelations R A M N).liftQ f relations_le_ker
  have hcomp : q.comp (mkQ R A) = f := by
    rw [mkQ_def]
    exact Submodule.liftQ_mkQ (balancedTensorRelations R A M N) f relations_le_ker
  have hq (m : M) (n : N) : q (tmul R A m n) = m ⊗ₜ[A] n := by
    rw [← mkQ_tmul, ← LinearMap.comp_apply, hcomp, TensorProduct.mapOfCompatibleSMul_tmul]
  have hleft : fromTensorProduct.comp q = LinearMap.id :=
    hom_ext fun m n ↦ by
      simp only [LinearMap.comp_apply, hq, fromTensorProduct_tmul, LinearMap.id_apply]
  have hsurj : Function.Surjective q := by
    apply Function.Surjective.of_comp (g := mkQ R A)
    rw [← LinearMap.coe_comp, hcomp]
    exact TensorProduct.mapOfCompatibleSMul_surjective A R R M N
  exact LinearEquiv.ofLinearMap q fromTensorProduct
    (LinearMap.ext fun z ↦ by
      obtain ⟨x, rfl⟩ := hsurj z
      simpa using congrArg q (LinearMap.congr_fun hleft x)) hleft

/-- The change-of-scalars map factors through the quotient by the balancing relations. -/
theorem tensorProductEquiv_comp_mkQ :
    (tensorProductEquiv R A M N).toLinearMap ∘ₗ mkQ R A =
      TensorProduct.mapOfCompatibleSMul A R R M N := by
  rw [mkQ_def]
  exact Submodule.liftQ_mkQ (balancedTensorRelations R A M N)
    (TensorProduct.mapOfCompatibleSMul A R R M N) relations_le_ker

/-- The comparison sends a balanced pure tensor to the corresponding ordinary pure tensor. -/
@[simp]
theorem tensorProductEquiv_tmul (m : M) (n : N) :
    tensorProductEquiv R A M N (tmul R A m n) = m ⊗ₜ[A] n := by
  rw [← mkQ_tmul]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.mapOfCompatibleSMul_tmul] using
    LinearMap.congr_fun (tensorProductEquiv_comp_mkQ (R := R) (A := A)) (m ⊗ₜ[R] n)

/-- The inverse comparison sends an ordinary pure tensor to the corresponding balanced one. -/
@[simp]
theorem tensorProductEquiv_symm_tmul (m : M) (n : N) :
    (tensorProductEquiv R A M N).symm (m ⊗ₜ[A] n) = tmul R A m n := by
  rw [LinearEquiv.symm_apply_eq, tensorProductEquiv_tmul]

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M'] [Module A M'] [Module Aᵐᵒᵖ M'] [IsCentralScalar A M']
  [SMulCommClass A R M'] [AddCommGroup N'] [Module R N'] [Module A N']
  [TensorProduct.CompatibleSMul A R M' N']

private theorem tensorProductEquiv_map_of_coe_eq
    (fR : M →ₗ[R] M') (gR : N →ₗ[R] N')
    (hf : ∀ (a : A) m, fR (MulOpposite.op a • m) = MulOpposite.op a • fR m)
    (hg : ∀ (a : A) n, gR (a • n) = a • gR n)
    (f : M →ₗ[A] M') (g : N →ₗ[A] N') (hfR : (fR : M → M') = f) (hgR : (gR : N → N') = g)
    (z : BalancedTensorProduct R A M N) :
    tensorProductEquiv R A M' N' (map fR gR hf hg z) =
      TensorProduct.map f g (tensorProductEquiv R A M N z) := by
  let tensorMap : M ⊗[A] N →ₗ[R] M' ⊗[A] N' :=
    { __ := TensorProduct.map f g
      map_smul' := fun r w ↦ by
        refine w.inductionOn (fun m n ↦ ?_) (fun x y hx hy ↦ ?_)
        · simp [TensorProduct.smul_tmul', ← hfR]
        · simp_all [smul_add] }
  have h : (tensorProductEquiv R A M' N').toLinearMap ∘ₗ map fR gR hf hg =
      tensorMap ∘ₗ (tensorProductEquiv R A M N).toLinearMap :=
    hom_ext fun _ _ ↦ by simp [tensorMap, hfR, hgR]
  exact LinearMap.congr_fun h z

variable
  [LinearMap.CompatibleSMul M M' R A] [LinearMap.CompatibleSMul N N' R A]

/-- The commutative comparison intertwines the maps induced by linear maps in both factors. -/
@[simp]
theorem tensorProductEquiv_map (f : M →ₗ[A] M') (g : N →ₗ[A] N')
    (z : BalancedTensorProduct R A M N) :
    tensorProductEquiv R A M' N'
        (map (f.restrictScalars R) (g.restrictScalars R)
          (fun a m ↦ by
            rw [LinearMap.coe_restrictScalars]
            simp only [op_smul_eq_smul, map_smul])
          (fun a n ↦ by
            rw [LinearMap.coe_restrictScalars, map_smul]) z) =
      TensorProduct.map f g (tensorProductEquiv R A M N z) :=
  tensorProductEquiv_map_of_coe_eq _ _ _ _ f g
    (LinearMap.coe_restrictScalars R f) (LinearMap.coe_restrictScalars R g) z

/-- The maps induced on the balanced and ordinary tensor products commute with the comparison
as a square of ground-ring linear maps. -/
theorem tensorProductEquiv_comp_map [LinearMap.CompatibleSMul (M ⊗[A] N) (M' ⊗[A] N') R A]
    (f : M →ₗ[A] M') (g : N →ₗ[A] N') :
    (tensorProductEquiv R A M' N').toLinearMap ∘ₗ
        map (f.restrictScalars R) (g.restrictScalars R)
          (fun a m ↦ by
            rw [LinearMap.coe_restrictScalars]
            simp only [op_smul_eq_smul, map_smul])
          (fun a n ↦ by
            rw [LinearMap.coe_restrictScalars, map_smul]) =
      (TensorProduct.map f g).restrictScalars R ∘ₗ (tensorProductEquiv R A M N).toLinearMap :=
  LinearMap.ext (tensorProductEquiv_map f g)

/-- The inverse comparison intertwines the maps induced by linear maps in both factors. -/
@[simp]
theorem tensorProductEquiv_symm_map (f : M →ₗ[A] M') (g : N →ₗ[A] N')
    (w : M ⊗[A] N) :
    (tensorProductEquiv R A M' N').symm (TensorProduct.map f g w) =
      map (f.restrictScalars R) (g.restrictScalars R)
        (fun a m ↦ by
          rw [LinearMap.coe_restrictScalars]
          simp only [op_smul_eq_smul, map_smul])
        (fun a n ↦ by
          rw [LinearMap.coe_restrictScalars, map_smul])
        ((tensorProductEquiv R A M N).symm w) := by
  rw [LinearEquiv.symm_apply_eq, tensorProductEquiv_map, LinearEquiv.apply_symm_apply]

/-- Naturality when the map on the left factor is the identity. -/
@[simp]
theorem tensorProductEquiv_map_id_left [TensorProduct.CompatibleSMul A R M N']
    (g : N →ₗ[A] N') (z : BalancedTensorProduct R A M N) :
    tensorProductEquiv R A M N'
        (map LinearMap.id (g.restrictScalars R) (fun _ _ ↦ rfl)
          (fun a n ↦ by
            rw [LinearMap.coe_restrictScalars, map_smul]) z) =
      TensorProduct.map LinearMap.id g (tensorProductEquiv R A M N z) :=
  tensorProductEquiv_map_of_coe_eq _ _ _ _ LinearMap.id g rfl (LinearMap.coe_restrictScalars R g) z

/-- Naturality when the map on the right factor is the identity. -/
@[simp]
theorem tensorProductEquiv_map_id_right [TensorProduct.CompatibleSMul A R M' N]
    (f : M →ₗ[A] M') (z : BalancedTensorProduct R A M N) :
    tensorProductEquiv R A M' N
        (map (f.restrictScalars R) LinearMap.id
          (fun a m ↦ by
            rw [LinearMap.coe_restrictScalars]
            simp only [op_smul_eq_smul, map_smul])
          (fun _ _ ↦ rfl) z) =
      TensorProduct.map f LinearMap.id (tensorProductEquiv R A M N z) :=
  tensorProductEquiv_map_of_coe_eq _ _ _ _ f LinearMap.id (LinearMap.coe_restrictScalars R f) rfl z

section LTensor

variable [Module R A] [IsScalarTower R A N] [IsScalarTower R A N']
  [TensorProduct.CompatibleSMul A R M N']

/-- The comparison commutes with tensoring a linear map on the left with a fixed module. -/
@[simp]
theorem tensorProductEquiv_lTensor (g : N →ₗ[A] N') (z : BalancedTensorProduct R A M N) :
    tensorProductEquiv R A M N' (lTensor R M g z) =
      g.lTensor M (tensorProductEquiv R A M N z) := by
  have h : lTensor R M g =
      map LinearMap.id (g.restrictScalars R) (fun _ _ ↦ rfl) (fun a n ↦ by
        rw [LinearMap.coe_restrictScalars, map_smul]) :=
    hom_ext fun _ _ ↦ by simp
  rw [h, LinearMap.lTensor_def, tensorProductEquiv_map_id_left]

/-- The inverse comparison commutes with tensoring a linear map on the left. -/
@[simp]
theorem tensorProductEquiv_symm_lTensor (g : N →ₗ[A] N') (w : M ⊗[A] N) :
    (tensorProductEquiv R A M N').symm (g.lTensor M w) =
      lTensor R M g ((tensorProductEquiv R A M N).symm w) := by
  rw [LinearEquiv.symm_apply_eq, tensorProductEquiv_lTensor, LinearEquiv.apply_symm_apply]

end LTensor

section SameRing

variable {S X Y X' Y' : Type*} [CommRing S]
  [AddCommGroup X] [Module S X] [Module Sᵐᵒᵖ X] [IsCentralScalar S X]
  [AddCommGroup X'] [Module S X'] [Module Sᵐᵒᵖ X'] [IsCentralScalar S X']
  [AddCommGroup Y] [Module S Y] [AddCommGroup Y'] [Module S Y']

/-- Naturality when the ground ring and the balancing ring coincide. -/
@[simp]
theorem tensorProductEquiv_map_sameRing (f : X →ₗ[S] X') (g : Y →ₗ[S] Y')
    (z : BalancedTensorProduct S S X Y) :
    tensorProductEquiv S S X' Y'
        (map f g (fun a x ↦ by simp only [op_smul_eq_smul, map_smul]) g.map_smul z) =
      TensorProduct.map f g (tensorProductEquiv S S X Y z) := by
  simpa only [LinearMap.restrictScalars_self] using tensorProductEquiv_map f g z

end SameRing

end TauCeti.BalancedTensorProduct
