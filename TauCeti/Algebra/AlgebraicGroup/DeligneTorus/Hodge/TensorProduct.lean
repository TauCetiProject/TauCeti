/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Hodge
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic

/-!
# Hodge components of a tensor product of representations of the Deligne torus

For real representations `V` and `W` of the Deligne torus `S`, the tensor product `V ⊗[ℝ] W` is a
representation through the diagonal coaction (`TauCeti.Comodule.tensor`). Under the canonical
identification `ℂ ⊗[ℝ] (V ⊗[ℝ] W) ≃ (ℂ ⊗[ℝ] V) ⊗[ℂ] (ℂ ⊗[ℝ] W)`, Hodge types add:

```text
(V ⊗ W)^{p,q} = ⨆_{a + c = p, b + d = q} V^{a,b} ⊗ W^{c,d},
```

where `V^{a,b} ⊗ W^{c,d}` denotes the image of the tensor product of the two subspaces.

The inclusion of each summand is a computation with the universal point of `𝔾ₘ × 𝔾ₘ`, which acts
on the tensor product through its actions on the factors (`TauCeti.Comodule.endOfPoint_tensor`).
Equality follows because the right-hand sides are the pieces of the tensor product of the Hodge
gradings of `ℂ ⊗[ℝ] V` and `ℂ ⊗[ℝ] W` (`TauCeti.InternalGrading.tensorProduct`), which span the
whole space, while the Hodge components of `V ⊗ W` are independent.

## Main results

* `TauCeti.DeligneTorus.distribBaseChange_symm_tmul_mem_hodgeComponent`: the tensor product of a
  vector of type `(p, q)` and a vector of type `(p', q')` has type `(p + p', q + q')`.
* `TauCeti.DeligneTorus.hodgeComponent_tensor`: `(V ⊗ W)^{p,q}` is the sum of the images of the
  `V^{a,b} ⊗ W^{p-a,q-b}`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27.
-/

public section

open WithConv TauCeti.Algebra
open scoped TensorProduct

namespace TauCeti.DeligneTorus

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [Comodule ℝ S V]
  [AddCommGroup W] [Module ℝ W] [Comodule ℝ S W]

attribute [local instance] Comodule.tensor

/-- **Hodge types add on tensor products.** If `v ∈ V^{p,q}` and `w ∈ W^{p',q'}`, then the image
of `v ⊗ w` in `ℂ ⊗[ℝ] (V ⊗[ℝ] W)` lies in `(V ⊗ W)^{p + p', q + q'}`. -/
theorem distribBaseChange_symm_tmul_mem_hodgeComponent {p q p' q' : ℤ} {v : ℂ ⊗[ℝ] V}
    {w : ℂ ⊗[ℝ] W} (hv : v ∈ hodgeComponent V p q) (hw : w ∈ hodgeComponent W p' q') :
    (TensorProduct.AlgebraTensorModule.distribBaseChange ℝ ℂ V W).symm (v ⊗ₜ[ℂ] w) ∈
      hodgeComponent (V ⊗[ℝ] W) (p + p') (q + q') := by
  rw [mem_hodgeComponent_iff] at hv hw ⊢
  rw [← AlgHom.distribBaseChange_symm_rTensor_tmul]
  have h := LinearMap.congr_fun (Comodule.endOfPoint_tensor (V := V) (W := W)
    splittingPoint.ofConv) (LinearMap.rTensor V
      (IsScalarTower.toAlgHom ℝ ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).toLinearMap v ⊗ₜ
    LinearMap.rTensor W
      (IsScalarTower.toAlgHom ℝ ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).toLinearMap w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul] at h
  rw [← h, hv, hw, TensorProduct.smul_tmul_smul, map_smul]
  simp [← ofAdd_add, add_comm]

/-- **The Hodge components of a tensor product.** `(V ⊗ W)^{p,q}` is the sum over `(a, b)` of
the images of `V^{a,b} ⊗ W^{p-a,q-b}` in `ℂ ⊗[ℝ] (V ⊗[ℝ] W)`. -/
theorem hodgeComponent_tensor (p q : ℤ) :
    hodgeComponent (V ⊗[ℝ] W) p q =
      ⨆ ab : ℤ × ℤ,
        ((hodgeComponent V ab.1 ab.2).map₂ (TensorProduct.mk ℂ (ℂ ⊗[ℝ] V) (ℂ ⊗[ℝ] W))
          (hodgeComponent W (p - ab.1) (q - ab.2))).map
            (TensorProduct.AlgebraTensorModule.distribBaseChange ℝ ℂ V W).symm.toLinearMap := by
  let G : InternalGrading ℂ (ℂ ⊗[ℝ] V) (ℤ × ℤ) :=
    ⟨fun ab ↦ hodgeComponent V ab.1 ab.2, isInternal_hodgeComponent V⟩
  let H : InternalGrading ℂ (ℂ ⊗[ℝ] W) (ℤ × ℤ) :=
    ⟨fun ab ↦ hodgeComponent W ab.1 ab.2, isInternal_hodgeComponent W⟩
  let T :=
    (G.tensorProduct H).map (TensorProduct.AlgebraTensorModule.distribBaseChange ℝ ℂ V W).symm
  have hle : T.piece ≤ fun pq ↦ hodgeComponent (V ⊗[ℝ] W) pq.1 pq.2 := fun pq ↦ by
    rw [InternalGrading.map_piece, Submodule.map_le_iff_le_comap]
    exact InternalGrading.tensorProduct_piece_le G H fun ab v hv w hw ↦ by
      simpa using distribBaseChange_symm_tmul_mem_hodgeComponent hv hw
  have hT := ((isInternal_hodgeComponent (V ⊗[ℝ] W)).submodule_iSupIndep.le_iff_eq_of_iSup_eq_top
    T.isInternal.submodule_iSup_eq_top).mp hle
  rw [← congrFun hT (p, q), InternalGrading.map_piece, InternalGrading.tensorProduct_piece_eq_iSup,
    Submodule.map_iSup]
  -- `(p, q) - ab` is `(p - ab.1, q - ab.2)` by definition of subtraction on `ℤ × ℤ`
  rfl

end TauCeti.DeligneTorus
