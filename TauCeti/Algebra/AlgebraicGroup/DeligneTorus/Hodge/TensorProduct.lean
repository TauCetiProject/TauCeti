/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Hodge
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction

/-!
# Hodge components of a tensor product of representations of the Deligne torus

For real representations `V` and `W` of the Deligne torus `S`, the tensor product `V ⊗[ℝ] W` is a
representation through the diagonal coaction (`TauCeti.Comodule.tensor`). Under the canonical
identification `ℂ ⊗[ℝ] (V ⊗[ℝ] W) ≃ (ℂ ⊗[ℝ] V) ⊗[ℂ] (ℂ ⊗[ℝ] W)`, Hodge types add:

```text
(V ⊗ W)^{p,q} = ⨁_{a + c = p, b + d = q} V^{a,b} ⊗ W^{c,d}.
```

The inclusion of each summand is a computation with the universal point of `𝔾ₘ × 𝔾ₘ`, which acts
on the tensor product through its actions on the factors (`TauCeti.Comodule.endOfPoint_tensor`).
Equality follows because both sides are internal direct sum decompositions of the whole space.

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

omit [Comodule ℝ S V] [Comodule ℝ S W] in
/-- Extending scalars from `ℂ` to a complex algebra `A` commutes with the comparison
`ℂ ⊗[ℝ] (V ⊗[ℝ] W) ≃ (ℂ ⊗[ℝ] V) ⊗[ℂ] (ℂ ⊗[ℝ] W)`. -/
private theorem rTensor_distribBaseChange_symm_tmul {A : Type*} [CommRing A] [Algebra ℂ A]
    (v : ℂ ⊗[ℝ] V) (w : ℂ ⊗[ℝ] W) :
    LinearMap.rTensor (V ⊗[ℝ] W) (IsScalarTower.toAlgHom ℝ ℂ A).toLinearMap
        ((TensorProduct.AlgebraTensorModule.distribBaseChange ℝ ℂ V W).symm (v ⊗ₜ[ℂ] w)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange ℝ A V W).symm
        (LinearMap.rTensor V (IsScalarTower.toAlgHom ℝ ℂ A).toLinearMap v ⊗ₜ[A]
          LinearMap.rTensor W (IsScalarTower.toAlgHom ℝ ℂ A).toLinearMap w) := by
  induction v using TensorProduct.inductionOn with
  | add v v' hv hv' => simp only [TensorProduct.add_tmul, map_add, hv, hv']
  | tmul c x =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | tmul d y => simp

/-- **Hodge types add on tensor products.** If `v ∈ V^{p,q}` and `w ∈ W^{p',q'}`, then the image
of `v ⊗ w` in `ℂ ⊗[ℝ] (V ⊗[ℝ] W)` lies in `(V ⊗ W)^{p + p', q + q'}`. -/
theorem distribBaseChange_symm_tmul_mem_hodgeComponent {p q p' q' : ℤ} {v : ℂ ⊗[ℝ] V}
    {w : ℂ ⊗[ℝ] W} (hv : v ∈ hodgeComponent V p q) (hw : w ∈ hodgeComponent W p' q') :
    (TensorProduct.AlgebraTensorModule.distribBaseChange ℝ ℂ V W).symm (v ⊗ₜ[ℂ] w) ∈
      hodgeComponent (V ⊗[ℝ] W) (p + p') (q + q') := by
  rw [mem_hodgeComponent_iff] at hv hw ⊢
  rw [rTensor_distribBaseChange_symm_tmul]
  have h := LinearMap.congr_fun (Comodule.endOfPoint_tensor (V := V) (W := W)
    splittingPoint.ofConv) (LinearMap.rTensor V
      (IsScalarTower.toAlgHom ℝ ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).toLinearMap v ⊗ₜ
    LinearMap.rTensor W
      (IsScalarTower.toAlgHom ℝ ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).toLinearMap w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul] at h
  rw [← h, hv, hw, TensorProduct.smul_tmul_smul, map_smul, MonoidAlgebra.single_mul_single,
    one_mul, ← ofAdd_add, Prod.mk_add_mk, neg_add, neg_add]

/-- The image in `ℂ ⊗[ℝ] (V ⊗[ℝ] W)` of `V^{a,b} ⊗ W^{c,d}`, for `(a, b) = ab` and
`(c, d) = cd`. -/
private noncomputable def tensorHodgePiece (ab cd : ℤ × ℤ) : Submodule ℂ (ℂ ⊗[ℝ] (V ⊗[ℝ] W)) :=
  ((hodgeComponent V ab.1 ab.2).map₂ (TensorProduct.mk ℂ (ℂ ⊗[ℝ] V) (ℂ ⊗[ℝ] W))
    (hodgeComponent W cd.1 cd.2)).map
      (TensorProduct.AlgebraTensorModule.distribBaseChange ℝ ℂ V W).symm.toLinearMap

private theorem tensorHodgePiece_le (ab cd : ℤ × ℤ) :
    tensorHodgePiece (V := V) (W := W) ab cd ≤
      hodgeComponent (V ⊗[ℝ] W) (ab.1 + cd.1) (ab.2 + cd.2) := by
  rw [tensorHodgePiece, Submodule.map_le_iff_le_comap]
  exact Submodule.map₂_le.mpr fun v hv w hw ↦
    distribBaseChange_symm_tmul_mem_hodgeComponent hv hw

private theorem iSup_tensorHodgePiece_eq_top :
    ⨆ (ab : ℤ × ℤ) (cd : ℤ × ℤ), tensorHodgePiece (V := V) (W := W) ab cd = ⊤ := by
  have hV := (isInternal_hodgeComponent V).submodule_iSup_eq_top
  have hW := (isInternal_hodgeComponent W).submodule_iSup_eq_top
  simp only [tensorHodgePiece, ← Submodule.map_iSup, ← Submodule.map₂_iSup_right,
    ← Submodule.map₂_iSup_left, hV, hW, TensorProduct.map₂_mk_top_top_eq_top, Submodule.map_top,
    LinearEquiv.range]

/-- **The Hodge components of a tensor product.** `(V ⊗ W)^{p,q}` is the sum over `(a, b)` of
the images of `V^{a,b} ⊗ W^{p-a,q-b}` in `ℂ ⊗[ℝ] (V ⊗[ℝ] W)`. -/
theorem hodgeComponent_tensor (p q : ℤ) :
    hodgeComponent (V ⊗[ℝ] W) p q =
      ⨆ ab : ℤ × ℤ,
        ((hodgeComponent V ab.1 ab.2).map₂ (TensorProduct.mk ℂ (ℂ ⊗[ℝ] V) (ℂ ⊗[ℝ] W))
          (hodgeComponent W (p - ab.1) (q - ab.2))).map
            (TensorProduct.AlgebraTensorModule.distribBaseChange ℝ ℂ V W).symm.toLinearMap := by
  let N : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℝ] (V ⊗[ℝ] W)) := fun pq ↦
    ⨆ ab : ℤ × ℤ, tensorHodgePiece ab (pq.1 - ab.1, pq.2 - ab.2)
  have hle : N ≤ fun pq ↦ hodgeComponent (V ⊗[ℝ] W) pq.1 pq.2 := fun pq ↦ iSup_le fun ab ↦ by
    simpa using tensorHodgePiece_le (V := V) (W := W) ab (pq.1 - ab.1, pq.2 - ab.2)
  have htop : iSup N = ⊤ := by
    refine eq_top_iff.mpr (iSup_tensorHodgePiece_eq_top (V := V) (W := W) ▸ ?_)
    refine iSup₂_le fun ab cd ↦ le_iSup_of_le (ab + cd) (le_iSup_of_le ab ?_)
    simp
  have hindep := (isInternal_hodgeComponent (V ⊗[ℝ] W)).submodule_iSupIndep
  exact (congrFun ((hindep.le_iff_eq_of_iSup_eq_top htop).mp hle) (p, q)).symm

end TauCeti.DeligneTorus
