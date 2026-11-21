/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Unit laws of the graded tensor product of Clifford modules

A zero space is a unit for the graded tensor product `AlgHom.cliffordProdTensor`, provided the
first factor carries the trivial grading.

* **Left unit.** If `M₁` is the zero space, its vectors act by zero, so with the grading `γ = 1`
  of `E` a vector `(0, w)` acts on `E ⊗ F` by `1 ⊗ c₂(w)`. The whole action is then
  `1 ⊗ ρ₂`, after deleting the zero summand with `QuadraticMap.IsometryEquiv.uniqueProd`. For
  `E = R` the left unitor `R ⊗ F ≃ F` intertwines the two actions
  (`AlgHom.lid_cliffordProdTensor`, `AlgHom.conjAlgEquiv_lid_cliffordProdTensor_one`). With the
  negative grading `γ = -1`, `R ⊗ F ≃ F` twists `ρ₂` by `CliffordAlgebra.involute`
  (`AlgHom.lid_cliffordProdTensor_neg_one`, `AlgHom.conjAlgEquiv_lid_cliffordProdTensor_neg_one`).
* **Right unit.** If `M₂` is the zero space, a vector `(v, 0)` acts by `c₁(v) ⊗ 1`, whatever the
  grading `γ` of `E`, and the whole action is `ρ₁ ⊗ 1` after deleting the zero summand with
  `QuadraticMap.IsometryEquiv.prodUnique`. For `F = R` the right unitor `E ⊗ R ≃ E` intertwines
  the two actions (`AlgHom.rid_cliffordProdTensor`, `AlgHom.conjAlgEquiv_rid_cliffordProdTensor`).

For the chirality grading of a spinor module, the zero space with its positive orientation has
`Γ = 1` (`CliffordAlgebra.complexVolume_positiveOrientation`), so it is a two-sided unit. With the
negative orientation, `Γ = -1` and `c(0, w) = -1 ⊗ c₂(w)`, which the left unitor carries to
`-c₂(w)` rather than `c₂(w)`: the unit is the positively oriented point. No finiteness or
invertibility of two is needed.

## Main results

* `AlgHom.cliffordProdTensor_eq_lTensor`: for `M₁ = 0` and `γ = 1`, the action is `1 ⊗ ρ₂`.
* `AlgHom.lid_cliffordProdTensor`, `AlgHom.conjAlgEquiv_lid_cliffordProdTensor_one`: for `M₁ = 0`,
  `E = R` and `γ = 1`, the left unitor intertwines the actions.
* `AlgHom.lid_cliffordProdTensor_neg_one`, `AlgHom.conjAlgEquiv_lid_cliffordProdTensor_neg_one`:
  for `M₁ = 0`, `E = R` and `γ = -1`, the left unitor twists `ρ₂` by `CliffordAlgebra.involute`.
* `AlgHom.cliffordProdTensor_eq_rTensor`: for `M₂ = 0`, the action is `ρ₁ ⊗ 1`.
* `AlgHom.rid_cliffordProdTensor`, `AlgHom.conjAlgEquiv_rid_cliffordProdTensor`: for `M₂ = 0` and
  `F = R`, the right unitor intertwines the actions.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed. (2007), Definition 2.2.42.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
-/

public section

open TensorProduct CliffordAlgebra

namespace AlgHom

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

section Left

variable [Unique M₁] (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E)
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- **Left unit law of the graded tensor product.** If `M₁` is the zero space and `E` carries the
trivial grading `γ = 1`, then `CliffordAlgebra (Q₁.prod Q₂)` acts on `E ⊗ F` by `1 ⊗ ρ₂`, after
deleting the zero summand with `QuadraticMap.IsometryEquiv.uniqueProd`. -/
theorem cliffordProdTensor_eq_lTensor (a : CliffordAlgebra (Q₁.prod Q₂)) :
    cliffordProdTensor ρ₁ 1 (one_mul 1)
        (fun v ↦ by simp [Subsingleton.elim v 0]) ρ₂ a =
      (ρ₂ (map (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂).toIsometry a)).lTensor E := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id]
  | ι x =>
    simp [cliffordProdTensor_ι, Subsingleton.elim x.1 0, LinearMap.lTensor_def,
      Module.End.one_eq_id]
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add, LinearMap.lTensor_add]
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul, map_mul, LinearMap.lTensor_mul]

/-- **The left unitor intertwines the graded tensor product with the second factor.** If `M₁` is
the zero space acting on `E = R` with the trivial grading, then `R ⊗ F ≃ F`, `r ⊗ f ↦ r • f`,
carries the action of `a` to that of its image in `CliffordAlgebra Q₂` under
`QuadraticMap.IsometryEquiv.uniqueProd`. -/
theorem lid_cliffordProdTensor (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R)
    (a : CliffordAlgebra (Q₁.prod Q₂)) (z : R ⊗[R] F) :
    TensorProduct.lid R F
        (cliffordProdTensor ρ₁ 1 (one_mul 1)
          (fun v ↦ by simp [Subsingleton.elim v 0]) ρ₂ a z) =
      ρ₂ (map (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂).toIsometry a)
        (TensorProduct.lid R F z) := by
  rw [cliffordProdTensor_eq_lTensor]
  induction z using TensorProduct.inductionOn with
  | tmul r f => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Conjugated algebra-homomorphism form of `AlgHom.lid_cliffordProdTensor`. -/
theorem conjAlgEquiv_lid_cliffordProdTensor_one (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R) :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ 1 (one_mul 1)
          (fun v ↦ by simp [Subsingleton.elim v 0]) ρ₂) =
      ρ₂.comp (map (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂).toIsometry) := by
  refine AlgHom.ext fun a ↦ LinearMap.ext fun f ↦ ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [lid_cliffordProdTensor, LinearEquiv.apply_symm_apply]

/-- For a trivial left quadratic module `M₁` and the negative grading `-1` on `R`, conjugating
`cliffordProdTensor` by `TensorProduct.lid R F` twists `ρ₂` by `CliffordAlgebra.involute`. -/
theorem conjAlgEquiv_lid_cliffordProdTensor_neg_one
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R) :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ (-1) (LinearMap.ext fun _ ↦ by simp)
          (fun v ↦ by simp [Subsingleton.elim v 0]) ρ₂) =
      (ρ₂.comp (CliffordAlgebra.involute : CliffordAlgebra Q₂ →ₐ[R] CliffordAlgebra Q₂)).comp
        (map (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂).toIsometry) := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun x ↦ LinearMap.ext fun f ↦ ?_
  simp [LinearEquiv.conjAlgEquiv_apply, cliffordProdTensor_ι_tmul, Subsingleton.elim x.1 0]

/-- Applied form of `AlgHom.conjAlgEquiv_lid_cliffordProdTensor_neg_one`. -/
theorem lid_cliffordProdTensor_neg_one (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R)
    (a : CliffordAlgebra (Q₁.prod Q₂)) (z : R ⊗[R] F) :
    TensorProduct.lid R F
        (cliffordProdTensor ρ₁ (-1) (LinearMap.ext fun _ ↦ by simp)
          (fun v ↦ by simp [Subsingleton.elim v 0]) ρ₂ a z) =
      ρ₂ (CliffordAlgebra.involute
        (map (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂).toIsometry a))
        (TensorProduct.lid R F z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using LinearMap.congr_fun
    (AlgHom.congr_fun (conjAlgEquiv_lid_cliffordProdTensor_neg_one (ρ₁ := ρ₁) (ρ₂ := ρ₂)) a)
    (TensorProduct.lid R F z)

end Left

section Right

variable [Unique M₂] (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- **Right unit law of the graded tensor product.** If `M₂` is the zero space, then
`CliffordAlgebra (Q₁.prod Q₂)` acts on `E ⊗ F` by `ρ₁ ⊗ 1`, after deleting the zero summand with
`QuadraticMap.IsometryEquiv.prodUnique`, whatever the grading of `E`. -/
theorem cliffordProdTensor_eq_rTensor (a : CliffordAlgebra (Q₁.prod Q₂)) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a =
      (ρ₁ (map (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂).toIsometry a)).rTensor F := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id]
  | ι x =>
    simp [cliffordProdTensor_ι, Subsingleton.elim x.2 0]
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add, LinearMap.rTensor_add]
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul, map_mul, LinearMap.rTensor_mul]

/-- **The right unitor intertwines the graded tensor product with the first factor.** If `M₂` is
the zero space acting on `F = R`, then `E ⊗ R ≃ E`, `e ⊗ r ↦ r • e`, carries the action of `a` to
that of its image in `CliffordAlgebra Q₁` under `QuadraticMap.IsometryEquiv.prodUnique`. -/
theorem rid_cliffordProdTensor (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R R)
    (a : CliffordAlgebra (Q₁.prod Q₂)) (z : E ⊗[R] R) :
    TensorProduct.rid R E (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a z) =
      ρ₁ (map (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂).toIsometry a)
        (TensorProduct.rid R E z) := by
  rw [cliffordProdTensor_eq_rTensor]
  induction z using TensorProduct.inductionOn with
  | tmul e r => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Conjugated algebra-homomorphism form of `AlgHom.rid_cliffordProdTensor`. -/
theorem conjAlgEquiv_rid_cliffordProdTensor (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R R) :
    ((TensorProduct.rid R E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) =
      ρ₁.comp (map (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂).toIsometry) := by
  refine AlgHom.ext fun a ↦ LinearMap.ext fun e ↦ ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [rid_cliffordProdTensor, LinearEquiv.apply_symm_apply]

end Right

end AlgHom
