/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants on products

An endomorphism `A` of `R × R` is determined by the images `A (1, 0)` and `A (0, 1)` of the
standard basis vectors, and its determinant is the `2 × 2` determinant of these two columns. This
is `Matrix.det_fin_two` read through the basis `Module.Basis.finTwoProd R`. It is the Jacobian
determinant in the change of variables formula for maps of the plane `ℝ × ℝ`.

Consequently `A` multiplies the wedge product of two linear forms `κ` and `α` on `R × R` by its
determinant: `κ (A e₁) α (A e₂) - κ (A e₂) α (A e₁) = det A (κ e₁ α e₂ - κ e₂ α e₁)`. This is the
transformation rule of a two-form on the plane under pullback.

On a general product `M × M'` with the product basis of bases `b` of `M` and `b'` of `M'`, a
family of vectors `(vᵢ, 0)`, `(0, v'ⱼ)` is block diagonal, so its determinant is the product
`det_b v * det_b' v'` of the determinants of the two blocks. This is how volumes of product
parallelepipeds factor.

## Main results

* `LinearMap.det_finTwoProd`: the determinant of an endomorphism of `R × R`.
* `LinearMap.det_mul_wedge_finTwoProd`: an endomorphism of `R × R` multiplies the wedge product
  of two linear forms by its determinant.
* `Module.Basis.prod_det_sumElim`: the determinant of a block family in a product basis.
-/

public section

namespace LinearMap

variable {R : Type*} [CommRing R]

/-- The determinant of an endomorphism of `R × R` in terms of the images `A (1, 0)` and
`A (0, 1)` of the standard basis vectors. -/
theorem det_finTwoProd (A : (R × R) →ₗ[R] R × R) :
    LinearMap.det A = (A (1, 0)).1 * (A (0, 1)).2 - (A (1, 0)).2 * (A (0, 1)).1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd R), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one]
  ring

/-- An endomorphism `A` of `R × R` multiplies the wedge product `κ ∧ α` of two linear forms on
`R × R`, evaluated on the standard basis vectors `(1, 0)` and `(0, 1)`, by its determinant. -/
theorem det_mul_wedge_finTwoProd (A : (R × R) →ₗ[R] R × R) (κ α : (R × R) →ₗ[R] R) :
    LinearMap.det A * (κ (1, 0) * α (0, 1) - κ (0, 1) * α (1, 0)) =
      κ (A (1, 0)) * α (A (0, 1)) - κ (A (0, 1)) * α (A (1, 0)) := by
  have h (φ : (R × R) →ₗ[R] R) (e : R × R) : φ e = e.1 * φ (1, 0) + e.2 * φ (0, 1) := by
    have he : e = e.1 • ((1, 0) : R × R) + e.2 • ((0, 1) : R × R) := by ext <;> simp
    conv_lhs => rw [he]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [det_finTwoProd, h κ (A (1, 0)), h κ (A (0, 1)), h α (A (1, 0)), h α (A (0, 1))]
  ring

end LinearMap

namespace Module.Basis

variable {R M M' ι ι' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- **The determinant of a block family in a product basis.** In the product basis of `b` and
`b'`, the family of vectors `(vᵢ, 0)` followed by `(0, v'ⱼ)` has determinant
`det_b v * det_b' v'`. -/
theorem prod_det_sumElim (b : Basis ι R M) (b' : Basis ι' R M') (v : ι → M) (v' : ι' → M') :
    (b.prod b').det (Sum.elim (fun i ↦ (v i, 0)) (fun j ↦ (0, v' j))) = b.det v * b'.det v' := by
  have := Module.Free.of_basis b
  have := Module.Free.of_basis b'
  have := Module.Finite.of_basis b
  have := Module.Finite.of_basis b'
  -- The block family is the image of the product basis under `f × g`, where `f` and `g` send
  -- the two bases to `v` and `v'`.
  set f := b.constr R v
  set g := b'.constr R v'
  have hfg : Sum.elim (fun i ↦ (v i, 0)) (fun j ↦ (0, v' j)) = ⇑(f.prodMap g) ∘ ⇑(b.prod b') := by
    funext i
    cases i <;> simp [f, g]
  have hf : b.det v = LinearMap.det f := by
    rw [← mul_one (LinearMap.det f), ← b.det_self, ← det_comp]
    congr 1
    funext i
    simp [f]
  have hg : b'.det v' = LinearMap.det g := by
    rw [← mul_one (LinearMap.det g), ← b'.det_self, ← det_comp]
    congr 1
    funext i
    simp [g]
  rw [hfg, det_comp, det_self, mul_one, LinearMap.det_prodMap, hf, hg]

end Module.Basis
