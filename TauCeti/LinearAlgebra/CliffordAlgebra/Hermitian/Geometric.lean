/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic

/-!
# The geometric convention for real Clifford actions

Let `V` be a real inner product space, `Q` a quadratic form on `V` and `S` a complex inner product
space with a real algebra map `ρ : Cℓ(V, Q) → End_ℂ(S)`; write `c(v) = ρ (ι Q v)` for Clifford
multiplication by `v`. The **geometric convention** for such an action, the one used for Clifford
modules and Dirac operators on Riemannian manifolds, has two clauses:

* the quadratic form is minus the squared norm, `Q v = -‖v‖²`, so that `c(v)² = -‖v‖²`;
* every `c(v)` is skew-Hermitian, `⟪c(v) s, t⟫ = -⟪s, c(v) t⟫`.

This file records it as the predicate `AlgHom.IsGeometricClifford` and derives its first
consequences: the polarized Clifford relation `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`, the relations
of a unit orthogonal pair `e₁, e₂` (`c(eᵢ)² = -1`, `c(e₁) c(e₂) = -c(e₂) c(e₁)` and
`(c(e₁) c(e₂))² = -1`), the equivalent adjoint form `c(v)* = -c(v)` of the second clause on a
finite-dimensional module, under which the existing Hermitian Clifford-module results such as
`CliffordAlgebra.adjoint_map_eq_map_star` apply, and the `*`-representation property of the
complex-linear extension of the action.

The skew-Hermitian clause is stated through inner products, so it makes sense on modules of any
dimension. The positive convention `c(v)² = +‖v‖²` is excluded by the first clause: for `V = ℝ`
and `S = ℂ`, the operator `c(e) = i` squares to `-1` and is skew-Hermitian, while `c(e) = 1`
squares to `+1` and is Hermitian.

## Main definitions

* `AlgHom.IsGeometricClifford ρ`: `Q v = -‖v‖²` and every `c(v)` is skew-Hermitian.

## Main results

* `AlgHom.IsGeometricClifford.map_ι_mul_map_ι_add_swap`: the polarized Clifford relation
  `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`.
* `AlgHom.IsGeometricClifford.map_ι_mul_map_ι_mul_self_of_orthonormal`: for a unit orthogonal
  pair, `(c(e₁) c(e₂))² = -1`.
* `AlgHom.isGeometricClifford_iff_adjoint`: on a finite-dimensional module the convention is
  `Q v = -‖v‖²` together with `c(v)* = -c(v)`.
* `AlgHom.IsGeometricClifford.inner_liftBaseChange_apply_left`: the complex-linear extension
  `ρ_ℂ = CliffordAlgebra.liftBaseChange ℂ Q ρ` of a geometric action satisfies
  `⟪ρ_ℂ(a) s, t⟫ = ⟪s, ρ_ℂ(conjStar a) t⟫` for the conjugate-linear Clifford involution
  `CliffordAlgebra.conjStar`, on a module of any dimension.

## References

* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Definition 12.1.10, p. 626, and
  Definition 12.1.64, pp. 653–654.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open CliffordAlgebra
open scoped InnerProductSpace

namespace AlgHom

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- **The geometric convention for a real Clifford action** `ρ : Cℓ(V, Q) → End_ℂ(S)`: the
quadratic form is minus the squared norm, `Q v = -‖v‖²`, and Clifford multiplication
`c(v) = ρ (ι Q v)` by every vector is skew-Hermitian. Then `c(v)² = -‖v‖²` and
`c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫` (`AlgHom.IsGeometricClifford.map_ι_mul_map_ι_add_swap`). -/
structure IsGeometricClifford (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) : Prop where
  /-- The quadratic form is minus the squared norm. -/
  apply_eq_neg_norm_sq : ∀ v, Q v = -‖v‖ ^ 2
  /-- Clifford multiplication by a vector is skew-Hermitian. -/
  inner_map_ι_apply_left : ∀ (v : V) (s t : S), ⟪ρ (ι Q v) s, t⟫_ℂ = -⟪s, ρ (ι Q v) t⟫_ℂ

namespace IsGeometricClifford

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- **The polarized Clifford relation** of the geometric convention:
`c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`. -/
theorem map_ι_mul_map_ι_add_swap (v w : V) :
    ρ (ι Q v) * ρ (ι Q w) + ρ (ι Q w) * ρ (ι Q v) = ((-2 * ⟪v, w⟫_ℝ : ℝ) : ℂ) • 1 := by
  rw [← map_mul ρ, ← map_mul ρ, ← map_add ρ,
    ι_mul_ι_add_swap_eq_neg_two_inner hρ.apply_eq_neg_norm_sq, AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one, Complex.coe_smul]

/-- In the geometric convention `c(v)² = -‖v‖²`. -/
theorem map_ι_mul_self (v : V) : ρ (ι Q v) * ρ (ι Q v) = ((-‖v‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rw [map_ι_mul_map_ι, hρ.apply_eq_neg_norm_sq]

/-- Clifford multiplications by orthogonal vectors anticommute. -/
theorem map_ι_mul_map_ι_comm_of_inner_eq_zero {v w : V} (h : ⟪v, w⟫_ℝ = 0) :
    ρ (ι Q v) * ρ (ι Q w) = -(ρ (ι Q w) * ρ (ι Q v)) := by
  rw [← map_mul ρ, ← map_mul ρ, ← map_neg ρ,
    ι_mul_ι_comm_of_isOrtho ((QuadraticMap.isOrtho_iff_inner_eq_zero hρ.apply_eq_neg_norm_sq).2 h)]

/-- Clifford multiplication by a unit vector squares to `-1`. -/
theorem map_ι_mul_self_of_norm_eq_one {v : V} (h : ‖v‖ = 1) : ρ (ι Q v) * ρ (ι Q v) = -1 := by
  simp [hρ.map_ι_mul_self, h]

/-- **A unit orthogonal pair**: for orthonormal `e₁, e₂`, the product `c(e₁) c(e₂)` squares to
`-1`, so that `i c(e₁) c(e₂)` is an involution. -/
theorem map_ι_mul_map_ι_mul_self_of_orthonormal {e₁ e₂ : V} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h : ⟪e₁, e₂⟫_ℝ = 0) :
    ρ (ι Q e₁) * ρ (ι Q e₂) * (ρ (ι Q e₁) * ρ (ι Q e₂)) = -1 := by
  rw [← map_mul ρ, ← map_mul ρ, ι_mul_ι_mul_self_of_isOrtho
    ((QuadraticMap.isOrtho_iff_inner_eq_zero hρ.apply_eq_neg_norm_sq).2 h), map_neg,
    AlgHom.commutes, hρ.apply_eq_neg_norm_sq, hρ.apply_eq_neg_norm_sq, h₁, h₂]
  simp

/-- **A geometric action is a `*`-representation**: under the geometric convention, the
complex-linear extension `ρ_ℂ` satisfies `⟪ρ_ℂ(a) s, t⟫ = ⟪s, ρ_ℂ(conjStar a) t⟫`, on a module
of any dimension. -/
theorem inner_liftBaseChange_apply_left (a : CliffordAlgebra (Q.baseChange ℂ)) (s t : S) :
    ⟪liftBaseChange ℂ Q ρ a s, t⟫_ℂ = ⟪s, liftBaseChange ℂ Q ρ (conjStar Q a) t⟫_ℂ := by
  refine sesqForm_map_eq_map_conjStar (liftBaseChange ℂ Q ρ) (innerₛₗ ℂ) (fun v x y ↦ ?_) a s t
  simpa only [innerₛₗ_apply_apply, liftBaseChange_ι_tmul, one_smul] using
    hρ.inner_map_ι_apply_left v x y

end IsGeometricClifford

/-- **The adjoint form of the geometric convention**: on a finite-dimensional module, the
convention says that `Q v = -‖v‖²` and that `c(v)* = -c(v)` for every vector. -/
theorem isGeometricClifford_iff_adjoint [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricClifford ↔
      (∀ v, Q v = -‖v‖ ^ 2) ∧ ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v) := by
  refine ⟨fun hρ ↦ ⟨hρ.apply_eq_neg_norm_sq, fun v ↦ ?_⟩, fun ⟨hQ, hρ⟩ ↦ ⟨hQ, fun v s t ↦ ?_⟩⟩
  · refine ((LinearMap.eq_adjoint_iff (-ρ (ι Q v)) (ρ (ι Q v))).2 fun s t ↦ ?_).symm
    rw [LinearMap.neg_apply, inner_neg_left, hρ.inner_map_ι_apply_left, neg_neg]
  · rw [← LinearMap.adjoint_inner_right, hρ, LinearMap.neg_apply, inner_neg_right]

end AlgHom
