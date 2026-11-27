/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Check: the coordinates of the split quadratic tensor product

Let `L/K` be an extension of fields of characteristic different from `2`, `σ` a `K`-automorphism
of `L` and `r ∈ L` a nonzero element with `σ r = -r` (for instance `L = K(√p)`, `r = √p`). The map
`L ⊗_K L → L × L`, `x ⊗ y ↦ (x y, x σ(y))` (`coordinates`), sends the two terms of
`e = (1 ⊗ 1 + (r²)⁻¹ (r ⊗ r)) / 2` to `(1/2, 1/2)` and `(1/2, -1/2)`, so `e` goes to the
idempotent `(1, 0)`. This fixes the order of the identity coordinate and the conjugate
coordinate, including over fields of residue characteristic two such as `ℚ₂(√2)`: only `2 ≠ 0`
in `L` is used.
-/

public section

open TensorProduct

namespace TauCeti.Huber.PlusRingCoordinatesCheck

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The map `L ⊗_K L → L × L`, `x ⊗ y ↦ (x y, x σ(y))`, for a `K`-automorphism `σ` of `L`. -/
noncomputable def coordinates (σ : L ≃ₐ[K] L) : L ⊗[K] L →ₐ[K] L × L :=
  Algebra.TensorProduct.productMap (AlgHom.prod (AlgHom.id K L) (AlgHom.id K L))
    (AlgHom.prod (AlgHom.id K L) σ.toAlgHom)

@[simp]
theorem coordinates_tmul (σ : L ≃ₐ[K] L) (x y : L) :
    coordinates σ (x ⊗ₜ y) = (x * y, x * σ y) := by
  simp [coordinates, Algebra.TensorProduct.productMap_apply_tmul]

variable {σ : L ≃ₐ[K] L} {r : L}

/-- The first term `(1 ⊗ 1) / 2` goes to `(1/2, 1/2)`. -/
example : coordinates σ ((2 : L)⁻¹ ⊗ₜ (1 : L)) = ((2 : L)⁻¹, (2 : L)⁻¹) := by
  simp

/-- The second term `(r²)⁻¹ (r ⊗ r) / 2` goes to `(1/2, -1/2)`. -/
example (hr : r ≠ 0) (hσ : σ r = -r) :
    coordinates σ (((2 : L)⁻¹ * (r ^ 2)⁻¹ * r) ⊗ₜ r) = ((2 : L)⁻¹, -(2 : L)⁻¹) := by
  rw [coordinates_tmul, hσ]
  congr 1 <;> field_simp

/-- *plus_ring_two_coordinates*: `(1 ⊗ 1 + (r²)⁻¹ (r ⊗ r)) / 2` goes to `(1, 0)`. -/
example (h2 : (2 : L) ≠ 0) (hr : r ≠ 0) (hσ : σ r = -r) :
    coordinates σ ((2 : L)⁻¹ ⊗ₜ (1 : L) + ((2 : L)⁻¹ * (r ^ 2)⁻¹ * r) ⊗ₜ r) = (1, 0) := by
  rw [map_add, coordinates_tmul, coordinates_tmul, hσ, map_one, Prod.mk_add_mk]
  congr 1 <;> field_simp <;> ring

end TauCeti.Huber.PlusRingCoordinatesCheck
