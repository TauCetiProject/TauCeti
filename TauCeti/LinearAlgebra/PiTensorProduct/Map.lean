/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Tensor maps of families of linear maps

Mathlib's `PiTensorProduct.map_update_add` says that `PiTensorProduct.map` is additive in each
factor. This file records the form of that statement used when two tensor maps are compared
directly: if two families of linear maps agree away from one index `k`, then the sum of their
tensor maps is the tensor map of the family whose `k`-th factor is the sum of the two `k`-th
factors. It also records that a tensor map over an empty index type is the identity, that a
semilinear tensor map along `σ` over an empty index type is `σ` under the scalar identification
`PiTensorProduct.isEmptyEquiv`, and that a tensor map with a zero factor is zero.

## Main results

* `TauCeti.PiTensorProduct.map_add_map_eq_map_update`: the sum of two tensor maps whose factors
  agree away from one index.
* `TauCeti.PiTensorProduct.map_of_isEmpty`: a tensor map over an empty index type is the
  identity.
* `TauCeti.PiTensorProduct.isEmptyEquiv_map`: over an empty index type, a tensor map along
  `σ : R →+* S` is `σ` under the identifications of the tensor products with the scalars.
* `TauCeti.PiTensorProduct.map_eq_zero_of_eq_zero`: a tensor map with a zero factor is zero.
-/

public section

open scoped TensorProduct

universe uι uR us ut

namespace TauCeti.PiTensorProduct

variable {ι : Type uι} {R : Type uR} {s : ι → Type us} {t : ι → Type ut}
  [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)] [∀ i, AddCommMonoid (t i)]
  [∀ i, Module R (t i)]

/-- Two tensor maps whose factors agree away from one index `k` add up to the tensor map with the
sum of their factors at `k`. -/
theorem map_add_map_eq_map_update [DecidableEq ι] (f g : ∀ i, s i →ₗ[R] t i) (k : ι)
    (h : ∀ i, i ≠ k → f i = g i) :
    PiTensorProduct.map f + PiTensorProduct.map g =
      PiTensorProduct.map (Function.update f k (f k + g k)) := by
  rw [PiTensorProduct.map_update_add, Function.update_eq_self,
    ← Function.eq_update_iff.2 ⟨rfl, fun i hi ↦ (h i hi).symm⟩]

/-- Over an empty index type, every tensor map of endomorphisms is the identity. -/
@[simp]
theorem map_of_isEmpty [IsEmpty ι] (f : ∀ i, s i →ₗ[R] s i) :
    PiTensorProduct.map f = LinearMap.id := by
  rw [Subsingleton.elim f fun _ ↦ LinearMap.id, PiTensorProduct.map_id]

section semilinear

variable {S : Type*} [CommSemiring S] {σ : R →+* S} {u : ι → Type*} [∀ i, AddCommMonoid (u i)]
  [∀ i, Module S (u i)]

/-- Over an empty index type, a tensor map along `σ : R →+* S` corresponds to `σ` under the
identifications `PiTensorProduct.isEmptyEquiv` of both tensor products with the scalars. -/
@[simp]
theorem isEmptyEquiv_map [IsEmpty ι] (f : ∀ i, s i →ₛₗ[σ] u i) (x : ⨂[R] i, s i) :
    PiTensorProduct.isEmptyEquiv ι (PiTensorProduct.map f x) =
      σ (PiTensorProduct.isEmptyEquiv ι x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A tensor map with a zero factor is zero. -/
theorem map_eq_zero_of_eq_zero (f : ∀ i, s i →ₛₗ[σ] u i) {k : ι} (hk : f k = 0) :
    PiTensorProduct.map f = 0 := by
  ext v
  simpa using (PiTensorProduct.tprod S).map_coord_zero k (by simp [hk])

end semilinear

end TauCeti.PiTensorProduct
