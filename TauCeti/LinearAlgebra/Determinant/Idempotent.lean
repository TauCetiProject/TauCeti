/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# The determinant of `1 + c • e` for an idempotent `e`

An idempotent endomorphism `e` of a finite-dimensional vector space splits it as the direct sum of
its range, on which `e` is the identity, and its kernel. So `1 + c • e` is the scalar `1 + c` on
the range and the identity on the kernel, and its determinant is `(1 + c) ^ r` with `r` the
dimension of the range of `e`.

## Main results

* `LinearMap.det_one_add_smul_of_isIdempotentElem`: `det (1 + c • e) = (1 + c) ^ dim (range e)`
  for an idempotent `e`.
-/

public section

open Module

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The determinant of `1 + c • e` for an idempotent `e`** is `(1 + c) ^ r`, where `r` is the
dimension of the range of `e`: in the splitting `V = range e ⊕ ker e`, the endomorphism
`1 + c • e` is the scalar `1 + c` on the first summand and the identity on the second. -/
theorem det_one_add_smul_of_isIdempotentElem {e : V →ₗ[K] V} (he : IsIdempotentElem e) (c : K) :
    LinearMap.det (1 + c • e) = (1 + c) ^ finrank K (range e) := by
  let φ := Submodule.prodEquivOfIsCompl _ _ (IsIdempotentElem.isCompl he)
  let g : Module.End K (range e × ker e) := prodMap ((1 + c) • LinearMap.id) LinearMap.id
  have key : (1 + c • e) ∘ₗ (φ : range e × ker e →ₗ[K] V) =
      (φ : range e × ker e →ₗ[K] V) ∘ₗ g := by
    ext x
    · have hx : e x = x := (IsIdempotentElem.mem_range_iff he).mp x.property
      simp [φ, g, hx, add_smul]
    · have hx : e x = 0 := x.property
      simp [φ, g, hx]
  have hconj : 1 + c • e = (φ : range e × ker e →ₗ[K] V) ∘ₗ g ∘ₗ φ.symm := by
    rw [← LinearMap.comp_assoc, ← key, LinearMap.comp_assoc, LinearEquiv.comp_symm,
      LinearMap.comp_id]
  rw [hconj, det_conj, det_prodMap, det_smul, det_id, det_id, mul_one, mul_one]

end LinearMap
