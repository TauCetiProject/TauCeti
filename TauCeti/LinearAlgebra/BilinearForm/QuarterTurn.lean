/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The quarter turn of a pair of vectors

For a bilinear form `B` on a module `M` and two vectors `q, p ∈ M`, the *quarter turn*
`LinearMap.BilinForm.quarterTurn B q p` is the endomorphism `v ↦ B(q, v) p - B(p, v) q` of `M`.
Its image lies in `span {q, p}`. When `B` is symmetric it is skew for `B`, and when `(q, p)` is
`B`-orthonormal it sends `q ↦ p` and `p ↦ -q`, so it restricts to a complex structure on the plane
`span {q, p}`. For the inner product of a Euclidean plane with an oriented orthonormal basis
`(q, p)` it is the rotation by `π / 2`.

## Main definitions

* `LinearMap.BilinForm.quarterTurn B q p`: the endomorphism `v ↦ B(q, v) p - B(p, v) q`.

## Main results

* `LinearMap.BilinForm.quarterTurn_mem_span`: the quarter turn takes values in `span {q, p}`.
* `LinearMap.BilinForm.apply_quarterTurn`: the quarter turn is skew for a symmetric form.
* `LinearMap.BilinForm.quarterTurn_quarterTurn`: for a `B`-orthonormal pair, the quarter turn
  squares to `-1` on `span {q, p}`.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- The quarter turn `v ↦ B(q, v) p - B(p, v) q` of a pair `(q, p)`. For a `B`-orthonormal pair it
is a complex structure on the plane spanned by `q` and `p`. -/
noncomputable def quarterTurn (B : BilinForm R M) (q p : M) : M →ₗ[R] M :=
  (B q).smulRight p - (B p).smulRight q

@[simp]
theorem quarterTurn_apply (q p v : M) : quarterTurn B q p v = B q v • p - B p v • q :=
  (rfl)

/-- The quarter turn of a pair takes values in the span of the pair. -/
theorem quarterTurn_mem_span (q p v : M) : quarterTurn B q p v ∈ Submodule.span R {q, p} :=
  Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The quarter turn of a pair is skew for a symmetric `B`. -/
theorem apply_quarterTurn (hB : B.IsSymm) (q p v w : M) :
    B (quarterTurn B q p v) w = -B v (quarterTurn B q p w) := by
  simp only [quarterTurn_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [hB.eq v p, hB.eq v q]
  ring

theorem quarterTurn_apply_left {q p : M} (hqq : B q q = 1) (hpq : B p q = 0) :
    quarterTurn B q p q = p := by
  simp [hqq, hpq]

theorem quarterTurn_apply_right {q p : M} (hqp : B q p = 0) (hpp : B p p = 1) :
    quarterTurn B q p p = -q := by
  simp [hqp, hpp]

/-- The quarter turn of a `B`-orthonormal pair squares to `-1` on the plane of the pair. -/
theorem quarterTurn_quarterTurn {q p v : M} (hqq : B q q = 1) (hqp : B q p = 0)
    (hpq : B p q = 0) (hpp : B p p = 1) (hv : v ∈ Submodule.span R {q, p}) :
    quarterTurn B q p (quarterTurn B q p v) = -v := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  simp only [map_add, map_smul, quarterTurn_apply_left hqq hpq, quarterTurn_apply_right hqp hpp,
    smul_neg, map_neg]
  abel

end LinearMap.BilinForm
