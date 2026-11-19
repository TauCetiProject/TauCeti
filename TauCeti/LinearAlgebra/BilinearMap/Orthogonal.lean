/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Rescaling orthogonal families

An indexed family `v` is orthogonal for a bilinear map `B` when `B (v i) (v j) = 0` for `i ≠ j`.
Rescaling each member of the family by a scalar keeps it orthogonal; in particular rescaling the
members of a basis by units, as in `Module.Basis.unitsSMul`, gives an orthogonal basis.

## Main results

* `LinearMap.IsOrthoᵢ.smul`: rescaling the members of an orthogonal family keeps it orthogonal.
* `LinearMap.IsOrthoᵢ.unitsSMul`: rescaling an orthogonal basis by units keeps it orthogonal.
-/

public section

open Module

namespace LinearMap.IsOrthoᵢ

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {B : M →ₗ[R] M →ₗ[R] N}

/-- Rescaling the members of an orthogonal family keeps it orthogonal. -/
theorem smul {v : ι → M} (hv : B.IsOrthoᵢ v) (c : ι → R) : B.IsOrthoᵢ fun i => c i • v i := by
  intro i j hij
  simp only [Function.onFun, map_smul, LinearMap.smul_apply, LinearMap.isOrthoᵢ_def.1 hv i j hij,
    smul_zero]

/-- Rescaling the members of an orthogonal basis by units keeps it orthogonal. -/
theorem unitsSMul {b : Basis ι R M} (hb : B.IsOrthoᵢ b) (c : ι → Rˣ) :
    B.IsOrthoᵢ (b.unitsSMul c) := by
  have h : ⇑(b.unitsSMul c) = fun i => (c i : R) • b i :=
    funext fun i => by rw [Basis.unitsSMul_apply, Units.smul_def]
  rw [h]
  exact hb.smul _

end LinearMap.IsOrthoᵢ
