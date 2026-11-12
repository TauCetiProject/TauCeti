/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Nonnegative sesquilinear forms over the complex numbers

## Main statements

* `LinearMap.IsNonneg.isSymm`: a nonnegative sesquilinear form over `ℂ` is Hermitian.
-/

public section

namespace LinearMap

open scoped ComplexOrder

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

/-- **A nonnegative sesquilinear form over `ℂ` is Hermitian.**  Nonnegativity makes every diagonal
value real, and polarizing at `x + y` and `x + I • y` then recovers `H x y = conj (H y x)`. -/
theorem IsNonneg.isSymm {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsNonneg) : H.IsSymm := by
  refine ⟨fun x y => ?_⟩
  have real : ∀ z, starRingEnd ℂ (H z z) = H z z := fun z => by
    rw [starRingEnd_apply]; exact (hH.nonneg z).star_eq
  have h1 := real (x + y)
  have h2 := real (x + Complex.I • y)
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    map_mul, map_neg, Complex.conj_I, RingHom.id_apply, real] at h1 h2
  linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
    (1 / 2 : ℂ) * (h1 + Complex.I * h2)

end LinearMap
