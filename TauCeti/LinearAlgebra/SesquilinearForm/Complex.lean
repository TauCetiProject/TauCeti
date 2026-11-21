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
# Hermitian sesquilinear forms over the complex numbers

A sesquilinear form `H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ`, conjugate-linear in its first argument, is Hermitian
(`LinearMap.IsSymm` for the conjugation `starRingEnd ℂ`, that is `starRingEnd ℂ (H x y) = H y x`)
as soon as every diagonal value `H x x` is real.  This is special to `ℂ`: by polarization the
diagonal of a complex sesquilinear form determines the whole form, whereas the diagonal of a real
bilinear form only sees its symmetric part, so over `ℝ` real diagonal values say nothing.

In particular a form that is nonnegative on the diagonal is Hermitian.  Nonnegativity here is
Mathlib's `LinearMap.IsNonneg` for the partial order on `ℂ` of the `ComplexOrder` scope (activate it
with `open scoped ComplexOrder`), and Mathlib's `LinearMap.IsPosSemidef` bundles `LinearMap.IsSymm`
with it; over `ℂ` the nonnegativity half alone therefore already gives positive semidefiniteness.

## Main statements

* `LinearMap.isSymm_iff_forall_isSelfAdjoint`: a sesquilinear form over `ℂ` is Hermitian exactly
  when all its diagonal values are self-adjoint, that is, real.
* `LinearMap.IsNonneg.isSymm`: a nonnegative sesquilinear form over `ℂ` is Hermitian.
-/

public section

namespace LinearMap

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

/-- **A sesquilinear form over `ℂ` is Hermitian exactly when its diagonal is real**:
`starRingEnd ℂ (H x y) = H y x` for all `x` and `y` if and only if `H x x` is self-adjoint for
every `x`.  No order on `ℂ` is involved. -/
theorem isSymm_iff_forall_isSelfAdjoint {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} :
    H.IsSymm ↔ ∀ x, IsSelfAdjoint (H x x) := by
  refine ⟨fun hH x => (starRingEnd_apply (H x x)).symm.trans (hH.eq x x), fun h => ⟨fun x y => ?_⟩⟩
  have real : ∀ z, starRingEnd ℂ (H z z) = H z z := fun z => by
    rw [starRingEnd_apply]; exact (h z).star_eq
  -- Polarize: the real diagonal values at `x + y` and `x + I • y` recover `H x y` from `H y x`.
  have h1 := real (x + y)
  have h2 := real (x + Complex.I • y)
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    map_mul, map_neg, Complex.conj_I, RingHom.id_apply, real] at h1 h2
  linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
    (1 / 2 : ℂ) * (h1 + Complex.I * h2)

open scoped ComplexOrder in
/-- **A nonnegative sesquilinear form over `ℂ` is Hermitian**: for the partial order of the
`ComplexOrder` scope, `0 ≤ H x x` for every `x` already gives `starRingEnd ℂ (H x y) = H y x`.  So
`H.IsNonneg` alone yields `H.IsPosSemidef`, as `⟨hH.isSymm, hH⟩`. -/
theorem IsNonneg.isSymm {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsNonneg) : H.IsSymm :=
  isSymm_iff_forall_isSelfAdjoint.mpr fun x => IsSelfAdjoint.of_nonneg (hH.nonneg x)

end LinearMap
