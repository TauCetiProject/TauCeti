/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Quadratic

/-!
# Unit norms in an unramified quadratic basis

Let `L/K` be an unramified quadratic extension of nonarchimedean local fields, and let `(1, ω)` be
a basis of `𝒪[L]` over `𝒪[K]`, with `T = Tr(ω)` and `N = N(ω)`. The norm of `x + y ω` is the
binary form `x² + T x y + N y²`. Modulo `𝓂[K]` this is the norm form of the residue extension
`𝓀[L]/𝓀[K]` in the basis given by `1` and the residue of `ω`, which is anisotropic. So the value
`x² + T x y + N y²` is a unit exactly when the pair `(x, y)` is primitive, that is when `x` or `y`
is a unit.

This is the unramified counterpart of
`TauCeti.isUnit_norm_iff_eisensteinQuadraticBasis_repr_zero`, where only the first coordinate
decides. It applies to the bases `(1, (√a - b)/s)` of
`TauCeti.exists_basis_integerRing_of_sq_eq_of_isUnit_discrim`. These include the basis
`(1, (√u - b)/π^e)` for the nonsquare unit `u` of maximal quadratic defect, and the basis
`(1, √a)` for a nonsquare unit `a` in odd residue characteristic.

## Main results

* `Module.Basis.isUnit_sq_add_mul_mul_trace_add_sq_mul_norm_iff`: in a basis `(1, ω)` of `𝒪[L]`
  over `𝒪[K]` for an unramified quadratic `L/K`, the value `x² + x y T + y² N` is a unit exactly
  when `x` or `y` is a unit.
* `TauCeti.isUnit_sq_add_mul_mul_trace_add_sq_mul_norm_iff_of_isUnit_discrim`: the same for an
  integer `ω` of `L` whose discriminant `Tr(ω)² - 4 N(ω)` is a unit.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter III, §5.
-/

public section

open ValuativeRel

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

namespace Module.Basis

/-- **Primitive pairs have unit norm in an unramified quadratic extension** (O'Meara §63A). Let
`L/K` be unramified and let `(1, ω)` be a basis of `𝒪[L]` over `𝒪[K]`, with `T = Tr(ω)` and
`N = N(ω)`. For `x y : 𝒪[K]`, the norm `x² + x y T + y² N` of `x + y ω` is a unit exactly when
`x` or `y` is a unit. -/
theorem isUnit_sq_add_mul_mul_trace_add_sq_mul_norm_iff [TauCeti.IsUnramified K L]
    (B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L]) (hB : B 0 = 1) (x y : 𝒪[K]) :
    IsUnit (x ^ 2 + x * y * Algebra.trace 𝒪[K] 𝒪[L] (B 1) +
        y ^ 2 * Algebra.norm 𝒪[K] (B 1)) ↔ IsUnit x ∨ IsUnit y := by
  have h := B.norm_eq_of_apply_zero_eq_one hB (B.equivFun.symm ![x, y])
  simp only [← B.equivFun_apply, LinearEquiv.apply_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  rw [← h, TauCeti.isUnit_norm_integerRing_iff,
    TauCeti.IsUnramified.isUnit_iff_exists_isUnit_repr B, Fin.exists_fin_two]
  simp

end Module.Basis

namespace TauCeti

variable [Algebra.IsQuadraticExtension K L]

/-- **Primitive pairs have unit norm at a unit discriminant** (O'Meara §63A). If `ω ∈ 𝒪[L]` has
discriminant `Tr(ω)² - 4 N(ω)` a unit of `𝒪[K]`, then for `x y : 𝒪[K]` the norm
`x² + x y Tr(ω) + y² N(ω)` of `x + y ω` is a unit exactly when `x` or `y` is a unit. -/
theorem isUnit_sq_add_mul_mul_trace_add_sq_mul_norm_iff_of_isUnit_discrim {ω : 𝒪[L]}
    (hω : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] ω ^ 2 - 4 * Algebra.norm 𝒪[K] ω)) (x y : 𝒪[K]) :
    IsUnit (x ^ 2 + x * y * Algebra.trace 𝒪[K] 𝒪[L] ω + y ^ 2 * Algebra.norm 𝒪[K] ω) ↔
      IsUnit x ∨ IsUnit y := by
  have := isUnramified_of_isUnit_discrim hω
  simpa using (unramifiedQuadraticBasis hω).isUnit_sq_add_mul_mul_trace_add_sq_mul_norm_iff
    (unramifiedQuadraticBasis_zero hω) x y

end TauCeti
