/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.LinearCombination

/-!
# A form that is both symmetric and alternating

Away from characteristic two a bilinear form cannot be both symmetric and alternating without
being zero: symmetry and alternation give `B x y = B y x` and `B x y = -B y x`, so `2 * B x y = 0`,
and cancelling the `2` leaves `B x y = 0`.

That cancellation is all the hypothesis on the ring there is: `2` has to be regular, and nothing
is asked of any other element, so the statement covers rings with zero divisors elsewhere.  Over a
field, or over any domain, `IsRegular.of_ne_zero` supplies the hypothesis from `(2 : R) ≠ 0`.

## Main results

* `TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`: a symmetric alternating form over a ring in which
  `2` is regular is zero.
* `TauCeti.BilinForm.nondegenerate_smul_iff`: scalar multiplication by a regular element
  preserves nondegeneracy.
* `TauCeti.BilinForm.nondegenerate_neg_iff`: negating a bilinear form preserves nondegeneracy.
* `Module.Basis.dualBasis_smul_apply`: the dual basis of a scalar multiple of a form.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

/-- **Away from characteristic two a symmetric alternating form is zero**: symmetry and alternation
force `2 * B x y = 0`, and a regular `2` cancels. -/
theorem eq_zero_of_isSymm_of_isAlt {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (h2 : IsLeftRegular (2 : R)) {B : BilinForm R M} (hsymm : B.IsSymm)
    (halt : B.IsAlt) : B = 0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have hzero : (2 : R) * B x y = 2 * 0 := by
    rw [mul_zero]
    linear_combination hsymm.eq x y - halt.neg_eq x y
  simpa using h2 hzero

/-- A scalar multiple of a bilinear form by a regular element is nondegenerate if and only if
the original form is nondegenerate. -/
@[simp]
theorem nondegenerate_smul_iff {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {B : BilinForm R M} {c : R} (hc : IsRegular c) :
    (c • B).Nondegenerate ↔ B.Nondegenerate := by
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨fun x hx ↦ hl x fun y ↦ ?_, fun y hy ↦ hr y fun x ↦ ?_⟩
    · specialize hx y
      simp only [LinearMap.smul_apply, smul_eq_mul, hx, mul_zero]
    · specialize hy x
      simp only [LinearMap.smul_apply, smul_eq_mul, hy, mul_zero]
  · rintro ⟨hl, hr⟩
    refine ⟨fun x hx ↦ hl x fun y ↦ ?_, fun y hy ↦ hr y fun x ↦ ?_⟩
    · specialize hx y
      simp only [LinearMap.smul_apply, smul_eq_mul, hc.left.mul_left_eq_zero_iff] at hx
      exact hx
    · specialize hy x
      simp only [LinearMap.smul_apply, smul_eq_mul, hc.left.mul_left_eq_zero_iff] at hy
      exact hy

/-- Negating a bilinear form preserves nondegeneracy. -/
@[simp]
theorem nondegenerate_neg_iff {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {B : BilinForm R M} :
    (-B).Nondegenerate ↔ B.Nondegenerate := by
  rw [← neg_one_smul R B]
  exact nondegenerate_smul_iff (isUnit_neg_one : IsUnit (-1 : R)).isRegular

end BilinForm

end TauCeti

namespace Module.Basis

/-- The basis dual to `b` for a nonzero scalar multiple `c • B` of a nondegenerate bilinear form
is `c⁻¹` times the basis dual to `b` for `B`. -/
@[simp]
theorem dualBasis_smul_apply {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (c : K) (hc : c ≠ 0) (i : ι) :
    LinearMap.BilinForm.dualBasis (c • B)
        ((TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hc)).mpr hB) b i =
      c⁻¹ • LinearMap.BilinForm.dualBasis B hB b i := by
  let hBc : (c • B).Nondegenerate :=
    (TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hc)).mpr hB
  apply LinearMap.ker_eq_bot.mp hBc.ker_eq_bot
  apply b.ext
  intro j
  simp only [map_smul]
  rw [LinearMap.BilinForm.apply_dualBasis_left]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [LinearMap.BilinForm.apply_dualBasis_left]
  split_ifs
  · simp only [mul_one, inv_mul_cancel₀ hc]
  · simp only [mul_zero]

end Module.Basis
