/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.LinearCombination

/-!
# Basic facts about bilinear forms

Away from characteristic two a bilinear form cannot be both symmetric and alternating without
being zero: symmetry and alternation give `B x y = B y x` and `B x y = -B y x`, so `2 * B x y = 0`,
and cancelling the `2` leaves `B x y = 0`.

That cancellation is all the hypothesis on the ring there is: `2` has to be regular, and nothing
is asked of any other element, so the statement covers rings with zero divisors elsewhere.  Over a
field, or over any domain, `IsRegular.of_ne_zero` supplies the hypothesis from `(2 : R) ≠ 0`.

For a nondegenerate symmetric bilinear form over a field, this file also records the two
reconstruction formulas associated to a finite basis and its dual basis.

## Main results

* `TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`: a symmetric alternating form over a ring in which
  `2` is regular is zero.
* `TauCeti.BilinForm.nondegenerate_smul_iff`: scalar multiplication by a regular element
  preserves nondegeneracy.
* `TauCeti.BilinForm.nondegenerate_neg_iff`: negating a bilinear form preserves nondegeneracy.
* `TauCeti.sum_dualBasis_smul_basis`: reconstruction from a basis and its dual.
* `TauCeti.sum_basis_smul_dualBasis`: reconstruction in the dual basis.
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

/-- A vector is reconstructed in a basis by pairing it with the dual basis of a nondegenerate
symmetric bilinear form. -/
theorem sum_dualBasis_smul_basis {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : BilinForm K V) (hB : B.Nondegenerate)
    (hBsymm : B.IsSymm) (b : Module.Basis ι K V) (x : V) :
    ∑ i, B (B.dualBasis hB b i) x • b i = x := by
  let d := B.dualBasis hB b
  calc
    _ = ∑ i, b.repr x i • b i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      calc
        B (d i) x = B x (d i) := hBsymm.eq (d i) x
        _ = (B.dualBasis hB d).repr x i :=
          (LinearMap.BilinForm.dualBasis_repr_apply hB d x i).symm
        _ = b.repr x i := by
          rw [LinearMap.BilinForm.dualBasis_dualBasis hB hBsymm b]
    _ = x := b.sum_repr x

/-- A vector is reconstructed in the dual basis by pairing it with the original basis of a
nondegenerate symmetric bilinear form. -/
theorem sum_basis_smul_dualBasis {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : BilinForm K V) (hB : B.Nondegenerate)
    (hBsymm : B.IsSymm) (b : Module.Basis ι K V) (x : V) :
    ∑ i, B (b i) x • B.dualBasis hB b i = x := by
  let d := B.dualBasis hB b
  calc
    _ = ∑ i, d.repr x i • d i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [LinearMap.BilinForm.dualBasis_repr_apply]
      exact hBsymm.eq (b i) x
    _ = x := d.sum_repr x

end TauCeti
