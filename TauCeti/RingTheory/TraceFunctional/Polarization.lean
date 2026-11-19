/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.Algebra.Star.Basic

/-!
# Polarization of tracial maps on complex star rings

On a non-unital complex star ring `A` whose scalar action satisfies `IsScalarTower ℂ A A` and
`StarModule ℂ A` (so `SMulCommClass ℂ A A` holds automatically via
`TauCeti.mul_smul_comm_of_starModule`), a `ℂ`-linear map `f : A → M` into any `ℂ`-module vanishes
on all commutators `a * b - b * a` as soon as it vanishes on self-adjoint commutators, and
vanishes on self-adjoint commutators as soon as `f (star a * a) = f (a * star a)` for every `a : A`.

The first reduction splits `a` and `b` into their Cartesian real and imaginary parts
`a = realPart a + I • imaginaryPart a`; the second evaluates `star_mul_self_sub_self_mul_star` at
`a + I • b` for self-adjoint `a` and `b`, giving
`star (a + I • b) * (a + I • b) - (a + I • b) * star (a + I • b) = (2 * I) • (a * b - b * a)`.

## Main results

* `TauCeti.forall_map_mul_comm_iff_isSelfAdjoint`: `f (a * b) = f (b * a)` for all `a, b` if and
  only if it holds for all self-adjoint `a, b`.
* `TauCeti.forall_map_mul_comm_iff_star_mul_self`: `f (a * b) = f (b * a)` for all `a, b` if and
  only if `f (star a * a) = f (a * star a)` for all `a`.

## References

* G. K. Pedersen, *C⋆-Algebras and Their Automorphism Groups*, second edition, Chapter 3.
-/

public section

open Complex

namespace TauCeti

variable {A M F : Type*} [NonUnitalNonAssocRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [StarModule ℂ A]
  [AddCommGroup M] [Module ℂ M] [FunLike F A M] [LinearMapClass F ℂ A M]

/-- **Cartesian reduction of traciality.** A `ℂ`-linear map out of a complex star ring vanishes on
all commutators if and only if it vanishes on commutators of self-adjoint elements. -/
theorem forall_map_mul_comm_iff_isSelfAdjoint (f : F) :
    (∀ a b : A, f (a * b) = f (b * a)) ↔
      ∀ a b : A, IsSelfAdjoint a → IsSelfAdjoint b → f (a * b) = f (b * a) := by
  have : SMulCommClass ℂ A A := ⟨fun c x y => (mul_smul_comm_of_starModule c x y).symm⟩
  refine ⟨fun h a b _ _ => h a b, fun h a b => ?_⟩
  have hrr := h (realPart a) (realPart b) (realPart a).prop (realPart b).prop
  have hri := h (realPart a) (imaginaryPart b) (realPart a).prop (imaginaryPart b).prop
  have hir := h (imaginaryPart a) (realPart b) (imaginaryPart a).prop (realPart b).prop
  have hii := h (imaginaryPart a) (imaginaryPart b) (imaginaryPart a).prop (imaginaryPart b).prop
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a, ← realPart_add_I_smul_imaginaryPart b]
  conv_rhs => rw [← realPart_add_I_smul_imaginaryPart b, ← realPart_add_I_smul_imaginaryPart a]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul,
    hrr, hri, hir, hii]
  module

/-- **Polarization criterion for traciality.** A `ℂ`-linear map `f` out of a complex star ring
satisfies `f (a * b) = f (b * a)` for all `a, b` if and only if `f (star a * a) = f (a * star a)`
for all `a`. -/
theorem forall_map_mul_comm_iff_star_mul_self (f : F) :
    (∀ a b : A, f (a * b) = f (b * a)) ↔ ∀ a : A, f (star a * a) = f (a * star a) := by
  have : SMulCommClass ℂ A A := ⟨fun c x y => (mul_smul_comm_of_starModule c x y).symm⟩
  rw [forall_map_mul_comm_iff_isSelfAdjoint]
  refine ⟨fun h a => ?_, fun h a b ha hb => ?_⟩
  · have hcomm := star_mul_self_sub_self_mul_star a
    apply sub_eq_zero.mp
    rw [← map_sub, hcomm, map_nsmul, map_smul, map_sub,
      h (realPart a) (imaginaryPart a) (realPart a).prop (imaginaryPart a).prop, sub_self,
      smul_zero, nsmul_zero]
  · -- For self-adjoint `a` and `b`, expand `star c * c - c * star c` at `c = a + I • b`.
    have hpol : star (a + I • b) * (a + I • b) - (a + I • b) * star (a + I • b) =
        (2 * I) • (a * b - b * a) := by
      rw [star_add, star_smul, ha.star_eq, hb.star_eq, star_def, conj_I]
      simp only [add_mul, mul_add, neg_smul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
      module
    have hf0 : (2 * I) • (f (a * b) - f (b * a)) = 0 := by
      rw [← map_sub, ← map_smul, ← hpol, map_sub, h (a + I • b), sub_self]
    have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
    apply sub_eq_zero.mp
    rw [← inv_smul_smul₀ h2I (f (a * b) - f (b * a)), hf0, smul_zero]

end TauCeti
