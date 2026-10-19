/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Normalized fractions and change of coefficients

A rational function has a unique relatively prime numerator and monic denominator. Consequently,
an embedding of coefficient fields carries its normalized numerator and denominator to those of
the image. These compatibility results allow invariance of a rational function to be checked on
its polynomial coefficients.
-/

public section

open Polynomial
open scoped nonZeroDivisors

namespace RatFunc

variable {F K : Type*} [Field F] [Field K]

/-- A relatively prime numerator and monic denominator are the normalized fraction of a rational
function. -/
theorem num_denom_eq_of_isCoprime_of_monic {z : RatFunc K} {p q : K[X]}
    (hpq : IsCoprime p q) (hq : q.Monic)
    (hz : z = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) :
    z.num = p ∧ z.denom = q := by
  have hcross := (num_mul_eq_mul_denom_iff hq.ne_zero).2 hz
  have hq_dvd : q ∣ z.denom :=
    hpq.symm.dvd_of_dvd_mul_left ⟨z.num, by simpa [mul_comm] using hcross.symm⟩
  have hdenom : z.denom = q := Polynomial.eq_of_monic_of_associated (monic_denom z) hq
    (associated_of_dvd_dvd ((denom_dvd hq.ne_zero).2 ⟨p, hz⟩) hq_dvd)
  exact ⟨mul_right_cancel₀ hq.ne_zero (hdenom ▸ hcross), hdenom⟩

/-- Embedding the coefficient field commutes with taking the normalized numerator. -/
@[simp]
theorem num_mapRingHom (f : F →+* K)
    (h : F[X]⁰ ≤ K[X]⁰.comap (Polynomial.mapRingHom f)) (z : RatFunc F) :
    (mapRingHom (Polynomial.mapRingHom f) h z).num = z.num.map f := by
  apply (num_denom_eq_of_isCoprime_of_monic
    ((isCoprime_num_denom z).map (Polynomial.mapRingHom f)) ((monic_denom z).map f) ?_).1
  rw [coe_mapRingHom_eq_coe_map]
  exact map_apply (Polynomial.mapRingHom f) h z

/-- Embedding the coefficient field commutes with taking the monic denominator. -/
@[simp]
theorem denom_mapRingHom (f : F →+* K)
    (h : F[X]⁰ ≤ K[X]⁰.comap (Polynomial.mapRingHom f)) (z : RatFunc F) :
    (mapRingHom (Polynomial.mapRingHom f) h z).denom = z.denom.map f := by
  apply (num_denom_eq_of_isCoprime_of_monic
    ((isCoprime_num_denom z).map (Polynomial.mapRingHom f)) ((monic_denom z).map f) ?_).2
  rw [coe_mapRingHom_eq_coe_map]
  exact map_apply (Polynomial.mapRingHom f) h z

end RatFunc

end
