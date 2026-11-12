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

/-- For relatively prime `p` and monic `q`, the normalized numerator and denominator of a rational
function are `p` and `q` exactly when it equals `p / q`. -/
theorem num_eq_and_denom_eq_iff_eq_div {z : RatFunc K} {p q : K[X]}
    (hpq : IsCoprime p q) (hq : q.Monic) :
    z.num = p ∧ z.denom = q ↔
      z = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q := by
  refine ⟨fun ⟨rfl, rfl⟩ ↦ (num_div_denom z).symm, fun hz ↦ ?_⟩
  have hcross := (num_mul_eq_mul_denom_iff hq.ne_zero).2 hz
  have hdenom : z.denom = q := eq_of_monic_of_associated (monic_denom z) hq <|
    associated_of_dvd_dvd ((denom_dvd hq.ne_zero).2 ⟨p, hz⟩)
      (hpq.symm.dvd_of_dvd_mul_left (hcross ▸ dvd_mul_left q z.num))
  exact ⟨mul_right_cancel₀ hq.ne_zero (hdenom ▸ hcross), hdenom⟩

/-- Embedding the coefficient field commutes with taking the normalized numerator. -/
@[simp]
theorem num_mapRingHom (f : F →+* K)
    (h : F[X]⁰ ≤ K[X]⁰.comap (Polynomial.mapRingHom f)) (z : RatFunc F) :
    (mapRingHom (Polynomial.mapRingHom f) h z).num = z.num.map f := by
  refine ((num_eq_and_denom_eq_iff_eq_div ((isCoprime_num_denom z).map (Polynomial.mapRingHom f))
    ((monic_denom z).map f)).2 ?_).1
  rw [coe_mapRingHom_eq_coe_map, map_apply, Polynomial.coe_mapRingHom]

/-- Embedding the coefficient field commutes with taking the monic denominator. -/
@[simp]
theorem denom_mapRingHom (f : F →+* K)
    (h : F[X]⁰ ≤ K[X]⁰.comap (Polynomial.mapRingHom f)) (z : RatFunc F) :
    (mapRingHom (Polynomial.mapRingHom f) h z).denom = z.denom.map f := by
  refine ((num_eq_and_denom_eq_iff_eq_div ((isCoprime_num_denom z).map (Polynomial.mapRingHom f))
    ((monic_denom z).map f)).2 ?_).2
  rw [coe_mapRingHom_eq_coe_map, map_apply, Polynomial.coe_mapRingHom]

end RatFunc

end
