/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification

/-!
# The absolute different of a cyclotomic extension

The cyclotomic level times the extension of the base different is contained in the
absolute different. In particular, the level times the absolute discriminant of the
base gives a positive rational integer in the absolute different when the level is
positive. This supplies an integer in the different for short-basis estimates.

The application to a cyclotomic extension of an imaginary quadratic field uses the
integer `q₁ * d` in the short-source-form argument of `New.Data.span_isShort_eq_top`
in `grh/src/New/UpperBound/Size/ShortColumns.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open NumberField

namespace IsCyclotomicExtension

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  (n : ℕ) [IsCyclotomicExtension {n} K E]

/-- In a cyclotomic extension of level `n`, multiplying the extended base different
by `n` gives an ideal contained in the absolute different of the extension. -/
theorem span_natCast_mul_map_differentIdeal_le :
    Ideal.span {(n : 𝓞 E)} * Ideal.map (algebraMap (𝓞 K) (𝓞 E)) (differentIdeal ℤ (𝓞 K)) ≤
      differentIdeal ℤ (𝓞 E) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 E)]
  apply Ideal.mul_mono_left
  rw [Ideal.span_singleton_le_iff_mem]
  exact natCast_mem_differentIdeal K E n

/-- The product of the level and the absolute value of the base discriminant belongs
to the absolute different of a cyclotomic extension. No coprimality is required. -/
theorem natCast_mul_natAbs_discr_mem_differentIdeal :
    ((n * (discr K).natAbs : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := by
  have hbase := (differentIdeal ℤ (𝓞 K)).absNorm_mem
  rw [absNorm_differentIdeal K (𝓞 K)] at hbase
  have h := Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton (n : 𝓞 E)))
    (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 E)) hbase)
  exact span_natCast_mul_map_differentIdeal_le K E n
    (by simpa only [Nat.cast_mul, map_natCast] using h)

end IsCyclotomicExtension
