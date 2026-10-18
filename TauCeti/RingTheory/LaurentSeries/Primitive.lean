/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries

/-!
# Primitives of formal Laurent series

Termwise integration gives a primitive of a Laurent series over a characteristic-zero field
exactly when its coefficient of exponent `-1` vanishes. Negative exponents are included: the
only obstruction is the logarithmic term `X⁻¹`. The primitive is normalized to have constant
coefficient zero, and every other primitive differs from it by a constant.

A formal one-form is written `f dX`; its residue is `f.coeff (-1)`. We use the existing
coefficient linear map rather than introducing a separate residue operation. The derivative
image is its kernel. The two integration identities also describe integration on arbitrary
series, by removing the residue term, and integration of derivatives, by removing the constant.

The construction uses Mathlib's `HahnSeries.ofSuppBddBelow` and
`LaurentSeries.derivative`; it introduces no new differentiation operation.
-/

public section

open HahnSeries

namespace TauCeti

variable (K : Type*) [Field K]

/-- Termwise integration with constant coefficient zero. The coefficient at exponent `n` is
`f.coeff (n - 1) / n`. Division by zero discards the residue term; in characteristic zero,
this is a primitive precisely when that residue vanishes. -/
noncomputable def laurentSeriesPrimitive : LaurentSeries K →ₗ[K] LaurentSeries K where
  toFun f := ofSuppBddBelow (fun n : ℤ ↦ f.coeff (n - 1) / (n : K)) <| by
    refine ⟨f.order + 1, fun n hn ↦ ?_⟩
    contrapose! hn
    simp [Function.mem_support, coeff_eq_zero_of_lt_order (by omega : n - 1 < f.order)]
  map_add' f g := by
    ext n
    simp [ofSuppBddBelow, add_div]
  map_smul' c f := by
    ext n
    simp [ofSuppBddBelow, mul_div_assoc]

/-- The coefficients of termwise integration, including the zero constant coefficient. -/
@[simp]
theorem coeff_laurentSeriesPrimitive (f : LaurentSeries K) (n : ℤ) :
    (laurentSeriesPrimitive K f).coeff n = f.coeff (n - 1) / (n : K) := (rfl)

/-- Integration of a Laurent monomial. For exponent `-1` the result is zero. -/
@[simp]
theorem laurentSeriesPrimitive_single (n : ℤ) (a : K) :
    laurentSeriesPrimitive K (single n a) = single (n + 1) (a / ((n + 1 : ℤ) : K)) := by
  ext m
  by_cases h : m = n + 1
  · subst m
    simp
  · have h' : m - 1 ≠ n := by omega
    simp [h, h']

/-- A nonzero multiple of `X⁻¹ dX` is not exact, in any characteristic. -/
theorem single_neg_one_not_mem_range_laurentSeries_derivative {a : K} (ha : a ≠ 0) :
    single (-1) a ∉ LinearMap.range (LaurentSeries.derivative K) := by
  rintro ⟨f, hf⟩
  apply ha
  simpa [LaurentSeries.derivative_apply] using
    congrArg (fun g : LaurentSeries K ↦ g.coeff (-1)) hf.symm

variable [CharZero K]

/-- Differentiating the termwise integral removes exactly the residue term. -/
theorem derivative_laurentSeriesPrimitive (f : LaurentSeries K) :
    LaurentSeries.derivative K (laurentSeriesPrimitive K f) =
      f - single (-1) (f.coeff (-1)) := by
  ext n
  by_cases hn : n = -1
  · subst n
    simp [LaurentSeries.derivative_apply]
  · have h : n + 1 ≠ 0 := by omega
    have hcast : (n : K) + 1 ≠ 0 := by exact_mod_cast h
    simp [LaurentSeries.derivative_apply, hn, mul_div_cancel₀ _ hcast]

/-- Integrating a derivative removes exactly the constant coefficient. -/
theorem laurentSeriesPrimitive_derivative (f : LaurentSeries K) :
    laurentSeriesPrimitive K (LaurentSeries.derivative K f) = f - single 0 (f.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hcast : (n : K) ≠ 0 := Int.cast_ne_zero.mpr hn
    simp [LaurentSeries.derivative_apply, hn, hcast]

/-- A residue-zero Laurent series is the derivative of its normalized termwise integral. -/
theorem derivative_laurentSeriesPrimitive_of_coeff_neg_one_eq_zero
    {f : LaurentSeries K} (hf : f.coeff (-1) = 0) :
    LaurentSeries.derivative K (laurentSeriesPrimitive K f) = f := by
  rw [derivative_laurentSeriesPrimitive]
  simp [hf]

/-- The derivative image consists exactly of the residue-zero Laurent series. -/
theorem mem_range_laurentSeries_derivative_iff (f : LaurentSeries K) :
    f ∈ LinearMap.range (LaurentSeries.derivative K) ↔ f.coeff (-1) = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    simp [LaurentSeries.derivative_apply]
  · intro hf
    exact ⟨laurentSeriesPrimitive K f,
      derivative_laurentSeriesPrimitive_of_coeff_neg_one_eq_zero K hf⟩

/-- The derivative image is the kernel of the residue coefficient linear map. -/
theorem range_laurentSeries_derivative :
    LinearMap.range (LaurentSeries.derivative K) =
      LinearMap.ker (HahnSeries.coeff.linearMap (-1) : LaurentSeries K →ₗ[K] K) := by
  ext f
  rw [mem_range_laurentSeries_derivative_iff]
  rfl

/-- Every primitive is the normalized termwise integral plus its own constant coefficient. -/
theorem eq_laurentSeriesPrimitive_add_single_of_derivative_eq
    {f g : LaurentSeries K} (hg : LaurentSeries.derivative K g = f) :
    g = laurentSeriesPrimitive K f + single 0 (g.coeff 0) := by
  rw [← hg, laurentSeriesPrimitive_derivative]
  simp

/-- All primitives of a residue-zero series differ from the normalized primitive by a constant. -/
theorem derivative_eq_iff_eq_laurentSeriesPrimitive_add_single
    {f g : LaurentSeries K} (hf : f.coeff (-1) = 0) :
    LaurentSeries.derivative K g = f ↔
      ∃ c : K, g = laurentSeriesPrimitive K f + single 0 c := by
  constructor
  · intro hg
    exact ⟨g.coeff 0, eq_laurentSeriesPrimitive_add_single_of_derivative_eq K hg⟩
  · rintro ⟨c, rfl⟩
    rw [map_add, derivative_laurentSeriesPrimitive_of_coeff_neg_one_eq_zero K hf]
    simp

/-- A residue-zero Laurent series has a unique primitive with constant coefficient zero. -/
theorem existsUnique_laurentSeries_primitive (f : LaurentSeries K) (hf : f.coeff (-1) = 0) :
    ∃! g : LaurentSeries K, LaurentSeries.derivative K g = f ∧ g.coeff 0 = 0 := by
  refine ⟨laurentSeriesPrimitive K f, ⟨?_, by simp⟩, ?_⟩
  · exact derivative_laurentSeriesPrimitive_of_coeff_neg_one_eq_zero K hf
  · intro g hg
    simpa [hg.2] using eq_laurentSeriesPrimitive_add_single_of_derivative_eq K hg.1

end TauCeti
