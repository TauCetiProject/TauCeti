/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries

/-!
# Primitives of formal Laurent series

Termwise integration gives a primitive of a Laurent series with coefficients in a `ℚ`-module
exactly when its coefficient of exponent `-1` vanishes. Negative exponents are included: the
only obstruction is the logarithmic term `X⁻¹`. The primitive is normalized to have constant
coefficient zero, and every other primitive differs from it by a constant. Integration is linear
over every semiring of scalars acting on the coefficients, like `LaurentSeries.derivative`.

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

variable (R : Type*) {V : Type*} [Semiring R] [AddCommGroup V] [Module R V]

/-- A Laurent monomial at exponent `-1` with a nonzero module coefficient is not exact.
This holds over any semiring of scalars, in any characteristic. -/
theorem single_neg_one_not_mem_range_laurentSeries_derivative {a : V} (ha : a ≠ 0) :
    single (-1) a ∉ LinearMap.range (LaurentSeries.derivative R) := by
  rintro ⟨f, hf⟩
  apply ha
  simpa [LaurentSeries.derivative_apply] using
    congrArg (fun g : LaurentSeries V ↦ g.coeff (-1)) hf.symm

variable [Module ℚ V]

/-- Termwise integration with constant coefficient zero. The coefficient at exponent `n` is
`(n : ℚ)⁻¹ • f.coeff (n - 1)`. Since `(0 : ℚ)⁻¹ = 0`, this discards the residue term; the result
is a primitive precisely when that residue vanishes. -/
noncomputable def laurentSeriesPrimitive : LaurentSeries V →ₗ[R] LaurentSeries V where
  toFun f := ofSuppBddBelow (fun n : ℤ ↦ (n : ℚ)⁻¹ • f.coeff (n - 1)) <| by
    refine ⟨f.order + 1, fun n hn ↦ ?_⟩
    contrapose! hn
    simp [Function.mem_support, coeff_eq_zero_of_lt_order (by omega : n - 1 < f.order)]
  map_add' f g := by
    ext n
    simp [ofSuppBddBelow]
  map_smul' c f := by
    ext n
    simp only [ofSuppBddBelow, coeff_smul, RingHom.id_apply]
    -- Rational scalars commute with every distributive action on a `ℚ`-module.
    exact smul_comm _ _ _

/-- The coefficients of termwise integration, including the zero constant coefficient. -/
@[simp]
theorem coeff_laurentSeriesPrimitive (f : LaurentSeries V) (n : ℤ) :
    (laurentSeriesPrimitive R f).coeff n = (n : ℚ)⁻¹ • f.coeff (n - 1) := (rfl)

/-- Integration of a Laurent monomial. For exponent `-1` the result is zero. -/
@[simp]
theorem laurentSeriesPrimitive_single (n : ℤ) (a : V) :
    laurentSeriesPrimitive R (single n a) = single (n + 1) (((n : ℚ) + 1)⁻¹ • a) := by
  ext m
  by_cases h : m = n + 1
  · subst m
    simp
  · have h' : m - 1 ≠ n := by omega
    simp [h, h']

/-- Differentiating the termwise integral removes exactly the residue term.
The priority is `high` so that `simp` uses this before Mathlib's simp lemma
`LaurentSeries.derivative_apply` rewrites the outer `derivative R` to `hasseDeriv R 1`. -/
@[simp high]
theorem derivative_laurentSeriesPrimitive (f : LaurentSeries V) :
    LaurentSeries.derivative R (laurentSeriesPrimitive R f) =
      f - single (-1) (f.coeff (-1)) := by
  ext n
  by_cases hn : n = -1
  · subst n
    simp [LaurentSeries.derivative_apply]
  · have hcast : (n : ℚ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    simp [LaurentSeries.derivative_apply, hn, ← Int.cast_smul_eq_zsmul ℚ, hcast]

/-- Integrating a derivative removes exactly the constant coefficient. -/
theorem laurentSeriesPrimitive_derivative (f : LaurentSeries V) :
    laurentSeriesPrimitive R (LaurentSeries.derivative R f) = f - single 0 (f.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hcast : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
    simp [LaurentSeries.derivative_apply, hn, ← Int.cast_smul_eq_zsmul ℚ, hcast]

/-- A residue-zero Laurent series is the derivative of its normalized termwise integral. -/
theorem derivative_laurentSeriesPrimitive_of_coeff_neg_one_eq_zero
    {f : LaurentSeries V} (hf : f.coeff (-1) = 0) :
    LaurentSeries.derivative R (laurentSeriesPrimitive R f) = f := by
  rw [derivative_laurentSeriesPrimitive]
  simp [hf]

/-- The derivative image consists exactly of the residue-zero Laurent series.
The priority is `high` so that `simp` uses this before the generic `LinearMap.mem_range`. -/
@[simp high]
theorem mem_range_laurentSeries_derivative_iff (f : LaurentSeries V) :
    f ∈ LinearMap.range (LaurentSeries.derivative R) ↔ f.coeff (-1) = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    simp [LaurentSeries.derivative_apply]
  · intro hf
    exact ⟨laurentSeriesPrimitive R f,
      derivative_laurentSeriesPrimitive_of_coeff_neg_one_eq_zero R hf⟩

/-- The derivative image is the kernel of the residue coefficient linear map. -/
theorem range_laurentSeries_derivative :
    LinearMap.range (LaurentSeries.derivative R) =
      LinearMap.ker (HahnSeries.coeff.linearMap (-1) : LaurentSeries V →ₗ[R] V) := by
  ext f
  rw [mem_range_laurentSeries_derivative_iff, LinearMap.mem_ker]
  simp

/-- Every primitive is the normalized termwise integral plus its own constant coefficient. -/
theorem eq_laurentSeriesPrimitive_add_single_of_derivative_eq
    {f g : LaurentSeries V} (hg : LaurentSeries.derivative R g = f) :
    g = laurentSeriesPrimitive R f + single 0 (g.coeff 0) := by
  rw [← hg, laurentSeriesPrimitive_derivative]
  simp

/-- All primitives of a residue-zero series differ from the normalized primitive by a constant. -/
theorem derivative_eq_iff_eq_laurentSeriesPrimitive_add_single
    {f g : LaurentSeries V} (hf : f.coeff (-1) = 0) :
    LaurentSeries.derivative R g = f ↔
      ∃ c : V, g = laurentSeriesPrimitive R f + single 0 c := by
  constructor
  · intro hg
    exact ⟨g.coeff 0, eq_laurentSeriesPrimitive_add_single_of_derivative_eq R hg⟩
  · rintro ⟨c, rfl⟩
    rw [map_add, derivative_laurentSeriesPrimitive_of_coeff_neg_one_eq_zero R hf]
    simp

/-- A residue-zero Laurent series has a unique primitive with constant coefficient zero. -/
theorem existsUnique_laurentSeries_primitive (f : LaurentSeries V) (hf : f.coeff (-1) = 0) :
    ∃! g : LaurentSeries V, LaurentSeries.derivative R g = f ∧ g.coeff 0 = 0 := by
  refine ⟨laurentSeriesPrimitive R f, ⟨?_, by simp⟩, ?_⟩
  · exact derivative_laurentSeriesPrimitive_of_coeff_neg_one_eq_zero R hf
  · intro g hg
    simpa [hg.2] using eq_laurentSeriesPrimitive_add_single_of_derivative_eq R hg.1

end TauCeti
