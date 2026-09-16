/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Integral elements fixed by the absolute Galois group

An algebraic integer in an algebraic closure of `ℚ` that is fixed by every `ℚ`-automorphism is
the image of a rational integer. This combines the fixed-field theorem for the algebraic closure
with the fact that `ℤ` is integrally closed in `ℚ`.

## Main result

* `TauCeti.AlgebraicClosure.exists_algebraMap_int_eq_of_isIntegral_of_fixed`: a fixed algebraic
  integer in `AlgebraicClosure ℚ` comes from `ℤ`.
-/

public section

namespace TauCeti.AlgebraicClosure

/-- An algebraic integer in `AlgebraicClosure ℚ` fixed by every `ℚ`-automorphism is the image of
a rational integer. -/
theorem exists_algebraMap_int_eq_of_isIntegral_of_fixed
    {x : _root_.AlgebraicClosure ℚ} (hx : IsIntegral ℤ x)
    (hfix : ∀ τ : Gal(_root_.AlgebraicClosure ℚ/ℚ), τ x = x) :
    ∃ z : ℤ, algebraMap ℤ (_root_.AlgebraicClosure ℚ) z = x := by
  obtain ⟨q, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp <|
    (isIntegral_algHom_iff ((Algebra.ofId ℚ (_root_.AlgebraicClosure ℚ)).restrictScalars ℤ)
      (algebraMap ℚ (_root_.AlgebraicClosure ℚ)).injective).mp hx
  exact ⟨z, IsScalarTower.algebraMap_apply ℤ ℚ (_root_.AlgebraicClosure ℚ) z⟩

end TauCeti.AlgebraicClosure

end
