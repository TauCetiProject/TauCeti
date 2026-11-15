/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Analysis.Complex.Norm

/-!
# Principal ideal norms from Galois conjugates

In a Galois number field, the product of the complex absolute values of the conjugates of
an algebraic integer is the absolute norm of its principal ideal. This combines
`Algebra.norm_eq_prod_automorphisms` with `Ideal.absNorm_span_singleton`.
-/

public section

open NumberField

namespace RingHom

/-- In a Galois number field, the product of the absolute values of the conjugates of an
algebraic integer is the absolute norm of its principal ideal, at any complex embedding. -/
theorem prod_norm_automorphisms_eq_absNorm {K : Type*} [Field K] [NumberField K]
    [IsGalois ℚ K] (φ : K →+* ℂ) (α : 𝓞 K) :
    (∏ σ : Gal(K/ℚ), ‖φ (σ (α : K))‖) = (Ideal.absNorm (Ideal.span {α}) : ℝ) := by
  classical
  calc
    _ = ‖φ (algebraMap ℚ K (Algebra.norm ℚ (α : K)))‖ := by
      rw [Algebra.norm_eq_prod_automorphisms, map_prod, Complex.norm_prod]
    _ = ‖(Algebra.norm ℤ α : ℂ)‖ := by
      rw [← Algebra.coe_norm_int]
      simp
    _ = (Ideal.absNorm (Ideal.span {α}) : ℝ) := by
      rw [Ideal.absNorm_span_singleton, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]

end RingHom
