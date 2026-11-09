/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Basic
public import TauCeti.RingTheory.Norm.Quadratic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.NormNum.IsSquare

/-!
# Quadratic norm equations over number fields

For a nonsquare `d` in a number field `K`, the equation `a = x² - d y²`, with `a ≠ 0`, has a
solution in `K` exactly when it has a solution in every finite and infinite completion of `K`.
This is the cyclic Hasse norm theorem for `K(√d)/K`, expressed in coordinates.

The local algebras are the scalar extensions `K_v ⊗[K] K(√d)`. In particular a split place
still uses the two-dimensional split algebra, rather than a field incorrectly assumed to have
degree two. The norm calculation in these algebras is
`TauCeti.Algebra.mem_range_normUnits_baseChange_iff_exists_sq_sub_mul_sq`.

`exists_sq_sub_five_mul_sq_iff_forall_completion` gives the explicit equation `a = x² - 5y²`
over `ℚ` and its completions.
Infinite places remain in the statement, including complex places for a general number field.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §4 (the cyclic Hasse norm theorem).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §2.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-- For a nonsquare `d` in a number field, solvability of the nonzero quadratic norm equation
`a = x² - d y²` is detected by all finite and infinite completions. -/
theorem exists_sq_sub_mul_sq_iff_forall_completion {d : K}
    (hd : ¬ IsSquare d) (a : Kˣ) :
    (∃ x y : K, (a : K) = x ^ 2 - d * y ^ 2) ↔
      (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K,
        algebraMap K (v.adicCompletion K) (a : K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) d * y ^ 2) ∧
      ∀ w : InfinitePlace K, ∃ x y : w.Completion,
        algebraMap K w.Completion (a : K) =
          x ^ 2 - algebraMap K w.Completion d * y ^ 2 := by
  have : Fact (¬ IsSquare d) := ⟨hd⟩
  have : NumberField (QuadraticAlgebra K d 0) := NumberField.of_module_finite K _
  have : Algebra.IsQuadraticExtension K (QuadraticAlgebra K d 0) :=
    ⟨QuadraticAlgebra.finrank_eq_two d 0⟩
  have hθ : (QuadraticAlgebra.omega : QuadraticAlgebra K d 0) ∉
      Set.range (algebraMap K (QuadraticAlgebra K d 0)) := by
    rintro ⟨x, hx⟩
    have := congrArg QuadraticAlgebra.im hx
    simp at this
  have hθ2 : (QuadraticAlgebra.omega : QuadraticAlgebra K d 0) ^ 2 =
      algebraMap K (QuadraticAlgebra K d 0) d := by
    simp [QuadraticAlgebra.omega_pow_two_eq_add, Algebra.algebraMap_eq_smul_one]
  rw [← mem_normGroup_iff_exists_sq_sub_mul_sq _ hθ hθ2,
    isGlobalNorm_iff_isLocalNormEverywhere K _, GlobalNumberFields.isLocalNormEverywhere_def]
  simp only [GlobalNumberFields.isFiniteLocalNorm_def,
    GlobalNumberFields.isInfiniteLocalNorm_def,
    Algebra.mem_range_normUnits_baseChange_iff_exists_sq_sub_mul_sq _ hθ hθ2,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

/-- **The Hasse norm test for `ℚ(√5)`.** A nonzero rational is a value of `x² - 5y²` over `ℚ`
exactly when it is a value over every finite and infinite completion of `ℚ`. -/
theorem exists_sq_sub_five_mul_sq_iff_forall_completion (a : ℚˣ) :
    (∃ x y : ℚ, (a : ℚ) = x ^ 2 - 5 * y ^ 2) ↔
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ x y : v.adicCompletion ℚ,
        algebraMap ℚ (v.adicCompletion ℚ) (a : ℚ) = x ^ 2 - 5 * y ^ 2) ∧
      ∀ w : InfinitePlace ℚ, ∃ x y : w.Completion,
        algebraMap ℚ w.Completion (a : ℚ) = x ^ 2 - 5 * y ^ 2 := by
  simpa using exists_sq_sub_mul_sq_iff_forall_completion
    (K := ℚ) (d := 5) (by norm_num) a

end TauCeti.ClassFieldTheory
