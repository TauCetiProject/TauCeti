/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootDiscriminant
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
import TauCeti.NumberTheory.NumberField.Discriminant.RootDiscr
import TauCeti.NumberTheory.NumberField.Quadratic.Model

/-!
# The root discriminant bound for the cyclotomic tower

Let `K` be a number field of discriminant `-d`, such as the imaginary quadratic field `ℚ(√-d)`
(`discr_quadraticAlgebra`), and `E` its cyclotomic extension of level `q₁`. The root
discriminant of `K` is at most `√d` (`TauCeti.NumberField.rootDiscr_le_sqrt_abs_discr`), so
`rd_E ≤ q₁ √d` (`rootDiscr_le_mul_sqrt`) and `1 ≤ rd_E ≤ q₁ d` (`rootDiscr_mem_Icc`), the
bounds needed when comparing the scale of an auxiliary prime level to the weights and principal
level. Stating them for every model of `K` lets them apply to `ℚ(√-d)` realized inside `ℂ` as
well as to `QuadraticAlgebra`.

The latter estimate is `New.rootDiscr_mem_Icc` in lsernau/grh-lean,
`New/Reduction/Data/AdmissibleData.lean` at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open NumberField

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- The quadratic field `ℚ(√-d)` has discriminant `-d`, as `-d ≡ 1 (mod 4)`. -/
theorem discr_quadraticAlgebra :
    discr (QuadraticAlgebra ℚ (Int.cast (-(P.d : ℤ))) 0) = -(P.d : ℤ) := by
  have : NeZero P.d := ⟨P.prime_d.ne_zero⟩
  have hsf : Squarefree (-(P.d : ℤ)) :=
    Int.squarefree_natAbs.mp (by simpa using P.prime_d.squarefree)
  have hd4 : (-(P.d : ℤ)) % 4 = 1 := by
    have := P.d_mod_eight
    omega
  exact QuadraticAlgebra.discr_eq_of_mod_four_eq_one hsf hd4

variable (s : ℕ) {K : Type*} (E : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [IsCyclotomicExtension {P.q₁ s} K E]

/-- Over a number field of discriminant `-d`, such as `ℚ(√-d)`, the cyclotomic extension of level
`q₁(s)` has root discriminant at most `q₁(s) √d`. -/
theorem rootDiscr_le_mul_sqrt (hK : discr K = -(P.d : ℤ)) :
    rootDiscr E ≤ P.q₁ s * √(P.d : ℝ) := by
  have hrd : rootDiscr K ≤ √(P.d : ℝ) := by
    simpa only [hK, Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] using
      TauCeti.NumberField.rootDiscr_le_sqrt_abs_discr K
  refine (IsCyclotomicExtension.rootDiscr_mem_Icc K E (P.q₁_pos s)).2.trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hrd (Nat.cast_nonneg _)

/-- **The root discriminant of `K(ζ_{q₁(s)})`** lies between `1` and `q₁(s) · d` when `K` has
discriminant `-d`. -/
theorem rootDiscr_mem_Icc (hK : discr K = -(P.d : ℤ)) :
    rootDiscr E ∈ Set.Icc 1 ((P.q₁ s : ℝ) * P.d) := by
  have hd : (1 : ℝ) ≤ P.d := by exact_mod_cast P.prime_d.one_lt.le
  refine ⟨TauCeti.NumberField.one_le_rootDiscr E, (P.rootDiscr_le_mul_sqrt s E hK).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr hd)) (Nat.cast_nonneg _)

end TauCeti.OneSidedBound.Parameters
