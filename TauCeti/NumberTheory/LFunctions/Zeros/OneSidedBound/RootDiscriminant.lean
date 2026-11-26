/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootDiscriminant
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
import TauCeti.NumberTheory.NumberField.Quadratic.Model

/-!
# The root discriminant bound for the cyclotomic tower

Over the imaginary quadratic field of discriminant `-d`, the cyclotomic extension of level
`q₁` has root discriminant at most `q₁ √d`. In particular `1 ≤ rd_E ≤ q₁ d`, the bounds needed
when comparing the scale of an auxiliary prime level to the weights and principal level.

The latter estimate is `New.rootDiscr_mem_Icc` in lsernau/grh-lean,
`New/Reduction/Data/AdmissibleData.lean` at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open NumberField

namespace TauCeti.OneSidedBound.Parameters

/-- The root discriminant of `ℚ(√−d, ζ_(q₁(s)))` is between `1` and `q₁(s) · d`. -/
theorem rootDiscr_mem_Icc (P : Parameters) (s : ℕ) (E : Type*)
    [Field E] [NumberField E] [Algebra (QuadraticAlgebra ℚ (Int.cast (-(P.d : ℤ))) 0) E]
    [IsCyclotomicExtension {P.q₁ s} (QuadraticAlgebra ℚ (Int.cast (-(P.d : ℤ))) 0) E] :
    rootDiscr E ∈ Set.Icc 1 ((P.q₁ s : ℝ) * P.d) := by
  have : NeZero P.d := ⟨P.prime_d.ne_zero⟩
  have hsf : Squarefree (-(P.d : ℤ)) := by
    exact Int.squarefree_natAbs.mp (by simpa using P.prime_d.squarefree)
  have hd4 : (-(P.d : ℤ)) % 4 = 1 := by
    have := P.d_mod_eight
    omega
  have h := IsCyclotomicExtension.rootDiscr_mem_Icc
    (QuadraticAlgebra ℚ (Int.cast (-(P.d : ℤ))) 0) E (P.q₁_pos s)
  have hb : rootDiscr (QuadraticAlgebra ℚ (Int.cast (-(P.d : ℤ))) 0) = √(P.d : ℝ) := by
    rw [rootDiscr_def, QuadraticAlgebra.discr_eq_of_mod_four_eq_one hsf hd4,
      QuadraticAlgebra.finrank_eq_two]
    simp [Real.sqrt_eq_rpow, one_div]
  have hd : (1 : ℝ) ≤ P.d := by exact_mod_cast P.prime_d.one_lt.le
  refine ⟨TauCeti.NumberField.one_le_rootDiscr E, ?_⟩
  rw [hb, mul_comm] at h
  exact le_trans h.2 <| mul_le_mul_of_nonneg_left
    (Real.sqrt_le_self_iff.mpr (Or.inr hd)) (Nat.cast_nonneg _)

end TauCeti.OneSidedBound.Parameters
