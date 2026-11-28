/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.Cyclotomic.DifferentSize

/-!
# Uniform placewise size of the different in the prime-sum tower

The quotient of the size of the cyclotomic different generator by `towerDeg s * √d`
is controlled entirely by derivatives at level `q₀`, independently of the tower exponent
and infinite place. This is the factorization used in
`New.Parameters.exists_abs_log_le_and_apply_deltaE_eq` of lsernau/grh-lean (`72fead1`).
-/

public section

open Polynomial NumberField NumberField.IsCMField

namespace TauCeti.OneSidedBound.Parameters

/-- For a generator in cyclotomic-derivative form, the placewise logarithmic error after
removing the scale `towerDeg s * √d` is bounded by the cyclotomic contribution at `q₀`. -/
theorem exists_pos_apply_different_generator (P : Parameters) (s : ℕ) {E : Type*}
    [Field E] [CharZero E] [IsCMField E] [Algebra.IsIntegral ℚ E]
    (v : InfinitePlace E) {ζ u b δ : E}
    (hζ : IsPrimitiveRoot ζ (P.q₁ s)) (hu : u * complexConj E u = 1) (hb : b ^ 2 = -(P.d : E))
    (hδ : δ = u * (cyclotomic (P.q₁ s) E).derivative.eval ζ * b) :
    ∃ A : ℝ, 0 < A ∧ v δ = A * towerDeg s * √(P.d : ℝ) ∧
      |Real.log A| ≤ ∑ w ∈ primitiveRoots P.q₀ ℂ,
        |Real.log ‖(cyclotomic P.q₀ ℂ).derivative.eval w‖| := by
  have hprimes : (towerDeg s).primeFactors ⊆ P.q₀.primeFactors := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    refine Nat.mem_primeFactors.mpr ⟨hpp, P.dvd_q₀_of_dvd_q₁ (s := s) hpp ?_, P.q₀_pos.ne'⟩
    rw [P.q₁_def s]
    exact hpd.trans (dvd_mul_left _ _)
  rw [hδ, P.q₁_def s]
  exact v.exists_pos_apply_cyclotomic_different_generator P.q₀_pos.ne' hprimes
    (by simpa only [P.q₁_def s] using hζ) hu hb

end TauCeti.OneSidedBound.Parameters
