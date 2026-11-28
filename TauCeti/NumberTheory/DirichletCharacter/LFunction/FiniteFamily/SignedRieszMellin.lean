/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin
import TauCeti.Analysis.Contour.Residue.Germ

/-!
# Poles of signed Dirichlet Riesz Mellin sums

In the signed sum for the Legendre-twisted prime remainder, each character contributes its
first Riesz Mellin expression minus that of its twist. At `ρ ≠ 0`, the residue is the
difference of the two total zero multiplicities divided by `ρ * (1 - ρ)`, before division
by the totient of the base modulus. At `ρ = 1` the residue and both multiplicities vanish.
Away from `0`, untwisted zeros cannot cancel where the twists have no zeros, and the
residue at such a real point in the critical strip is nonnegative. This is the sign
condition used in applying the one-sided Landau theorem.

The signed residue calculation is the one used in `New.isPolar_primeRemainder` in
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

namespace TauCeti

open Contour

variable {ι κ : Type*} {M N : ℕ} [NeZero M] [NeZero N]
  {t : Finset ι} {u : Finset κ} {χ : ι → DirichletCharacter ℂ M} {ψ : κ → DirichletCharacter ℂ N}

/-- Away from the origin, the residue of the signed sum is the difference of the two total
zero multiplicities divided by `ρ * (1 - ρ)`. -/
theorem residue_sum_sub_rieszRemainderMellin {ρ : ℂ} (h₀ : ρ ≠ 0) :
    residue ((∑ i ∈ t, rieszRemainderMellin (χ i).LFunction) -
      ∑ i ∈ u, rieszRemainderMellin (ψ i).LFunction) ρ =
      (((∑ i ∈ t, analyticOrderNatAt (χ i).LFunction ρ : ℕ) : ℂ) -
        ((∑ i ∈ u, analyticOrderNatAt (ψ i).LFunction ρ : ℕ) : ℂ)) /
        (ρ * (1 - ρ)) := by
  rw [residue_sub (MeromorphicAt.sum fun _ _ ↦ meromorphicAt_rieszRemainderMellin _ _)
    (MeromorphicAt.sum fun _ _ ↦ meromorphicAt_rieszRemainderMellin _ _),
    residue_sum t (fun _ _ ↦ meromorphicAt_rieszRemainderMellin _ _),
    residue_sum u (fun _ _ ↦ meromorphicAt_rieszRemainderMellin _ _)]
  simp only [DirichletCharacter.residue_rieszRemainderMellin_LFunction _ h₀,
    Nat.cast_sum, sub_div, Finset.sum_div]

/-- The signed sum has a pole away from the origin exactly where the two total zero
multiplicities differ. -/
@[simp] theorem meromorphicOrderAt_sum_sub_rieszRemainderMellin_neg_iff {ρ : ℂ} (h₀ : ρ ≠ 0) :
    meromorphicOrderAt ((∑ i ∈ t, rieszRemainderMellin (χ i).LFunction) -
      ∑ i ∈ u, rieszRemainderMellin (ψ i).LFunction) ρ < 0 ↔
      (∑ i ∈ t, analyticOrderNatAt (χ i).LFunction ρ) ≠
        ∑ i ∈ u, analyticOrderNatAt (ψ i).LFunction ρ := by
  rw [meromorphicOrderAt_lt_zero_iff_residue_ne_zero
    ((MeromorphicAt.sum fun _ _ ↦ meromorphicAt_rieszRemainderMellin _ _).sub
      (MeromorphicAt.sum fun _ _ ↦ meromorphicAt_rieszRemainderMellin _ _))
    (neg_one_le_meromorphicOrderAt_sum_sub_rieszRemainderMellin
      (fun i _ ↦ (χ i).meromorphic_LFunction) (fun i _ ↦ (ψ i).meromorphic_LFunction) h₀),
    residue_sum_sub_rieszRemainderMellin h₀]
  by_cases h₁ : ρ = 1
  · subst ρ
    simp
  · have hden := mul_ne_zero h₀ (sub_ne_zero.mpr (Ne.symm h₁))
    rw [div_ne_zero_iff, and_iff_left hden, sub_ne_zero]
    exact not_congr Nat.cast_inj

/-- At a positive real point the residue has nonnegative real part exactly when the second
family's total zero multiplicity there is at most the first family's. -/
theorem residue_sum_sub_rieszRemainderMellin_re_nonneg_iff {β : ℝ} (hβ : 0 < β) :
    0 ≤ (residue ((∑ i ∈ t, rieszRemainderMellin (χ i).LFunction) -
      ∑ i ∈ u, rieszRemainderMellin (ψ i).LFunction) β).re ↔
      (∑ i ∈ u, analyticOrderNatAt (ψ i).LFunction β) ≤
        ∑ i ∈ t, analyticOrderNatAt (χ i).LFunction β := by
  rw [residue_sum_sub_rieszRemainderMellin (Complex.ofReal_ne_zero.mpr hβ.ne')]
  by_cases hβ₁ : 1 ≤ β
  · simp [hβ₁]
  · simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [le_div_iff₀ (mul_pos hβ (sub_pos.mpr (lt_of_not_ge hβ₁))), zero_mul, sub_nonneg]
    exact Nat.cast_le

end TauCeti
