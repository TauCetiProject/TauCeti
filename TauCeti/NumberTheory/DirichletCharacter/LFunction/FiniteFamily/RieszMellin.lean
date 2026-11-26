/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.RieszMellin
import TauCeti.Analysis.Contour.Residue.Germ
import TauCeti.Analysis.Meromorphic.Order

/-!
# Poles of signed Dirichlet Riesz Mellin sums

In the signed sum for the Legendre-twisted prime remainder, each character contributes its
first Riesz Mellin expression minus that of its twist. The residue is the difference of the
two total zero multiplicities divided by `ρ * (1 - ρ)`, before division by the totient of
the base modulus. Where the twists have no zeros, the original zeros cannot cancel, and the
residue at a real point of the critical strip is nonnegative. This is the sign condition
used in applying the one-sided Landau theorem.

The signed residue calculation is the one used in `New.isPolar_primeRemainder` in
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open Finset TauCeti TauCeti.Contour

namespace DirichletCharacter

variable {ι : Type*} {M N : ℕ} [NeZero M] [NeZero N]
  {t : Finset ι} {χ : ι → DirichletCharacter ℂ M} {ψ : ι → DirichletCharacter ℂ N}

/-- The difference between two finite sums of Dirichlet Riesz Mellin expressions, with the
same indexing set, has at most a simple pole away from the origin. -/
theorem neg_one_le_meromorphicOrderAt_sum_sub_rieszRemainderMellin {ρ : ℂ} (h₀ : ρ ≠ 0) :
    -1 ≤ meromorphicOrderAt (∑ i ∈ t,
      (rieszRemainderMellin (χ i).LFunction - rieszRemainderMellin (ψ i).LFunction)) ρ := by
  have hm (L : ℂ → ℂ) := (meromorphicNFOn_rieszRemainderMellin L (Set.mem_univ ρ)).meromorphicAt
  apply le_meromorphicOrderAt_sum (fun i _ ↦ (hm _).sub (hm _))
  intro i _
  rw [sub_eq_add_neg]
  refine (le_min ?_ ?_).trans (meromorphicOrderAt_add (hm _) (hm _).neg)
  · exact (χ i).neg_one_le_meromorphicOrderAt_rieszRemainderMellin_LFunction h₀
  · rw [← meromorphicOrderAt_neg (f := rieszRemainderMellin (ψ i).LFunction)]
    exact (ψ i).neg_one_le_meromorphicOrderAt_rieszRemainderMellin_LFunction h₀

/-- Away from the origin, the residue of the signed sum is the difference of the two total
zero multiplicities divided by `ρ * (1 - ρ)`. -/
theorem residue_sum_sub_rieszRemainderMellin {ρ : ℂ} (h₀ : ρ ≠ 0) :
    residue (∑ i ∈ t,
      (rieszRemainderMellin (χ i).LFunction - rieszRemainderMellin (ψ i).LFunction)) ρ =
      (((∑ i ∈ t, analyticOrderNatAt (χ i).LFunction ρ : ℕ) : ℂ) -
        ((∑ i ∈ t, analyticOrderNatAt (ψ i).LFunction ρ : ℕ) : ℂ)) /
        (ρ * (1 - ρ)) := by
  have hm (L : ℂ → ℂ) := (meromorphicNFOn_rieszRemainderMellin L (Set.mem_univ ρ)).meromorphicAt
  rw [residue_sum t (fun i _ ↦ (hm _).sub (hm _))]
  simp only [Nat.cast_sum, sub_div, sum_div]
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun i _ ↦ by
    rw [residue_sub (hm _) (hm _), (χ i).residue_rieszRemainderMellin_LFunction h₀,
      (ψ i).residue_rieszRemainderMellin_LFunction h₀]

/-- The signed sum has a pole away from the origin exactly where the two total zero
multiplicities differ. -/
theorem meromorphicOrderAt_sum_sub_rieszRemainderMellin_neg_iff {ρ : ℂ} (h₀ : ρ ≠ 0) :
    meromorphicOrderAt (∑ i ∈ t,
      (rieszRemainderMellin (χ i).LFunction - rieszRemainderMellin (ψ i).LFunction)) ρ < 0 ↔
      (∑ i ∈ t, analyticOrderNatAt (χ i).LFunction ρ) ≠
        ∑ i ∈ t, analyticOrderNatAt (ψ i).LFunction ρ := by
  have hm (L : ℂ → ℂ) := (meromorphicNFOn_rieszRemainderMellin L (Set.mem_univ ρ)).meromorphicAt
  rw [meromorphicOrderAt_lt_zero_iff_residue_ne_zero
    (MeromorphicAt.sum fun i _ ↦ (hm _).sub (hm _))
    (neg_one_le_meromorphicOrderAt_sum_sub_rieszRemainderMellin h₀),
    residue_sum_sub_rieszRemainderMellin h₀]
  by_cases h₁ : ρ = 1
  · subst ρ
    simp [analyticOrderNatAt_LFunction_eq_zero_of_one_le_re]
  · have hden := mul_ne_zero h₀ (sub_ne_zero.mpr (Ne.symm h₁))
    rw [div_ne_zero_iff, and_iff_left hden, sub_ne_zero]
    exact not_congr Nat.cast_inj

/-- At a positive real point the residue has nonnegative real part exactly when the second
family's total zero multiplicity there is at most the first family's. -/
theorem residue_sum_sub_rieszRemainderMellin_re_nonneg_iff {β : ℝ} (hβ : 0 < β) :
    0 ≤ (residue (∑ i ∈ t,
      (rieszRemainderMellin (χ i).LFunction - rieszRemainderMellin (ψ i).LFunction)) β).re ↔
      (∑ i ∈ t, analyticOrderNatAt (ψ i).LFunction β) ≤
        ∑ i ∈ t, analyticOrderNatAt (χ i).LFunction β := by
  rw [residue_sum_sub_rieszRemainderMellin (Complex.ofReal_ne_zero.mpr hβ.ne')]
  by_cases hβ₁ : 1 ≤ β
  · have hβc : 1 ≤ (β : ℂ).re := by simpa using hβ₁
    have hχ : (∑ i ∈ t, analyticOrderNatAt (χ i).LFunction β) = 0 :=
      sum_eq_zero fun i _ ↦ (χ i).analyticOrderNatAt_LFunction_eq_zero_of_one_le_re hβc
    have hψ : (∑ i ∈ t, analyticOrderNatAt (ψ i).LFunction β) = 0 :=
      sum_eq_zero fun i _ ↦ (ψ i).analyticOrderNatAt_LFunction_eq_zero_of_one_le_re hβc
    simp [hχ, hψ]
  · simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [le_div_iff₀ (mul_pos hβ (sub_pos.mpr (lt_of_not_ge hβ₁))), zero_mul, sub_nonneg]
    exact Nat.cast_le

end DirichletCharacter
