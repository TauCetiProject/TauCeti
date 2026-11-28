/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.RingTheory.IntegralDomain

/-!
# Character sums averaged over subgroup translates

Averaging a character over a coset of a finite subgroup annihilates it unless its restriction
is trivial. Averaging a weighted character sum over translates of a finite subset of that
subgroup therefore keeps just the characters trivial on the subgroup. The cardinality of the
subset is the surviving multiplicity. The translating coset representative may differ by
summand, as in sums over a family of cosets. Neither normality nor finiteness of the ambient
group is required.

For conjugated complex character sums, compose the characters with complex conjugation; this
leaves the condition of being trivial on the subgroup unchanged. This is the form used to average
the thick-place contribution in Levent Alpöge's `Deduction.CharacterBalanceMoves.core`.
-/

public section

open scoped BigOperators

namespace MonoidHom

variable {G 𝕜 : Type*} [Group G] [CommRing 𝕜] [IsDomain 𝕜] [Algebra ℚ≥0 𝕜]

open scoped Classical in
/-- The mean of a character on a left coset `gH` is its value at `g` if its restriction to
`H` is trivial, and is zero otherwise. -/
theorem expect_apply_mul_eq_ite (χ : G →* 𝕜) (H : Subgroup G) [Fintype H] (g : G) :
    (𝔼 u : H, χ (g * u)) = if χ.comp H.subtype = 1 then χ g else 0 := by
  classical
  simp_rw [map_mul, ← Finset.mul_expect, ← Subgroup.subtype_apply, ← MonoidHom.comp_apply]
  split_ifs with h
  · simp [h]
  · rw [Finset.expect, sum_hom_units_eq_zero (χ.comp H.subtype) h, smul_zero, mul_zero]

end MonoidHom

namespace Subgroup

open scoped Classical in
/-- The mean over `u ∈ H` of the weighted character sums on `g i * u * T` projects onto the
characters trivial on `H`. Each retained summand is counted `T.card` times. -/
theorem expect_sum_sum_mul_apply_mul_eq_card_mul_sum_filter {G 𝕜 ι : Type*} [Group G]
    [CommRing 𝕜] [IsDomain 𝕜] [Algebra ℚ≥0 𝕜] (H : Subgroup G) [Fintype H] (T : Finset H)
    (I : Finset ι) (χ : ι → G →* 𝕜) (c : ι → 𝕜) (g : ι → G) :
    (𝔼 u : H, ∑ t ∈ T, ∑ i ∈ I, c i * χ i (g i * u * t)) =
      (T.card : 𝕜) * ∑ i ∈ I.filter (fun i ↦ (χ i).comp H.subtype = 1), c i * χ i (g i) := by
  classical
  simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect, mul_assoc (g _) _ _]
  simp_rw [← Subgroup.coe_mul]
  have h (i : ι) (t : H) : (𝔼 u : H, χ i (g i * (↑(u * t) : G))) =
      if (χ i).comp H.subtype = 1 then χ i (g i) else 0 :=
    (Fintype.expect_equiv (Equiv.mulRight t) _ (fun u : H ↦ χ i (g i * u))
      fun _ ↦ rfl).trans
      ((χ i).expect_apply_mul_eq_ite H (g i))
  simp_rw [h, mul_ite, mul_zero, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]

end Subgroup
