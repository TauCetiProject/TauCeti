/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.CheegerConstant
public import TauCeti.Combinatorics.CoboundaryExpansion.StarBound

/-!
# Cross-degree star bound on the complete two-complex

This file lifts the star bound `Fintype.card V * α.gaugeDist ℓ ≤ 3 * α.defect ℓ` on `complete V`
to cross-degree cochain distance `Cochain.gaugeDistErr` and the cross-degree Cheeger constant
`TauCeti.h1Err`:

* `TauCeti.Cochain.card_mul_gaugeDistErr_le`: for `2 ≤ n` and any degree-`n` cochain `α` on
  `complete V`, `Fintype.card V * α.gaugeDistErr ≤ 3 * (α.defect (movedNorm (Fin n)) / n)`.
* `TauCeti.Cochain.card_div_three_le_defect_div_gaugeDistErr`: pointwise expansion ratio lower bound
  `(Fintype.card V : ℝ) / 3 ≤ α.defect (movedNorm (Fin n)) / n / α.gaugeDistErr` whenever
  `0 < α.gaugeDistErr` and `2 ≤ n`.
* `TauCeti.card_div_three_le_h1Err_of_exists` and `TauCeti.card_div_three_le_h1Err`: every
  complete complex with `3 ≤ Fintype.card V` satisfies
  `(Fintype.card V : ℝ) / 3 ≤ h1Err (complete V)`.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, Zenodo, doi:10.5281/zenodo.23245792, version 7, Proposition 1 and Corollary 2.
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117,
  Proposition 3.2.
-/

public section

open Finset

namespace TauCeti

open Equiv Equiv.Perm TwoComplex

namespace Cochain

section CrossDegreeStarBound

variable {V : Type*} [Fintype V] {n : ℕ}

/-- Cross-degree star bound in counting form: for `2 ≤ n` and any degree-`n` cochain `α` on
`complete V`, `Fintype.card V * α.gaugeDistErr ≤ 3 * (α.defect (movedNorm (Fin n)) / n)`. -/
theorem card_mul_gaugeDistErr_le [LinearOrder V]
    (α : Cochain (complete V) (Perm (Fin n))) (hn : 2 ≤ n) :
    (Fintype.card V : ℝ) * α.gaugeDistErr ≤ 3 * (α.defect (movedNorm (Fin n)) / n) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hgd : (Fintype.card V : ℝ) * α.gaugeDistErr ≤
      (Fintype.card V : ℝ) * (α.gaugeDist (movedNorm (Fin n)) / n) :=
    mul_le_mul_of_nonneg_left (α.gaugeDistErr_le_gaugeDist_div hn) (Nat.cast_nonneg _)
  have hstar := div_le_div_of_nonneg_right
    (TauCeti.card_mul_gaugeDist_le (movedNorm (Fin n)) isConjInvariant_movedNorm α) hn_pos.le
  calc (Fintype.card V : ℝ) * α.gaugeDistErr
      ≤ (Fintype.card V : ℝ) * (α.gaugeDist (movedNorm (Fin n)) / n) := hgd
    _ = ((Fintype.card V : ℝ) * α.gaugeDist (movedNorm (Fin n))) / n := by ring
    _ ≤ (3 * α.defect (movedNorm (Fin n))) / n := hstar
    _ = 3 * (α.defect (movedNorm (Fin n)) / n) := by ring

/-- Pointwise cross-degree star bound for a degree-`n` cochain (`2 ≤ n`) at positive
`gaugeDistErr`. -/
theorem card_div_three_le_defect_div_gaugeDistErr [LinearOrder V]
    {α : Cochain (complete V) (Perm (Fin n))} (hn : 2 ≤ n) (hα : 0 < α.gaugeDistErr) :
    (Fintype.card V : ℝ) / 3 ≤ α.defect (movedNorm (Fin n)) / n / α.gaugeDistErr := by
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hα, mul_comm _ (3 : ℝ)]
  exact α.card_mul_gaugeDistErr_le hn

end CrossDegreeStarBound

end Cochain

section CrossDegreeStarBound

variable {V : Type*} [Fintype V]

/-- The star bound as a lower bound on `h1Err (complete V)`, whenever some cochain of degree at
least `2` has strictly positive cross-degree gauge distance. -/
theorem card_div_three_le_h1Err_of_exists
    (hne : ∃ (n : ℕ) (α : Cochain (complete V) (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) :
    (Fintype.card V : ℝ) / 3 ≤ h1Err (complete V) := by
  let _ : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  exact le_h1Err_of_forall_defect hne fun _ _ hα =>
    Cochain.card_div_three_le_defect_div_gaugeDistErr (by omega) hα

/-- Unconditional cross-degree star bound: when `3 ≤ Fintype.card V`,
`(Fintype.card V : ℝ) / 3 ≤ h1Err (complete V)`. -/
theorem card_div_three_le_h1Err (hV : 3 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) / 3 ≤ h1Err (complete V) :=
  let ⟨α, hα⟩ := exists_gaugeDistErr_pos_complete hV (n := 2) (by decide)
  card_div_three_le_h1Err_of_exists ⟨0, α, hα⟩

end CrossDegreeStarBound

end TauCeti

end
