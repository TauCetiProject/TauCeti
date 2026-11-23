/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Complete
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Coboundary constants of the complete complex on four vertices

On `complete (Fin 4)` there are six edges and four triangles, so the cost of a gauge and the
defect of a cochain are explicit finite sums (`TauCeti.Cochain.cost_complete_fin_four`,
`TauCeti.Cochain.defect_complete_fin_four`). With binary coefficients `Equiv.Perm (Fin 2)` and the
moved-point norm, every cochain has a gauge of cost at most half its defect, and the cochain with
a single transposition edge has defect `4` and gauge distance `2`. Hence:

* `TauCeti.h1_complete_fin_four_movedNorm_fin_two`: `h1 (complete (Fin 4)) (movedNorm (Fin 2)) = 2`;
* `TauCeti.h1Sym_complete_fin_four_lt_h1_movedNorm_fin_two`: the same-degree permutation constant
  `h1Sym (complete (Fin 4)) = 4 / 3` lies strictly below this binary constant. So on four
  vertices the comparison `h1Sym X ≤ h1 X (movedNorm (Fin 2))` of Chapman and Lubotzky is strict.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792, Proposition 5 (the binary and `Sym(3)`
  constants on four vertices).
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117,
  footnote 2 (the comparison with `𝔽₂` coefficients).
-/

public section

open Finset Equiv Equiv.Perm

namespace TauCeti

open TwoComplex

namespace Cochain

variable {G : Type*} [Group G]

/-- On `complete (Fin 4)`, the cost of a gauge is the sum of its six edge terms. -/
theorem cost_complete_fin_four (ℓ : GroupNorm G) (α : Cochain (complete (Fin 4)) G)
    (β : Fin 4 → G) :
    α.cost ℓ β = ℓ ((β 0)⁻¹ * α 0 1 * β 1) + ℓ ((β 0)⁻¹ * α 0 2 * β 2) +
      ℓ ((β 0)⁻¹ * α 0 3 * β 3) + ℓ ((β 1)⁻¹ * α 1 2 * β 2) + ℓ ((β 1)⁻¹ * α 1 3 * β 3) +
      ℓ ((β 2)⁻¹ * α 2 3 * β 3) := by
  rw [cost_complete, sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_four]
  ring

/-- On `complete (Fin 4)`, the defect of a cochain is the sum of the holonomy norms of its four
triangles. -/
theorem defect_complete_fin_four (ℓ : GroupNorm G) (α : Cochain (complete (Fin 4)) G) :
    α.defect ℓ = ℓ (α.holonomy 0 1 2) + ℓ (α.holonomy 0 1 3) + ℓ (α.holonomy 0 2 3) +
      ℓ (α.holonomy 1 2 3) := by
  rw [defect_complete, sum_filter, Fintype.sum_prod_type]
  simp [Fintype.sum_prod_type, Fin.sum_univ_four]

end Cochain

/-- Every binary cochain on `complete (Fin 4)` has a gauge costing at most half its defect. -/
private theorem Cochain.exists_two_mul_cost_le_defect_fin_four
    (α : Cochain (complete (Fin 4)) (Perm (Fin 2))) :
    ∃ β : Fin 4 → Perm (Fin 2),
      2 * α.cost (movedNorm (Fin 2)) β ≤ α.defect (movedNorm (Fin 2)) := by
  -- the claim only depends on the six edge values `α u v`, `u < v`, so it is a finite check
  have key : ∀ a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : Perm (Fin 2), ∃ b₀ b₁ b₂ b₃ : Perm (Fin 2),
      2 * (#(b₀⁻¹ * a₀₁ * b₁).support + #(b₀⁻¹ * a₀₂ * b₂).support +
        #(b₀⁻¹ * a₀₃ * b₃).support + #(b₁⁻¹ * a₁₂ * b₂).support + #(b₁⁻¹ * a₁₃ * b₃).support +
        #(b₂⁻¹ * a₂₃ * b₃).support) ≤
      #(a₀₁ * a₁₂ * a₀₂⁻¹).support + #(a₀₁ * a₁₃ * a₀₃⁻¹).support +
        #(a₀₂ * a₂₃ * a₀₃⁻¹).support + #(a₁₂ * a₂₃ * a₁₃⁻¹).support := by
    decide +kernel
  obtain ⟨b₀, b₁, b₂, b₃, h⟩ := key (α 0 1) (α 0 2) (α 0 3) (α 1 2) (α 1 3) (α 2 3)
  refine ⟨![b₀, b₁, b₂, b₃], ?_⟩
  rw [Cochain.cost_complete_fin_four, Cochain.defect_complete_fin_four]
  simp only [Cochain.holonomy_def, α.apply_swap 0 2, α.apply_swap 0 3, α.apply_swap 1 3,
    movedNorm_apply, Matrix.cons_val]
  exact_mod_cast h

/-- The binary cochain on `complete (Fin 4)` carrying the transposition on the edge `(0, 1)`. -/
private noncomputable def oneEdge : Cochain (complete (Fin 4)) (Perm (Fin 2)) :=
  Cochain.singleEdge _ 0 1 (swap 0 1)

private theorem defect_oneEdge : oneEdge.defect (movedNorm (Fin 2)) = 4 := by
  rw [Cochain.defect_complete_fin_four]
  norm_num [oneEdge, Cochain.holonomy_def, movedNorm_apply]

private theorem two_le_cost_oneEdge (β : Fin 4 → Perm (Fin 2)) :
    2 ≤ oneEdge.cost (movedNorm (Fin 2)) β := by
  rw [Cochain.cost_complete_fin_four]
  have key : ∀ b₀ b₁ b₂ b₃ : Perm (Fin 2), 2 ≤ #(b₀⁻¹ * swap 0 1 * b₁).support +
      #(b₀⁻¹ * b₂).support + #(b₀⁻¹ * b₃).support + #(b₁⁻¹ * b₂).support + #(b₁⁻¹ * b₃).support +
      #(b₂⁻¹ * b₃).support := by
    decide
  simpa [oneEdge, movedNorm_apply] using (Nat.cast_le (α := ℝ)).mpr (key (β 0) (β 1) (β 2) (β 3))

/-- The binary coboundary constant of the complete complex on four vertices is `2`, attained by
a single transposition edge, with defect `4` and gauge distance `2`. -/
theorem h1_complete_fin_four_movedNorm_fin_two :
    h1 (complete (Fin 4)) (movedNorm (Fin 2)) = 2 := by
  have hD : (2 : ℝ) ≤ oneEdge.gaugeDist (movedNorm (Fin 2)) :=
    (oneEdge.le_gaugeDist_iff _).mpr two_le_cost_oneEdge
  have hpos : 0 < oneEdge.gaugeDist (movedNorm (Fin 2)) := two_pos.trans_le hD
  refine le_antisymm ((h1_le_div hpos).trans ?_) (le_h1_of_forall ⟨oneEdge, hpos⟩ fun α hα => ?_)
  · rw [defect_oneEdge, div_le_iff₀ hpos]
    linarith
  · obtain ⟨β, hβ⟩ := α.exists_two_mul_cost_le_defect_fin_four
    rw [le_div_iff₀ hα]
    linarith [α.gaugeDist_le_cost (movedNorm (Fin 2)) β]

/-- On four vertices the same-degree permutation constant `h1Sym (complete (Fin 4)) = 4 / 3` lies
strictly below the binary constant `h1 (complete (Fin 4)) (movedNorm (Fin 2)) = 2`. -/
theorem h1Sym_complete_fin_four_lt_h1_movedNorm_fin_two :
    h1Sym (complete (Fin 4)) < h1 (complete (Fin 4)) (movedNorm (Fin 2)) := by
  rw [h1Sym_complete (by simp), h1_complete_fin_four_movedNorm_fin_two]
  norm_num

end TauCeti
