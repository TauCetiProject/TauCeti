/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.BigOperators.Pi

/-!
# Point-separating subalgebras of a finite product of a field

For a field `K` and a finite type `ι`, a subalgebra of `ι → K` that separates the points of `ι`
is everything (`Subalgebra.eq_top_of_separates_points`). This is the finite, purely algebraic
form of the Stone–Weierstrass theorem. The proof is Lagrange interpolation: for each `j ≠ i`
some affine function of an element of the subalgebra is `1` at `i` and `0` at `j`, and the
product of these is the indicator `Pi.single i 1` of `i`
(`Subalgebra.single_one_mem_of_separates_points`).
-/

public section

namespace Subalgebra

variable {K ι : Type*} [Field K] [Finite ι] {S : Subalgebra K (ι → K)}

/-- A subalgebra of `ι → K` that separates the points of the finite type `ι` contains the
indicator function of each point. -/
theorem single_one_mem_of_separates_points [DecidableEq ι]
    (h : ∀ i j, i ≠ j → ∃ f ∈ S, f i ≠ f j) (i : ι) : Pi.single i (1 : K) ∈ S := by
  have := Fintype.ofFinite ι
  -- for each `j ≠ i`, a function in `S` that is `1` at `i` and `0` at `j`
  have hfactor : ∀ j, ∃ g ∈ S, g i = 1 ∧ (i ≠ j → g j = 0) := by
    intro j
    by_cases hij : i = j
    · exact ⟨1, S.one_mem, rfl, fun h => absurd hij h⟩
    obtain ⟨f, hf, hfij⟩ := h i j hij
    refine ⟨(f i - f j)⁻¹ • (f - algebraMap K _ (f j)),
      S.smul_mem (S.sub_mem hf (S.algebraMap_mem _)) _, ?_, fun _ => ?_⟩ <;>
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, smul_eq_mul, sub_self, mul_zero, inv_mul_cancel₀ (sub_ne_zero.mpr hfij)]
  choose g hgS hgi hgj using hfactor
  -- Lagrange interpolation: the indicator of `i` is the product of these functions
  have hprod : Pi.single i 1 = ∏ j, g j := by
    funext k
    rw [Finset.prod_apply]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same, eq_comm]
      exact Finset.prod_eq_one fun j _ => hgi j
    · rw [Pi.single_eq_of_ne hk, eq_comm]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (hgj k (Ne.symm hk))
  exact hprod ▸ S.prod_mem fun j _ => hgS j

/-- **Finite Stone–Weierstrass theorem.** A subalgebra of `ι → K` that separates the points of
the finite type `ι` is `⊤`. -/
theorem eq_top_of_separates_points (h : ∀ i j, i ≠ j → ∃ f ∈ S, f i ≠ f j) : S = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← Finset.univ_sum_single f]
  refine S.sum_mem fun i _ => ?_
  rw [← mul_one (f i), ← smul_eq_mul, Pi.single_smul']
  exact S.smul_mem (single_one_mem_of_separates_points h i) _

end Subalgebra
