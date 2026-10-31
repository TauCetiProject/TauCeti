/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Basic
import TauCeti.Analysis.ExteriorPower.Plucker
import TauCeti.NumberTheory.NumberField.FinitePlace

/-!
# Height of a subspace in terms of a spanning family

The Euclidean height of a subspace is at most the product of the Euclidean
heights of any basis. The constant is one: the local estimate is Hadamard's
inequality at infinity and the ultrametric determinant bound at finite places.
This bound lets one estimate the height of a kernel using its defining forms
and dot-product duality.

We first bound the relative Arakelov height of a Plücker vector, including
dependent families with the projective zero convention. Taking degree roots
gives the absolute Euclidean bound for vectors and subspaces.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, Ann. of Math. 177 (2013), §6.1, (6.11).
-/

public noncomputable section

open scoped BigOperators
open NumberField Set Module

namespace TauCeti

variable {K ι : Type*} [Field K] [NumberField K] [LinearOrder ι] [Finite ι] {p : ℕ}

/-- The relative Arakelov height of the Plücker vector is at most the product
of the relative Arakelov heights of the vectors, even for dependent families. -/
theorem arakelovMulHeight_plucker_le_prod (x : Fin p → ι → K) :
    arakelovMulHeight (plucker x) ≤ ∏ i, arakelovMulHeight (x i) := by
  classical
  -- Match the coordinate Fintype chosen internally by `arakelovMulHeight_eq`.
  let _ := Fintype.ofFinite ι
  by_cases hx : LinearIndependent K x
  · have hp : plucker x ≠ 0 := (plucker_ne_zero_iff x).2 hx
    have hrow (i) : x i ≠ 0 := hx.ne_zero i
    have : Nonempty (powersetCard ι p) := by
      obtain ⟨s, _⟩ := Function.ne_iff.mp hp
      exact ⟨s⟩
    have hinf (w : InfinitePlace K) :
        (∑ s, ‖w.embedding (plucker x s)‖ ^ 2) ^ ((w.mult : ℝ) / 2) ≤
          ∏ i, (∑ j, ‖w.embedding (x i j)‖ ^ 2) ^ ((w.mult : ℝ) / 2) := by
      have h := sum_norm_plucker_sq_le (fun i j ↦ w.embedding (x i j))
      simp_rw [plucker_map] at h
      exact (Real.rpow_le_rpow (by positivity) h
        (by positivity : 0 ≤ (w.mult : ℝ) / 2)).trans_eq
        (Real.finsetProd_rpow Finset.univ (fun i ↦ ∑ j, ‖w.embedding (x i j)‖ ^ 2)
          (fun _ _ ↦ by positivity) _).symm
    have hfin (v : FinitePlace K) :
        (⨆ s, v (plucker x s)) ≤ ∏ i, ⨆ j, v (x i j) := by
      exact ciSup_le fun s ↦ v.val.plucker_le_prod_iSup (FinitePlace.add_le v) x s
    -- The height formula chooses `Fintype.ofFinite` for the Plücker coordinates;
    -- align it with the powerset-cardinality instance used in the local bound.
    rw [arakelovMulHeight_eq hp,
      Subsingleton.elim (Fintype.ofFinite (powersetCard ι p))
        (powersetCard.instFintypeElemFinset ι p)]
    simp_rw [arakelovMulHeight_eq (hrow _)]
    rw [Finset.prod_mul_distrib, Finset.prod_comm,
      prod_finprod_comm _ _ (fun i _ ↦ FinitePlace.hasFiniteMulSupport_iSup (hrow i))]
    apply mul_le_mul
    · exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun w _ ↦ hinf w
    · exact finprod_le_finprod₀ (FinitePlace.hasFiniteMulSupport_iSup hp)
        (fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass _ _)
        (.prod (fun i ↦ FinitePlace.hasFiniteMulSupport_iSup (hrow i)) _) hfin
    · exact finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass _ _
    · exact Finset.prod_nonneg fun _ _ ↦ by positivity
  · rw [← plucker_ne_zero_iff, not_not] at hx
    rw [hx, arakelovMulHeight_zero]
    exact Finset.one_le_prod₀ fun _ _ ↦ one_le_arakelovMulHeight _

/-- The absolute Euclidean height of a Plücker vector is at most the product
of the absolute Euclidean heights of the original vectors. Dependent families
have a zero Plücker vector, of Euclidean height zero. -/
theorem height2_plucker_le_prod (x : Fin p → ι → K) :
    height2 (plucker x) ≤ ∏ i, height2 (x i) := by
  classical
  by_cases hx : LinearIndependent K x
  · have hp : plucker x ≠ 0 := (plucker_ne_zero_iff x).2 hx
    have h := Real.rpow_le_rpow (arakelovMulHeight_nonneg (plucker x))
      (arakelovMulHeight_plucker_le_prod x) (by positivity : 0 ≤ (1 : ℝ) / finrank ℚ K)
    rw [← Real.finsetProd_rpow _ _ (fun _ _ ↦ arakelovMulHeight_nonneg _) _,
      arakelovMulHeight_eq_height2, ite_eq_right hp] at h
    simpa only [arakelovMulHeight_eq_height2, ite_eq_right (hx.ne_zero _)] using h
  · rw [← plucker_ne_zero_iff, not_not] at hx
    rw [hx, height2_zero]
    exact Finset.prod_nonneg fun _ _ ↦ height2_nonneg _

end TauCeti

namespace Submodule

open TauCeti

variable {K ι : Type*} [Field K] [NumberField K] [LinearOrder ι] [Finite ι]

/-- A subspace's absolute Euclidean height is at most the product of the
Euclidean heights of any linearly independent spanning family. -/
theorem subspaceHeight_le_prod {p : ℕ} {x : Fin p → ι → K}
    (hx : LinearIndependent K x) :
    subspaceHeight (span K (range x)) ≤ ∏ i, height2 (x i) := by
  rw [subspaceHeight_span_range hx]
  exact height2_plucker_le_prod x

/-- The relative Arakelov height of a subspace is bounded by the product of
relative Arakelov heights of its basis vectors. -/
theorem relativeSubspaceArakelovHeight_le_prod {U : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K U) :
    relativeSubspaceArakelovHeight U ≤ ∏ i, arakelovMulHeight (b i : ι → K) := by
  rw [relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker b]
  exact arakelovMulHeight_plucker_le_prod _

end Submodule
