/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Basic
import TauCeti.Analysis.ExteriorPower.Plucker
import TauCeti.InformationTheory.Coding.GeneratorParityCheck
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic

/-!
# Height of a subspace in terms of a spanning family

The Euclidean height of a subspace is at most the product of the Euclidean
heights of any basis. The constant is one: the local estimate is Hadamard's
inequality at infinity and the ultrametric determinant bound at finite places.
This bound lets one estimate the height of a kernel using its defining forms
and dot-product duality (`Matrix.subspaceHeight_ker_mulVecLin` and
`Matrix.subspaceHeight_ker_mulVecLin_le_prod`).

We first bound the relative Arakelov height of a Plücker vector, including
dependent families with the projective zero convention. Taking degree roots
gives the absolute Euclidean bound for vectors and subspaces, both for
linearly independent families and, by passing to a maximal independent
subfamily, for arbitrary finite families of nonzero tuples.

## Main results

* `TauCeti.arakelovMulHeight_plucker_le_prod` and `TauCeti.height2_plucker_le_prod`: Hadamard-type
  product bounds on the relative Arakelov and absolute Euclidean heights of a Plücker vector.
* `Submodule.subspaceHeight_le_prod`, `Submodule.subspaceHeight_span_range_le_prod`, and
  `Submodule.relativeSubspaceArakelovHeight_le_prod`: bounds on the height of a subspace in terms of
  an independent or arbitrary nonzero spanning family.
* `Matrix.relativeSubspaceArakelovHeight_ker_mulVecLin`, `Matrix.subspaceHeight_ker_mulVecLin`, and
  `Matrix.subspaceHeight_ker_mulVecLin_le_prod`: kernel height equalities and row-product bound for
  an arbitrary matrix.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, Ann. of Math. 177 (2013), §6.1, (6.11) and (6.13).
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

/-- A subspace's absolute Euclidean height is at most the product of the
Euclidean heights of any finite spanning family of nonzero tuples, without
assuming linear independence: passing to a maximal linearly independent
subfamily drops only factors `height2 (x i) ≥ 1`. -/
theorem subspaceHeight_span_range_le_prod {m : Type*} [Fintype m] {x : m → ι → K}
    (hx : ∀ i, x i ≠ 0) :
    subspaceHeight (span K (range x)) ≤ ∏ i, height2 (x i) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K x
  let _ : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  let e : Fin (Fintype.card κ) ↪ m := (Fintype.equivFin κ).symm.toEmbedding.trans ⟨a, ha⟩
  have hli' : LinearIndependent K (x ∘ e) := hli.comp _ (Fintype.equivFin κ).symm.injective
  have hrange : range (x ∘ e) = range (x ∘ a) := by
    ext v
    simp only [mem_range, Function.comp_apply, e, Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply]
    exact ⟨fun ⟨j, hj⟩ ↦ ⟨(Fintype.equivFin κ).symm j, hj⟩,
      fun ⟨k, hk⟩ ↦ ⟨Fintype.equivFin κ k, by simpa using hk⟩⟩
  rw [← hspan, ← hrange]
  refine (subspaceHeight_le_prod hli').trans ?_
  calc ∏ j, height2 ((x ∘ e) j)
      = ∏ i ∈ Finset.univ.map e, height2 (x i) :=
        (Finset.prod_map Finset.univ e fun i ↦ height2 (x i)).symm
    _ = ∏ i : m, if i ∈ Finset.univ.map e then height2 (x i) else 1 := by
        rw [Finset.prod_ite_mem, Finset.univ_inter]
    _ ≤ ∏ i : m, height2 (x i) := Finset.prod_le_prod₀ (fun i _ ↦ by
        split_ifs
        · exact height2_nonneg _
        · exact zero_le_one) fun i _ ↦ by
        split_ifs
        · exact le_rfl
        · exact one_le_height2_of_ne_zero (hx i)

/-- The relative Arakelov height of a subspace is bounded by the product of
relative Arakelov heights of its basis vectors. -/
theorem relativeSubspaceArakelovHeight_le_prod {U : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K U) :
    relativeSubspaceArakelovHeight U ≤ ∏ i, arakelovMulHeight (b i : ι → K) := by
  rw [relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker b]
  exact arakelovMulHeight_plucker_le_prod _

end Submodule

namespace Matrix

open Submodule TauCeti

variable {K m ι : Type*} [Field K] [NumberField K] [Fintype ι] [LinearOrder ι]

/-- The relative Arakelov height of the kernel of a matrix equals the relative
Arakelov height of its row space, without assuming linearly independent rows. -/
theorem relativeSubspaceArakelovHeight_ker_mulVecLin [Finite m] (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).relativeSubspaceArakelovHeight =
      (span K (range A.row)).relativeSubspaceArakelovHeight := by
  cases nonempty_fintype m
  rw [← checkedBy_def, checkedBy_eq_euclideanDual_generatedBy,
    relativeSubspaceArakelovHeight_euclideanDual, generatedBy_eq_span_rows]

/-- The absolute Euclidean height of the kernel of a matrix equals the absolute
Euclidean height of its row space, without assuming linearly independent rows. -/
theorem subspaceHeight_ker_mulVecLin [Finite m] (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).subspaceHeight = (span K (range A.row)).subspaceHeight := by
  cases nonempty_fintype m
  rw [← checkedBy_def, checkedBy_eq_euclideanDual_generatedBy,
    subspaceHeight_euclideanDual, generatedBy_eq_span_rows]

/-- The absolute Euclidean height of the kernel of a matrix with nonzero rows is
at most the product of the absolute Euclidean heights of its rows. -/
theorem subspaceHeight_ker_mulVecLin_le_prod [Fintype m] {A : Matrix m ι K}
    (hA : ∀ i, A.row i ≠ 0) :
    (LinearMap.ker A.mulVecLin).subspaceHeight ≤ ∏ i, height2 (A.row i) := by
  rw [A.subspaceHeight_ker_mulVecLin]
  exact subspaceHeight_span_range_le_prod hA

end Matrix
