/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.Order.Northcott
public import TauCeti.InformationTheory.Coding.EuclideanDual
public import TauCeti.LinearAlgebra.Projectivization.Plucker

import Mathlib.NumberTheory.Height.NumberField
import TauCeti.NumberTheory.Height.Basic
import TauCeti.NumberTheory.Height.Northcott

/-!
# The relative height of a subspace

Let `K` be a field with admissible absolute values (`Height.AdmissibleAbsValues K`), for
instance a number field, and let `ι` be a finite linearly ordered type. The relative height of a
subspace `U` of `K^ι` is the multiplicative height of its Plücker point, that is, the projective
height `Height.mulHeight` of the Plücker coordinates of any basis of `U`. Its logarithm is the
relative logarithmic height. Neither needs a number field or characteristic zero.

The zero subspace and the whole space have height `1`, and a line has the height of any nonzero
vector spanning it. The height of a subspace does not depend on the spanning vectors: over `ℚ`
the line spanned by `(2, 2)` has height `1`, so no primitive spanning vector is needed.

A subspace and its orthogonal complement for the dot product, `Submodule.euclideanDual`, have the
same height: up to a common nonzero factor and signs, the Plücker coordinates of the complement
are the complementary Plücker coordinates of the subspace. Over `ℚ`, the line spanned by `(1, 2)`
and the line spanned by `(-2, 1)`, its orthogonal complement in `ℚ²`, both have height `2`.

If the field has finitely many elements of bounded height, for instance a number field, then
`K^ι` has finitely many subspaces of bounded height, of all dimensions together. A subspace is
determined by its dimension and its Plücker point, and the projective space of each dimension
has finitely many points of bounded height.

## Main definitions

* `Submodule.relativeSubspaceHeight U`: the multiplicative height of the Plücker point of `U`.
* `Submodule.relativeSubspaceLogHeight U`: its logarithm.

## Main results

* `Submodule.relativeSubspaceHeight_eq_mulHeight_plucker`: the height of `U` is the height of
  the Plücker coordinates of any basis of `U`.
* `Submodule.relativeSubspaceHeight_span_range`: the height of the span of a linearly
  independent family is the height of its Plücker coordinates.
* `Submodule.relativeSubspaceHeight_bot`, `Submodule.relativeSubspaceHeight_top`: the zero
  subspace and the whole space have height `1`.
* `Submodule.relativeSubspaceHeight_span_singleton`: the line spanned by a nonzero vector has the
  height of that vector.
* `Submodule.relativeSubspaceHeight_euclideanDual`: the orthogonal complement of `U` for the dot
  product has the height of `U`.
* `Submodule.instNorthcottRelativeSubspaceHeight` and
  `Submodule.instNorthcottRelativeSubspaceLogHeight`: the Northcott property for the relative
  height and the relative logarithmic height.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §2.8.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §6.1, (6.13).
* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of
  Math. **85** (1967), 430–472.
-/

public section

namespace Submodule

open Height TauCeti Set Module

variable {ι K : Type*} [LinearOrder ι] [Finite ι] [Field K] [AdmissibleAbsValues K]
  (U : Submodule K (ι → K))

/-- The relative multiplicative height of a subspace `U` of `ι → K`: the multiplicative height
`Height.mulHeight` of the Plücker coordinates of any basis of `U`
(`relativeSubspaceHeight_eq_mulHeight_plucker`). -/
noncomputable def relativeSubspaceHeight : ℝ :=
  (relativePluckerPoint U).mulHeight

/-- The relative logarithmic height of a subspace `U` of `ι → K`: the logarithmic height
`Height.logHeight` of the Plücker coordinates of any basis of `U`. -/
noncomputable def relativeSubspaceLogHeight : ℝ :=
  (relativePluckerPoint U).logHeight

/-- The relative logarithmic height is the logarithm of the relative height. -/
theorem relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight :
    relativeSubspaceLogHeight U = Real.log (relativeSubspaceHeight U) :=
  Projectivization.logHeight_eq_log_mulHeight _

variable {U} in
/-- The relative height of `U` is the multiplicative height of the Plücker coordinates of any
basis of `U`. -/
theorem relativeSubspaceHeight_eq_mulHeight_plucker {p : ℕ} (b : Basis (Fin p) K U) :
    relativeSubspaceHeight U = mulHeight (plucker fun i ↦ (b i : ι → K)) := by
  obtain rfl : finrank K U = p := (finrank_eq_card_basis b).trans (Fintype.card_fin p)
  rw [relativeSubspaceHeight, relativePluckerPoint_eq_mk b, Projectivization.mulHeight_mk]

variable {U} in
/-- The relative logarithmic height of `U` is the logarithmic height of the Plücker coordinates of
any basis of `U`. -/
theorem relativeSubspaceLogHeight_eq_logHeight_plucker {p : ℕ} (b : Basis (Fin p) K U) :
    relativeSubspaceLogHeight U = logHeight (plucker fun i ↦ (b i : ι → K)) := by
  rw [relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight,
    relativeSubspaceHeight_eq_mulHeight_plucker b,
    logHeight_eq_log_mulHeight]

/-- The relative height of the span of a linearly independent family is the multiplicative height
of its Plücker coordinates. -/
theorem relativeSubspaceHeight_span_range {p : ℕ} {x : Fin p → ι → K}
    (hx : LinearIndependent K x) :
    relativeSubspaceHeight (span K (range x)) = mulHeight (plucker x) := by
  rw [relativeSubspaceHeight_eq_mulHeight_plucker (Basis.span hx)]
  simp_rw [Basis.coe_span_apply]

/-- The relative logarithmic height of the span of a linearly independent family is the
logarithmic height of its Plücker coordinates. -/
theorem relativeSubspaceLogHeight_span_range {p : ℕ} {x : Fin p → ι → K}
    (hx : LinearIndependent K x) :
    relativeSubspaceLogHeight (span K (range x)) = logHeight (plucker x) := by
  rw [relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight,
    relativeSubspaceHeight_span_range hx,
    logHeight_eq_log_mulHeight]

/-- The relative height of a subspace is at least `1`. -/
theorem one_le_relativeSubspaceHeight : 1 ≤ relativeSubspaceHeight U :=
  Projectivization.one_le_mulHeight _

/-- The relative height of a subspace is positive. -/
theorem relativeSubspaceHeight_pos : 0 < relativeSubspaceHeight U :=
  Projectivization.mulHeight_pos _

/-- The relative logarithmic height of a subspace is nonnegative. -/
theorem relativeSubspaceLogHeight_nonneg : 0 ≤ relativeSubspaceLogHeight U :=
  Projectivization.logHeight_nonneg _

/-- The zero subspace has relative height `1`. -/
@[simp]
theorem relativeSubspaceHeight_bot : relativeSubspaceHeight (⊥ : Submodule K (ι → K)) = 1 := by
  have h := relativeSubspaceHeight_span_range (linearIndependent_empty_type (ι := Fin 0)
    (R := K) (v := fun _ ↦ (0 : ι → K)))
  rw [range_eq_empty, span_empty] at h
  rw [h, funext (plucker_of_isEmpty _), ← Pi.one_def, mulHeight_one]

/-- The whole space has relative height `1`. -/
@[simp]
theorem relativeSubspaceHeight_top : relativeSubspaceHeight (⊤ : Submodule K (ι → K)) = 1 := by
  have := Fintype.ofFinite ι
  let b := (Pi.basisFun K ι).reindex (Fintype.equivFin ι)
  have h := relativeSubspaceHeight_span_range b.linearIndependent
  rw [b.span_eq] at h
  -- The only `#ι`-element subset of `ι` is `ι` itself.
  have : Subsingleton (powersetCard ι (Fintype.card ι)) :=
    ⟨fun s t ↦ Subtype.ext <| (Finset.eq_univ_of_card _ (powersetCard.card_eq s)).trans
      (Finset.eq_univ_of_card _ (powersetCard.card_eq t)).symm⟩
  rw [h, mulHeight_eq_one_of_subsingleton]

/-- The zero subspace has relative logarithmic height `0`. -/
@[simp]
theorem relativeSubspaceLogHeight_bot :
    relativeSubspaceLogHeight (⊥ : Submodule K (ι → K)) = 0 := by
  simp [relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight]

/-- The whole space has relative logarithmic height `0`. -/
@[simp]
theorem relativeSubspaceLogHeight_top :
    relativeSubspaceLogHeight (⊤ : Submodule K (ι → K)) = 0 := by
  simp [relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight]

/-- The relative height of the line spanned by a nonzero vector is the height of the vector. -/
@[simp]
theorem relativeSubspaceHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    relativeSubspaceHeight (K ∙ x) = mulHeight x := by
  have h := relativeSubspaceHeight_span_range (linearIndependent_unique_iff.2 hx :
    LinearIndependent K ![x])
  rw [Matrix.range_cons, Matrix.range_empty, union_empty] at h
  rw [h, ← mulHeight_comp_equiv powersetCard.ofSingleton]
  congr 1
  ext i
  simp

/-- The relative logarithmic height of the line spanned by a nonzero vector is the logarithmic
height of the vector. -/
@[simp]
theorem relativeSubspaceLogHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    relativeSubspaceLogHeight (K ∙ x) = logHeight x := by
  rw [relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight,
    relativeSubspaceHeight_span_singleton hx,
    logHeight_eq_log_mulHeight]

/-- **Duality of heights.** The orthogonal complement of a subspace `U` of `ι → K` for the dot
product has the relative height of `U`. -/
@[simp]
theorem relativeSubspaceHeight_euclideanDual [Fintype ι] :
    relativeSubspaceHeight U.euclideanDual = relativeSubspaceHeight U := by
  let b := finBasis K U
  let b' := finBasis K U.euclideanDual
  obtain ⟨c, hc, h⟩ :=
    exists_plucker_eq_mul_plucker_compl_or_eq_neg (finrank_add_finrank_euclideanDual U)
    b.linearIndependent_coe_basis b'.linearIndependent_coe_basis
    fun i j ↦ mem_euclideanDual.1 (b' j).2 _ (b i).2
  rw [relativeSubspaceHeight_eq_mulHeight_plucker b', relativeSubspaceHeight_eq_mulHeight_plucker b,
    mulHeight_eq_of_forall_eq_or_eq_neg h]
  -- The tuple `fun t ↦ c * plucker _ (compl _ t)` is `c • (plucker _ ∘ compl _)` pointwise.
  exact (mulHeight_smul_eq_mulHeight _ hc).trans (mulHeight_comp_equiv _ _)

/-- The orthogonal complement of a subspace `U` of `ι → K` for the dot product has the relative
logarithmic height of `U`. -/
@[simp]
theorem relativeSubspaceLogHeight_euclideanDual [Fintype ι] :
    relativeSubspaceLogHeight U.euclideanDual = relativeSubspaceLogHeight U := by
  simp [relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight]

/-- The relative height of subspaces has the Northcott property whenever the scalar height does,
for instance over a number field: for every `B` there are finitely many subspaces of `ι → K` of
relative height at most `B`, of all dimensions together. -/
instance instNorthcottRelativeSubspaceHeight [Northcott (mulHeight₁ (K := K))] :
    Northcott (relativeSubspaceHeight (ι := ι) (K := K)) where
  finite_le B := by
    have := Fintype.ofFinite ι
    -- The subspaces of height at most `B` have dimension at most `#ι` and a Plücker point of
    -- height at most `B`, and the pair of these determines the subspace.
    have hS : (⋃ p ∈ Iic (Fintype.card ι), Sigma.mk p ''
        {x : Projectivization K (powersetCard ι p → K) | x.mulHeight ≤ B}).Finite :=
      (finite_Iic _).biUnion fun p _ ↦ (Northcott.finite_le B).image _
    refine (hS.preimage finrank_relativePluckerPoint_injective.injOn).subset fun U hU ↦ ?_
    simp only [mem_preimage, mem_iUnion, mem_image, mem_ofPred_eq, exists_prop]
    refine ⟨finrank K U, ?_, relativePluckerPoint U, hU, rfl⟩
    exact (Submodule.finrank_le U).trans_eq (Module.finrank_fintype_fun_eq_card K)

/-- The relative logarithmic height of subspaces has the Northcott property whenever the relative
height does. -/
instance instNorthcottRelativeSubspaceLogHeight
    [Northcott (relativeSubspaceHeight (ι := ι) (K := K))] :
    Northcott (relativeSubspaceLogHeight (ι := ι) (K := K)) := by
  have heq : relativeSubspaceLogHeight (ι := ι) (K := K) = Real.log ∘ relativeSubspaceHeight :=
    funext relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight
  rw [heq]
  exact Northcott.comp_of_bddAbove _ _ fun B ↦
    bddAbove_def.mpr ⟨Real.exp B, fun _ ↦ Real.le_exp_of_log_le⟩

end Submodule

/-! The line spanned by `(2, 2)` has height `1`: no primitive spanning vector is needed. The line
spanned by `(1, 2)` has height `2`. -/

example : (ℚ ∙ ![(2 : ℚ), 2]).relativeSubspaceHeight = 1 := by
  rw [Submodule.relativeSubspaceHeight_span_singleton (by simp)]
  calc Height.mulHeight ![(2 : ℚ), 2]
      _ = Height.mulHeight ((2 : ℚ) • (1 : Fin 2 → ℚ)) := by
        congr 1; ext i; fin_cases i <;> simp
      _ = 1 := by rw [Height.mulHeight_smul_eq_mulHeight _ two_ne_zero, Height.mulHeight_one]

example : (ℚ ∙ ![(1 : ℚ), 2]).relativeSubspaceHeight = 2 := by
  rw [Submodule.relativeSubspaceHeight_span_singleton (by simp)]
  calc Height.mulHeight ![(1 : ℚ), 2]
      _ = Height.mulHeight (![(1 : ℚ), 2] ∘ Equiv.swap 0 1) :=
        (Height.mulHeight_comp_equiv (Equiv.swap 0 1) _).symm
      _ = Height.mulHeight ![(2 : ℚ), 1] := by congr 1; ext i; fin_cases i <;> rfl
      _ = 2 := by
        rw [← Height.mulHeight₁_eq_mulHeight]
        exact_mod_cast Rat.mulHeight₁_natCast 2

/-! In `ℚ²` the orthogonal complement of the line spanned by `(1, 2)` is the line spanned by
`(-2, 1)`, so the two lines have the same height. -/

example : (ℚ ∙ ![(-2 : ℚ), 1]).relativeSubspaceHeight =
    (ℚ ∙ ![(1 : ℚ), 2]).relativeSubspaceHeight := by
  have h : ℚ ∙ ![(-2 : ℚ), 1] = (ℚ ∙ ![(1 : ℚ), 2]).euclideanDual := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_euclideanDual_span]
      simp [dotProduct, Fin.sum_univ_two]
    · have h := Submodule.finrank_add_finrank_euclideanDual (ℚ ∙ ![(1 : ℚ), 2])
      rw [finrank_span_singleton (by simp), Fintype.card_fin] at h
      rw [finrank_span_singleton (by simp)]
      omega
  rw [h, Submodule.relativeSubspaceHeight_euclideanDual]

/-! Over `ℚ` the Northcott instance applies through Mathlib's number-field instance for the scalar
height. -/

example (B : ℝ) : {U : Submodule ℚ (Fin 3 → ℚ) | U.relativeSubspaceHeight ≤ B}.Finite :=
  Northcott.finite_le B
