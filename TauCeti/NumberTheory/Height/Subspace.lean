/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.Projectivization
public import TauCeti.LinearAlgebra.Projectivization.Plucker

import Mathlib.NumberTheory.Height.NumberField

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

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §2.8.
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
  -- The single coordinate of the unique element of the singleton `{i}` is `i`.
  have hi : (powersetCard.ofFinEmbEquiv.symm (powersetCard.ofSingleton i)) 0 = i := by
    have h := powersetCard.mem_coe_iff.2 <|
      (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (powersetCard.ofSingleton i) _).1 ⟨0, rfl⟩
    exact Finset.mem_singleton.1 h
  simp [plucker_apply, Matrix.det_unique, hi]

/-- The relative logarithmic height of the line spanned by a nonzero vector is the logarithmic
height of the vector. -/
@[simp]
theorem relativeSubspaceLogHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    relativeSubspaceLogHeight (K ∙ x) = logHeight x := by
  rw [relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight,
    relativeSubspaceHeight_span_singleton hx,
    logHeight_eq_log_mulHeight]

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
