/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Comparison
public import TauCeti.NumberTheory.Height.Subspace

/-!
# The relative Arakelov height of a subspace

Let `K` be a number field and `ι` a finite linearly ordered type. The relative Arakelov height of
a subspace `U` of `K^ι` is the relative Euclidean projective height `TauCeti.arakelovMulHeight` of
its Plücker point, that is, of the Plücker coordinates of any basis of `U`. It differs from the
relative sup height `Submodule.relativeSubspaceHeight` only at the infinite places, where it uses
the Euclidean norm of the Plücker vector instead of its maximum norm. The zero subspace and the
whole space have height `1`, and a line has the height of any nonzero vector spanning it.

Comparing the two norms at the infinite places, for `U` of dimension `k` and `n = #ι`,
`relativeSubspaceHeight U ≤ relativeSubspaceArakelovHeight U` and
`relativeSubspaceArakelovHeight U ≤ √(n.choose k) ^ [K : ℚ] · relativeSubspaceHeight U`, since the
Plücker vector has `n.choose k` coordinates. The first bound transfers the Northcott property of
the sup height: `K^ι` has finitely many subspaces of bounded Arakelov height, of all dimensions
together.

## Main definitions

* `Submodule.relativeSubspaceArakelovHeight U`: the relative Arakelov height of `U`.
* `Submodule.relativeSubspaceArakelovLogHeight U`: its logarithm.

## Main results

* `Submodule.relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker`: the height of `U` is
  the Arakelov height of the Plücker coordinates of any basis of `U`.
* `Submodule.relativeSubspaceHeight_le_relativeSubspaceArakelovHeight` and
  `Submodule.relativeSubspaceArakelovHeight_le_sqrt_choose_pow_mul_relativeSubspaceHeight`: the
  comparison with the relative sup height.
* `Submodule.instNorthcottRelativeSubspaceArakelovHeight` and
  `Submodule.instNorthcottRelativeSubspaceArakelovLogHeight`: the Northcott property.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §6.1 and §6.3.
* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of
  Math. **85** (1967), 430–472.
-/

public noncomputable section

namespace Submodule

open Height TauCeti Set Module NumberField

variable {ι K : Type*} [LinearOrder ι] [Finite ι] [Field K] [NumberField K]
  (U : Submodule K (ι → K))

/-- The relative Arakelov height of a subspace `U` of `ι → K`: the relative Euclidean projective
height `TauCeti.arakelovMulHeight` of the Plücker coordinates of any basis of `U`
(`relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker`). -/
def relativeSubspaceArakelovHeight : ℝ :=
  arakelovMulHeight (relativePluckerPoint U).rep

/-- The relative logarithmic Arakelov height of a subspace `U` of `ι → K`: the logarithm of
`relativeSubspaceArakelovHeight U`. -/
def relativeSubspaceArakelovLogHeight : ℝ :=
  arakelovLogHeight (relativePluckerPoint U).rep

/-- The relative logarithmic Arakelov height is the logarithm of the relative Arakelov height. -/
theorem relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight :
    relativeSubspaceArakelovLogHeight U = Real.log (relativeSubspaceArakelovHeight U) :=
  arakelovLogHeight_eq_log_arakelovMulHeight _

variable {U} in
/-- The relative Arakelov height of `U` is the Arakelov height of the Plücker coordinates of any
basis of `U`. -/
theorem relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker {p : ℕ}
    (b : Basis (Fin p) K U) :
    relativeSubspaceArakelovHeight U = arakelovMulHeight (plucker fun i ↦ (b i : ι → K)) := by
  obtain rfl : finrank K U = p := (finrank_eq_card_basis b).trans (Fintype.card_fin p)
  -- The chosen representative of the Plücker point is a nonzero multiple of the coordinates.
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K _
    ((plucker_ne_zero_iff _).2 b.linearIndependent_coe_basis)
  rw [relativeSubspaceArakelovHeight, relativePluckerPoint_eq_mk b, ← ha, Units.smul_def,
    arakelovMulHeight_smul _ a.ne_zero]

variable {U} in
/-- The relative logarithmic Arakelov height of `U` is the logarithmic Arakelov height of the
Plücker coordinates of any basis of `U`. -/
theorem relativeSubspaceArakelovLogHeight_eq_arakelovLogHeight_plucker {p : ℕ}
    (b : Basis (Fin p) K U) :
    relativeSubspaceArakelovLogHeight U = arakelovLogHeight (plucker fun i ↦ (b i : ι → K)) := by
  rw [relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight,
    relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker b,
    arakelovLogHeight_eq_log_arakelovMulHeight]

/-- The relative Arakelov height of the span of a linearly independent family is the Arakelov
height of its Plücker coordinates. -/
theorem relativeSubspaceArakelovHeight_span_range {p : ℕ} {x : Fin p → ι → K}
    (hx : LinearIndependent K x) :
    relativeSubspaceArakelovHeight (span K (range x)) = arakelovMulHeight (plucker x) := by
  rw [relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker (Basis.span hx)]
  simp_rw [Basis.coe_span_apply]

/-- The relative logarithmic Arakelov height of the span of a linearly independent family is the
logarithmic Arakelov height of its Plücker coordinates. -/
theorem relativeSubspaceArakelovLogHeight_span_range {p : ℕ} {x : Fin p → ι → K}
    (hx : LinearIndependent K x) :
    relativeSubspaceArakelovLogHeight (span K (range x)) = arakelovLogHeight (plucker x) := by
  rw [relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight,
    relativeSubspaceArakelovHeight_span_range hx, arakelovLogHeight_eq_log_arakelovMulHeight]

/-- The relative Arakelov height of a subspace is at least `1`. -/
theorem one_le_relativeSubspaceArakelovHeight : 1 ≤ relativeSubspaceArakelovHeight U :=
  one_le_arakelovMulHeight _

/-- The relative Arakelov height of a subspace is positive. -/
theorem relativeSubspaceArakelovHeight_pos : 0 < relativeSubspaceArakelovHeight U :=
  arakelovMulHeight_pos _

/-- The relative logarithmic Arakelov height of a subspace is nonnegative. -/
theorem relativeSubspaceArakelovLogHeight_nonneg : 0 ≤ relativeSubspaceArakelovLogHeight U :=
  arakelovLogHeight_nonneg _

/-- The relative sup height of a subspace is at most its relative Arakelov height. -/
theorem relativeSubspaceHeight_le_relativeSubspaceArakelovHeight :
    relativeSubspaceHeight U ≤ relativeSubspaceArakelovHeight U := by
  rw [relativeSubspaceHeight_eq_mulHeight_plucker (finBasis K U),
    relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker (finBasis K U)]
  exact mulHeight_le_arakelovMulHeight _

/-- The relative Arakelov height of a subspace `U` of dimension `k` is at most
`√(#ι.choose k) ^ [K : ℚ]` times its relative sup height: its Plücker vector has `#ι.choose k`
coordinates. -/
theorem relativeSubspaceArakelovHeight_le_sqrt_choose_pow_mul_relativeSubspaceHeight :
    relativeSubspaceArakelovHeight U ≤
      √((Nat.card ι).choose (finrank K U)) ^ finrank ℚ K * relativeSubspaceHeight U := by
  set x : Fin (finrank K U) → ι → K := fun i ↦ (finBasis K U i : ι → K)
  have hx : plucker x ≠ 0 := (plucker_ne_zero_iff _).2 (finBasis K U).linearIndependent_coe_basis
  -- The Plücker vector is nonzero, so its index type is nonempty.
  have : Nonempty (powersetCard ι (finrank K U)) := by
    by_contra h
    exact hx (funext fun s ↦ (not_nonempty_iff.1 h).elim s)
  rw [relativeSubspaceHeight_eq_mulHeight_plucker (finBasis K U),
    relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker (finBasis K U),
    ← powersetCard.card]
  exact arakelovMulHeight_le_sqrt_natCard_pow_mul_mulHeight _

/-- The relative logarithmic sup height of a subspace is at most its relative logarithmic Arakelov
height. -/
theorem relativeSubspaceLogHeight_le_relativeSubspaceArakelovLogHeight :
    relativeSubspaceLogHeight U ≤ relativeSubspaceArakelovLogHeight U := by
  rw [relativeSubspaceLogHeight_eq_log_relativeSubspaceHeight,
    relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight]
  exact Real.log_le_log (relativeSubspaceHeight_pos U)
    (relativeSubspaceHeight_le_relativeSubspaceArakelovHeight U)

/-- The relative logarithmic Arakelov height of a subspace `U` of dimension `k` exceeds its
relative logarithmic sup height by at most `[K : ℚ] / 2 · log (#ι.choose k)`. -/
theorem relativeSubspaceArakelovLogHeight_le_mul_log_choose_add_relativeSubspaceLogHeight :
    relativeSubspaceArakelovLogHeight U ≤
      finrank ℚ K / 2 * Real.log ((Nat.card ι).choose (finrank K U)) +
        relativeSubspaceLogHeight U := by
  rw [relativeSubspaceLogHeight_eq_logHeight_plucker (finBasis K U),
    relativeSubspaceArakelovLogHeight_eq_arakelovLogHeight_plucker (finBasis K U),
    ← powersetCard.card]
  exact arakelovLogHeight_le_mul_log_natCard_add_logHeight _

/-- The zero subspace has relative Arakelov height `1`. -/
@[simp]
theorem relativeSubspaceArakelovHeight_bot :
    relativeSubspaceArakelovHeight (⊥ : Submodule K (ι → K)) = 1 := by
  refine le_antisymm ?_ (one_le_relativeSubspaceArakelovHeight _)
  simpa using relativeSubspaceArakelovHeight_le_sqrt_choose_pow_mul_relativeSubspaceHeight
    (⊥ : Submodule K (ι → K))

/-- The whole space has relative Arakelov height `1`. -/
@[simp]
theorem relativeSubspaceArakelovHeight_top :
    relativeSubspaceArakelovHeight (⊤ : Submodule K (ι → K)) = 1 := by
  have := Fintype.ofFinite ι
  refine le_antisymm ?_ (one_le_relativeSubspaceArakelovHeight _)
  simpa [Nat.card_eq_fintype_card, finrank_fintype_fun_eq_card] using
    relativeSubspaceArakelovHeight_le_sqrt_choose_pow_mul_relativeSubspaceHeight
      (⊤ : Submodule K (ι → K))

/-- The zero subspace has relative logarithmic Arakelov height `0`. -/
@[simp]
theorem relativeSubspaceArakelovLogHeight_bot :
    relativeSubspaceArakelovLogHeight (⊥ : Submodule K (ι → K)) = 0 := by
  simp [relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight]

/-- The whole space has relative logarithmic Arakelov height `0`. -/
@[simp]
theorem relativeSubspaceArakelovLogHeight_top :
    relativeSubspaceArakelovLogHeight (⊤ : Submodule K (ι → K)) = 0 := by
  simp [relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight]

/-- The relative Arakelov height of the line spanned by a nonzero vector is the Arakelov height of
the vector. -/
@[simp]
theorem relativeSubspaceArakelovHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    relativeSubspaceArakelovHeight (K ∙ x) = arakelovMulHeight x := by
  have h := relativeSubspaceArakelovHeight_span_range (linearIndependent_unique_iff.2 hx :
    LinearIndependent K ![x])
  rw [Matrix.range_cons, Matrix.range_empty, union_empty] at h
  rw [h, ← arakelovMulHeight_comp_equiv powersetCard.ofSingleton]
  congr 1
  ext i
  simp

/-- The relative logarithmic Arakelov height of the line spanned by a nonzero vector is the
logarithmic Arakelov height of the vector. -/
@[simp]
theorem relativeSubspaceArakelovLogHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    relativeSubspaceArakelovLogHeight (K ∙ x) = arakelovLogHeight x := by
  rw [relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight,
    relativeSubspaceArakelovHeight_span_singleton hx, arakelovLogHeight_eq_log_arakelovMulHeight]

/-- The relative Arakelov height of subspaces has the Northcott property: for every `B` there are
finitely many subspaces of `ι → K` of relative Arakelov height at most `B`, of all dimensions
together. -/
instance instNorthcottRelativeSubspaceArakelovHeight :
    Northcott (relativeSubspaceArakelovHeight (ι := ι) (K := K)) where
  finite_le B := (Northcott.finite_le (h := relativeSubspaceHeight (ι := ι) (K := K)) B).subset
    fun U hU ↦ (relativeSubspaceHeight_le_relativeSubspaceArakelovHeight U).trans hU

/-- The relative logarithmic Arakelov height of subspaces has the Northcott property. -/
instance instNorthcottRelativeSubspaceArakelovLogHeight :
    Northcott (relativeSubspaceArakelovLogHeight (ι := ι) (K := K)) := by
  have heq : relativeSubspaceArakelovLogHeight (ι := ι) (K := K) =
      Real.log ∘ relativeSubspaceArakelovHeight :=
    funext relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight
  rw [heq]
  exact Northcott.comp_of_bddAbove _ _ fun B ↦
    bddAbove_def.mpr ⟨Real.exp B, fun _ ↦ Real.le_exp_of_log_le⟩

end Submodule

/-! Over `ℚ` there are finitely many subspaces of bounded relative logarithmic Arakelov height. -/

example (B : ℝ) :
    {U : Submodule ℚ (Fin 3 → ℚ) | U.relativeSubspaceArakelovLogHeight ≤ B}.Finite :=
  Northcott.finite_le B
