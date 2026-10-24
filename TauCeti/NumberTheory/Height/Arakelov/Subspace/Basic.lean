/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Comparison
public import TauCeti.NumberTheory.Height.Subspace.Basic

/-!
# The Arakelov height of a subspace

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

The absolute height `Submodule.subspaceHeight U` is the `[K : ℚ]`-th root of the relative Arakelov
height, equivalently the absolute Euclidean height `TauCeti.height2` of the Plücker coordinates of
any basis of `U`. This is the height of a subspace in Evertse–Ferretti's quantitative Subspace
Theorem. It inherits the Northcott property.

The orthogonal complement of `U` for the dot product, `Submodule.euclideanDual`, has the same
relative Arakelov height and the same absolute height as `U`, since its Plücker coordinates are
the complementary Plücker coordinates of `U` up to a common nonzero factor and signs. Over `ℚ`,
the plane in `ℚ³` orthogonal to `(1, 2, 2)` has absolute height `3`, the Euclidean norm of
`(1, 2, 2)`.

## Main definitions

* `Submodule.relativeSubspaceArakelovHeight U`: the relative Arakelov height of `U`.
* `Submodule.relativeSubspaceArakelovLogHeight U`: its logarithm.
* `Submodule.subspaceHeight U`: the absolute Euclidean height of `U`.
* `Submodule.subspaceLogHeight U`: its logarithm.

## Main results

* `Submodule.relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker`: the height of `U` is
  the Arakelov height of the Plücker coordinates of any basis of `U`.
* `Submodule.relativeSubspaceHeight_le_relativeSubspaceArakelovHeight` and
  `Submodule.relativeSubspaceArakelovHeight_le_sqrt_choose_pow_mul_relativeSubspaceHeight`: the
  comparison with the relative sup height.
* `Submodule.instNorthcottRelativeSubspaceArakelovHeight` and
  `Submodule.instNorthcottRelativeSubspaceArakelovLogHeight`: the Northcott property.
* `Submodule.subspaceHeight_eq_height2_plucker`: the absolute height of `U` is the absolute
  Euclidean height of the Plücker coordinates of any basis of `U`.
* `Submodule.relativeSubspaceHeight_rpow_le_subspaceHeight` and
  `Submodule.subspaceHeight_le_sqrt_choose_mul_relativeSubspaceHeight_rpow`: the comparison with
  the absolute sup height, with their logarithmic forms.
* `Submodule.relativeSubspaceArakelovHeight_euclideanDual` and
  `Submodule.subspaceHeight_euclideanDual`: the orthogonal complement of `U` for the dot product
  has the height of `U`, with their logarithmic forms.
* `Submodule.finite_subspaceHeight_le`, `Submodule.instNorthcottSubspaceHeight` and
  `Submodule.instNorthcottSubspaceLogHeight`: Northcott's theorem for the absolute height.

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

/-- **Duality of heights.** The orthogonal complement of a subspace `U` of `ι → K` for the dot
product has the relative Arakelov height of `U`. -/
@[simp]
theorem relativeSubspaceArakelovHeight_euclideanDual [Fintype ι] :
    relativeSubspaceArakelovHeight U.euclideanDual = relativeSubspaceArakelovHeight U := by
  let b := finBasis K U
  let b' := finBasis K U.euclideanDual
  obtain ⟨c, hc, h⟩ :=
    exists_plucker_eq_mul_plucker_compl_or_eq_neg (finrank_add_finrank_euclideanDual U)
    b.linearIndependent_coe_basis b'.linearIndependent_coe_basis
    fun i j ↦ mem_euclideanDual.1 (b' j).2 _ (b i).2
  rw [relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker b',
    relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker b,
    arakelovMulHeight_eq_of_forall_eq_or_eq_neg h]
  -- The tuple `fun t ↦ c * plucker _ (compl _ t)` is `c • (plucker _ ∘ compl _)` pointwise.
  exact (arakelovMulHeight_smul _ hc).trans (arakelovMulHeight_comp_equiv _ _)

/-- The orthogonal complement of a subspace `U` of `ι → K` for the dot product has the relative
logarithmic Arakelov height of `U`. -/
@[simp]
theorem relativeSubspaceArakelovLogHeight_euclideanDual [Fintype ι] :
    relativeSubspaceArakelovLogHeight U.euclideanDual = relativeSubspaceArakelovLogHeight U := by
  simp [relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight]

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

/-! ### The absolute Euclidean height of a subspace -/

/-- The absolute Euclidean height of a subspace `U` of `ι → K`: the `[K : ℚ]`-th root of its
relative Arakelov height. It is the absolute Euclidean height `TauCeti.height2` of the Plücker
coordinates of any basis of `U` (`subspaceHeight_eq_height2_plucker`). -/
def subspaceHeight : ℝ :=
  relativeSubspaceArakelovHeight U ^ (finrank ℚ K : ℝ)⁻¹

/-- The absolute logarithmic Euclidean height of a subspace `U` of `ι → K`: the logarithm of
`subspaceHeight U`. -/
def subspaceLogHeight : ℝ :=
  Real.log (subspaceHeight U)

/-- The absolute logarithmic height of a subspace is the logarithm of its absolute height. -/
theorem subspaceLogHeight_eq_log_subspaceHeight :
    subspaceLogHeight U = Real.log (subspaceHeight U) :=
  (rfl)

/-- The relative Arakelov height of a subspace is the `[K : ℚ]`-th power of its absolute
height. -/
theorem subspaceHeight_pow_finrank :
    subspaceHeight U ^ finrank ℚ K = relativeSubspaceArakelovHeight U :=
  Real.rpow_inv_natCast_pow (relativeSubspaceArakelovHeight_pos U).le finrank_pos.ne'

/-- The absolute logarithmic height of a subspace is its relative logarithmic Arakelov height
divided by `[K : ℚ]`. -/
theorem subspaceLogHeight_eq_relativeSubspaceArakelovLogHeight_div :
    subspaceLogHeight U = relativeSubspaceArakelovLogHeight U / finrank ℚ K := by
  rw [subspaceLogHeight, subspaceHeight,
    relativeSubspaceArakelovLogHeight_eq_log_relativeSubspaceArakelovHeight,
    Real.log_rpow (relativeSubspaceArakelovHeight_pos U), inv_mul_eq_div]

variable {U} in
/-- The absolute height of `U` is the absolute Euclidean height of the Plücker coordinates of any
basis of `U`. -/
theorem subspaceHeight_eq_height2_plucker {p : ℕ} (b : Basis (Fin p) K U) :
    subspaceHeight U = height2 (plucker fun i ↦ (b i : ι → K)) := by
  have h := arakelovMulHeight_eq_height2 (plucker fun i ↦ (b i : ι → K))
  rwa [ite_eq_right ((plucker_ne_zero_iff _).2 b.linearIndependent_coe_basis), one_div,
    ← relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker b] at h

/-- The absolute height of the span of a linearly independent family is the absolute Euclidean
height of its Plücker coordinates. -/
theorem subspaceHeight_span_range {p : ℕ} {x : Fin p → ι → K} (hx : LinearIndependent K x) :
    subspaceHeight (span K (range x)) = height2 (plucker x) := by
  rw [subspaceHeight_eq_height2_plucker (Basis.span hx)]
  simp_rw [Basis.coe_span_apply]

/-- The absolute height of a subspace is at least `1`. -/
theorem one_le_subspaceHeight : 1 ≤ subspaceHeight U :=
  Real.one_le_rpow (one_le_relativeSubspaceArakelovHeight U) (by positivity)

/-- The absolute height of a subspace is positive. -/
theorem subspaceHeight_pos : 0 < subspaceHeight U :=
  zero_lt_one.trans_le (one_le_subspaceHeight U)

/-- The absolute logarithmic height of a subspace is nonnegative. -/
theorem subspaceLogHeight_nonneg : 0 ≤ subspaceLogHeight U :=
  Real.log_nonneg (one_le_subspaceHeight U)

/-- The zero subspace has absolute height `1`. -/
@[simp]
theorem subspaceHeight_bot : subspaceHeight (⊥ : Submodule K (ι → K)) = 1 := by
  simp [subspaceHeight]

/-- The whole space has absolute height `1`. -/
@[simp]
theorem subspaceHeight_top : subspaceHeight (⊤ : Submodule K (ι → K)) = 1 := by
  simp [subspaceHeight]

/-- The zero subspace has absolute logarithmic height `0`. -/
@[simp]
theorem subspaceLogHeight_bot : subspaceLogHeight (⊥ : Submodule K (ι → K)) = 0 := by
  simp [subspaceLogHeight]

/-- The whole space has absolute logarithmic height `0`. -/
@[simp]
theorem subspaceLogHeight_top : subspaceLogHeight (⊤ : Submodule K (ι → K)) = 0 := by
  simp [subspaceLogHeight]

/-- The absolute height of the line spanned by a nonzero vector is the absolute Euclidean height
of the vector. -/
@[simp]
theorem subspaceHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    subspaceHeight (K ∙ x) = height2 x := by
  have h := arakelovMulHeight_eq_height2 x
  rwa [ite_eq_right hx, one_div, ← relativeSubspaceArakelovHeight_span_singleton hx] at h

/-- The absolute logarithmic height of the line spanned by a nonzero vector is the logarithm of
the absolute Euclidean height of the vector. -/
@[simp]
theorem subspaceLogHeight_span_singleton {x : ι → K} (hx : x ≠ 0) :
    subspaceLogHeight (K ∙ x) = Real.log (height2 x) := by
  rw [subspaceLogHeight, subspaceHeight_span_singleton hx]

/-- **Duality of heights**, Evertse–Ferretti (6.13). The orthogonal complement of a subspace `U` of
`ι → K` for the dot product has the absolute height of `U`. -/
@[simp]
theorem subspaceHeight_euclideanDual [Fintype ι] :
    subspaceHeight U.euclideanDual = subspaceHeight U := by
  simp [subspaceHeight]

/-- The orthogonal complement of a subspace `U` of `ι → K` for the dot product has the absolute
logarithmic height of `U`. -/
@[simp]
theorem subspaceLogHeight_euclideanDual [Fintype ι] :
    subspaceLogHeight U.euclideanDual = subspaceLogHeight U := by
  simp [subspaceLogHeight]

/-- The absolute sup height of a subspace, the `[K : ℚ]`-th root of its relative sup height, is at
most its absolute Euclidean height. -/
theorem relativeSubspaceHeight_rpow_le_subspaceHeight :
    relativeSubspaceHeight U ^ (finrank ℚ K : ℝ)⁻¹ ≤ subspaceHeight U :=
  Real.rpow_le_rpow (relativeSubspaceHeight_pos U).le
    (relativeSubspaceHeight_le_relativeSubspaceArakelovHeight U) (by positivity)

/-- The absolute Euclidean height of a subspace `U` of dimension `k` is at most `√(#ι.choose k)`
times its absolute sup height, the `[K : ℚ]`-th root of its relative sup height. -/
theorem subspaceHeight_le_sqrt_choose_mul_relativeSubspaceHeight_rpow :
    subspaceHeight U ≤
      √((Nat.card ι).choose (finrank K U)) * relativeSubspaceHeight U ^ (finrank ℚ K : ℝ)⁻¹ := by
  have hd : (finrank ℚ K : ℕ) ≠ 0 := finrank_pos.ne'
  calc subspaceHeight U
      ≤ (√((Nat.card ι).choose (finrank K U)) ^ finrank ℚ K * relativeSubspaceHeight U) ^
          (finrank ℚ K : ℝ)⁻¹ :=
        Real.rpow_le_rpow (relativeSubspaceArakelovHeight_pos U).le
          (relativeSubspaceArakelovHeight_le_sqrt_choose_pow_mul_relativeSubspaceHeight U)
          (by positivity)
    _ = _ := by
        rw [Real.mul_rpow (by positivity) (relativeSubspaceHeight_pos U).le,
          Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) hd]

/-- The absolute logarithmic sup height of a subspace, its relative logarithmic sup height divided
by `[K : ℚ]`, is at most its absolute logarithmic Euclidean height. -/
theorem relativeSubspaceLogHeight_div_le_subspaceLogHeight :
    relativeSubspaceLogHeight U / finrank ℚ K ≤ subspaceLogHeight U := by
  rw [subspaceLogHeight_eq_relativeSubspaceArakelovLogHeight_div]
  exact div_le_div_of_nonneg_right
    (relativeSubspaceLogHeight_le_relativeSubspaceArakelovLogHeight U) (Nat.cast_nonneg _)

/-- The absolute logarithmic Euclidean height of a subspace `U` of dimension `k` exceeds its
absolute logarithmic sup height by at most `log (#ι.choose k) / 2`. -/
theorem subspaceLogHeight_le_log_choose_div_two_add_relativeSubspaceLogHeight_div :
    subspaceLogHeight U ≤
      Real.log ((Nat.card ι).choose (finrank K U)) / 2 +
        relativeSubspaceLogHeight U / finrank ℚ K := by
  have hd : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.2 finrank_pos
  rw [subspaceLogHeight_eq_relativeSubspaceArakelovLogHeight_div, div_le_iff₀ hd]
  exact (relativeSubspaceArakelovLogHeight_le_mul_log_choose_add_relativeSubspaceLogHeight
    U).trans_eq (by field_simp)

/-- **Northcott's theorem for subspaces** (Schmidt): for every `B` there are finitely many
subspaces of `ι → K` of absolute height at most `B`, of all dimensions together. -/
theorem finite_subspaceHeight_le (B : ℝ) :
    {U : Submodule K (ι → K) | subspaceHeight U ≤ B}.Finite :=
  (Northcott.finite_le (h := relativeSubspaceArakelovHeight (ι := ι) (K := K))
    (B ^ finrank ℚ K)).subset fun U hU ↦ by
      rw [Set.mem_ofPred_eq, ← subspaceHeight_pow_finrank]
      exact pow_le_pow_left₀ (subspaceHeight_pos U).le hU _

/-- The absolute height of subspaces has the Northcott property. -/
instance instNorthcottSubspaceHeight : Northcott (subspaceHeight (ι := ι) (K := K)) :=
  ⟨finite_subspaceHeight_le⟩

/-- The absolute logarithmic height of subspaces has the Northcott property. -/
instance instNorthcottSubspaceLogHeight : Northcott (subspaceLogHeight (ι := ι) (K := K)) :=
  Northcott.comp_of_bddAbove (subspaceHeight (ι := ι) (K := K)) Real.log fun B ↦
    bddAbove_def.mpr ⟨Real.exp B, fun _ ↦ Real.le_exp_of_log_le⟩

end Submodule

/-! Over `ℚ` there are finitely many subspaces of bounded relative logarithmic Arakelov height. -/

example (B : ℝ) :
    {U : Submodule ℚ (Fin 3 → ℚ) | U.relativeSubspaceArakelovLogHeight ≤ B}.Finite :=
  Northcott.finite_le B

/-! Over `ℚ`, the line spanned by `(2, 2)` has absolute height `√2`: no primitive spanning vector
is needed. -/

open TauCeti NumberField in
example : (ℚ ∙ ![(2 : ℚ), 2]).subspaceHeight = √2 := by
  have h : ![(2 : ℚ), 2] = (2 : ℚ) • (1 : Fin 2 → ℚ) := by
    ext i; fin_cases i <;> simp
  have hw : (default : InfinitePlace ℚ).IsReal := by
    rw [Subsingleton.elim default Rat.infinitePlace]; exact Rat.isReal_infinitePlace
  rw [Submodule.subspaceHeight_span_singleton (by simp), h, height2_smul _ two_ne_zero, height2_eq]
  simp [InfinitePlace.mult, hw, Real.sqrt_eq_rpow, Fintype.card_eq_nat_card,
    -Nat.card_eq_fintype_card, Nat.card_fin]

/-! Over `ℚ`, the plane in `ℚ³` orthogonal to `(1, 2, 2)` has absolute height `3`, the Euclidean
norm of `(1, 2, 2)`. -/

open TauCeti NumberField in
example : (ℚ ∙ ![(1 : ℚ), 2, 2]).euclideanDual.subspaceHeight = 3 := by
  have hw : (default : InfinitePlace ℚ).IsReal := by
    rw [Subsingleton.elim default Rat.infinitePlace]; exact Rat.isReal_infinitePlace
  -- At every finite place the coordinates have absolute value at most `1`, and the first is `1`.
  have hfin (v : FinitePlace ℚ) : ⨆ i, v (![(1 : ℚ), 2, 2] i) = 1 := by
    have h2 : v 2 ≤ 1 := by
      simpa [one_add_one_eq_two] using FinitePlace.add_le v 1 1
    refine le_antisymm (ciSup_le fun i ↦ ?_) ?_
    · fin_cases i <;> simp [h2]
    · exact le_ciSup_of_le (Set.finite_range _).bddAbove 0 (by simp)
  -- `height2` sums over the `Fintype` instance obtained from `Finite`.
  have hsum :
      (letI := Fintype.ofFinite (Fin 3); ∑ i, ((![(1 : ℚ), 2, 2] i : ℚ) : ℝ) ^ 2) = 3 ^ 2 := by
    convert (show ∑ i : Fin 3, ((![(1 : ℚ), 2, 2] i : ℚ) : ℝ) ^ 2 = 3 ^ 2 by
      norm_num [Fin.sum_univ_three])
  rw [Submodule.subspaceHeight_euclideanDual, Submodule.subspaceHeight_span_singleton (by simp),
    height2_eq]
  have h3 : ((3 : ℝ) ^ 2) ^ (2⁻¹ : ℝ) = 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  simp [InfinitePlace.mult, hw, hfin, hsum, h3]

/-! Over `ℚ` there are finitely many subspaces of bounded absolute logarithmic height. -/

example (B : ℝ) : {U : Submodule ℚ (Fin 3 → ℚ) | U.subspaceLogHeight ≤ B}.Finite :=
  Northcott.finite_le B
