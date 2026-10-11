/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.FiniteInf
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Flattening the boundary of an orthant

The boundary of the nonnegative orthant in `(ι → ℝ) × ℝ` is PL homeomorphic to `ι → ℝ`.
The forward map subtracts the last coordinate from every other coordinate. Its inverse
adjoins a zero coordinate and subtracts the minimum of all the coordinates. The minimum
includes the adjoined zero, so the construction also works when `ι` is empty.

This is the local polyhedral model at a vertex of a simplex boundary: below the opposite
facet, the simplex boundary is a neighbourhood of the apex in the orthant boundary.
Both coordinate maps have explicit affine formulas on polyhedral cells.

The finite-minimum decomposition reuses `Finset.infCell` and
`Finset.infAffine_eq_of_mem_infCell`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
  Springer (1972), Chapters 1--2 (polyhedral local models and vertex stars).
-/

public section

noncomputable section

open Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- A point of the orthant boundary has nonnegative coordinates, at least one of which
is zero. -/
@[simp]
theorem mem_frontier_nonnegOrthant_iff [Finite ι] (p : (ι → ℝ) × ℝ) :
    p ∈ frontier (Ici (0 : (ι → ℝ) × ℝ)) ↔
      (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ (p.2 = 0 ∨ ∃ i, p.1 i = 0) := by
  have hpi : interior (Ici (0 : ι → ℝ)) = {x | ∀ i, 0 < x i} := by
    have heq : Ici (0 : ι → ℝ) = pi univ (fun _ => Ici (0 : ℝ)) := by
      ext x
      simp [Pi.le_def]
    rw [heq, interior_pi_set (finite_univ)]
    ext x
    simp
  rw [frontier, isClosed_Ici.closure_eq]
  have hprod : Ici (0 : (ι → ℝ) × ℝ) =
      Ici (0 : ι → ℝ) ×ˢ Ici (0 : ℝ) := by ext p; rfl
  rw [hprod, interior_prod_eq, hpi, interior_Ici]
  simp only [mem_sdiff, mem_prod, mem_Ici, mem_ofPred_eq, mem_Ioi, Pi.le_def, Pi.zero_apply]
  constructor
  · rintro ⟨⟨hx, ht⟩, h⟩
    refine ⟨hx, ht, ?_⟩
    by_cases hzero : p.2 = 0
    · exact Or.inl hzero
    · right
      have hn : ¬ ∀ i, 0 < p.1 i := fun hxpos =>
        h ⟨hxpos, lt_of_le_of_ne ht (Ne.symm hzero)⟩
      obtain ⟨i, hi⟩ := not_forall.mp hn
      exact ⟨i, le_antisymm (not_lt.mp hi) (hx i)⟩
  · rintro ⟨hx, ht, hz⟩
    refine ⟨⟨hx, ht⟩, ?_⟩
    rcases hz with h | ⟨i, h⟩
    · simp [h]
    · rintro ⟨hxpos, _⟩
      simpa [h] using hxpos i

omit [Fintype ι] in
/-- The linear flattening map subtracting the last coordinate from the others. -/
def orthantProjection : ((ι → ℝ) × ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _) -
      ContinuousLinearMap.snd ℝ _ _

omit [Fintype ι] in
/-- Each flat coordinate is the difference from the last orthant coordinate. -/
@[simp]
theorem orthantProjection_apply (p : (ι → ℝ) × ℝ) (i : ι) :
    orthantProjection p i = p.1 i - p.2 := (rfl)

private def extendedCoordinate (i : Option ι) : (ι → ℝ) →ᴬ[ℝ] ℝ :=
  match i with
  | none => ContinuousAffineMap.const ℝ _ 0
  | some j => (ContinuousLinearMap.proj j).toContinuousAffineMap

private def orthantMin (y : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Option ι => extendedCoordinate i y)

private theorem orthantMin_le_zero (y : ι → ℝ) : orthantMin y ≤ 0 :=
  Finset.inf'_le _ (Finset.mem_univ none)

private theorem orthantMin_le (y : ι → ℝ) (i : ι) : orthantMin y ≤ y i :=
  Finset.inf'_le _ (Finset.mem_univ (some i))

/-- Lift flat coordinates to the boundary of the nonnegative orthant. Adjoin zero and
subtract the minimum coordinate, making every coordinate nonnegative and one zero. -/
def orthantLift (y : ι → ℝ) : (ι → ℝ) × ℝ :=
  (fun i => y i - orthantMin y, -orthantMin y)

/-- The explicit inverse formula, using the minimum of zero and the given coordinates. -/
theorem orthantLift_def (y : ι → ℝ) :
    orthantLift y =
      let m := Finset.univ.inf' Finset.univ_nonempty (Option.elim' 0 y)
      ((fun i => y i - m), -m) := by
  have heq : (fun i : Option ι => extendedCoordinate i y) = Option.elim' 0 y := by
    funext i
    cases i <;> rfl
  simp only [orthantLift, orthantMin, heq]

/-- Nonnegative flat coordinates lift to the face with last coordinate zero. -/
theorem orthantLift_of_nonneg {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) :
    orthantLift y = (y, 0) := by
  have hm : orthantMin y = 0 := by
    apply le_antisymm (orthantMin_le_zero y)
    apply Finset.le_inf'
    intro i _
    cases i with
    | none => simp [extendedCoordinate]
    | some i => exact hy i
  simp [orthantLift, hm]

@[simp]
theorem orthantLift_zero : orthantLift (0 : ι → ℝ) = 0 :=
  orthantLift_of_nonneg (fun _ => le_rfl)

/-- The lift is piecewise affine on the whole coordinate space, with one minimum cell
for each coordinate, including the adjoined zero coordinate. -/
theorem isPiecewiseAffineOn_orthantLift :
    IsPiecewiseAffineOn (orthantLift : (ι → ℝ) → (ι → ℝ) × ℝ) univ := by
  classical
  let A : Option ι → (ι → ℝ) →ᴬ[ℝ] ((ι → ℝ) × ℝ) := fun j =>
    ((ContinuousAffineMap.id ℝ (ι → ℝ)) -
      (ContinuousLinearMap.pi fun _ : ι =>
        (extendedCoordinate j).contLinear).toContinuousAffineMap).prod (-extendedCoordinate j)
  -- Every extended coordinate is linear, including the zero coordinate.
  have hA (j : Option ι) (y : ι → ℝ) :
      A j y = ((fun i => y i - extendedCoordinate j y), -extendedCoordinate j y) := by
    cases j <;> rfl
  refine isPiecewiseAffineOn_of_finite
    (C := Finset.univ.infCell (extendedCoordinate (ι := ι))) (A := fun j => A j)
    (fun j => Finset.univ.isConvexPolyhedron_infCell _ j)
    (Finset.univ.subset_iUnion_infCell Finset.univ_nonempty _) ?_
  intro j y hy
  rw [hA, orthantLift, orthantMin,
    Finset.univ.infAffine_eq_of_mem_infCell Finset.univ_nonempty _ j hy.2]

/-- The lift lands on the actual topological boundary of the orthant. -/
theorem orthantLift_mem_frontier (y : ι → ℝ) :
    orthantLift y ∈ frontier (Ici (0 : (ι → ℝ) × ℝ)) := by
  classical
  rw [mem_frontier_nonnegOrthant_iff]
  refine ⟨fun i => sub_nonneg.mpr (orthantMin_le y i), neg_nonneg.mpr (orthantMin_le_zero y), ?_⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i : Option ι => extendedCoordinate i y)
  have hi' : orthantMin y = extendedCoordinate i y := hi
  cases i with
  | none => exact Or.inl (by simp [orthantLift, hi', extendedCoordinate])
  | some i => exact Or.inr ⟨i, by simp [orthantLift, hi', extendedCoordinate]⟩

/-- Projecting a lifted point recovers its flat coordinates. -/
@[simp]
theorem orthantProjection_orthantLift (y : ι → ℝ) :
    orthantProjection (orthantLift y) = y := by
  ext i
  simp [orthantLift]

/-- Subtracting the last lifted coordinate recovers each original coordinate. -/
@[simp]
theorem orthantLift_fst_sub_snd (y : ι → ℝ) (i : ι) :
    (orthantLift y).1 i - (orthantLift y).2 = y i := by
  simpa only [orthantProjection_apply] using congrFun (orthantProjection_orthantLift y) i

private theorem orthantMin_orthantProjection {p : (ι → ℝ) × ℝ}
    (hp : p ∈ frontier (Ici (0 : (ι → ℝ) × ℝ))) :
    orthantMin (orthantProjection p) = -p.2 := by
  obtain ⟨hx, ht, hz⟩ := (mem_frontier_nonnegOrthant_iff p).mp hp
  apply le_antisymm
  · rcases hz with h | ⟨i, h⟩
    · simpa [h] using orthantMin_le_zero (orthantProjection p)
    · simpa [h] using orthantMin_le (orthantProjection p) i
  · apply Finset.le_inf'
    intro i _
    cases i with
    | none => simpa [extendedCoordinate] using neg_nonpos.mpr ht
    | some i => simp only [extendedCoordinate, ContinuousLinearMap.coe_toContinuousAffineMap,
        ContinuousLinearMap.proj_apply, orthantProjection_apply]; linarith [hx i]

/-- Lifting the flat coordinates of an orthant boundary point recovers that point. -/
theorem orthantLift_orthantProjection {p : (ι → ℝ) × ℝ}
    (hp : p ∈ frontier (Ici (0 : (ι → ℝ) × ℝ))) :
    orthantLift (orthantProjection p) = p := by
  simp [orthantLift, orthantMin_orthantProjection hp]

/-- A PL homeomorphism flattening the boundary of the nonnegative orthant. With `ι = Fin n`,
this identifies an `(n + 1)`-orthant boundary with `ℝⁿ`, including `n = 0`. -/
def orthantBoundaryHomeomorph :
    frontier (Ici (0 : (ι → ℝ) × ℝ)) ≃ₜ (ι → ℝ) where
  toFun p := orthantProjection p.1
  invFun y := ⟨orthantLift y, orthantLift_mem_frontier y⟩
  left_inv p := Subtype.ext (orthantLift_orthantProjection p.2)
  right_inv := orthantProjection_orthantLift
  continuous_toFun := orthantProjection.continuous.comp continuous_subtype_val
  continuous_invFun :=
    (continuousOn_univ.mp isPiecewiseAffineOn_orthantLift.continuousOn).subtype_mk _

/-- The homeomorphism reads the linear flattening coordinates. -/
@[simp]
theorem orthantBoundaryHomeomorph_apply
    (p : frontier (Ici (0 : (ι → ℝ) × ℝ))) (i : ι) :
    orthantBoundaryHomeomorph p i = p.1.1 i - p.1.2 := (rfl)

/-- The inverse homeomorphism is the minimum-subtraction lift. -/
@[simp]
theorem coe_orthantBoundaryHomeomorph_symm_apply (y : ι → ℝ) :
    ((orthantBoundaryHomeomorph.symm y : frontier (Ici (0 : (ι → ℝ) × ℝ))) :
      (ι → ℝ) × ℝ) = orthantLift y := (rfl)

end TauCeti
