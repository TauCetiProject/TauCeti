/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.AlternatingForm
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration

/-!
# The full-weight type-`C` carrier is the symplectic group

`TauCeti.SpStd.groupScheme n` is the explicit full-weight Chevalley carrier of type `C_(n+1)`, the
smallest closed subgroup scheme of `GL_(2n+2)` containing the divided-power exponentials of the
Bourbaki-numbered Chevalley generators together with the weight torus of the standard lattice.
`TauCeti.SpStd.mem_GLSymplecticFin_of_mem_points` is the containment in one direction, that every
point of the carrier preserves the standard alternating form. This file supplies the other: over a
field the two point groups are equal.

## The numbered root subgroups

Each numbered root generator squares to zero in the standard representation, so its divided-power
exponential is `1 + u X` for `X` the integral matrix `TauCeti.SpStd.rootIntMatrix` of the
generator. In the enumerated coordinate basis that matrix is the single unit `E_{i,m+i}` at the
final node and the difference `E_{i,i+1} - E_{m+i+1,m+i}` of two units at a nonfinal one. Those are
the matrices of the symplectic group's long-root transvection at the terminal coordinate and of its
difference short-root element at an adjacent pair, so the carrier's four families of numbered root
points are the corresponding elements of `TauCeti.GLSymplecticFin`, and the terminal coordinate is
what makes them the Bourbaki simple roots of type `C`.

## What is not proved

The identifications of the numbered root points hold over every commutative ring; it is the
equality of the two point groups that needs a field, and it is asserted only there. Nothing below
asserts that the carrier is reductive, that its weight torus is maximal, or that the two group
*schemes* agree.

## Main results

* `TauCeti.SpStd.rootIntMatrix_inl_last`, `TauCeti.SpStd.rootIntMatrix_inr_last`,
  `TauCeti.SpStd.rootIntMatrix_inl_of_ne_last` and `TauCeti.SpStd.rootIntMatrix_inr_of_ne_last`:
  the integral matrices of the numbered root generators.
* `TauCeti.SpStd.coe_rootSubgroupPoints_eq_one_add_smul`: a root-subgroup point is `1 + u X`.
* `TauCeti.SpStd.rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit` and its three
  siblings: each numbered root point is
  the corresponding long-root transvection or difference short-root element of the symplectic
  group.
* `TauCeti.SpStd.points_eq_GLSymplecticFin`: the carrier points are exactly the symplectic
  matrices, over every field.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/
public section

open Matrix

namespace TauCeti.SpStd

universe v

variable (n : ℕ)

/-- The integral matrix of the final raising generator is a single matrix unit. -/
theorem rootIntMatrix_inl_last :
    rootIntMatrix n (.inl (Fin.last n)) =
      Matrix.single (finSumFinEquiv (Sum.inl (Fin.last n)))
        (finSumFinEquiv (Sum.inr (Fin.last n))) 1 := by
  ext r s
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective s
  apply Int.cast_injective (α := ℚ)
  rw [intCast_rootIntMatrix, val_rootGenerator_inl, positiveRootMatrix_last]
  cases a <;> cases b <;>
    simp [Matrix.single_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

/-- The integral matrix of the final lowering generator is a single matrix unit. -/
theorem rootIntMatrix_inr_last :
    rootIntMatrix n (.inr (Fin.last n)) =
      Matrix.single (finSumFinEquiv (Sum.inr (Fin.last n)))
        (finSumFinEquiv (Sum.inl (Fin.last n))) 1 := by
  ext r s
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective s
  apply Int.cast_injective (α := ℚ)
  rw [intCast_rootIntMatrix, val_rootGenerator_inr, negativeRootMatrix_last]
  cases a <;> cases b <;>
    simp [Matrix.single_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

/-- The integral matrix of a nonfinal raising generator is a difference of two matrix units. -/
theorem rootIntMatrix_inl_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootIntMatrix n (.inl i) =
      Matrix.single (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl (next n i hi))) 1 -
        Matrix.single (finSumFinEquiv (Sum.inr (next n i hi))) (finSumFinEquiv (Sum.inr i)) 1 := by
  ext r s
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective s
  apply Int.cast_injective (α := ℚ)
  rw [intCast_rootIntMatrix, val_rootGenerator_inl, positiveRootMatrix_of_ne_last n i hi]
  cases a <;> cases b <;>
    simp [Matrix.single_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

/-- The integral matrix of a nonfinal lowering generator is a difference of two matrix units. -/
theorem rootIntMatrix_inr_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootIntMatrix n (.inr i) =
      Matrix.single (finSumFinEquiv (Sum.inl (next n i hi))) (finSumFinEquiv (Sum.inl i)) 1 -
        Matrix.single (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr (next n i hi))) 1 := by
  ext r s
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective s
  apply Int.cast_injective (α := ℚ)
  rw [intCast_rootIntMatrix, val_rootGenerator_inr, negativeRootMatrix_of_ne_last n i hi]
  cases a <;> cases b <;>
    simp [Matrix.single_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

/-- The matrix of a carrier root subgroup point is `1 + u X` for the integral matrix `X` of the
corresponding root generator. -/
theorem coe_rootSubgroupPoints_eq_one_add_smul (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    ((rootSubgroupPoints n k A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
        Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) A) =
      1 + Multiplicative.toAdd u • (rootIntMatrix n k).map (Int.cast : ℤ → A) := by
  rw [coe_rootSubgroupPoints]
  simpa only [MulEquiv.apply_symm_apply] using
    (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_one_add_smul
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
      (isNilpotent_rep_rootGenerator n k) (latticeBasis n) (rootIntMatrix n k)
      (nilpotencyClass_rep_rootGenerator n k).le
      (rep_rootGenerator_latticeBasis_eq_sum n k)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u))

variable {A : Type v} [CommRing A]

/-- The final raising point of the carrier is the positive long-root transvection. -/
theorem rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit (u : Multiplicative A) :
    (rootSubgroupPoints n (.inl (Fin.last n)) A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      ((GLSymplecticFin.positiveLongRootTransvectionUnit (Fin.last n)
        (Multiplicative.toAdd u) : GLSymplecticFin (n + 1) A) :
          GL (Fin ((n + 1) + (n + 1))) A) := by
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inl_last,
    GLSymplecticFin.coe_positiveLongRootTransvectionUnit, coe_transvectionUnit]
  ext r s
  simp [Matrix.transvection, Matrix.single_apply]

/-- The final lowering point of the carrier is the negative long-root transvection. -/
theorem rootSubgroupPoints_inr_last_eq_negativeLongRootTransvectionUnit (u : Multiplicative A) :
    (rootSubgroupPoints n (.inr (Fin.last n)) A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      ((GLSymplecticFin.negativeLongRootTransvectionUnit (Fin.last n)
        (Multiplicative.toAdd u) : GLSymplecticFin (n + 1) A) :
          GL (Fin ((n + 1) + (n + 1))) A) := by
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inr_last,
    GLSymplecticFin.coe_negativeLongRootTransvectionUnit, coe_transvectionUnit]
  ext r s
  simp [Matrix.transvection, Matrix.single_apply]

/-- A nonfinal raising point of the carrier is the difference short-root element. -/
theorem rootSubgroupPoints_inl_of_ne_last_eq_differenceShortRootUnit (i : Fin (n + 1))
    (hi : i ≠ Fin.last n)
    (u : Multiplicative A) :
    (rootSubgroupPoints n (.inl i) A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      ((GLSymplecticFin.differenceShortRootUnit (lt_next n i hi).ne
        (Multiplicative.toAdd u) : GLSymplecticFin (n + 1) A) :
          GL (Fin ((n + 1) + (n + 1))) A) := by
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inl_of_ne_last n i hi,
    GLSymplecticFin.coe_differenceShortRootUnit_eq_one_add_single_sub_single]
  ext r s
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.single_apply, smul_eq_mul, Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sub,
    mul_sub, mul_ite, mul_one, mul_zero]
  split_ifs <;> ring

/-- A nonfinal lowering point of the carrier is the opposite difference short-root element. -/
theorem rootSubgroupPoints_inr_of_ne_last_eq_differenceShortRootUnit (i : Fin (n + 1))
    (hi : i ≠ Fin.last n)
    (u : Multiplicative A) :
    (rootSubgroupPoints n (.inr i) A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      ((GLSymplecticFin.differenceShortRootUnit (lt_next n i hi).ne'
        (Multiplicative.toAdd u) : GLSymplecticFin (n + 1) A) :
          GL (Fin ((n + 1) + (n + 1))) A) := by
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inr_of_ne_last n i hi,
    GLSymplecticFin.coe_differenceShortRootUnit_eq_one_add_single_sub_single]
  ext r s
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.single_apply, smul_eq_mul, Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sub,
    mul_sub, mul_ite, mul_one, mul_zero]
  split_ifs <;> ring

section Field

variable {K : Type v} [Field K]

/-- **The full-weight type-`C` carrier is the symplectic group over a field.** Its points always
preserve the standard alternating form, and over a field the numbered root subgroups already
generate every symplectic matrix, so the containment is an equality. -/
theorem points_eq_GLSymplecticFin : points n K = GLSymplecticFin (n + 1) K := by
  refine le_antisymm (fun g hg => mem_GLSymplecticFin_of_mem_points n hg) fun g hg => ?_
  have hH : (points n K).comap (GLSymplecticFin (n + 1) K).subtype = ⊤ := by
    refine GLSymplecticFin.eq_top_of_adjacent_of_long _ (Fin.last n) ?_ ?_ ?_
    · intro i j hij c hadj
      rw [Subgroup.mem_comap, Subgroup.coe_subtype]
      rcases hadj with hadj | hadj
      · have hi : i ≠ Fin.last n := by
          intro h
          subst h
          have := j.isLt
          simp only [Fin.val_last] at hadj
          omega
        have hj : j = next n i hi := Fin.ext (by rw [val_next]; omega)
        subst hj
        have hmem := (rootSubgroupPoints n (.inl i) K (Multiplicative.ofAdd c)).2
        rwa [rootSubgroupPoints_inl_of_ne_last_eq_differenceShortRootUnit n i hi
          (Multiplicative.ofAdd c)] at hmem
      · have hj : j ≠ Fin.last n := by
          intro h
          subst h
          have := i.isLt
          simp only [Fin.val_last] at hadj
          omega
        have hi : i = next n j hj := Fin.ext (by rw [val_next]; omega)
        subst hi
        have hmem := (rootSubgroupPoints n (.inr j) K (Multiplicative.ofAdd c)).2
        rwa [rootSubgroupPoints_inr_of_ne_last_eq_differenceShortRootUnit n j hj
          (Multiplicative.ofAdd c)] at hmem
    · intro c
      rw [Subgroup.mem_comap, Subgroup.coe_subtype]
      have hmem := (rootSubgroupPoints n (.inl (Fin.last n)) K (Multiplicative.ofAdd c)).2
      rwa [rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit n
        (Multiplicative.ofAdd c)] at hmem
    · intro c
      rw [Subgroup.mem_comap, Subgroup.coe_subtype]
      have hmem := (rootSubgroupPoints n (.inr (Fin.last n)) K (Multiplicative.ofAdd c)).2
      rwa [rootSubgroupPoints_inr_last_eq_negativeLongRootTransvectionUnit n
        (Multiplicative.ofAdd c)] at hmem
  have hmem : (⟨g, hg⟩ : GLSymplecticFin (n + 1) K) ∈
      (points n K).comap (GLSymplecticFin (n + 1) K).subtype := hH ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

end Field

end TauCeti.SpStd
