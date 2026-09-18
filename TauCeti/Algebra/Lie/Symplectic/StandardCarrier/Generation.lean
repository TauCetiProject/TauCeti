/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.IntegralMatrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic
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
generator, which `AlternatingForm.lean` computes in the enumerated coordinate basis: the single
unit `E_{i,m+i}` at the final node, the difference `E_{i,i+1} - E_{m+i+1,m+i}` of two units at a
nonfinal one. Those are
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

* `TauCeti.SpStd.rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit` and its three
  siblings: each numbered root point is the corresponding long-root transvection or difference
  short-root element of the symplectic group.
* `TauCeti.SpStd.points_eq_GLSymplecticFin`: the carrier points are exactly the symplectic
  matrices, over every field.
* `TauCeti.SpStd.pointsMulEquivGLSymplecticFin`: the resulting multiplicative equivalence, with
  equations describing both directions on matrices and its action on every numbered simple-root
  subgroup and the weight torus.

## References

The decisive input is formal rather than bibliographic: the generation theorem
`TauCeti.GLSymplecticFin.eq_top_of_adjacent_of_long`, from
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/TorusGeneration.lean`, is what reduces
the equality of point groups to the four root identifications below.

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/
public section

open Matrix

namespace TauCeti.SpStd

universe v

variable (n : ℕ)

variable {A : Type v} [CommRing A]

/-- The final raising point of the carrier is the positive long-root transvection. -/
-- Not `@[simp]`: `coe_rootSubgroupPoints` is already a simp lemma and rewrites this
-- left-hand side first, so a simp normal form stated against `rootSubgroupPoints` is
-- unreachable. Consumers rewrite with it by name.
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
-- Not `@[simp]`: `coe_rootSubgroupPoints` is already a simp lemma and rewrites this
-- left-hand side first, so a simp normal form stated against `rootSubgroupPoints` is
-- unreachable. Consumers rewrite with it by name.
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
-- Not `@[simp]`: `coe_rootSubgroupPoints` is already a simp lemma and rewrites this
-- left-hand side first, so a simp normal form stated against `rootSubgroupPoints` is
-- unreachable. Consumers rewrite with it by name.
theorem rootSubgroupPoints_inl_eq_differenceShortRootUnit_of_ne_last (i : Fin (n + 1))
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
-- Not `@[simp]`: `coe_rootSubgroupPoints` is already a simp lemma and rewrites this
-- left-hand side first, so a simp normal form stated against `rootSubgroupPoints` is
-- unreachable. Consumers rewrite with it by name.
theorem rootSubgroupPoints_inr_eq_differenceShortRootUnit_of_ne_last (i : Fin (n + 1))
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
        rwa [rootSubgroupPoints_inl_eq_differenceShortRootUnit_of_ne_last n i hi
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
        rwa [rootSubgroupPoints_inr_eq_differenceShortRootUnit_of_ne_last n j hj
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

/-! ## The point-group equivalence -/

/-- **The full-weight type-`C_(n+1)` carrier's points are the symplectic group**, as a
multiplicative equivalence. This packages `TauCeti.SpStd.points_eq_GLSymplecticFin` in the form
needed to transport endomorphisms and subgroups while leaving the underlying matrices unchanged. -/
noncomputable def pointsMulEquivGLSymplecticFin (K : Type v) [Field K] :
    points n K ≃* GLSymplecticFin (n + 1) K :=
  MulEquiv.subgroupCongr (points_eq_GLSymplecticFin n)

/-- The symplectic element underlying a point of the carrier is that point. This is
`MulEquiv.subgroupCongr_apply` stated for the named equivalence, so that consumers need not unfold
`TauCeti.SpStd.pointsMulEquivGLSymplecticFin`. -/
@[simp]
theorem coe_pointsMulEquivGLSymplecticFin_apply (g : points n K) :
    ((pointsMulEquivGLSymplecticFin n K g : GLSymplecticFin (n + 1) K) :
        GL (Fin ((n + 1) + (n + 1))) K) =
      (g : GL (Fin ((n + 1) + (n + 1))) K) :=
  MulEquiv.subgroupCongr_apply _ g

/-- The point of the carrier underlying a symplectic element is that element. This is
`MulEquiv.subgroupCongr_symm_apply` stated for the named equivalence. -/
@[simp]
theorem coe_pointsMulEquivGLSymplecticFin_symm_apply (g : GLSymplecticFin (n + 1) K) :
    (((pointsMulEquivGLSymplecticFin n K).symm g : points n K) :
        GL (Fin ((n + 1) + (n + 1))) K) =
      (g : GL (Fin ((n + 1) + (n + 1))) K) :=
  MulEquiv.subgroupCongr_symm_apply _ g

/-- Under the point-group equivalence, the final positive simple-root subgroup is the positive
long-root transvection subgroup of the symplectic group. -/
@[simp]
theorem pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_last
    (u : Multiplicative K) :
    pointsMulEquivGLSymplecticFin n K
        (rootSubgroupPoints n (.inl (Fin.last n)) K u) =
      GLSymplecticFin.positiveLongRootTransvectionUnit (Fin.last n)
        (Multiplicative.toAdd u) := by
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFin_apply,
    rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit]

/-- Under the point-group equivalence, the final negative simple-root subgroup is the negative
long-root transvection subgroup of the symplectic group. -/
@[simp]
theorem pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inr_last
    (u : Multiplicative K) :
    pointsMulEquivGLSymplecticFin n K
        (rootSubgroupPoints n (.inr (Fin.last n)) K u) =
      GLSymplecticFin.negativeLongRootTransvectionUnit (Fin.last n)
        (Multiplicative.toAdd u) := by
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFin_apply,
    rootSubgroupPoints_inr_last_eq_negativeLongRootTransvectionUnit]

/-- Under the point-group equivalence, a nonfinal positive simple-root subgroup is the adjacent
difference-root subgroup of the symplectic group. -/
@[simp]
theorem pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_of_ne_last
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) (u : Multiplicative K) :
    pointsMulEquivGLSymplecticFin n K (rootSubgroupPoints n (.inl i) K u) =
      GLSymplecticFin.differenceShortRootUnit (lt_next n i hi).ne
        (Multiplicative.toAdd u) := by
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFin_apply,
    rootSubgroupPoints_inl_eq_differenceShortRootUnit_of_ne_last n i hi]

/-- Under the point-group equivalence, a nonfinal negative simple-root subgroup is the opposite
adjacent difference-root subgroup of the symplectic group. -/
@[simp]
theorem pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inr_of_ne_last
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) (u : Multiplicative K) :
    pointsMulEquivGLSymplecticFin n K (rootSubgroupPoints n (.inr i) K u) =
      GLSymplecticFin.differenceShortRootUnit (lt_next n i hi).ne'
        (Multiplicative.toAdd u) := by
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFin_apply,
    rootSubgroupPoints_inr_eq_differenceShortRootUnit_of_ne_last n i hi]

/-- Under the point-group equivalence, the carrier's weight torus is the standard paired diagonal
torus. Its first-block coordinate at `i` is the character of the classical type-`C` weight
`ε_i`; the second block is its inverse. -/
@[simp]
theorem pointsMulEquivGLSymplecticFin_weightTorusPoints
    (s : Fin (n + 1) → Kˣ) :
    pointsMulEquivGLSymplecticFin n K (weightTorusPoints n K s) =
      GLSymplecticFin.diagonal fun i ↦
        TauCeti.torusCharacter s (DynkinType.TypeC.weight (n + 1) i) := by
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFin_apply, coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, GLSymplecticFin.coe_diagonal]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [diagGL_coe, Matrix.diagonal_apply]
  congr 1
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
  · rw [finSumFinEquiv_apply_left, GLSymplecticFin.diagonalCoordinates_castAdd,
      basisWeight_apply, finSumFinEquiv_symm_apply_castAdd]
    have hweight :
        weight n (.inl i) = DynkinType.TypeC.weight (n + 1) i := by
      funext j
      exact weight_inl n i j
    rw [hweight]
  · rw [finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat,
      GLSymplecticFin.diagonalCoordinates_addNat, basisWeight_apply,
      ← Fin.natAdd_eq_addNat,
      finSumFinEquiv_symm_apply_natAdd]
    have hweight :
        weight n (.inr i) = -DynkinType.TypeC.weight (n + 1) i := by
      funext j
      exact weight_inr n i j
    rw [hweight, torusCharacter_neg]

end Field

end TauCeti.SpStd
