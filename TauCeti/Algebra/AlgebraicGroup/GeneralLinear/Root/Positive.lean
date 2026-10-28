/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Over
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Base
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Space
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Tangent

/-!
# Positive and simple roots of the standard general-linear torus and Borel

For the diagonal torus and upper-triangular Borel of `GL_n`, the intrinsic positive
adjoint roots are exactly `e_i - e_j` with `i < j`. In `GL_(r+1)` the simple roots are
exactly the consecutive differences `e_i - e_(i+1)`. The numbered equivalence onto
these intrinsic simple roots indexes the normalized root-space trivializations of a
pinning. These results hold over every nontrivial commutative ring, including rings
with zero divisors; connectedness of the base is not required.

The root-space calculation uses `GeneralLinear.rootSpaceEquiv` and the matrix tangent
criterion in `GeneralLinear.UpperTriangular.Tangent`. The simple-root comparison follows
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Pinning.Basic`, using the indecomposable
positive-root criterion `TauCeti.mem_support_iff_isPos_and_forall_ne_add`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1 and Example 21.2.
-/

public section

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] [Nontrivial R] {n r : ℕ}

/-- A root of the diagonal datum is positive for the upper-triangular Borel exactly
when its row index is smaller than its column index. This includes rank zero. -/
@[simp↓]
theorem isPositiveRoot_diagonalRoot_iff_lt (p : DiagonalRootIndex n) :
    (splitMaximalTorus R n).IsPositiveRoot (UpperTriangular.definingHopfIdeal R n)
        ((diagonalRootDatum.{u} n).root p) ↔ p.1.1.down < p.1.2.down := by
  have hne : p.1.1.down ≠ p.1.2.down := fun h ↦ p.2 (ULift.down_injective h)
  have hvector :
      Derivation.cotangentLinearEquiv (B := R)
          (matrixUnitTangent (k := R) p.1.1.down p.1.2.down) ∈
        (UpperTriangular.definingHopfIdeal R n).lieSubalgebra ↔
          p.1.1.down < p.1.2.down := by
    rw [UpperTriangular.mem_lieSubalgebra_definingHopfIdeal_iff,
      ← cotangentDualMatrixEquiv_apply, cotangentDualMatrixEquiv_matrixUnitTangent,
      TauCeti.single_mem_upperTriangular_iff one_ne_zero]
    exact ⟨fun h ↦ lt_of_le_of_ne h hne, le_of_lt⟩
  rw [SplitMaximalTorus.isPositiveRoot_iff, splitMaximalTorus_coordinateMap]
  have hspace := (rootSpaceEquiv (R := R) p 1).property
  rw [rootSpaceEquiv_apply_coe, one_smul] at hspace
  refine ⟨fun h ↦ hvector.mp (h.2 _ hspace), fun hp ↦ ?_⟩
  refine ⟨ofAdd_root_mem_nontrivialAdjointWeights (k := R) p, fun x hx ↦ ?_⟩
  obtain ⟨c, hc⟩ := (rootSpaceEquiv (R := R) p).surjective ⟨x, hx⟩
  have heq : c • matrixUnitTangent (k := R) p.1.1.down p.1.2.down = x := by
    simpa only [rootSpaceEquiv_apply_coe] using congrArg Subtype.val hc
  rw [← heq, map_smul]
  exact (UpperTriangular.definingHopfIdeal R n).lieSubalgebra.smul_mem c (hvector.mpr hp)

/-- The intrinsic positive roots for the standard general-linear torus and Borel are
exactly the positive roots of its diagonal root datum. -/
theorem isPositiveRoot_diagonalRoot_iff
    (p : DiagonalRootIndex (r + 1)) :
    (splitMaximalTorus R (r + 1)).IsPositiveRoot (UpperTriangular.definingHopfIdeal R (r + 1))
        ((diagonalRootDatum.{u} (r + 1)).root p) ↔ (diagonalRootBase.{u} r).IsPos p := by
  rw [diagonalRootBase_isPos_iff]
  exact isPositiveRoot_diagonalRoot_iff_lt p

/-- Every intrinsic positive root is a positive root of the diagonal root datum. -/
theorem isPositiveRoot_iff_exists_diagonalRoot (α : ULift.{u} (Fin (r + 1)) →₀ ℤ) :
    (splitMaximalTorus R (r + 1)).IsPositiveRoot (UpperTriangular.definingHopfIdeal R (r + 1)) α ↔
      ∃ p : DiagonalRootIndex (r + 1),
        α = (diagonalRootDatum.{u} (r + 1)).root p ∧ (diagonalRootBase.{u} r).IsPos p := by
  constructor
  · intro h
    have hweight := ((splitMaximalTorus R (r + 1)).isPositiveRoot_iff
      (UpperTriangular.definingHopfIdeal R (r + 1)) α).mp h
    rw [splitMaximalTorus_coordinateMap] at hweight
    obtain ⟨p, hp⟩ := (mem_nontrivialAdjointWeights_iff_exists_diagonalRoot
      (k := R) (Multiplicative.ofAdd α)).mp hweight.1
    have heq := Multiplicative.ofAdd.injective hp
    exact ⟨p, heq, isPositiveRoot_diagonalRoot_iff p |>.mp (heq ▸ h)⟩
  · rintro ⟨p, rfl, hp⟩
    exact (isPositiveRoot_diagonalRoot_iff p).mpr hp

/-- The intrinsic simple roots are precisely the members of the consecutive-root base. -/
@[simp↓]
theorem isSimpleRoot_diagonalRoot_iff
    (p : DiagonalRootIndex (r + 1)) :
    (splitMaximalTorus R (r + 1)).IsSimpleRoot (UpperTriangular.definingHopfIdeal R (r + 1))
        ((diagonalRootDatum.{u} (r + 1)).root p) ↔ p ∈ (diagonalRootBase.{u} r).support := by
  rw [SplitMaximalTorus.isSimpleRoot_iff, mem_support_iff_isPos_and_forall_ne_add]
  refine and_congr (isPositiveRoot_diagonalRoot_iff p) ?_
  constructor
  · intro h j k hj hk
    exact h _ _ ((isPositiveRoot_diagonalRoot_iff j).mpr hj)
      ((isPositiveRoot_diagonalRoot_iff k).mpr hk)
  · intro h β γ hβ hγ
    obtain ⟨j, rfl, hj⟩ := (isPositiveRoot_iff_exists_diagonalRoot β).mp hβ
    obtain ⟨k, rfl, hk⟩ := (isPositiveRoot_iff_exists_diagonalRoot γ).mp hγ
    exact h j k hj hk

/-- The consecutive simple roots exhaust the actual simple adjoint weights selected by
the upper-triangular Borel. -/
theorem isSimpleRoot_iff_exists_diagonalSimpleRoot (α : ULift.{u} (Fin (r + 1)) →₀ ℤ) :
    (splitMaximalTorus R (r + 1)).IsSimpleRoot (UpperTriangular.definingHopfIdeal R (r + 1)) α ↔
      ∃ i : Fin r, α = (diagonalRootDatum.{u} (r + 1)).root (diagonalSimpleRootIndex r i) := by
  constructor
  · intro h
    have hpos := ((splitMaximalTorus R (r + 1)).isSimpleRoot_iff
      (UpperTriangular.definingHopfIdeal R (r + 1)) α).mp h
    obtain ⟨p, rfl, _⟩ := (isPositiveRoot_iff_exists_diagonalRoot α).mp hpos.1
    obtain ⟨i, rfl⟩ := (mem_diagonalRootBase_support.{u} r p).mp
      ((isSimpleRoot_diagonalRoot_iff p).mp h)
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact (isSimpleRoot_diagonalRoot_iff _).mpr
      ((mem_diagonalRootBase_support.{u} r _).mpr ⟨i, rfl⟩)

/-- Bourbaki numbering as an equivalence onto the intrinsic simple roots of the standard
general-linear torus and Borel. -/
def diagonalSimpleRootEquiv :
    Fin r ≃ {α // (splitMaximalTorus R (r + 1)).IsSimpleRoot
      (UpperTriangular.definingHopfIdeal R (r + 1)) α} :=
  Equiv.ofBijective (fun i ↦ ⟨(diagonalRootDatum.{u} (r + 1)).root (diagonalSimpleRootIndex r i),
    (isSimpleRoot_iff_exists_diagonalSimpleRoot _).mpr ⟨i, rfl⟩⟩) <| by
      constructor
      · intro i j h
        exact diagonalSimpleRootIndex_injective r
          ((diagonalRootDatum.{u} (r + 1)).root.injective (congrArg Subtype.val h))
      · intro α
        obtain ⟨i, hi⟩ := (isSimpleRoot_iff_exists_diagonalSimpleRoot α.val).mp α.property
        exact ⟨i, Subtype.ext hi.symm⟩

/-- The intrinsic simple root at number `i` is the consecutive coordinate difference. -/
@[simp]
theorem diagonalSimpleRootEquiv_apply (i : Fin r) :
    (diagonalSimpleRootEquiv (R := R) i).val =
      (diagonalRootDatum.{u} (r + 1)).root (diagonalSimpleRootIndex r i) := (rfl)

end

end TauCeti.GeneralLinear
