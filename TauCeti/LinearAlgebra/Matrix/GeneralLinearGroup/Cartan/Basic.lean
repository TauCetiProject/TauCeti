/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SingularValues
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DoubleCoset

/-!
# The KAK decomposition of the real and complex general linear groups

Every invertible real or complex matrix is `U * diagonal d * V`, with `U`, `V` orthogonal or
unitary and `d` positive and decreasing. The diagonal `d` is unique, even when entries repeat;
the two compact factors need not be unique. Thus the closed positive chamber parametrizes
the double cosets of the maximal compact subgroup.

`Matrix.GeneralLinearGroup.existsUnique_pos_antitone_and_eq_unitary_mul_diagonal_mul_unitary`
gives existence and chamber uniqueness.
`Matrix.GeneralLinearGroup.mem_doubleCoset_unitarySubgroup_iff_singularValues_eq` identifies
compact double cosets by the existing operator singular values. These statements include
`GL₀`, and require no choices of compact factors in their interfaces.

The analytic input is the operator singular value decomposition in
`TauCeti.Analysis.InnerProductSpace.SingularValues`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Chapter VII.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Section 2.6.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Two invertible matrices belong to the same compact double coset exactly when all their
singular values agree. For real matrices the compact subgroup is the orthogonal group. -/
theorem mem_doubleCoset_unitarySubgroup_iff_singularValues_eq
    (g h : GL ι 𝕜) :
    h ∈ DoubleCoset.doubleCoset g (unitarySubgroup (GL ι 𝕜))
        (unitarySubgroup (GL ι 𝕜)) ↔
      (toEuclideanLin (g : Matrix ι ι 𝕜)).singularValues =
        (toEuclideanLin (h : Matrix ι ι 𝕜)).singularValues := by
  rw [← exists_unitary_mul_mul_unitary_iff_singularValues_eq]
  constructor
  · intro hh
    obtain ⟨U, hU, V, hV, hh⟩ := DoubleCoset.mem_doubleCoset.mp hh
    -- The standard equivalence forgets the units wrapper of a unitary invertible matrix.
    exact ⟨unitarySubgroupUnitsEquiv ⟨U, hU⟩, unitarySubgroupUnitsEquiv ⟨V, hV⟩,
      congrArg Units.val hh⟩
  · rintro ⟨U, V, hh⟩
    let U' := unitarySubgroupUnitsEquiv.symm U
    let V' := unitarySubgroupUnitsEquiv.symm V
    refine DoubleCoset.mem_doubleCoset.mpr ⟨U', U'.property, V', V'.property, ?_⟩
    -- Equality of units is equality of their underlying matrices.
    exact Units.ext hh

/-- The KAK decomposition of `GLₙ(ℝ)` and `GLₙ(ℂ)`: each invertible matrix has a unique
positive decreasing diagonal factor between two compact factors. Uniqueness concerns the
diagonal only, so repeated singular values are allowed. -/
theorem existsUnique_pos_antitone_and_eq_unitary_mul_diagonal_mul_unitary (g : GL (Fin n) 𝕜) :
    ∃! d : Fin n → ℝ, (∀ i, 0 < d i) ∧ Antitone d ∧
      ∃ U V : unitaryGroup (Fin n) 𝕜,
        (g : Matrix (Fin n) (Fin n) 𝕜) =
          (U : Matrix (Fin n) (Fin n) 𝕜) * diagonal (fun i ↦ (d i : 𝕜)) * V := by
  let A := toEuclideanLin (g : Matrix (Fin n) (Fin n) 𝕜)
  have hunit : IsUnit A := g.isUnit.map (toLpLinAlgEquiv (R := 𝕜) (n := Fin n) 2)
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp
    ((LinearMap.isUnit_iff_ker_eq_bot A).mp hunit)
  have hpos (i : Fin n) : 0 < A.singularValues i :=
    A.injective_iff_forall_lt_finrank_singularValues_pos.mp hinj i
      (by simp)
  refine ⟨fun i ↦ A.singularValues i,
    ⟨hpos, fun _ _ hij ↦ A.singularValues_antitone hij,
      exists_unitary_mul_diagonal_mul_unitary _⟩, ?_⟩
  rintro d ⟨hd, hanti, U, V, h⟩
  funext i
  exact (singularValues_toEuclideanLin_of_unitary_mul_diagonal_mul_unitary
    (g : Matrix (Fin n) (Fin n) 𝕜) d (fun j ↦ (hd j).le) hanti U V h i).symm

end Matrix.GeneralLinearGroup
