/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.StandardComodule
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The torus centralizer of the type-D spin carrier

The full spin representation of the type-`Dₙ` carrier has one coordinate line for every spin
weight, and those weights are pairwise distinct. Over an infinite field, a carrier point commuting
with the weight torus must therefore be diagonal in the spin basis. Conversely every diagonal
carrier point commutes with that torus.

Thus the centralizer of the weight torus is the inverse image of the ambient diagonal torus. This
does not yet identify all diagonal carrier points with weight-torus points; that further
identification is needed before this calculation yields a maximal torus.

## Main declarations

* `TauCeti.TypeDSpinCarrier.diagonalPoints`: the diagonal points of the spin carrier.
* `TauCeti.TypeDSpinCarrier.centralizer_range_weightTorusPoints_eq_diagonalPoints`: the
  pointwise torus-centralizer calculation over an infinite field.
* `TauCeti.TypeDSpinCarrier.eq_diagonalPoints_of_le_of_isMulCommutative`: maximality of the
  diagonal carrier points among commutative point subgroups.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.

The point-group argument follows
`TauCeti.SlStd.centralizer_range_weightTorusPoints_eq_diagonalPoints`.
-/

public section

open Matrix

namespace TauCeti.TypeDSpinCarrier

universe u

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

/-! ## Diagonal carrier points -/

/-- The subgroup of type-`Dₙ` spin-carrier points whose ambient matrices are diagonal. -/
def diagonalPoints (K : Type u) [CommRing K] : Subgroup (points n hn K) :=
  (diagonalTorus K (dimension n)).comap (points n hn K).subtype

/-- A spin-carrier point belongs to `diagonalPoints` exactly when its ambient matrix is diagonal. -/
@[simp]
theorem mem_diagonalPoints_iff {K : Type u} [CommRing K] {g : points n hn K} :
    g ∈ diagonalPoints n hn K ↔ g.1.1.IsDiag := by
  rw [diagonalPoints, Subgroup.mem_comap, mem_diagonalTorus_iff]
  rfl

/-- Every point of the spin weight torus is diagonal in the ambient general linear group. -/
theorem coe_weightTorusPoints_mem_diagonalTorus (K : Type u) [CommRing K]
    (s : Fin n → Kˣ) :
    (weightTorusPoints n hn K s : GL (Fin (dimension n)) K) ∈
      diagonalTorus K (dimension n) := by
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]
  exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨_, rfl⟩

/-- The spin weight torus is contained in the subgroup of diagonal carrier points. -/
theorem range_weightTorusPoints_le_diagonalPoints (K : Type u) [CommRing K] :
    (weightTorusPoints n hn K).range ≤ diagonalPoints n hn K := by
  rintro _ ⟨s, rfl⟩
  rw [diagonalPoints, Subgroup.mem_comap]
  exact coe_weightTorusPoints_mem_diagonalTorus n hn K s

/-- The diagonal carrier points form a commutative group. -/
instance instIsMulCommutativeDiagonalPoints (K : Type u) [CommRing K] :
    IsMulCommutative (diagonalPoints n hn K) :=
  (diagonalTorus K (dimension n)).comap_injective_isMulCommutative
    (points n hn K).subtype_injective

/-! ## The centralizer -/

/-- If the spin weight characters remain distinct over a ring without zero divisors, the
centralizer of the weight torus in the carrier points is exactly the diagonal subgroup. -/
theorem centralizer_range_weightTorusPoints_eq_diagonalPoints_of_weightChar_basisWeight_injective
    (K : Type u) [CommRing K] [IsCancelMulZero K]
    (hchar : Function.Injective (weightChar K ∘ basisWeight n)) :
    Subgroup.centralizer
        ((weightTorusPoints n hn K).range : Set (points n hn K)) = diagonalPoints n hn K := by
  apply le_antisymm
  · intro g hg
    rw [mem_diagonalPoints_iff]
    intro i j hij
    have hchar_ne : weightChar K (basisWeight n i) ≠ weightChar K (basisWeight n j) :=
      fun h ↦ hij (hchar h)
    obtain ⟨s, hs⟩ := DFunLike.ne_iff.mp hchar_ne
    simp only [weightChar_apply] at hs
    have hcomm := Subgroup.mem_centralizer_iff.mp hg (weightTorusPoints n hn K s) ⟨s, rfl⟩
    have hmatrix := congrArg (fun x : points n hn K ↦
      ((x : GL (Fin (dimension n)) K) : Matrix (Fin (dimension n)) (Fin (dimension n)) K)) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe] at hmatrix
    exact apply_eq_zero_of_commute_diagonal hmatrix (fun h ↦ hs (Units.ext h))
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨s, rfl⟩ := hd
    have hdDiag := coe_weightTorusPoints_mem_diagonalTorus n hn K s
    have hcomm : Commute
        (weightTorusPoints n hn K s : GL (Fin (dimension n)) K) g :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.le_centralizer (diagonalTorus K (dimension n)) hdDiag) g hg |>.symm
    exact (Commute.of_map (points n hn K).subtype_injective hcomm).eq

/-- Over an infinite field, the centralizer of the spin weight torus in the type-`Dₙ` carrier
is exactly the subgroup of diagonal carrier points. -/
theorem centralizer_range_weightTorusPoints_eq_diagonalPoints
    (K : Type u) [Field K] [Infinite K] :
    Subgroup.centralizer
        ((weightTorusPoints n hn K).range : Set (points n hn K)) = diagonalPoints n hn K := by
  apply centralizer_range_weightTorusPoints_eq_diagonalPoints_of_weightChar_basisWeight_injective
  exact weightChar_injective.comp fun i j hij ↦ by
    apply basisCharacter_injective n
    simp only [basisCharacter, hij]

/-- Over an infinite field, the diagonal spin-carrier points are self-centralizing. -/
theorem centralizer_diagonalPoints_eq_diagonalPoints
    (K : Type u) [Field K] [Infinite K] :
    Subgroup.centralizer (diagonalPoints n hn K : Set (points n hn K)) =
      diagonalPoints n hn K := by
  apply le_antisymm
  · calc
      Subgroup.centralizer (diagonalPoints n hn K : Set (points n hn K)) ≤
          Subgroup.centralizer
            ((weightTorusPoints n hn K).range : Set (points n hn K)) :=
        Subgroup.centralizer_le
          (SetLike.coe_subset_coe.mpr (range_weightTorusPoints_le_diagonalPoints n hn K))
      _ = diagonalPoints n hn K :=
        centralizer_range_weightTorusPoints_eq_diagonalPoints n hn K
  · exact Subgroup.le_centralizer _

/-- Over an infinite field, no commutative subgroup of the spin carrier properly contains all
diagonal carrier points. -/
theorem eq_diagonalPoints_of_le_of_isMulCommutative
    (K : Type u) [Field K] [Infinite K]
    (H : Subgroup (points n hn K)) [IsMulCommutative H]
    (hH : diagonalPoints n hn K ≤ H) :
    H = diagonalPoints n hn K :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative
    (centralizer_diagonalPoints_eq_diagonalPoints n hn K) hH

end

end TauCeti.TypeDSpinCarrier
