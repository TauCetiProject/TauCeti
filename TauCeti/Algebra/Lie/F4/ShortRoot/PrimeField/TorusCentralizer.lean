/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PreservesBracket
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The centralizer of the short-root F₄ weight torus

Over an infinite field of characteristic two, a point of the short-root carrier centralizes
its weight torus exactly when its matrix is diagonal. Character separation first gives a
block-diagonal matrix, with a two-dimensional zero-weight block. The two distinguished
zero-weight vectors are brackets of opposite short simple-root vectors. Since the carrier
preserves the bracket and each nonzero-weight line, it preserves these two lines separately.
Thus the zero-weight block is diagonal too.

The bracket argument works over every commutative `𝔽₂`-algebra, including nonreduced ones.
Identifying diagonal carrier points with the weight torus, and hence proving that the torus
is self-centralizing, remains a separate question. No identification with the pinned simply
connected group scheme of type `F₄` is asserted.

## Main declarations

* `Matrix.isDiag_of_preserves_f4ShortRootBracket_of_weight_support`: bracket preservation refines
  the weight-block condition to diagonality over any commutative `𝔽₂`-algebra.
* `mem_centralizer_range_weightTorusPoints_iff_isDiag`: over an infinite field, a carrier point
  centralizes the weight torus exactly when its matrix is diagonal.
* `centralizer_range_weightTorusPoints_eq_comap_diagonalTorus`: the subgroup form.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §16.1 and §26.3.
* Character separation uses `TauCeti.weightChar_injective` from
  `TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic`.
-/

public section

open Matrix

namespace Matrix

open TauCeti TauCeti.DynkinType

universe u

/-- A bracket-preserving matrix with no entries between distinct short-root weights is
diagonal. The two zero-weight basis vectors are brackets of opposite simple-root vectors,
so their lines are preserved individually, without a reducedness or invertibility assumption. -/
theorem isDiag_of_preserves_f4ShortRootBracket_of_weight_support
    {A : Type u} [CommRing A] [Algebra (ZMod 2) A]
    (M : Matrix (Fin 26) (Fin 26) A)
    (hM : ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix M)
    (hweight : ∀ i j, f4ShortRootWeight i ≠ f4ShortRootWeight j → M i j = 0) :
    M.IsDiag := by
  have hcol (a : Fin 26) (ha : f4ShortRootWeight a ≠ 0) :
      M.col a = M a a • Pi.single a 1 := by
    ext i
    by_cases hi : i = a
    · subst i
      simp
    · have hne : f4ShortRootWeight i ≠ f4ShortRootWeight a := by
        intro h
        exact hi (f4ShortRootWeight_injOn (fun hi0 ↦ ha (h.symm.trans hi0)) ha h)
      simp only [col_apply, Pi.smul_apply, Pi.single_apply, hi, ite_false, smul_eq_mul, mul_zero]
      exact hweight i a hne
  have h12 : M.col 12 = (M 11 11 * M 14 14) • Pi.single 12 1 :=
    ConstantMultiplication.Preserves.col_eq_smul_single (ZMod 2) 26 f4ShortRootBracketMatrix
      hM (hcol 11 (by decide)) (hcol 14 (by decide))
      f4ShortRootBracketMatrix_col_fourteen_eleven
  have h13 : M.col 13 = (M 10 10 * M 15 15) • Pi.single 13 1 :=
    ConstantMultiplication.Preserves.col_eq_smul_single (ZMod 2) 26 f4ShortRootBracketMatrix
      hM (hcol 10 (by decide)) (hcol 15 (by decide))
      f4ShortRootBracketMatrix_col_fifteen_ten
  intro i j hij
  obtain ⟨s, hs⟩ : ∃ s : A, M.col j = s • Pi.single j 1 := by
    by_cases hj : f4ShortRootWeight j = 0
    · rcases (f4ShortRootWeight_eq_zero_iff j).mp hj with rfl | rfl
      · exact ⟨_, h12⟩
      · exact ⟨_, h13⟩
    · exact ⟨_, hcol j hj⟩
  simpa only [col_apply, Pi.smul_apply, Pi.single_apply, hij, ite_false, smul_eq_mul,
    mul_zero] using congrFun hs i

end Matrix

namespace TauCeti.F4ShortRoot.PrimeField

open TauCeti.DynkinType

universe u v

variable {A : Type u} [CommRing A] [IsCancelMulZero A] [Algebra (ZMod 2) A]

/-- If distinct weights define distinct characters over the coefficient ring, a point of the
short-root carrier centralizes the weight torus exactly when its matrix is block diagonal for the
short-root weights. -/
theorem mem_centralizer_range_weightTorusPoints_iff_apply_eq_zero_of_weightChar_injective
    (hchar : Function.Injective
      (weightChar A : (Fin 4 → ℤ) → ((Fin 4 → Aˣ) →* Aˣ))) (g : points A) :
    g ∈ Subgroup.centralizer (Set.range (weightTorusPoints A)) ↔
      ∀ i j, f4ShortRootWeight i ≠ f4ShortRootWeight j →
        (((g : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) i j) = 0 := by
  constructor
  · intro hg i j hij
    have hchar_ne : weightChar A (f4ShortRootWeight i) ≠
        weightChar A (f4ShortRootWeight j) :=
      hchar.ne hij
    obtain ⟨s, hs⟩ := DFunLike.ne_iff.mp hchar_ne
    simp only [weightChar_apply] at hs
    have hcomm := Subgroup.mem_centralizer_iff.mp hg (weightTorusPoints A s) ⟨s, rfl⟩
    have hmatrix := congrArg (fun x : points A ↦
      ((x : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
      F4ShortRoot.coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe] at hmatrix
    exact apply_eq_zero_of_commute_diagonal hmatrix (fun h ↦ hs (Units.ext h))
  · intro hblock
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨s, rfl⟩ := hd
    have hmatrix : Commute
        (Matrix.diagonal fun i ↦ (torusCharacter s (f4ShortRootWeight i) : A))
        ((g : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) := by
      rw [Commute]
      ext i j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases hij : f4ShortRootWeight i = f4ShortRootWeight j
      · rw [hij, mul_comm]
      · rw [hblock i j hij, mul_zero, zero_mul]
    have hgeneralLinear : Commute
        (weightTorusPoints A s : GL (Fin 26) A) (g : GL (Fin 26) A) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_weightTorusPoints, F4ShortRoot.coe_weightTorusPoints,
        UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
      exact hmatrix.eq
    exact (Commute.of_map (points A).subtype_injective hgeneralLinear).eq

/-- When distinct weights define distinct characters, the torus centralizer consists of
exactly the diagonal carrier points. -/
theorem mem_centralizer_range_weightTorusPoints_iff_isDiag_of_weightChar_injective
    (hchar : Function.Injective
      (weightChar A : (Fin 4 → ℤ) → ((Fin 4 → Aˣ) →* Aˣ))) (g : points A) :
    g ∈ Subgroup.centralizer (Set.range (weightTorusPoints A)) ↔
      ((g : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A).IsDiag := by
  rw [mem_centralizer_range_weightTorusPoints_iff_apply_eq_zero_of_weightChar_injective hchar]
  constructor
  · exact Matrix.isDiag_of_preserves_f4ShortRootBracket_of_weight_support _
      (preservesBracket_of_mem_points g.2)
  · intro h i j hij
    exact h (fun heq ↦ hij (congrArg f4ShortRootWeight heq))

variable {k : Type v} [Field k] [Algebra (ZMod 2) k] [Infinite k]

/-- Over an infinite field of characteristic two, a carrier point centralizes the weight
torus exactly when its matrix is diagonal. -/
@[simp]
theorem mem_centralizer_range_weightTorusPoints_iff_isDiag (g : points k) :
    g ∈ Subgroup.centralizer (Set.range (weightTorusPoints k)) ↔
      ((g : GL (Fin 26) k) : Matrix (Fin 26) (Fin 26) k).IsDiag :=
  mem_centralizer_range_weightTorusPoints_iff_isDiag_of_weightChar_injective
    weightChar_injective g

/-- Over an infinite field of characteristic two, the weight-torus centralizer is the inverse
image of the ambient diagonal torus in `GL₂₆`. This does not identify it with the weight torus. -/
theorem centralizer_range_weightTorusPoints_eq_comap_diagonalTorus :
    Subgroup.centralizer (Set.range (weightTorusPoints k)) =
      (diagonalTorus k 26).comap (points k).subtype := by
  ext g
  simp only [mem_centralizer_range_weightTorusPoints_iff_isDiag, Subgroup.mem_comap,
    Subgroup.subtype_apply, mem_diagonalTorus_iff]

end TauCeti.F4ShortRoot.PrimeField
