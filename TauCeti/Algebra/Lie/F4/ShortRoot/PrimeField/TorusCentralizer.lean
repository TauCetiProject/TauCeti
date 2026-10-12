/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The centralizer of the short-root F₄ weight torus

Over an infinite field of characteristic two, this file characterizes the centralizer of the
weight torus in the short-root carrier's point group. A commuting matrix has no entry between
distinct weight spaces, and conversely every carrier point with that weight-block form commutes
with the torus.

Unlike the seven-dimensional short-root representation of `G₂`, the short-root representation
of `F₄` has the zero weight with multiplicity two. Thus character separation gives a single
two-dimensional zero-weight block rather than forcing the whole centralizer to be diagonal. A
subsequent identification of the centralizer with the torus must use the carrier equations to
control this block.

## Main declaration

* `mem_centralizer_range_weightTorusPoints_iff_apply_eq_zero`: a carrier point centralizes the
  weight torus exactly when its entries between distinct weights vanish.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §16.1 and §26.3.
* Character separation uses `TauCeti.weightChar_injective` from
  `TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic`.
-/

public section

open Matrix

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
    g ∈ Subgroup.centralizer ((weightTorusPoints A).range : Set (points A)) ↔
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

variable {k : Type v} [Field k] [Algebra (ZMod 2) k] [Infinite k]

/-- Over an infinite field of characteristic two, a point of the short-root carrier centralizes
the weight torus exactly when its matrix is block diagonal for the short-root weights. In
particular, the only block of size greater than one is the two-dimensional zero-weight block. -/
theorem mem_centralizer_range_weightTorusPoints_iff_apply_eq_zero (g : points k) :
    g ∈ Subgroup.centralizer ((weightTorusPoints k).range : Set (points k)) ↔
      ∀ i j, f4ShortRootWeight i ≠ f4ShortRootWeight j →
        (((g : GL (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) i j) = 0 :=
  mem_centralizer_range_weightTorusPoints_iff_apply_eq_zero_of_weightChar_injective
    weightChar_injective g

end TauCeti.F4ShortRoot.PrimeField
