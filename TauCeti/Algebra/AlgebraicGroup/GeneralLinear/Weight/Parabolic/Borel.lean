/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Basic
public import TauCeti.Algebra.AlgebraicGroup.Parabolic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
import Mathlib.Data.Fin.Tuple.Sort
import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic.Geometry
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Borel

/-!
# Weight parabolics of the general linear group are parabolic

For integer weights `w` on the coordinates of `GL_N`, the weight parabolic `P(w)` consists of the
invertible matrices whose `(i,j)` entry vanishes whenever `w i < w j`. This file shows that
`P(w)` contains a conjugate of the upper-triangular subgroup by a permutation matrix, and hence
that `P(w)` is a parabolic subgroup of `GL_N` over every field.

If `w ∘ τ` is antitone for a permutation `τ` of the coordinates, then conjugating an
upper-triangular matrix by the permutation matrix of `τ` gives a matrix in `P(w)`. Such a
permutation always exists: sort the weights in decreasing order. When `w` itself is antitone no
permutation is needed, and `P(w)` contains the upper-triangular subgroup; these are the standard
parabolics. Since `P(w)` is smooth, containing a conjugate of the upper-triangular Borel subgroup
makes it parabolic.

By `TauCeti.GeneralLinear.Dynamic.parabolicDefiningHopfIdeal_weightCocharacter`, the weight
parabolic is the dynamic parabolic `P(λ)` of the diagonal cocharacter `λ(t) = diag(t ^ w i)`, so
these results say that `P(λ)` is parabolic for every diagonal cocharacter of `GL_N`.

## Main declarations

All declarations below are in the `TauCeti.GeneralLinear` namespace.

* `weightParabolicDefiningHopfIdeal_le_conjugate_upperTriangular_definingHopfIdeal`: if `w ∘ τ`
  is antitone, the weight parabolic contains the conjugate of the upper-triangular subgroup by the
  permutation matrix of `τ`.
* `weightParabolicDefiningHopfIdeal_le_upperTriangular_definingHopfIdeal`: for antitone `w`, the
  weight parabolic contains the upper-triangular subgroup.
* `isParabolic_weightParabolicDefiningHopfIdeal` and
  `isParabolicOverAlgClosed_weightParabolicDefiningHopfIdeal`: every weight parabolic is a
  parabolic subgroup of `GL_N`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13 and §17.c.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ}

/-- **Weight parabolics contain conjugates of the upper-triangular subgroup.** If `w ∘ τ` is
antitone, the closed subgroup cut out by the weight-parabolic ideal of `w` contains the conjugate
of the upper-triangular subgroup by the permutation matrix of `τ`. Containment of closed
subgroups is the reversed inequality of Hopf ideals. -/
theorem weightParabolicDefiningHopfIdeal_le_conjugate_upperTriangular_definingHopfIdeal
    {w : Fin N → ℤ} {τ : Equiv.Perm (Fin N)} (hτ : Antitone (w ∘ τ)) :
    weightParabolicDefiningHopfIdeal R w ≤
      (UpperTriangular.definingHopfIdeal R N).conjugate
        (generalLinearToPoint (R := R) N (permutationGL τ)) := by
  let Q := CommHopfAlgCat.quotient (coordinateHopfAlgebra R N)
    (UpperTriangular.definingHopfIdeal R N)
  let π : coordinateHopfAlgebra R N →ₐc[R] Q := (CommHopfAlgCat.mkQuotient _ _).hom
  let g : WithConv (coordinateHopfAlgebra R N →ₐ[R] R) :=
    (pointsMulEquiv (R := R) (A := R) N).symm (permutationGL τ)
  -- The generic point of the upper-triangular subgroup is an upper-triangular matrix.
  have hM (a b : Fin N) (hba : b < a) :
      (pointsMulEquiv N (toConv (π : coordinateHopfAlgebra R N →ₐ[R] Q)) :
        Matrix (Fin N) (Fin N) Q) a b = 0 := by
    rw [pointsMulEquiv_apply, pointToGeneralLinear_apply]
    refine (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr (HopfIdeal.mem_toIdeal.mp ?_)
    rw [UpperTriangular.definingHopfIdeal_toIdeal]
    exact Ideal.subset_span ((UpperTriangular.mem_definingRelationSet_iff R N _).mpr
      ⟨a, b, hba, rfl⟩)
  -- Conjugating the generic point by `g` reindexes its matrix along `τ`.
  have hkey : pointsMulEquiv N
      (toConv ((π : coordinateHopfAlgebra R N →ₐ[R] Q).comp
        (HopfAlgebra.pointConjugationAlgHom g))) =
      τ.reindexGL Q (pointsMulEquiv N (toConv (π : coordinateHopfAlgebra R N →ₐ[R] Q))) := by
    rw [pointsMulEquiv_toConv_comp_pointConjugationAlgHom, map_permutationGL,
      permutationGL_mul_mul_inv]
  have hle := HopfIdeal.conjugate_inv_le_of_mem_quotientPointsSubgroup_mkQuotient
    (UpperTriangular.definingHopfIdeal R N) (weightParabolicDefiningHopfIdeal R w) g
    ((mem_weightParabolicDefiningPointsSubgroup_iff_blockTriangular R w _).mpr (by
      rw [hkey]
      intro i j hij
      have hw : w i < w j := OrderDual.toDual_lt_toDual.mp hij
      rw [Equiv.coe_reindexGL, Matrix.submatrix_apply]
      refine hM _ _ (lt_of_not_ge fun h ↦ ?_)
      have := hτ h
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
      exact this.not_gt hw))
  simpa [g] using HopfIdeal.conjugate_mono g hle

/-- **Standard weight parabolics contain the upper-triangular subgroup.** For an antitone weight
`w`, every upper-triangular matrix lies in the weight parabolic of `w`. -/
theorem weightParabolicDefiningHopfIdeal_le_upperTriangular_definingHopfIdeal
    {w : Fin N → ℤ} (hw : Antitone w) :
    weightParabolicDefiningHopfIdeal R w ≤ UpperTriangular.definingHopfIdeal R N := by
  have h := weightParabolicDefiningHopfIdeal_le_conjugate_upperTriangular_definingHopfIdeal R
    (τ := 1) (w := w) (by rwa [Equiv.Perm.coe_one, Function.comp_id])
  rwa [map_one, ← pointsMulEquiv_symm_apply, map_one, HopfIdeal.conjugate_one] at h

variable (k : Type u) [Field k]

/-- **Every weight parabolic of `GL_N` is a parabolic subgroup** over every field: it is smooth
and contains a conjugate of the upper-triangular Borel subgroup. -/
theorem isParabolic_weightParabolicDefiningHopfIdeal (w : Fin N → ℤ) :
    HopfIdeal.IsParabolic k (coordinateHopfAlgebra k N) (weightParabolicDefiningHopfIdeal k w) :=
  ((UpperTriangular.isBorel_definingHopfIdeal k N).conjugate _).isParabolic.of_le
    (weightParabolicDefiningHopfIdeal_le_conjugate_upperTriangular_definingHopfIdeal k
      (Tuple.antitone_sortDesc w))
    (smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra k w)

/-- Over an algebraically closed field, every weight parabolic of `GL_N` is a parabolic
subgroup. -/
theorem isParabolicOverAlgClosed_weightParabolicDefiningHopfIdeal [IsAlgClosed k]
    (w : Fin N → ℤ) :
    HopfIdeal.IsParabolicOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra k N))
      (weightParabolicDefiningHopfIdeal k w) :=
  ((UpperTriangular.isBorelOverAlgClosed_definingHopfIdeal k N).conjugate
      _).isParabolicOverAlgClosed.of_le
    (weightParabolicDefiningHopfIdeal_le_conjugate_upperTriangular_definingHopfIdeal k
      (Tuple.antitone_sortDesc w))
    (smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra k w)

end

end TauCeti.GeneralLinear
