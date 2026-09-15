/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Splitting
public import TauCeti.Algebra.Lie.F4.ShortRoot.PinnedMultiplication

/-!
# Multiplicativity of the special isogeny of type F4 in characteristic two

The matrix formula `TauCeti.F4ShortRoot.specialIsogenyMatrix` for the special isogeny of type `F₄`
reads the `(p, q)` entry of `τ g` as the `p`th short-root quotient coordinate of the conjugate
`g Bq g⁻¹` of the `q`th representing matrix. This file proves that the formula is multiplicative on
the matrices preserving the invariant symmetric multiplication of the twenty-six-dimensional
module, over a ring of characteristic two, and that the pinned data lies in that subgroup.

Multiplicativity asks that the twenty-six representing matrices and the twenty-six quotient
coordinates split a subspace stable under conjugation. That subspace is the copy of the represented
Chevalley algebra, the matrices differentiating the multiplication, stable because `g` is
multiplicative for the multiplication; inside it the kernel of the quotient coordinates is the
short-root ideal, spanned by the multiplication operators, and it is stable for the same reason,
since a multiplicative matrix permutes the multiplication operators through its tautological action
on their index. The splitting itself,
`TauCeti.F4ShortRoot.eq_sum_quotientMatrix_add_multiplicationBy`, holds only in characteristic two,
which is where the multiplication operators span an ideal. Multiplicativity fails on the whole of
`GL₂₆`, so the hypothesis cannot be dropped.

Nothing here transports the formula to a group of matrix-valued points: the carrier built from this
representation is not identified with the pinned simply connected group scheme of type `F₄`, and
constructions transfer to that group scheme only along such an identification. No fixed-point
subgroup is formed and no finiteness or simplicity is claimed.

## Main definitions

* `TauCeti.F4ShortRoot.multiplicationStabilizer`: the invertible matrices preserving the invariant
  multiplication.

## Main results

* `TauCeti.F4ShortRoot.specialIsogenyMatrix_mul`: **the special isogeny is multiplicative on
  matrices preserving the multiplication**, in characteristic two.
* `TauCeti.F4ShortRoot.rootElementUnit_mem_multiplicationStabilizer` and
  `TauCeti.F4ShortRoot.mem_multiplicationStabilizer_of_coe_eq_diagonal`: the pinned data lies in
  the subgroup.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §7.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R]

open TauCeti.DynkinType

/-- **The stabilizer of the invariant multiplication**: the invertible matrices multiplicative for
the invariant symmetric multiplication of the twenty-six-dimensional module of type `F₄`. -/
def multiplicationStabilizer : Subgroup (GeneralLinearGroup (Fin 26) R) where
  carrier := {g | PreservesMultiplication (g : Matrix (Fin 26) (Fin 26) R)}
  one_mem' := preservesMultiplication_one
  mul_mem' := fun {g h} hg hh => by
    change PreservesMultiplication ((g * h : GeneralLinearGroup (Fin 26) R) :
      Matrix (Fin 26) (Fin 26) R)
    rw [Units.val_mul]
    exact hg.mul hh
  inv_mem' := fun {g} hg => hg.of_mul_eq_one
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

/-- The defining condition of the stabilizer of the multiplication. -/
theorem mem_multiplicationStabilizer {g : GeneralLinearGroup (Fin 26) R} :
    g ∈ multiplicationStabilizer ↔
      PreservesMultiplication (g : Matrix (Fin 26) (Fin 26) R) := Iff.rfl

/-- Every numbered simple root element lies in the stabilizer of the multiplication. -/
theorem rootElementUnit_mem_multiplicationStabilizer (k : Fin 4 ⊕ Fin 4) (u : R) :
    rootElementUnit k u ∈ multiplicationStabilizer := by
  rw [mem_multiplicationStabilizer, coe_rootElementUnit]
  exact preservesMultiplication_rootElementMatrix k u

/-- Every point of the weight torus lies in the stabilizer of the multiplication. -/
theorem mem_multiplicationStabilizer_of_coe_eq_diagonal {g : GeneralLinearGroup (Fin 26) R}
    (s : Fin 4 → Rˣ)
    (hg : (g : Matrix (Fin 26) (Fin 26) R) =
      Matrix.diagonal fun a => (torusCharacter s (f4ShortRootWeight a) : R)) :
    g ∈ multiplicationStabilizer := by
  rw [mem_multiplicationStabilizer, hg]
  exact preservesMultiplication_weightTorusMatrix s

/-! ## Multiplicativity -/

variable [CharP R 2]

/-- **The special isogeny of type `F₄` is multiplicative in characteristic two** on matrices
preserving the invariant multiplication. Multiplicativity fails on the whole of `GL₂₆`: it is the
preservation hypothesis, which the pinned type-`F₄` data satisfies, that makes the quotient by the
short-root ideal an invariant subquotient and so turns the formula into a homomorphism. -/
theorem specialIsogenyMatrix_mul {g h : GeneralLinearGroup (Fin 26) R}
    (hg : PreservesMultiplication (g : Matrix (Fin 26) (Fin 26) R))
    (hh : PreservesMultiplication (h : Matrix (Fin 26) (Fin 26) R)) :
    specialIsogenyMatrix (g * h) = specialIsogenyMatrix g * specialIsogenyMatrix h := by
  have hgi : (g : Matrix (Fin 26) (Fin 26) R) * (↑g⁻¹ : Matrix (Fin 26) (Fin 26) R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hig : (↑g⁻¹ : Matrix (Fin 26) (Fin 26) R) * (g : Matrix (Fin 26) (Fin 26) R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hhi : (h : Matrix (Fin 26) (Fin 26) R) * (↑h⁻¹ : Matrix (Fin 26) (Fin 26) R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hih : (↑h⁻¹ : Matrix (Fin 26) (Fin 26) R) * (h : Matrix (Fin 26) (Fin 26) R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  ext p q
  set W : Matrix (Fin 26) (Fin 26) R := (h : Matrix (Fin 26) (Fin 26) R) *
    (quotientMatrix q).map (Int.cast : ℤ → R) * (↑h⁻¹ : Matrix (Fin 26) (Fin 26) R) with hWdef
  have hWder : IsDerivation W := (isDerivation_map_quotientMatrix q).conj hh hhi hih
  have hsplit := eq_sum_quotientMatrix_add_multiplicationBy hWder
  have hconj : (g : Matrix (Fin 26) (Fin 26) R) * W * (↑g⁻¹ : Matrix (Fin 26) (Fin 26) R) =
      (∑ k, quotientCoordinate k W • ((g : Matrix (Fin 26) (Fin 26) R) *
          (quotientMatrix k).map (Int.cast : ℤ → R) * (↑g⁻¹ : Matrix (Fin 26) (Fin 26) R))) +
        multiplicationBy ((g : Matrix (Fin 26) (Fin 26) R) *ᵥ
          fun a => W (idealRow a) (idealCol a)) := by
    conv_lhs => rw [hsplit]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_smul, Matrix.smul_mul]
    · rw [hg.mulVec, Matrix.mul_assoc, hgi, mul_one]
  have hcoe : ((g * h : GeneralLinearGroup (Fin 26) R) : Matrix (Fin 26) (Fin 26) R) *
      (quotientMatrix q).map (Int.cast : ℤ → R) *
      ((↑(g * h)⁻¹ : GeneralLinearGroup (Fin 26) R) : Matrix (Fin 26) (Fin 26) R) =
      (g : Matrix (Fin 26) (Fin 26) R) * W * (↑g⁻¹ : Matrix (Fin 26) (Fin 26) R) := by
    rw [hWdef, Units.val_mul, _root_.mul_inv_rev, Units.val_mul]
    noncomm_ring
  rw [specialIsogenyMatrix_apply, hcoe, hconj, quotientCoordinate_add,
    quotientCoordinate_multiplicationBy, add_zero, quotientCoordinate_sum, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [quotientCoordinate_smul, specialIsogenyMatrix_apply, specialIsogenyMatrix_apply, hWdef,
      mul_comm]

/-- **The special isogeny is multiplicative on the stabilizer of the multiplication.** -/
theorem specialIsogenyMatrix_mul_of_mem_multiplicationStabilizer
    {g h : GeneralLinearGroup (Fin 26) R} (hg : g ∈ multiplicationStabilizer)
    (hh : h ∈ multiplicationStabilizer) :
    specialIsogenyMatrix (g * h) = specialIsogenyMatrix g * specialIsogenyMatrix h :=
  specialIsogenyMatrix_mul hg hh

end TauCeti.F4ShortRoot
