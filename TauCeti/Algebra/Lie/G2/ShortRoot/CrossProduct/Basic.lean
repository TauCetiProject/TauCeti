/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.Basic
public import TauCeti.LinearAlgebra.Matrix.Alternating

/-!
# The type-G2 cross product

The seven-dimensional module of type `G₂` carries an invariant alternating multiplication, the
*cross product*, together with an invariant symmetric bilinear form. This file writes down the
cross product and the invariant form of the dual module in the weight basis of
`TauCeti.Algebra.Lie.G2.ShortRoot.Basic`, says what it is for a matrix to preserve the cross
product, and records the contraction of an alternating matrix against it.

The dual form is the one that appears in the applications, because they transport alternating
matrices by congruence `W ↦ g W gᵀ`: what such an argument needs is the matrix `B` with
`g B gᵀ = B`, which is the Gram matrix of the induced form on the dual module, not of the form on
the module itself. For an invertible `g` the two conditions are equivalent, since `gᵀ G g = G` is
the same as `g G⁻¹ gᵀ = G⁻¹`; the congruence form is stated because it is what the proofs use and
because it does not assume invertibility.

Read on alternating matrices, congruence `W ↦ g W gᵀ` is the exterior square of `g`. Away from
characteristic two, the contraction kernel identifies the copy of the Lie algebra inside the
alternating matrices. It is stable under congruence because `g` preserves the cross product. In
characteristic three, the span of `crossBivector` is its short-root ideal and is stable when `g`
also fixes the invariant dual form. These facts drive the multiplicativity of the special isogeny;
the isogeny itself appears downstream, in
`TauCeti.Algebra.Lie.G2.ShortRoot.IsogenyMultiplicative`.

## Main definitions

* `TauCeti.G2ShortRoot.crossOperator` and `TauCeti.G2ShortRoot.invariantDualForm`: the cross
  product, and the invariant symmetric form of the dual module, in the weight basis, with their
  tables `TauCeti.G2ShortRoot.crossOperator_def` and `TauCeti.G2ShortRoot.invariantDualForm_def`.
* `TauCeti.G2ShortRoot.crossBivector`: the cross-product operators transported by the invariant
  dual form, alternating matrices that span the short-root ideal in characteristic three.
* `Matrix.PreservesG2Cross`: multiplicativity of a matrix for the cross product.
* `Matrix.g2CrossMap`: the contraction of a matrix against the cross product, as a linear map.

## Main results

* `Matrix.preservesG2Cross_one` and `Matrix.PreservesG2Cross.mul`: the matrices preserving the
  cross product are closed under multiplication and contain the identity.
* `Matrix.PreservesG2Cross.map` and `TauCeti.G2ShortRoot.preservesDualForm_map`: both invariance
  conditions transport along any ring homomorphism.
* `Matrix.g2CrossMap_mul_mul_transpose`: a matrix preserving the cross product intertwines the
  congruence action on alternating matrices with its tautological action on vectors.
* `Matrix.g2CrossMap_rankTwo`: contraction of `u vᵀ - v uᵀ` is twice `u × v`.
* `TauCeti.G2ShortRoot.mul_crossBivector_mul_transpose`: stability of the short-root span under
  congruence.
* `Matrix.g2CrossMap_crossBivector`: in characteristic three the short-root matrices lie in the
  kernel of the contraction.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6, for the cross product and the short-root ideal in characteristic three.
* The coordinate cross-product and invariant-form development was adapted from the earlier closed
  [Tau Ceti PR #6708](https://github.com/TauCetiProject/TauCeti/pull/6708).
-/

public section

open Matrix

universe u

namespace TauCeti.G2ShortRoot

variable {R : Type u} [CommRing R]

/-- The seven matrices of the invariant cross product of the seven-dimensional module of type `G₂`,
in the weight basis of `TauCeti.Algebra.Lie.G2.ShortRoot.Basic`: `crossOperator k` is the operator
`v ↦ e_k × v` of the alternating multiplication the Lie algebra acts on by derivations. -/
def crossOperator : Fin 7 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 0, 0, -2, 0, 0, 0;
      0, 0, 0, 0, -2, 0, 0;
      0, 0, 0, 0, 0, -2, 0;
      0, 0, 0, 0, 0, 0, -1;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 2, 0, 0, 0, 0;
      0, 0, 0, 2, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0;
      0, 0, 0, 0, 0, 0, -2;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, -2, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 2, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, -2;
      0, 0, 0, 0, 0, 0, 0],
    !![2, 0, 0, 0, 0, 0, 0;
      0, -2, 0, 0, 0, 0, 0;
      0, 0, -2, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 2, 0, 0;
      0, 0, 0, 0, 0, 2, 0;
      0, 0, 0, 0, 0, 0, -2],
    !![0, 0, 0, 0, 0, 0, 0;
      2, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0;
      0, 0, 0, -2, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 2, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      2, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -2, 0, 0, 0;
      0, 0, 0, 0, -2, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 2, 0, 0, 0, 0, 0;
      0, 0, 2, 0, 0, 0, 0;
      0, 0, 0, 2, 0, 0, 0]]

/-- The Gram matrix, in the dual of the weight basis, of the invariant symmetric bilinear form
induced on the dual of the seven-dimensional module. Equivalently it is the invariant symmetric
tensor in the module tensored with itself, the inverse of the Gram matrix of the invariant form on
the module itself, taken primitive over the integers. It pairs the coordinate of a weight with the
coordinate of its negative, and a matrix preserves it by the congruence `g B gᵀ = B`. -/
def invariantDualForm : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 0, 0, 0, 0, 0, 2;
    0, 0, 0, 0, 0, -2, 0;
    0, 0, 0, 0, 2, 0, 0;
    0, 0, 0, -1, 0, 0, 0;
    0, 0, 2, 0, 0, 0, 0;
    0, -2, 0, 0, 0, 0, 0;
    2, 0, 0, 0, 0, 0, 0]

/-- **The table of the cross-product operators**, the defining equation of
`TauCeti.G2ShortRoot.crossOperator`. -/
theorem crossOperator_def :
    crossOperator =
    ![!![0, 0, 0, -2, 0, 0, 0;
        0, 0, 0, 0, -2, 0, 0;
        0, 0, 0, 0, 0, -2, 0;
        0, 0, 0, 0, 0, 0, -1;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0],
      !![0, 0, 2, 0, 0, 0, 0;
        0, 0, 0, 2, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, -1, 0;
        0, 0, 0, 0, 0, 0, -2;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0],
      !![0, -2, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 2, 0, 0, 0;
        0, 0, 0, 0, 1, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, -2;
        0, 0, 0, 0, 0, 0, 0],
      !![2, 0, 0, 0, 0, 0, 0;
        0, -2, 0, 0, 0, 0, 0;
        0, 0, -2, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 2, 0, 0;
        0, 0, 0, 0, 0, 2, 0;
        0, 0, 0, 0, 0, 0, -2],
      !![0, 0, 0, 0, 0, 0, 0;
        2, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, -1, 0, 0, 0, 0;
        0, 0, 0, -2, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 2, 0],
      !![0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        2, 0, 0, 0, 0, 0, 0;
        0, 1, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, -2, 0, 0, 0;
        0, 0, 0, 0, -2, 0, 0],
      !![0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        1, 0, 0, 0, 0, 0, 0;
        0, 2, 0, 0, 0, 0, 0;
        0, 0, 2, 0, 0, 0, 0;
        0, 0, 0, 2, 0, 0, 0]] := (rfl)

/-- **The table of the invariant dual form**, the defining equation of
`TauCeti.G2ShortRoot.invariantDualForm`. -/
theorem invariantDualForm_def :
    invariantDualForm =
    !![0, 0, 0, 0, 0, 0, 2;
      0, 0, 0, 0, 0, -2, 0;
      0, 0, 0, 0, 2, 0, 0;
      0, 0, 0, -1, 0, 0, 0;
      0, 0, 2, 0, 0, 0, 0;
      0, -2, 0, 0, 0, 0, 0;
      2, 0, 0, 0, 0, 0, 0] := (rfl)

/-- A nonzero cross-product coefficient has output weight equal to the sum of the input weights. -/
theorem weight_eq_add_of_crossOperator_ne_zero (k i j : Fin 7) (h : crossOperator k i j ≠ 0) :
    weight i = weight k + weight j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [crossOperator_def] at h <;> decide

/-- The invariant dual form pairs only basis vectors whose weights sum to zero. -/
theorem weight_add_eq_zero_of_invariantDualForm_ne_zero (i j : Fin 7)
    (h : invariantDualForm i j ≠ 0) :
    weight i + weight j = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [invariantDualForm_def] at h <;> decide

/-- The seven matrices `crossOperator a * invariantDualForm`, the cross-product operators
transported by the invariant dual form. They are alternating, and in characteristic three they
span the short-root ideal of the Lie algebra, read inside the alternating matrices. -/
def crossBivector (a : Fin 7) : Matrix (Fin 7) (Fin 7) ℤ :=
  crossOperator a * invariantDualForm

/-- **The entries of the transported cross-product operators**, computed once from the two tables
so that a coordinate argument does not recompute a matrix product for every entry it reads. -/
theorem crossBivector_eq :
    crossBivector =
  ![!![0, 0, 0, 2, 0, 0, 0;
        0, 0, -4, 0, 0, 0, 0;
        0, 4, 0, 0, 0, 0, 0;
        -2, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0],
      !![0, 0, 0, 0, 4, 0, 0;
        0, 0, 0, -2, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 2, 0, 0, 0, 0, 0;
        -4, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0],
      !![0, 0, 0, 0, 0, 4, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, -2, 0, 0, 0;
        0, 0, 2, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        -4, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0],
      !![0, 0, 0, 0, 0, 0, 4;
        0, 0, 0, 0, 0, 4, 0;
        0, 0, 0, 0, -4, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 4, 0, 0, 0, 0;
        0, -4, 0, 0, 0, 0, 0;
        -4, 0, 0, 0, 0, 0, 0],
      !![0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 4;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, -2, 0, 0;
        0, 0, 0, 2, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, -4, 0, 0, 0, 0, 0],
      !![0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 4;
        0, 0, 0, 0, 0, -2, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 2, 0, 0, 0;
        0, 0, -4, 0, 0, 0, 0],
      !![0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0, 2;
        0, 0, 0, 0, 0, -4, 0;
        0, 0, 0, 0, 4, 0, 0;
        0, 0, 0, -2, 0, 0, 0]]
  := by
  decide +kernel

/-- Transporting a cross-product operator by the invariant dual form gives the corresponding
alternating matrix. This is the defining equation of `TauCeti.G2ShortRoot.crossBivector`, stated
because the module system hides the body from a consumer. -/
theorem crossBivector_def (a : Fin 7) :
    crossOperator a * invariantDualForm = crossBivector a := by
  rw [crossBivector]

/-- A matrix **preserves the cross product** when it is multiplicative for it,
`g (u × v) = (g u) × (g v)`, written as one matrix identity for each basis vector of the first
argument. -/
def _root_.Matrix.PreservesG2Cross (g : Matrix (Fin 7) (Fin 7) R) : Prop :=
  ∀ k, g * (crossOperator k).map (Int.cast : ℤ → R) =
    (∑ a, g a k • (crossOperator a).map (Int.cast : ℤ → R)) * g

/-- The defining equations of cross-product preservation. -/
theorem _root_.Matrix.preservesG2Cross_def (g : Matrix (Fin 7) (Fin 7) R) :
    PreservesG2Cross g ↔ ∀ k, g * (crossOperator k).map (Int.cast : ℤ → R) =
      (∑ a, g a k • (crossOperator a).map (Int.cast : ℤ → R)) * g := Iff.rfl

/-- The identity matrix preserves the cross product. -/
@[simp]
theorem _root_.Matrix.preservesG2Cross_one :
    PreservesG2Cross (1 : Matrix (Fin 7) (Fin 7) R) := fun k => by
  rw [one_mul, mul_one, Finset.sum_eq_single k]
  · rw [Matrix.one_apply_eq, one_smul]
  · exact fun b _ hb => by rw [Matrix.one_apply_ne hb, zero_smul]
  · exact fun hk => absurd (Finset.mem_univ k) hk

/-- **Matrices preserving the cross product are closed under multiplication.** -/
theorem _root_.Matrix.PreservesG2Cross.mul {g h : Matrix (Fin 7) (Fin 7) R}
    (hg : PreservesG2Cross g) (hh : PreservesG2Cross h) : PreservesG2Cross (g * h) := fun k => by
  have hsum : ∀ a : Fin 7, g * (crossOperator a).map (Int.cast : ℤ → R) * h =
      (∑ b, g b a • (crossOperator b).map (Int.cast : ℤ → R)) * (g * h) := fun a => by
    rw [hg a]; noncomm_ring
  calc g * h * (crossOperator k).map (Int.cast : ℤ → R)
      = g * ((∑ a, h a k • (crossOperator a).map (Int.cast : ℤ → R)) * h) := by
        rw [mul_assoc, hh k]
    _ = ∑ a, h a k • (g * (crossOperator a).map (Int.cast : ℤ → R) * h) := by
        rw [Finset.sum_mul, Matrix.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by
          rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    _ = ∑ a, ∑ b, (h a k * g b a) • (crossOperator b).map (Int.cast : ℤ → R) * (g * h) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hsum a, Finset.sum_mul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun b _ => by rw [Matrix.smul_mul, smul_smul, Matrix.smul_mul]
    _ = (∑ b, (g * h) b k • (crossOperator b).map (Int.cast : ℤ → R)) * (g * h) := by
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_apply, ← Finset.sum_mul, ← Finset.sum_smul]
        exact congrArg (fun c : R => c • (crossOperator b).map (Int.cast : ℤ → R) * (g * h))
          (Finset.sum_congr rfl fun a _ => mul_comm _ _)

/-- Preserving the type-`G₂` cross product is inherited by the image of a matrix under a ring
homomorphism. -/
theorem _root_.Matrix.PreservesG2Cross.map {S : Type*} [CommRing S] (f : R →+* S)
    {g : Matrix (Fin 7) (Fin 7) R} (hg : PreservesG2Cross g) : PreservesG2Cross (g.map f) := by
  have hcast : ∀ a : Fin 7, ((crossOperator a).map (Int.cast : ℤ → R)).map f =
      (crossOperator a).map (Int.cast : ℤ → S) := fun a => by
    rw [Matrix.map_map]
    exact congrArg _ (funext fun z => map_intCast f z)
  intro k
  have h := congrArg (fun N : Matrix (Fin 7) (Fin 7) R => N.map f) (hg k)
  simp only [Matrix.map_mul, hcast] at h
  rw [h]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
    map_mul, map_intCast]

/-- Fixing the invariant dual form by congruence is inherited by the image of a matrix under a
ring homomorphism. -/
theorem preservesDualForm_map {S T : Type*} [Ring S] [Ring T] (f : S →+* T)
    {M : Matrix (Fin 7) (Fin 7) S}
    (h : M * invariantDualForm.map (Int.cast : ℤ → S) * Mᵀ =
      invariantDualForm.map (Int.cast : ℤ → S)) :
    M.map f * invariantDualForm.map (Int.cast : ℤ → T) * (M.map f)ᵀ =
      invariantDualForm.map (Int.cast : ℤ → T) := by
  have hform : (invariantDualForm.map (Int.cast : ℤ → S)).map (f : S → T) =
      invariantDualForm.map (Int.cast : ℤ → T) := by
    rw [Matrix.map_map]
    exact congrArg _ (funext fun z => map_intCast f z)
  have himg := congrArg (fun N : Matrix (Fin 7) (Fin 7) S => N.map (f : S →+* T)) h
  simp only [Matrix.map_mul, Matrix.transpose_map] at himg
  rwa [hform] at himg

/-- **The span of the alternating matrices `crossBivector` is stable under congruence.** A matrix
preserving the cross product and fixing the invariant dual form by congruence permutes them
through the tautological action on their index. -/
theorem mul_crossBivector_mul_transpose {g : Matrix (Fin 7) (Fin 7) R} (hg : PreservesG2Cross g)
    (hB : g * invariantDualForm.map (Int.cast : ℤ → R) * gᵀ =
      invariantDualForm.map (Int.cast : ℤ → R))
    (k : Fin 7) :
    g * (crossBivector k).map (Int.cast : ℤ → R) * gᵀ =
      ∑ a, g a k • (crossBivector a).map (Int.cast : ℤ → R) := by
  have hmap : ∀ a : Fin 7, (crossBivector a).map (Int.cast : ℤ → R) =
      (crossOperator a).map (Int.cast : ℤ → R) * invariantDualForm.map (Int.cast : ℤ → R) :=
      fun a => by
    rw [← crossBivector_def a]
    exact Matrix.map_mul (f := (Int.castRingHom R))
  calc g * (crossBivector k).map (Int.cast : ℤ → R) * gᵀ
      = (g * (crossOperator k).map (Int.cast : ℤ → R)) *
          invariantDualForm.map (Int.cast : ℤ → R) * gᵀ := by rw [hmap k]; noncomm_ring
    _ = (∑ a, g a k • (crossOperator a).map (Int.cast : ℤ → R)) *
          (g * invariantDualForm.map (Int.cast : ℤ → R) * gᵀ) := by rw [hg k]; noncomm_ring
    _ = ∑ a, g a k • (crossBivector a).map (Int.cast : ℤ → R) := by
        rw [hB, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc, hmap a]

/-- The cross product contracted against a matrix: the `m`-th coordinate of `g2CrossMap W` pairs `W`
with the `m`-th row of the cross-product operators. It reads the cross product on the exterior
square up to a factor of two, `g2CrossMap (u vᵀ - v uᵀ) = 2 (u × v)`, the two counting the two
orderings of the double contraction. -/
def _root_.Matrix.g2CrossMap : Matrix (Fin 7) (Fin 7) R →ₗ[R] Fin 7 → R where
  toFun W m := ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * Wᵀ) m k
  map_add' W V := by
    ext m
    simp [Matrix.transpose_add, Matrix.mul_add, Finset.sum_add_distrib]
  map_smul' c W := by
    ext m
    simp [Matrix.transpose_smul, Finset.mul_sum]

/-- The defining formula of the contraction. -/
theorem _root_.Matrix.g2CrossMap_def (W : Matrix (Fin 7) (Fin 7) R) (m : Fin 7) :
    g2CrossMap W m = ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * Wᵀ) m k := (rfl)

/-- The contraction of the image of an integral matrix is the integer contraction, coerced. -/
theorem _root_.Matrix.g2CrossMap_map (W : Matrix (Fin 7) (Fin 7) ℤ) (m : Fin 7) :
    g2CrossMap (W.map (Int.cast : ℤ → R)) m = ((g2CrossMap W m : ℤ) : R) := by
  have key : ∀ k : Fin 7,
      (crossOperator k).map (Int.cast : ℤ → R) * (W.map (Int.cast : ℤ → R))ᵀ =
        ((crossOperator k).map (Int.cast : ℤ → ℤ) * Wᵀ).map (Int.cast : ℤ → R) := fun k => by
    have hcast : (crossOperator k).map (Int.cast : ℤ → ℤ) = crossOperator k := by
      ext a b
      simp
    rw [hcast, ← Matrix.transpose_map]
    exact (Matrix.map_mul (L := crossOperator k) (M := Wᵀ) (f := Int.castRingHom R)).symm
  rw [g2CrossMap_def, g2CrossMap_def, Int.cast_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [key k, Matrix.map_apply]

/-- **In characteristic three the matrices spanning the short-root ideal lie in the kernel of the
contraction**: over the integers their contractions are divisible by three. -/
@[simp]
theorem _root_.Matrix.g2CrossMap_crossBivector [CharP R 3] (a m : Fin 7) :
    g2CrossMap ((crossBivector a).map (Int.cast : ℤ → R)) m = 0 := by
  rw [g2CrossMap_map, CharP.intCast_eq_zero_iff R 3]
  revert a m
  decide +kernel

/-- **The contraction is equivariant.** A matrix preserving the cross product intertwines its
congruence action on alternating matrices with its tautological action on vectors. -/
theorem _root_.Matrix.g2CrossMap_mul_mul_transpose {g : Matrix (Fin 7) (Fin 7) R}
    (hg : PreservesG2Cross g) (W : Matrix (Fin 7) (Fin 7) R) (m : Fin 7) :
    g2CrossMap (g * W * gᵀ) m = ∑ c, g m c * g2CrossMap W c := by
  have hT : (g * W * gᵀ)ᵀ = g * Wᵀ * gᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    noncomm_ring
  have hL : ∀ k : Fin 7,
      ((crossOperator k).map (Int.cast : ℤ → R) * (g * Wᵀ * gᵀ)) m k =
        ∑ a, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a := fun k => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => congrArg _ (Matrix.transpose_apply g a k)
  have step : ∀ a : Fin 7,
      ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a =
        ∑ c, g m c * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ) c a := fun a => by
    have h1 : ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a =
        ((∑ k, g k a • (crossOperator k).map (Int.cast : ℤ → R)) * g * Wᵀ) m a := by
      rw [Finset.sum_mul, Finset.sum_mul, Matrix.sum_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_comm]
    have h2 : ∑ c, g m c * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ) c a =
        (g * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ)) m a := Matrix.mul_apply.symm
    rw [h1, h2, ← hg a]
    noncomm_ring
  calc g2CrossMap (g * W * gᵀ) m
      = ∑ k, ∑ a, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a := by
        rw [g2CrossMap_def, hT]
        exact Finset.sum_congr rfl fun k _ => hL k
    _ = ∑ a, ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a :=
        Finset.sum_comm
    _ = ∑ a, ∑ c, g m c * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ) c a :=
        Finset.sum_congr rfl fun a _ => step a
    _ = ∑ c, ∑ a, g m c * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ) c a := Finset.sum_comm
    _ = ∑ c, g m c * g2CrossMap W c :=
        Finset.sum_congr rfl fun c _ => by rw [g2CrossMap_def, Finset.mul_sum]

/-- The contraction written entrywise. -/
theorem _root_.Matrix.g2CrossMap_apply (W : Matrix (Fin 7) (Fin 7) R) (m : Fin 7) :
    g2CrossMap W m = ∑ k, ∑ l, ((crossOperator k m l : ℤ) : R) * W k l := by
  rw [g2CrossMap_def]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.map_apply, Matrix.transpose_apply]

/-- **The contraction of a rank-two alternating matrix is twice the cross product.** The cross
product `u × v` is written through `crossOperator`, avoiding a second public definition of the
same bilinear operation. -/
theorem _root_.Matrix.g2CrossMap_rankTwo (u v : Fin 7 → R) (m : Fin 7) :
    g2CrossMap (Matrix.of fun i j => u i * v j - v i * u j) m =
      2 * ∑ k, u k * ∑ l, ((crossOperator k m l : ℤ) : R) * v l := by
  classical
  rw [g2CrossMap_apply]
  fin_cases m <;> simp [Fin.sum_univ_seven, crossOperator] <;> ring

/-- **The matrices `crossBivector` are alternating** over any commutative ring. -/
@[simp]
theorem transpose_crossBivector_map (l : Fin 7) :
    ((crossBivector l).map (Int.cast : ℤ → R))ᵀ = -(crossBivector l).map (Int.cast : ℤ → R) :=
  Matrix.transpose_map_of_transpose_eq_neg (Int.castRingHom R)
    (by revert l; decide +kernel)

/-- The matrices `crossBivector` have zero diagonal. -/
@[simp]
theorem crossBivector_apply_self (l a : Fin 7) : crossBivector l a a = 0 := by
  revert l a
  decide +kernel

end TauCeti.G2ShortRoot
