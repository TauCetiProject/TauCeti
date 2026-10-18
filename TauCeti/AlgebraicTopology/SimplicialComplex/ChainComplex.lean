/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Algebra.BigOperators.AlternatingSum
public import TauCeti.AlgebraicTopology.SimplicialComplex.Cell

/-!
# The ordered simplicial chain complex

For a simplicial complex with linearly ordered vertices, its simplicial chains are the free
modules on the faces of each dimension.  The boundary of a face with increasing vertex list
`[v₀, ..., vₙ]` is the alternating sum of the faces obtained by deleting one vertex:

`∂[v₀, ..., vₙ] = ∑ j, (-1) ^ j [v₀, ..., v̂ⱼ, ..., vₙ]`.

This file packages the alternating boundary as a chain complex over any coefficient ring.  The
signs are central, so the coefficient ring need not be commutative.

The comparison with the cellular chain complex of the realization is separate.  Both complexes
are indexed by `RealizationCell`, so that comparison reduces to computing the cellular incidence
coefficients in these ordered coordinates.

## Main definitions

* `TauCeti.OrderedSimplicialChain`: finite linear combinations of ordered simplicial cells.
* `TauCeti.OrderedSimplicialChain.boundary`: the alternating simplicial boundary.
* `TauCeti.orderedSimplicialChainComplex`: the resulting chain complex of modules.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1.
-/

public section

noncomputable section

open CategoryTheory Finsupp

universe u v

namespace TauCeti

variable {ι : Type u} [LinearOrder ι]
variable (K : _root_.AbstractSimplicialComplex ι)

/-- Ordered simplicial `n`-chains with coefficients in `R`: finite linear combinations of the
`n`-dimensional faces, oriented by their increasing vertex enumerations. -/
abbrev OrderedSimplicialChain (R : Type v) [Semiring R] (n : ℕ) :=
  _root_.AbstractSimplicialComplex.RealizationCell K n →₀ R

namespace OrderedSimplicialChain

variable {K}
variable (R : Type v) [Ring R]

/-- The boundary of a single `(n + 1)`-dimensional simplicial cell is the alternating sum of its
deleted-vertex faces. -/
def boundaryCell {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    OrderedSimplicialChain K R n :=
  ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • single (c.face j) 1

/-- The explicit alternating-sum formula for the boundary of one cell. -/
theorem boundaryCell_def {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    boundaryCell R c = ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • single (c.face j) 1 :=
  (rfl)

/-- The ordered simplicial boundary, extended linearly from cells. -/
def boundary (n : ℕ) : OrderedSimplicialChain K R (n + 1) →ₗ[R] OrderedSimplicialChain K R n :=
  linearCombination R (boundaryCell R)

/-- The boundary of a cell with coefficient one is its alternating deleted-face sum. -/
theorem boundary_single_one {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    boundary R n (single c 1) = boundaryCell R c := by
  rw [boundary, linearCombination_single, one_smul]

/-- The boundary of a scalar multiple of a cell is the corresponding alternating sum with that
coefficient on every face. -/
@[simp]
theorem boundary_single {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) (a : R) :
    boundary R n (single c a) =
      ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • single (c.face j) a := by
  have hc : ∀ j : ℕ, a * (-1 : R) ^ j = (-1) ^ j * a := fun j ↦
    ((Commute.neg_one_right a).pow_right j).eq
  simp only [boundary, linearCombination_single, boundaryCell, Finset.smul_sum, smul_single,
    smul_eq_mul, mul_one, hc]

/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) :
    boundary (K := K) R n ∘ₗ boundary (K := K) R (n + 1) = 0 := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, LinearMap.zero_apply,
    boundary_single, map_sum, map_smul, Finset.smul_sum]
  have h := sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
      (fun i j ↦ single ((c.face i).face j) (1 : R)) fun i j hij ↦ by
        exact congrArg (fun d ↦ single d (1 : R))
          (by simpa [Fin.succAbove_castSucc_of_le i j hij,
              Fin.predAbove_castSucc_of_le j i hij] using
            (_root_.AbstractSimplicialComplex.RealizationCell.face_face c i.castSucc j).symm)
  simp_rw [← Int.cast_smul_eq_zsmul R] at h
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one, Finset.smul_sum] using h

end OrderedSimplicialChain

/-- The ordered simplicial chain complex of `K`, with one basis vector for every face and the
usual alternating deleted-vertex boundary. -/
def orderedSimplicialChainComplex (R : Type v) [Ring R] :
    ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (OrderedSimplicialChain K R n))
    (fun n ↦ ModuleCat.ofHom (OrderedSimplicialChain.boundary (K := K) R n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, OrderedSimplicialChain.boundary_boundary (K := K)]
      rfl

variable {K}
variable (R : Type v) [Ring R]

/-- The object in degree `n` of the ordered simplicial chain complex is the free module on the
`n`-dimensional faces. -/
@[simp]
theorem orderedSimplicialChainComplex_X (n : ℕ) :
    (orderedSimplicialChainComplex K R).X n = ModuleCat.of R (OrderedSimplicialChain K R n) :=
  (rfl)

/-- After identifying the objects with the free modules on cells, the differential of the
ordered simplicial chain complex is the alternating simplicial boundary. -/
@[simp]
theorem orderedSimplicialChainComplex_d (n : ℕ) :
    (orderedSimplicialChainComplex K R).d (n + 1) n =
      eqToHom (orderedSimplicialChainComplex_X R (n + 1)) ≫
        ModuleCat.ofHom (OrderedSimplicialChain.boundary (K := K) R n) ≫
          eqToHom (orderedSimplicialChainComplex_X R n).symm := by
  simp only [orderedSimplicialChainComplex, ChainComplex.of_d]
  rfl

end TauCeti
