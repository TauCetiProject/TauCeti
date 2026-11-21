/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Triple.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The Maslov index of a triangle domain

The holomorphic triangle maps of Heegaard Floer homology count the Whitney triangles of Maslov
index zero, and their grading properties rest on the additivity of the Maslov index under
juxtaposition with Whitney disks. Sarkar computes the Maslov index of a Whitney triangle from its
domain alone, extending Lipshitz's formula `μ = e(D) + n_x(D) + n_y(D)` for disks
(`TauCeti.HeegaardRegionSystem.maslovIndex`). This file defines Sarkar's expression for the
abstract incidence data `TauCeti.HeegaardTripleRegionSystem` of a triple diagram
`(Σ, α, β, γ, z)` with `n` curves in each family, and proves its additivity at each of the three
corners.

For a triangle domain `D` with corners `x ∈ T_α ∩ T_β`, `y ∈ T_β ∩ T_γ` and `w ∈ T_α ∩ T_γ`
(`TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain`), whose boundary runs along `α` from `x` to
`w`, along `γ` from `w` to `y` and along `β` from `y` to `x`, the index is

`μ(D) = e(D) + n_x(D) + n_w(D) + ∂_β D · ∂_γ D - n / 2`

(`TauCeti.HeegaardTripleRegionSystem.maslovIndex`). Here `e(D)` is the Euler measure, in which
every corner contributes a quarter; `n_p(D)` is the point measure, the average multiplicity of
`D` at the four corners at the point `p`, summed over the points of a generator; and
`∂_β D · ∂_γ D` is the intersection number of the `β`- and `γ`-parts of the boundary of `D`. The
corner `y` enters only through the corner conditions on `D`.

The two `1`-chains in an intersection number `∂_β D · ∂_γ E` meet at points of `β ∩ γ`, where
they may have endpoints, so Sarkar averages the intersection numbers of the four small diagonal
translates of the first chain with the second. At a crossing this contributes the sum of the
coefficients of `∂_β D` on the two `β`-arcs there times the sum of the coefficients of `∂_γ E` on
the two `γ`-arcs, divided by four, with the sign of the crossing. In terms of the region
multiplicities, the sum of the coefficients of `∂_γ E` times that sign is the change, across `γ`,
of the sum of the multiplicities of `E` on the two sides of `β`. So the intersection numbers below
are defined from the region labels alone, with no separate record of crossing signs
(`TauCeti.HeegaardTripleRegionSystem.alphaBetaIntersection`,
`TauCeti.HeegaardTripleRegionSystem.betaGammaIntersection`,
`TauCeti.HeegaardTripleRegionSystem.gammaAlphaIntersection`). Each can be read along either of its
two curves, and the two readings agree at every compatible crossing.

The key identity, Sarkar's Theorem 3.1, compares point measures at the two ends of a boundary
arc: if the `α`-part of the boundary of `D` runs from `x` to `w`, then for every domain `E`,
`n_w(E) - n_x(E) = ∂E · ∂_α D`. It follows by summation by parts along the curves. Together with
the antisymmetry of the intersection numbers it gives:

* the formula is cyclically symmetric: `n_x + n_w + ∂_β D · ∂_γ D`,
  `n_w + n_y + ∂_α D · ∂_β D` and `n_y + n_x + ∂_γ D · ∂_α D` agree for a triangle domain;
* the index is additive under juxtaposition with a disk domain at each corner, with the disk
  domain contributing its Lipshitz index `e + n + n`; in particular adding the whole surface adds
  two when the region Euler characteristics are those of a closed surface of genus `n`.

The Euler characteristics `χ(R)` of the regions are not determined by the incidence data, so they
are an explicit argument, as for disks. The identification of `μ(D)` with the expected dimension
of the moduli space of holomorphic triangles in the class with domain `D` is Sarkar's
Theorem 4.1, and is not formalized here.

## Main definitions

* `TauCeti.HeegaardTripleRegionSystem.alphaBetaPointMeasure`,
  `TauCeti.HeegaardTripleRegionSystem.betaGammaPointMeasure`,
  `TauCeti.HeegaardTripleRegionSystem.alphaGammaPointMeasure`: the point measures at the points of
  `α ∩ β`, `β ∩ γ` and `α ∩ γ`.
* `TauCeti.HeegaardTripleRegionSystem.alphaBetaGeneratorPointMeasure` and its two counterparts:
  the point measures `n_x(D)`, `n_y(D)`, `n_w(D)` of generators.
* `TauCeti.HeegaardTripleRegionSystem.eulerMeasure`: the Euler measure `e(D)`.
* `TauCeti.HeegaardTripleRegionSystem.alphaBetaIntersection`,
  `TauCeti.HeegaardTripleRegionSystem.betaGammaIntersection`,
  `TauCeti.HeegaardTripleRegionSystem.gammaAlphaIntersection`: the intersection numbers
  `∂_α D · ∂_β E`, `∂_β D · ∂_γ E` and `∂_γ D · ∂_α E`.
* `TauCeti.HeegaardTripleRegionSystem.maslovIndex`: Sarkar's Maslov index of a triangle domain.

## Main results

* `TauCeti.HeegaardTripleRegionSystem.alphaBetaIntersection_apply_alpha` and its two
  counterparts: each intersection number read along its other curve.
* `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain.alphaGammaGeneratorPointMeasure_sub` and
  its two counterparts: Sarkar's point measure identity along the three edges of a triangle
  domain.
* `TauCeti.HeegaardTripleRegionSystem.IsAlphaBetaDomainBetween.alphaBetaGeneratorPointMeasure_sub`
  and its two counterparts: the same identity for the disk domains of the three Heegaard diagrams
  of the triple.
* `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain.maslovIndex_eq_alphaBetaIntersection` and
  `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain.maslovIndex_eq_gammaAlphaIntersection`: the
  two cyclically rotated forms of the formula.
* `TauCeti.HeegaardTripleRegionSystem.IsAlphaBetaDomainBetween.maslovIndex_add`,
  `TauCeti.HeegaardTripleRegionSystem.IsBetaGammaDomainBetween.maslovIndex_add` and
  `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain.maslovIndex_add`: additivity under
  juxtaposition with a disk domain at the corners `x`, `y` and `w`.
* `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain.maslovIndex_one_add`: adding the whole
  surface adds two to the Maslov index of a triangle domain on a closed surface of genus `n`.

## References

* S. Sarkar, *Maslov index formulas for Whitney n-gons*, J. Symplectic Geom. **9** (2011),
  [arXiv:math/0609673](https://arxiv.org/abs/math/0609673): the formula
  `μ(D) = ι(D) + 2e(D) - k(n - 2)/2` with
  `ι(D) = μ_{p^{n,1}}(D) + μ_{p^{1,2}}(D) + ∑_{n ≥ j > l > 1} ∂_j D · ∂_l D - e(D)` (§2), the
  corner-averaged intersection numbers (§2), the point measure identity (Theorem 3.1), cyclic
  symmetry (Theorem 3.2) and additivity (Theorem 3.3). For triangles, with the tori ordered
  `T_α, T_γ, T_β` so that `p^{1,2} = w`, `p^{2,3} = y` and `p^{3,1} = x`, and with `k = n`, this
  is the formula above.
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), Corollary 4.10, the index
  formula for disks.
-/

public section

open Finset

namespace TauCeti

namespace HeegaardTripleRegionSystem

universe u₁ u₂ u₃ v w

section Crossing

variable {P B R : Type*}

/-- The pairing behind the three intersection numbers below, along a curve family with arcs
labelled by `B`, successor `next`, side regions `left` and `right`, boundary map `bd`, and
crossings `ι : P → B` with another family: at each crossing, the sum of the coefficients of `bd E`
on the two arcs there times the change across the other curve of the sum of the multiplicities of
`D` on the two sides of the first, summed and divided by four. -/
private def crossingPairing [Fintype P] (next : Equiv.Perm B) (left right : B → R)
    (bd : (R → ℤ) →+ B → ℤ) (ι : P → B) : (R → ℤ) →+ (R → ℤ) →+ ℚ :=
  AddMonoidHom.mk' (fun D => AddMonoidHom.mk' (fun E =>
    ((∑ p, (bd E (next.symm (ι p)) + bd E (ι p)) *
      (D (left (ι p)) + D (right (ι p)) -
        (D (left (next.symm (ι p))) + D (right (next.symm (ι p))))) : ℤ) : ℚ) / 4)
    (fun E E' => by
      rw [← add_div, ← Int.cast_add, ← sum_add_distrib]
      congr 3
      exact funext fun p => by simp only [map_add, Pi.add_apply]; ring))
    (fun D D' => by
      ext E
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← add_div, ← Int.cast_add, ← sum_add_distrib]
      congr 3
      exact funext fun p => by simp only [Pi.add_apply]; ring)

end Crossing

variable {n : ℕ} {PointAB : Type u₁} {PointBC : Type u₂} {PointAC : Type u₃} {Region : Type v}
  {Basepoint : Type w}
  (T : HeegaardTripleRegionSystem n PointAB PointBC PointAC Region Basepoint)

section PointMeasure

/-- The point measure `n_p(D)` at a point `p` of `α ∩ β`: the average multiplicity of `D` at the
four corners at `p`, read along the `α`-arcs ending and starting at `p`. -/
def alphaBetaPointMeasure : (Region → ℤ) →+ PointAB → ℚ where
  toFun D p := ((D (T.alphaLeft (T.alphaNext.symm (.inl p))) +
    D (T.alphaRight (T.alphaNext.symm (.inl p))) + (D (T.alphaLeft (.inl p)) +
      D (T.alphaRight (.inl p))) : ℤ) : ℚ) / 4
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply, Int.cast_add]; ring

/-- The point measure `n_p(D)` at a point `p` of `β ∩ γ`: the average multiplicity of `D` at the
four corners at `p`, read along the `β`-arcs ending and starting at `p`. -/
def betaGammaPointMeasure : (Region → ℤ) →+ PointBC → ℚ where
  toFun D p := ((D (T.betaLeft (T.betaNext.symm (.inr p))) +
    D (T.betaRight (T.betaNext.symm (.inr p))) + (D (T.betaLeft (.inr p)) +
      D (T.betaRight (.inr p))) : ℤ) : ℚ) / 4
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply, Int.cast_add]; ring

/-- The point measure `n_p(D)` at a point `p` of `α ∩ γ`: the average multiplicity of `D` at the
four corners at `p`, read along the `α`-arcs ending and starting at `p`. -/
def alphaGammaPointMeasure : (Region → ℤ) →+ PointAC → ℚ where
  toFun D p := ((D (T.alphaLeft (T.alphaNext.symm (.inr p))) +
    D (T.alphaRight (T.alphaNext.symm (.inr p))) + (D (T.alphaLeft (.inr p)) +
      D (T.alphaRight (.inr p))) : ℤ) : ℚ) / 4
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply, Int.cast_add]; ring

@[simp]
theorem alphaBetaPointMeasure_apply (D : Region → ℤ) (p : PointAB) :
    T.alphaBetaPointMeasure D p = ((D (T.alphaLeft (T.alphaNext.symm (.inl p))) +
      D (T.alphaRight (T.alphaNext.symm (.inl p))) + (D (T.alphaLeft (.inl p)) +
        D (T.alphaRight (.inl p))) : ℤ) : ℚ) / 4 :=
  (rfl)

@[simp]
theorem betaGammaPointMeasure_apply (D : Region → ℤ) (p : PointBC) :
    T.betaGammaPointMeasure D p = ((D (T.betaLeft (T.betaNext.symm (.inr p))) +
      D (T.betaRight (T.betaNext.symm (.inr p))) + (D (T.betaLeft (.inr p)) +
        D (T.betaRight (.inr p))) : ℤ) : ℚ) / 4 :=
  (rfl)

@[simp]
theorem alphaGammaPointMeasure_apply (D : Region → ℤ) (p : PointAC) :
    T.alphaGammaPointMeasure D p = ((D (T.alphaLeft (T.alphaNext.symm (.inr p))) +
      D (T.alphaRight (T.alphaNext.symm (.inr p))) + (D (T.alphaLeft (.inr p)) +
        D (T.alphaRight (.inr p))) : ℤ) : ℚ) / 4 :=
  (rfl)

/-- The point measure at a point of `α ∩ β` can also be read along the `β`-arcs. -/
theorem alphaBetaPointMeasure_apply_beta (D : Region → ℤ) (p : PointAB) :
    T.alphaBetaPointMeasure D p = ((D (T.betaLeft (T.betaNext.symm (.inl p))) +
      D (T.betaRight (T.betaNext.symm (.inl p))) + (D (T.betaLeft (.inl p)) +
        D (T.betaRight (.inl p))) : ℤ) : ℚ) / 4 := by
  rw [alphaBetaPointMeasure_apply, (T.crossing_alphaBeta p).corner_sum_eq D]

/-- The point measure at a point of `β ∩ γ` can also be read along the `γ`-arcs. -/
theorem betaGammaPointMeasure_apply_gamma (D : Region → ℤ) (p : PointBC) :
    T.betaGammaPointMeasure D p = ((D (T.gammaLeft (T.gammaNext.symm (.inl p))) +
      D (T.gammaRight (T.gammaNext.symm (.inl p))) + (D (T.gammaLeft (.inl p)) +
        D (T.gammaRight (.inl p))) : ℤ) : ℚ) / 4 := by
  rw [betaGammaPointMeasure_apply, (T.crossing_betaGamma p).corner_sum_eq D]

/-- The point measure at a point of `α ∩ γ` can also be read along the `γ`-arcs. -/
theorem alphaGammaPointMeasure_apply_gamma (D : Region → ℤ) (p : PointAC) :
    T.alphaGammaPointMeasure D p = ((D (T.gammaLeft (T.gammaNext.symm (.inr p))) +
      D (T.gammaRight (T.gammaNext.symm (.inr p))) + (D (T.gammaLeft (.inr p)) +
        D (T.gammaRight (.inr p))) : ℤ) : ℚ) / 4 := by
  rw [alphaGammaPointMeasure_apply, (T.crossing_alphaGamma p).corner_sum_eq D]

/-- The whole surface has point measure one at every point of `α ∩ β`. -/
@[simp]
theorem alphaBetaPointMeasure_one : T.alphaBetaPointMeasure 1 = 1 := by
  ext p
  simp only [alphaBetaPointMeasure_apply, Pi.one_apply]
  norm_num

/-- The whole surface has point measure one at every point of `β ∩ γ`. -/
@[simp]
theorem betaGammaPointMeasure_one : T.betaGammaPointMeasure 1 = 1 := by
  ext p
  simp only [betaGammaPointMeasure_apply, Pi.one_apply]
  norm_num

/-- The whole surface has point measure one at every point of `α ∩ γ`. -/
@[simp]
theorem alphaGammaPointMeasure_one : T.alphaGammaPointMeasure 1 = 1 := by
  ext p
  simp only [alphaGammaPointMeasure_apply, Pi.one_apply]
  norm_num

/-- The point measure `n_x(D) = ∑ᵢ n_{xᵢ}(D)` of a generator `x` of `(Σ, α, β)`. -/
def alphaBetaGeneratorPointMeasure (x : T.alphaBeta.Generator) : (Region → ℤ) →+ ℚ where
  toFun D := ∑ i, T.alphaBetaPointMeasure D (T.alphaBeta.point x i)
  map_zero' := by simp
  map_add' D E := by simp only [map_add, Pi.add_apply, sum_add_distrib]

/-- The point measure `n_y(D) = ∑ᵢ n_{yᵢ}(D)` of a generator `y` of `(Σ, β, γ)`. -/
def betaGammaGeneratorPointMeasure (y : T.betaGamma.Generator) : (Region → ℤ) →+ ℚ where
  toFun D := ∑ i, T.betaGammaPointMeasure D (T.betaGamma.point y i)
  map_zero' := by simp
  map_add' D E := by simp only [map_add, Pi.add_apply, sum_add_distrib]

/-- The point measure `n_w(D) = ∑ᵢ n_{wᵢ}(D)` of a generator `w` of `(Σ, α, γ)`. -/
def alphaGammaGeneratorPointMeasure (w : T.alphaGamma.Generator) : (Region → ℤ) →+ ℚ where
  toFun D := ∑ i, T.alphaGammaPointMeasure D (T.alphaGamma.point w i)
  map_zero' := by simp
  map_add' D E := by simp only [map_add, Pi.add_apply, sum_add_distrib]

@[simp]
theorem alphaBetaGeneratorPointMeasure_apply (x : T.alphaBeta.Generator) (D : Region → ℤ) :
    T.alphaBetaGeneratorPointMeasure x D = ∑ i, T.alphaBetaPointMeasure D (T.alphaBeta.point x i) :=
  (rfl)

@[simp]
theorem betaGammaGeneratorPointMeasure_apply (y : T.betaGamma.Generator) (D : Region → ℤ) :
    T.betaGammaGeneratorPointMeasure y D =
      ∑ i, T.betaGammaPointMeasure D (T.betaGamma.point y i) :=
  (rfl)

@[simp]
theorem alphaGammaGeneratorPointMeasure_apply (w : T.alphaGamma.Generator) (D : Region → ℤ) :
    T.alphaGammaGeneratorPointMeasure w D =
      ∑ i, T.alphaGammaPointMeasure D (T.alphaGamma.point w i) :=
  (rfl)

/-- The point measure of the whole surface at a generator of `(Σ, α, β)` is `n`. -/
theorem alphaBetaGeneratorPointMeasure_one (x : T.alphaBeta.Generator) :
    T.alphaBetaGeneratorPointMeasure x 1 = n := by
  simp

/-- The point measure of the whole surface at a generator of `(Σ, β, γ)` is `n`. -/
theorem betaGammaGeneratorPointMeasure_one (y : T.betaGamma.Generator) :
    T.betaGammaGeneratorPointMeasure y 1 = n := by
  simp

/-- The point measure of the whole surface at a generator of `(Σ, α, γ)` is `n`. -/
theorem alphaGammaGeneratorPointMeasure_one (w : T.alphaGamma.Generator) :
    T.alphaGammaGeneratorPointMeasure w 1 = n := by
  simp

end PointMeasure

section Intersection

/-- The intersection number `∂_α D · ∂_β E` of the `α`-part of the boundary of `D` with the
`β`-part of the boundary of `E`, in Sarkar's convention averaging over the four diagonal translates
of the first chain. It is computed along the `β`-arcs: at each point of `α ∩ β`, the sum of the
coefficients of `∂_β E` on the two `β`-arcs there times the change across `α` of the sum of the
multiplicities of `D` on the two sides of `β`, divided by four.
`TauCeti.HeegaardTripleRegionSystem.alphaBetaIntersection_apply_alpha` computes it along the
`α`-arcs. -/
def alphaBetaIntersection [Fintype PointAB] : (Region → ℤ) →+ (Region → ℤ) →+ ℚ :=
  crossingPairing T.betaNext T.betaLeft T.betaRight T.betaBoundary Sum.inl

/-- The intersection number `∂_β D · ∂_γ E` of the `β`-part of the boundary of `D` with the
`γ`-part of the boundary of `E`, computed along the `γ`-arcs: at each point of `β ∩ γ`, the sum of
the coefficients of `∂_γ E` on the two `γ`-arcs there times the change across `β` of the sum of
the multiplicities of `D` on the two sides of `γ`, divided by four.
`TauCeti.HeegaardTripleRegionSystem.betaGammaIntersection_apply_beta` computes it along the
`β`-arcs. -/
def betaGammaIntersection [Fintype PointBC] : (Region → ℤ) →+ (Region → ℤ) →+ ℚ :=
  crossingPairing T.gammaNext T.gammaLeft T.gammaRight T.gammaBoundary Sum.inl

/-- The intersection number `∂_γ D · ∂_α E` of the `γ`-part of the boundary of `D` with the
`α`-part of the boundary of `E`, computed along the `α`-arcs: at each point of `α ∩ γ`, the sum of
the coefficients of `∂_α E` on the two `α`-arcs there times the change across `γ` of the sum of
the multiplicities of `D` on the two sides of `α`, divided by four.
`TauCeti.HeegaardTripleRegionSystem.gammaAlphaIntersection_apply_gamma` computes it along the
`γ`-arcs. -/
def gammaAlphaIntersection [Fintype PointAC] : (Region → ℤ) →+ (Region → ℤ) →+ ℚ :=
  crossingPairing T.alphaNext T.alphaLeft T.alphaRight T.alphaBoundary Sum.inr

theorem alphaBetaIntersection_apply [Fintype PointAB] (D E : Region → ℤ) :
    T.alphaBetaIntersection D E =
      ((∑ p : PointAB, (T.betaBoundary E (T.betaNext.symm (.inl p)) + T.betaBoundary E (.inl p)) *
        (D (T.betaLeft (.inl p)) + D (T.betaRight (.inl p)) -
          (D (T.betaLeft (T.betaNext.symm (.inl p))) +
            D (T.betaRight (T.betaNext.symm (.inl p))))) : ℤ) : ℚ) / 4 :=
  (rfl)

theorem betaGammaIntersection_apply [Fintype PointBC] (D E : Region → ℤ) :
    T.betaGammaIntersection D E =
      ((∑ p : PointBC,
        (T.gammaBoundary E (T.gammaNext.symm (.inl p)) + T.gammaBoundary E (.inl p)) *
          (D (T.gammaLeft (.inl p)) + D (T.gammaRight (.inl p)) -
            (D (T.gammaLeft (T.gammaNext.symm (.inl p))) +
              D (T.gammaRight (T.gammaNext.symm (.inl p))))) : ℤ) : ℚ) / 4 :=
  (rfl)

theorem gammaAlphaIntersection_apply [Fintype PointAC] (D E : Region → ℤ) :
    T.gammaAlphaIntersection D E =
      ((∑ p : PointAC,
        (T.alphaBoundary E (T.alphaNext.symm (.inr p)) + T.alphaBoundary E (.inr p)) *
          (D (T.alphaLeft (.inr p)) + D (T.alphaRight (.inr p)) -
            (D (T.alphaLeft (T.alphaNext.symm (.inr p))) +
              D (T.alphaRight (T.alphaNext.symm (.inr p))))) : ℤ) : ℚ) / 4 :=
  (rfl)

/-- The intersection number `∂_α D · ∂_β E` computed along the `α`-arcs: it is minus the sum, over
the points of `α ∩ β`, of the coefficients of `∂_α D` on the two `α`-arcs there times the change
across `β` of the sum of the multiplicities of `E` on the two sides of `α`, divided by four. -/
theorem alphaBetaIntersection_apply_alpha [Fintype PointAB] (D E : Region → ℤ) :
    T.alphaBetaIntersection D E =
      -((∑ p : PointAB,
        (T.alphaBoundary D (T.alphaNext.symm (.inl p)) + T.alphaBoundary D (.inl p)) *
          (E (T.alphaLeft (.inl p)) + E (T.alphaRight (.inl p)) -
            (E (T.alphaLeft (T.alphaNext.symm (.inl p))) +
              E (T.alphaRight (T.alphaNext.symm (.inl p))))) : ℤ) : ℚ) / 4 := by
  rw [alphaBetaIntersection_apply, ← Int.cast_neg, ← sum_neg_distrib]
  congr 3
  exact funext fun p => by
    simp only [alphaBoundary_apply, betaBoundary_apply]
    linear_combination (T.crossing_alphaBeta p).cross_add_cross_eq_zero D E

/-- The intersection number `∂_β D · ∂_γ E` computed along the `β`-arcs: it is minus the sum, over
the points of `β ∩ γ`, of the coefficients of `∂_β D` on the two `β`-arcs there times the change
across `γ` of the sum of the multiplicities of `E` on the two sides of `β`, divided by four. -/
theorem betaGammaIntersection_apply_beta [Fintype PointBC] (D E : Region → ℤ) :
    T.betaGammaIntersection D E =
      -((∑ p : PointBC,
        (T.betaBoundary D (T.betaNext.symm (.inr p)) + T.betaBoundary D (.inr p)) *
          (E (T.betaLeft (.inr p)) + E (T.betaRight (.inr p)) -
            (E (T.betaLeft (T.betaNext.symm (.inr p))) +
              E (T.betaRight (T.betaNext.symm (.inr p))))) : ℤ) : ℚ) / 4 := by
  rw [betaGammaIntersection_apply, ← Int.cast_neg, ← sum_neg_distrib]
  congr 3
  exact funext fun p => by
    simp only [betaBoundary_apply, gammaBoundary_apply]
    linear_combination (T.crossing_betaGamma p).cross_add_cross_eq_zero D E

/-- The intersection number `∂_γ D · ∂_α E` computed along the `γ`-arcs: it is minus the sum, over
the points of `α ∩ γ`, of the coefficients of `∂_γ D` on the two `γ`-arcs there times the change
across `α` of the sum of the multiplicities of `E` on the two sides of `γ`, divided by four. -/
theorem gammaAlphaIntersection_apply_gamma [Fintype PointAC] (D E : Region → ℤ) :
    T.gammaAlphaIntersection D E =
      -((∑ p : PointAC,
        (T.gammaBoundary D (T.gammaNext.symm (.inr p)) + T.gammaBoundary D (.inr p)) *
          (E (T.gammaLeft (.inr p)) + E (T.gammaRight (.inr p)) -
            (E (T.gammaLeft (T.gammaNext.symm (.inr p))) +
              E (T.gammaRight (T.gammaNext.symm (.inr p))))) : ℤ) : ℚ) / 4 := by
  rw [gammaAlphaIntersection_apply, ← Int.cast_neg, ← sum_neg_distrib]
  congr 3
  exact funext fun p => by
    simp only [alphaBoundary_apply, gammaBoundary_apply]
    linear_combination (T.crossing_alphaGamma p).cross_add_cross_eq_zero E D

/-- Sarkar's point measure identity along `α`: pairing the boundary of `∂_α X` with the point
measures of `Y` gives `∂Y · ∂_α X = -∂_α X · ∂_β Y + ∂_γ Y · ∂_α X`. -/
private theorem sum_alphaArcBoundary_mul [Fintype PointAB] [Fintype PointAC]
    (X Y : Region → ℤ) :
    ∑ q, (T.alphaArcBoundary (T.alphaBoundary X) q : ℚ) *
        Sum.elim (T.alphaBetaPointMeasure Y) (T.alphaGammaPointMeasure Y) q =
      -T.alphaBetaIntersection X Y + T.gammaAlphaIntersection Y X := by
  rw [HeegaardRegionSystem.sum_mul_cornerSum_div_four T.alphaNext T.alphaLeft T.alphaRight X Y
      _ _
      (fun q => by simp only [alphaArcBoundary_apply, alphaBoundary_apply])
      (by rintro (p | p) <;>
        simp only [Sum.elim_inl, Sum.elim_inr, alphaBetaPointMeasure_apply,
          alphaGammaPointMeasure_apply]),
    Fintype.sum_sum_type, alphaBetaIntersection_apply_alpha, gammaAlphaIntersection_apply]
  simp only [alphaBoundary_apply]
  push_cast
  ring

/-- Sarkar's point measure identity along `β`: pairing the boundary of `∂_β X` with the point
measures of `Y` gives `∂Y · ∂_β X = ∂_α Y · ∂_β X - ∂_β X · ∂_γ Y`. -/
private theorem sum_betaArcBoundary_mul [Fintype PointAB] [Fintype PointBC]
    (X Y : Region → ℤ) :
    ∑ q, (T.betaArcBoundary (T.betaBoundary X) q : ℚ) *
        Sum.elim (T.alphaBetaPointMeasure Y) (T.betaGammaPointMeasure Y) q =
      T.alphaBetaIntersection Y X - T.betaGammaIntersection X Y := by
  rw [HeegaardRegionSystem.sum_mul_cornerSum_div_four T.betaNext T.betaLeft T.betaRight X Y
      _ _
      (fun q => by simp only [betaArcBoundary_apply, betaBoundary_apply])
      (by rintro (p | p) <;>
        simp only [Sum.elim_inl, Sum.elim_inr, alphaBetaPointMeasure_apply_beta,
          betaGammaPointMeasure_apply]),
    Fintype.sum_sum_type, alphaBetaIntersection_apply, betaGammaIntersection_apply_beta]
  simp only [betaBoundary_apply]
  push_cast
  ring

/-- Sarkar's point measure identity along `γ`: pairing the boundary of `∂_γ X` with the point
measures of `Y` gives `∂Y · ∂_γ X = ∂_β Y · ∂_γ X - ∂_γ X · ∂_α Y`. -/
private theorem sum_gammaArcBoundary_mul [Fintype PointBC] [Fintype PointAC]
    (X Y : Region → ℤ) :
    ∑ q, (T.gammaArcBoundary (T.gammaBoundary X) q : ℚ) *
        Sum.elim (T.betaGammaPointMeasure Y) (T.alphaGammaPointMeasure Y) q =
      T.betaGammaIntersection Y X - T.gammaAlphaIntersection X Y := by
  rw [HeegaardRegionSystem.sum_mul_cornerSum_div_four T.gammaNext T.gammaLeft T.gammaRight X Y
      _ _
      (fun q => by simp only [gammaArcBoundary_apply, gammaBoundary_apply])
      (by rintro (p | p) <;>
        simp only [Sum.elim_inl, Sum.elim_inr, betaGammaPointMeasure_apply_gamma,
          alphaGammaPointMeasure_apply_gamma]),
    Fintype.sum_sum_type, betaGammaIntersection_apply, gammaAlphaIntersection_apply_gamma]
  simp only [gammaBoundary_apply]
  push_cast
  ring

variable {T} in
/-- Sarkar's point measure identity along the `α`-edge of a triangle domain: the boundary of the
`α`-part of `∂D` runs from `x` to `w`, so for every domain `Y`,
`n_w(Y) - n_x(Y) = ∂Y · ∂_α D = -∂_α D · ∂_β Y + ∂_γ Y · ∂_α D`. -/
theorem IsTriangleDomain.alphaGammaGeneratorPointMeasure_sub [Fintype PointAB] [Fintype PointAC]
    {x : T.alphaBeta.Generator} {y : T.betaGamma.Generator} {w : T.alphaGamma.Generator}
    {D : Region → ℤ} (hD : T.IsTriangleDomain x y w D) (Y : Region → ℤ) :
    T.alphaGammaGeneratorPointMeasure w Y - T.alphaBetaGeneratorPointMeasure x Y =
      -T.alphaBetaIntersection D Y + T.gammaAlphaIntersection Y D := by
  rw [← T.sum_alphaArcBoundary_mul D Y, (isTriangleDomain_iff.mp hD).1, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Int.cast_neg, neg_mul, sum_neg_distrib,
    HeegaardIntersectionSystem.sum_generatorChain_mul, alphaBetaGeneratorPointMeasure_apply,
    alphaGammaGeneratorPointMeasure_apply]
  ring

variable {T} in
/-- Sarkar's point measure identity along the `β`-edge of a triangle domain: the boundary of the
`β`-part of `∂D` runs from `y` to `x`, so for every domain `Y`,
`n_x(Y) - n_y(Y) = ∂Y · ∂_β D = ∂_α Y · ∂_β D - ∂_β D · ∂_γ Y`. -/
theorem IsTriangleDomain.alphaBetaGeneratorPointMeasure_sub [Fintype PointAB] [Fintype PointBC]
    {x : T.alphaBeta.Generator} {y : T.betaGamma.Generator} {w : T.alphaGamma.Generator}
    {D : Region → ℤ} (hD : T.IsTriangleDomain x y w D) (Y : Region → ℤ) :
    T.alphaBetaGeneratorPointMeasure x Y - T.betaGammaGeneratorPointMeasure y Y =
      T.alphaBetaIntersection Y D - T.betaGammaIntersection D Y := by
  rw [← T.sum_betaArcBoundary_mul D Y, (isTriangleDomain_iff.mp hD).2.1, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Int.cast_neg, neg_mul, sum_neg_distrib,
    HeegaardIntersectionSystem.sum_generatorChain_mul, alphaBetaGeneratorPointMeasure_apply,
    betaGammaGeneratorPointMeasure_apply]
  ring

variable {T} in
/-- Sarkar's point measure identity along the `γ`-edge of a triangle domain: the boundary of the
`γ`-part of `∂D` runs from `w` to `y`, so for every domain `Y`,
`n_y(Y) - n_w(Y) = ∂Y · ∂_γ D = ∂_β Y · ∂_γ D - ∂_γ D · ∂_α Y`. -/
theorem IsTriangleDomain.betaGammaGeneratorPointMeasure_sub [Fintype PointBC] [Fintype PointAC]
    {x : T.alphaBeta.Generator} {y : T.betaGamma.Generator} {w : T.alphaGamma.Generator}
    {D : Region → ℤ} (hD : T.IsTriangleDomain x y w D) (Y : Region → ℤ) :
    T.betaGammaGeneratorPointMeasure y Y - T.alphaGammaGeneratorPointMeasure w Y =
      T.betaGammaIntersection Y D - T.gammaAlphaIntersection D Y := by
  rw [← T.sum_gammaArcBoundary_mul D Y, (isTriangleDomain_iff.mp hD).2.2, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Int.cast_neg, neg_mul, sum_neg_distrib,
    HeegaardIntersectionSystem.sum_generatorChain_mul, betaGammaGeneratorPointMeasure_apply,
    alphaGammaGeneratorPointMeasure_apply]
  ring

variable {T} in
/-- Sarkar's point measure identity for a disk domain `D` from `x` to `x'` in `(Σ, α, β)`: the
boundary of the `β`-part of `∂D` runs from `x'` to `x`, so for every domain `Y`,
`n_x(Y) - n_{x'}(Y) = ∂Y · ∂_β D = ∂_α Y · ∂_β D - ∂_β D · ∂_γ Y`. -/
theorem IsAlphaBetaDomainBetween.alphaBetaGeneratorPointMeasure_sub [Fintype PointAB]
    [Fintype PointBC] {x x' : T.alphaBeta.Generator} {D : Region → ℤ}
    (hD : T.IsAlphaBetaDomainBetween x x' D) (Y : Region → ℤ) :
    T.alphaBetaGeneratorPointMeasure x Y - T.alphaBetaGeneratorPointMeasure x' Y =
      T.alphaBetaIntersection Y D - T.betaGammaIntersection D Y := by
  rw [← T.sum_betaArcBoundary_mul D Y, (isAlphaBetaDomainBetween_iff.mp hD).2.1,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, Pi.zero_apply, Int.cast_sub,
    Int.cast_zero, sub_mul, zero_mul, sum_sub_distrib, sum_const_zero, add_zero,
    HeegaardIntersectionSystem.sum_generatorChain_mul, alphaBetaGeneratorPointMeasure_apply]

variable {T} in
/-- Sarkar's point measure identity for a disk domain `D` from `y` to `y'` in `(Σ, β, γ)`: the
boundary of the `β`-part of `∂D` runs from `y` to `y'`, so for every domain `Y`,
`n_{y'}(Y) - n_y(Y) = ∂Y · ∂_β D = ∂_α Y · ∂_β D - ∂_β D · ∂_γ Y`. -/
theorem IsBetaGammaDomainBetween.betaGammaGeneratorPointMeasure_sub [Fintype PointAB]
    [Fintype PointBC] {y y' : T.betaGamma.Generator} {D : Region → ℤ}
    (hD : T.IsBetaGammaDomainBetween y y' D) (Y : Region → ℤ) :
    T.betaGammaGeneratorPointMeasure y' Y - T.betaGammaGeneratorPointMeasure y Y =
      T.alphaBetaIntersection Y D - T.betaGammaIntersection D Y := by
  rw [← T.sum_betaArcBoundary_mul D Y, (isBetaGammaDomainBetween_iff.mp hD).2.1,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, Pi.zero_apply, Int.cast_sub,
    Int.cast_zero, sub_mul, zero_mul, sum_sub_distrib, sum_const_zero, zero_add,
    HeegaardIntersectionSystem.sum_generatorChain_mul, betaGammaGeneratorPointMeasure_apply]

variable {T} in
/-- Sarkar's point measure identity for a disk domain `D` from `w` to `w'` in `(Σ, α, γ)`: the
boundary of the `γ`-part of `∂D` runs from `w'` to `w`, so for every domain `Y`,
`n_w(Y) - n_{w'}(Y) = ∂Y · ∂_γ D = ∂_β Y · ∂_γ D - ∂_γ D · ∂_α Y`. -/
theorem IsAlphaGammaDomainBetween.alphaGammaGeneratorPointMeasure_sub [Fintype PointBC]
    [Fintype PointAC] {w w' : T.alphaGamma.Generator} {D : Region → ℤ}
    (hD : T.IsAlphaGammaDomainBetween w w' D) (Y : Region → ℤ) :
    T.alphaGammaGeneratorPointMeasure w Y - T.alphaGammaGeneratorPointMeasure w' Y =
      T.betaGammaIntersection Y D - T.gammaAlphaIntersection D Y := by
  rw [← T.sum_gammaArcBoundary_mul D Y, (isAlphaGammaDomainBetween_iff.mp hD).2.2,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, Pi.zero_apply, Int.cast_sub,
    Int.cast_zero, sub_mul, zero_mul, sum_sub_distrib, sum_const_zero, zero_add,
    HeegaardIntersectionSystem.sum_generatorChain_mul, alphaGammaGeneratorPointMeasure_apply]

end Intersection

section MaslovIndex

variable [Fintype PointAB] [Fintype PointBC] [Fintype PointAC] [Fintype Region]

/-- The Euler measure `e(D) = ∑ χ(R) D(R) - ∑ₚ n_p(D)` of a domain, the second sum running over
the intersection points of all three kinds, where `χ(R)` is the Euler characteristic of the region
`R`, supplied as `χ`. Each of the four corners at a point contributes a quarter of the multiplicity
of its region to the point measure there, so this is `∑ D(R) (χ(R) - k(R) / 4)`, where `k(R)` is
the number of corners of `R`. -/
def eulerMeasure (χ : Region → ℤ) : (Region → ℤ) →+ ℚ where
  toFun D := ∑ r, (χ r : ℚ) * D r - ∑ p, T.alphaBetaPointMeasure D p -
    ∑ p, T.betaGammaPointMeasure D p - ∑ p, T.alphaGammaPointMeasure D p
  map_zero' := by simp
  map_add' D E := by
    simp only [map_add, Pi.add_apply, Int.cast_add, mul_add, sum_add_distrib]
    ring

@[simp]
theorem eulerMeasure_apply (χ : Region → ℤ) (D : Region → ℤ) :
    T.eulerMeasure χ D = ∑ r, (χ r : ℚ) * D r - ∑ p, T.alphaBetaPointMeasure D p -
      ∑ p, T.betaGammaPointMeasure D p - ∑ p, T.alphaGammaPointMeasure D p :=
  (rfl)

/-- The Euler measure of the whole surface is `∑ χ(R) - #(α ∩ β) - #(β ∩ γ) - #(α ∩ γ)`, the
Euler characteristic of the surface assembled from the regions, the arcs and the intersection
points. -/
theorem eulerMeasure_one (χ : Region → ℤ) :
    T.eulerMeasure χ 1 = ∑ r, (χ r : ℚ) - Fintype.card PointAB - Fintype.card PointBC -
      Fintype.card PointAC := by
  simp [eulerMeasure_apply]

/-- Sarkar's Maslov index `μ(D) = e(D) + n_x(D) + n_w(D) + ∂_β D · ∂_γ D - n / 2` of a domain `D`
of a triangle with corners `x ∈ T_α ∩ T_β`, `y ∈ T_β ∩ T_γ` and `w ∈ T_α ∩ T_γ`, for the Euler
characteristics `χ` of the regions. The corner `y` enters only through the corner conditions on
`D`; `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain.maslovIndex_eq_alphaBetaIntersection`
and `TauCeti.HeegaardTripleRegionSystem.IsTriangleDomain.maslovIndex_eq_gammaAlphaIntersection`
give the forms in which `y` appears. -/
def maslovIndex (χ : Region → ℤ) (x : T.alphaBeta.Generator) (w : T.alphaGamma.Generator)
    (D : Region → ℤ) : ℚ :=
  T.eulerMeasure χ D + T.alphaBetaGeneratorPointMeasure x D +
    T.alphaGammaGeneratorPointMeasure w D + T.betaGammaIntersection D D - n / 2

@[simp]
theorem maslovIndex_apply (χ : Region → ℤ) (x : T.alphaBeta.Generator)
    (w : T.alphaGamma.Generator) (D : Region → ℤ) :
    T.maslovIndex χ x w D = T.eulerMeasure χ D + T.alphaBetaGeneratorPointMeasure x D +
      T.alphaGammaGeneratorPointMeasure w D + T.betaGammaIntersection D D - n / 2 :=
  (rfl)

variable {T} {x x' : T.alphaBeta.Generator} {y y' : T.betaGamma.Generator}
  {w w' : T.alphaGamma.Generator} {D E : Region → ℤ}

/-- Cyclic symmetry of Sarkar's formula: for a triangle domain,
`μ(D) = e(D) + n_w(D) + n_y(D) + ∂_α D · ∂_β D - n / 2`. -/
theorem IsTriangleDomain.maslovIndex_eq_alphaBetaIntersection (χ : Region → ℤ)
    (hD : T.IsTriangleDomain x y w D) :
    T.maslovIndex χ x w D = T.eulerMeasure χ D + T.alphaGammaGeneratorPointMeasure w D +
      T.betaGammaGeneratorPointMeasure y D + T.alphaBetaIntersection D D - n / 2 := by
  have := hD.alphaBetaGeneratorPointMeasure_sub D
  rw [maslovIndex_apply]
  linarith

/-- Cyclic symmetry of Sarkar's formula: for a triangle domain,
`μ(D) = e(D) + n_y(D) + n_x(D) + ∂_γ D · ∂_α D - n / 2`. -/
theorem IsTriangleDomain.maslovIndex_eq_gammaAlphaIntersection (χ : Region → ℤ)
    (hD : T.IsTriangleDomain x y w D) :
    T.maslovIndex χ x w D = T.eulerMeasure χ D + T.betaGammaGeneratorPointMeasure y D +
      T.alphaBetaGeneratorPointMeasure x D + T.gammaAlphaIntersection D D - n / 2 := by
  have := hD.betaGammaGeneratorPointMeasure_sub D
  rw [maslovIndex_apply]
  linarith

/-- Additivity at the corner `x`: juxtaposing a disk domain `D` from `x` to `x'` in `(Σ, α, β)` with
a triangle domain `E` at the corner `x'` adds the Lipshitz index `e(D) + n_x(D) + n_{x'}(D)` of
`D` to the Maslov index. -/
theorem IsAlphaBetaDomainBetween.maslovIndex_add (χ : Region → ℤ)
    (hD : T.IsAlphaBetaDomainBetween x x' D) (hE : T.IsTriangleDomain x' y w E) :
    T.maslovIndex χ x w (D + E) =
      T.eulerMeasure χ D + T.alphaBetaGeneratorPointMeasure x D +
        T.alphaBetaGeneratorPointMeasure x' D + T.maslovIndex χ x' w E := by
  obtain ⟨-, -, hDγ⟩ := isAlphaBetaDomainBetween_iff.mp hD
  have hβ := hD.alphaBetaGeneratorPointMeasure_sub E
  have hα := hE.alphaGammaGeneratorPointMeasure_sub D
  -- `D` has no `γ`-boundary, so its intersection numbers with `γ`-parts vanish.
  have h₁ : T.gammaAlphaIntersection D E = 0 := by
    rw [gammaAlphaIntersection_apply_gamma, hDγ]; simp
  have h₂ : ∀ X, T.betaGammaIntersection X D = 0 := fun X => by
    rw [betaGammaIntersection_apply, hDγ]; simp
  simp only [maslovIndex_apply, map_add, AddMonoidHom.add_apply, h₂]
  linarith

/-- Additivity at the corner `y`: juxtaposing a disk domain `D` from `y` to `y'` in `(Σ, β, γ)` with
a triangle domain `E` at the corner `y'` adds the Lipshitz index `e(D) + n_y(D) + n_{y'}(D)` of
`D` to the Maslov index. -/
theorem IsBetaGammaDomainBetween.maslovIndex_add (χ : Region → ℤ)
    (hD : T.IsBetaGammaDomainBetween y y' D) (hE : T.IsTriangleDomain x y' w E) :
    T.maslovIndex χ x w (D + E) =
      T.eulerMeasure χ D + T.betaGammaGeneratorPointMeasure y D +
        T.betaGammaGeneratorPointMeasure y' D + T.maslovIndex χ x w E := by
  obtain ⟨hDα, -, -⟩ := isBetaGammaDomainBetween_iff.mp hD
  have hβ := hD.betaGammaGeneratorPointMeasure_sub D
  have hEβ := hE.alphaBetaGeneratorPointMeasure_sub D
  have hEγ := hE.betaGammaGeneratorPointMeasure_sub D
  -- `D` has no `α`-boundary, so its intersection numbers with `α`-parts vanish.
  have h₁ : ∀ X, T.alphaBetaIntersection D X = 0 := fun X => by
    rw [alphaBetaIntersection_apply_alpha, hDα]; simp
  have h₂ : T.gammaAlphaIntersection E D = 0 := by rw [gammaAlphaIntersection_apply, hDα]; simp
  simp only [maslovIndex_apply, map_add, AddMonoidHom.add_apply]
  rw [h₁] at hβ hEβ
  linarith

/-- Additivity at the corner `w`: juxtaposing a triangle domain `E` at the corner `w` with a disk
domain `D` from `w` to `w'` in `(Σ, α, γ)` adds the Lipshitz index `e(D) + n_w(D) + n_{w'}(D)` of
`D` to the Maslov index. -/
theorem IsTriangleDomain.maslovIndex_add (χ : Region → ℤ) (hE : T.IsTriangleDomain x y w E)
    (hD : T.IsAlphaGammaDomainBetween w w' D) :
    T.maslovIndex χ x w' (E + D) =
      T.maslovIndex χ x w E + (T.eulerMeasure χ D + T.alphaGammaGeneratorPointMeasure w D +
        T.alphaGammaGeneratorPointMeasure w' D) := by
  obtain ⟨-, hDβ, -⟩ := isAlphaGammaDomainBetween_iff.mp hD
  have hγ := hD.alphaGammaGeneratorPointMeasure_sub E
  have hEα := hE.alphaGammaGeneratorPointMeasure_sub D
  -- `D` has no `β`-boundary, so its intersection numbers with `β`-parts vanish.
  have h₁ : T.alphaBetaIntersection E D = 0 := by rw [alphaBetaIntersection_apply, hDβ]; simp
  have h₂ : ∀ X, T.betaGammaIntersection D X = 0 := fun X => by
    rw [betaGammaIntersection_apply_beta, hDβ]; simp
  simp only [maslovIndex_apply, map_add, AddMonoidHom.add_apply, h₂]
  linarith

/-- Adding the whole surface to a triangle domain adds two to its Maslov index, when the region
Euler characteristics are those of a closed surface of genus `n`, that is
`∑ χ(R) - #(α ∩ β) - #(β ∩ γ) - #(α ∩ γ) = 2 - 2n`. -/
theorem IsTriangleDomain.maslovIndex_one_add {χ : Region → ℤ}
    (hχ : ∑ r, χ r - Fintype.card PointAB - Fintype.card PointBC - Fintype.card PointAC =
      2 - 2 * (n : ℤ))
    (hE : T.IsTriangleDomain x y w E) :
    T.maslovIndex χ x w (1 + E) = T.maslovIndex χ x w E + 2 := by
  have hχ' : ∑ r, (χ r : ℚ) - Fintype.card PointAB - Fintype.card PointBC -
      Fintype.card PointAC = 2 - 2 * n := by exact_mod_cast hχ
  rw [(isAlphaBetaDomainBetween_one x).maslovIndex_add χ hE, eulerMeasure_one,
    alphaBetaGeneratorPointMeasure_one]
  linarith

end MaslovIndex

end HeegaardTripleRegionSystem

end TauCeti
