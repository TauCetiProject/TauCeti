/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Triple.MaslovIndex
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# The triple diagram of three lines on the torus

On the torus `ℝ² / ℤ²` let `α` be the line `y = 0` oriented by increasing `x`, `β` the line
`x = 0` oriented by increasing `y`, and `γ` the line `x + y = 1 / 2` oriented from `(1 / 2, 0)`
towards `(0, 1 / 2)`. The three lines meet pairwise once: `α ∩ β = {(0, 0)}`,
`β ∩ γ = {(0, 1 / 2)}` and `α ∩ γ = {(1 / 2, 0)}`. They cut the torus into three discs: the
triangle `Δ` with these three vertices, the triangle `Δ'` with vertices `(1 / 2, 1)`, `(1, 1)` and
`(1, 1 / 2)`, and a hexagon. Each line carries two intersection points, so each curve is cut into
two arcs.

`TauCeti.HeegaardTripleRegionSystem.torusTriple` records this incidence data, with the regions
`Δ`, `Δ'` and the hexagon labelled `0`, `1` and `2`, and the basepoint in the hexagon. The
boundary of `Δ`, oriented with `Δ` on its left, runs along `α` from `(0, 0)` to `(1 / 2, 0)`, along
`γ` to `(0, 1 / 2)` and along `β` back to `(0, 0)`, so `Δ` is a triangle domain. It is the
standard small triangle of a holomorphic triangle map, and Sarkar's formula gives it Maslov index
zero (`TauCeti.HeegaardTripleRegionSystem.maslovIndex_torusTriple_single_zero`): its Euler measure
is `1 - 3 / 4 = 1 / 4`, its point measures at the corners `(0, 0)` and `(1 / 2, 0)` are `1 / 4`
each, the intersection number `∂_β Δ · ∂_γ Δ` is `-1 / 4`, and `n / 2 = 1 / 2`. Adding the whole
torus gives Maslov index two. As for the other region systems, the identification of the labels
with the complementary regions of the three lines is geometric and is not formalized here.

## Main definitions

* `TauCeti.HeegaardTripleRegionSystem.torusTriple`: the incidence data of the three lines.

## Main results

* `TauCeti.HeegaardTripleRegionSystem.isTriangleDomain_torusTriple_single_zero`: the triangle `Δ`
  is a triangle domain.
* `TauCeti.HeegaardTripleRegionSystem.maslovIndex_torusTriple_single_zero`: it has Maslov index
  zero.
* `TauCeti.HeegaardTripleRegionSystem.maslovIndex_torusTriple_one_add_single_zero`: together with
  the whole torus it has Maslov index two.

## References

* S. Sarkar, *Maslov index formulas for Whitney n-gons*, J. Symplectic Geom. **9** (2011),
  [arXiv:math/0609673](https://arxiv.org/abs/math/0609673), Theorem 3.5: a domain of a triangle
  that is a disjoint union of small triangles has Maslov index zero.
-/

public section

namespace TauCeti

namespace HeegaardTripleRegionSystem

/-- The intersection data of two closed curves meeting once. -/
def torusIntersection : HeegaardIntersectionSystem 1 Unit where
  pointFintype := inferInstance
  alpha _ := 0
  beta _ := 0

/-- The incidence data of the three lines `y = 0`, `x = 0` and `x + y = 1 / 2` on the torus, with
the triangle with vertices `(0, 0)`, `(1 / 2, 0)`, `(0, 1 / 2)` labelled `0`, the triangle with
vertices `(1 / 2, 1)`, `(1, 1)`, `(1, 1 / 2)` labelled `1`, the hexagon labelled `2` and the
basepoint in the hexagon. On each curve the two points are `Sum.inl ()` and `Sum.inr ()`: on `α`
the points `(0, 0)` and `(1 / 2, 0)`, on `β` the points `(0, 0)` and `(0, 1 / 2)`, on `γ` the
points `(0, 1 / 2)` and `(1 / 2, 0)`. -/
def torusTriple : HeegaardTripleRegionSystem 1 Unit Unit Unit (Fin 3) Unit where
  alphaBeta := torusIntersection
  betaGamma := torusIntersection
  alphaGamma := torusIntersection
  alphaNext := Equiv.swap (.inl ()) (.inr ())
  alphaNext_isCycleOn := isCycleOn_swap_fiber (by rintro (⟨⟩ | ⟨⟩) <;> simp) _
  betaNext := Equiv.swap (.inl ()) (.inr ())
  betaNext_isCycleOn := isCycleOn_swap_fiber (by rintro (⟨⟩ | ⟨⟩) <;> simp) _
  gammaNext := Equiv.swap (.inl ()) (.inr ())
  gammaNext_isCycleOn := isCycleOn_swap_fiber (by rintro (⟨⟩ | ⟨⟩) <;> simp) _
  alphaLeft := Sum.elim (fun _ => 0) (fun _ => 2)
  alphaRight := Sum.elim (fun _ => 2) (fun _ => 1)
  betaLeft := Sum.elim (fun _ => 2) (fun _ => 1)
  betaRight := Sum.elim (fun _ => 0) (fun _ => 2)
  gammaLeft := Sum.elim (fun _ => 2) (fun _ => 0)
  gammaRight := Sum.elim (fun _ => 1) (fun _ => 2)
  crossing_alphaBeta := by simp only [HeegaardRegionSystem.isCrossingCompatible_iff]; decide
  crossing_betaGamma := by simp only [HeegaardRegionSystem.isCrossingCompatible_iff]; decide
  crossing_alphaGamma := by simp only [HeegaardRegionSystem.isCrossingCompatible_iff]; decide
  basepoint _ := 2

/-- Every intersection point is the unique point of every generator of a curve meeting another
once. -/
private theorem torusIntersection_generatorChain (g : torusIntersection.Generator) :
    torusIntersection.generatorChain g = 1 := by
  classical
  ext q
  simp [HeegaardIntersectionSystem.generatorChain_apply]

/-- The triangle with vertices `(0, 0)`, `(1 / 2, 0)` and `(0, 1 / 2)` is a triangle domain. -/
theorem isTriangleDomain_torusTriple_single_zero (x : torusTriple.alphaBeta.Generator)
    (y : torusTriple.betaGamma.Generator) (w : torusTriple.alphaGamma.Generator) :
    torusTriple.IsTriangleDomain x y w (Pi.single 0 1) := by
  refine isTriangleDomain_iff.mpr ⟨?_, ?_, ?_⟩ <;>
  · ext (⟨⟩ | ⟨⟩) <;>
      simp [torusTriple, torusIntersection_generatorChain x, torusIntersection_generatorChain y,
        torusIntersection_generatorChain w]

/-- The small triangle with vertices `(0, 0)`, `(1 / 2, 0)` and `(0, 1 / 2)` has Maslov index zero,
all three regions being discs. -/
theorem maslovIndex_torusTriple_single_zero (x : torusTriple.alphaBeta.Generator)
    (w : torusTriple.alphaGamma.Generator) :
    torusTriple.maslovIndex 1 x w (Pi.single 0 1) = 0 := by
  rw [maslovIndex_apply, eulerMeasure_apply, alphaBetaGeneratorPointMeasure_apply,
    alphaGammaGeneratorPointMeasure_apply, betaGammaIntersection_apply]
  simp only [Fintype.sum_unique, PUnit.default_eq_unit,
    alphaBetaPointMeasure_apply, betaGammaPointMeasure_apply, alphaGammaPointMeasure_apply,
    gammaBoundary_apply]
  norm_num [torusTriple, Pi.single_apply]

/-- The small triangle together with the whole torus has Maslov index two. -/
theorem maslovIndex_torusTriple_one_add_single_zero (x : torusTriple.alphaBeta.Generator)
    (y : torusTriple.betaGamma.Generator) (w : torusTriple.alphaGamma.Generator) :
    torusTriple.maslovIndex 1 x w (1 + Pi.single 0 1) = 2 := by
  rw [(isTriangleDomain_torusTriple_single_zero x y w).maslovIndex_one_add (by simp),
    maslovIndex_torusTriple_single_zero, zero_add]

end HeegaardTripleRegionSystem

end TauCeti
