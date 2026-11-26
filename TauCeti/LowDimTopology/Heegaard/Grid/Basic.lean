/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.MarkingCount
public import TauCeti.LowDimTopology.Heegaard.HatDifferential
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.GroupTheory.Perm.ProdCongr
import TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# The multi-pointed Heegaard diagram of a grid diagram

An `n × n` grid diagram `G` on the torus `ℝ² / ℤ²` is a Heegaard diagram of genus one with `n`
`α`-curves, the horizontal grid circles, `n` `β`-curves, the vertical grid circles, and `2n`
basepoints, the `O`-markings (the `w` basepoints) and the `X`-markings (the `z` basepoints). This
file records it as abstract region incidence data, `TauCeti.GridDiagram.heegaardRegionSystem`,
and compares the Heegaard Floer notions of `TauCeti.HeegaardRegionSystem` with the combinatorial
notions of grid homology.

The intersection points and the regions are both indexed by `Fin n × Fin n`: the point `(c, r)`
is where the vertical circle `c` meets the horizontal circle `r`, and the region `(c, r)` is the
square whose lower-left corner is that point, the convention of `TauCeti.GridDiagram.OSet` and
`TauCeti.GridRectangle.coveredSquares`. The horizontal circles are oriented to the right and the
vertical circles upwards, so the square above the arc of the horizontal circle starting at
`(c, r)` is on its left and the square to the right of the arc of the vertical circle starting at
`(c, r)` is on its right. Every region is a square, a disk with a corner at each of the four grid
points around it. With Euler characteristic `1` for every region the four quarter corners cancel
it, and the Euler measure of every domain is `0`
(`TauCeti.GridDiagram.heegaardRegionSystem_eulerMeasure_const_one_eq_zero`).

* **Generators.** A generator, one intersection point on each horizontal and each vertical
  circle, is a grid state (`TauCeti.GridDiagram.gridStateEquivGenerator`).
* **Rectangles.** The domain of a toroidal rectangle (`TauCeti.GridRectangle.domain`) has
  multiplicity one on the squares it covers, and distinct rectangles from `x` to `y` have
  distinct domains (`TauCeti.GridRectangleBetween.toGridRectangle_domain_injective`). Its
  boundary turns at the four corners of the rectangle, so the domain of an oriented rectangle
  from `x` to `y` is a domain from `x` to `y` (`TauCeti.GridDiagram.isDomainBetween_domain`).
  Across a horizontal or vertical circle its multiplicity jumps only at the sides of the
  rectangle (`TauCeti.GridDiagram.alphaBoundary_domain`,
  `TauCeti.GridDiagram.betaBoundary_domain`).
* **Maslov index.** The point measure of a rectangle is `1` at an interior grid point, `1 / 2` on
  a side and `1 / 4` at a corner. Lipshitz's formula therefore gives the domain of a rectangle
  from `x` to `y` the Maslov index `1 + 2 #(x ∩ Int(r))`
  (`TauCeti.GridDiagram.maslovIndex_domain`), which is `1` exactly when the rectangle is empty
  (`TauCeti.GridDiagram.maslovIndex_domain_eq_one_iff`).
* **Gradings.** The basepoint multiplicities of a rectangle are its numbers of `O`- and
  `X`-markings (`TauCeti.GridDiagram.sum_domain_basepoint_inl`,
  `TauCeti.GridDiagram.sum_domain_basepoint_inr`). With the grading formulas of
  `TauCeti.KnotTheory.Grid.Grading.MarkingCount`, the Heegaard Floer gradings
  `μ(D) - 2 n_O(D)`, `μ(D) - 2 n_X(D)` and `n_X(D) - n_O(D)` of a rectangle from `x` to `y` are the
  differences `M_O(x) - M_O(y)`, `M_X(x) - M_X(y)` and `A(x) - A(y)` of the grid gradings
  (`TauCeti.GridDiagram.maslovIndex_domain_sub_two_mul_sum_basepoint_inl`,
  `TauCeti.GridDiagram.maslovIndex_domain_sub_two_mul_sum_basepoint_inr`,
  `TauCeti.GridDiagram.sum_domain_basepoint_inr_sub_sum_domain_basepoint_inl`).
* **The hat differential.** The domain of an empty rectangle which covers no marking, a
  rectangle counted by the fully blocked grid complex, is one of the domains counted by the hat
  differential of the multi-pointed diagram (`TauCeti.GridDiagram.domain_mem_hatDomains`).

The converse, that every nonnegative domain of Maslov index one is the domain of an empty
rectangle, is `TauCeti.GridDiagram.exists_gridRectangleBetween_isEmpty_domain_eq` in
`TauCeti.LowDimTopology.Heegaard.Grid.HatDifferential`. The grading formulas hold for every
domain, not only for rectangles, by `TauCeti.LowDimTopology.Heegaard.Grid.Grading`.

## References

* C. Manolescu, P. Ozsváth and S. Sarkar, *A combinatorial description of knot Floer homology*,
  Ann. of Math. **169** (2009), [arXiv:math/0607691](https://arxiv.org/abs/math/0607691), where
  a grid diagram is viewed as a multi-pointed Heegaard diagram of `S³` and its index-one domains
  are identified with empty rectangles.
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Grid Homology for Knots and Links*, Mathematical
  Surveys and Monographs **208**, AMS, 2015, Chapter 4, for rectangles and the grid gradings.
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), §4, for the index formula.
-/

public section

namespace TauCeti

open Finset

variable {n : ℕ}

namespace GridRectangle

/-- The domain of a toroidal rectangle: multiplicity one on each square it covers and zero on
every other square. -/
noncomputable def domain (R : GridRectangle n) : Fin n × Fin n → ℤ :=
  Set.indicator R.coveredSquares 1

@[simp]
theorem domain_apply (R : GridRectangle n) (q : Fin n × Fin n) :
    R.domain q = if q ∈ R.coveredSquares then 1 else 0 := by
  simp only [domain, Set.indicator_apply, Finset.mem_coe, Pi.one_apply]

/-- The domain of a rectangle is the product of the indicators of its covered columns and of its
covered rows. -/
theorem domain_apply_mk (R : GridRectangle n) (c r : Fin n) :
    R.domain (c, r) =
      (if c ∈ Grid.cIco R.left R.right then 1 else 0) *
        if r ∈ Grid.cIco R.bottom R.top then 1 else 0 := by
  simp only [domain_apply, mem_coveredSquares, mem_coveredColumns, mem_coveredRows]
  split_ifs <;> simp_all

/-- The domain of a rectangle is nonnegative. -/
theorem domain_nonneg (R : GridRectangle n) : 0 ≤ R.domain :=
  Set.indicator_nonneg fun _ _ => zero_le_one

end GridRectangle

namespace GridRectangleBetween

variable {x y : GridState n}

/-- **Distinct rectangles from `x` to `y` have distinct domains.** The two rectangles from `x` to
`y` with the same side columns cover the complementary arcs of columns. -/
theorem toGridRectangle_domain_injective :
    Function.Injective fun R : GridRectangleBetween x y => R.toGridRectangle.domain := by
  intro R S h
  rcases R.eq_or_eq_swapSides S with rfl | rfl
  · rfl
  -- The square at the lower-left corner of `R` is covered by `R` and not by `R.swapSides`.
  have h₁ := congrFun h (R.left, R.bottom)
  simp only [GridRectangle.domain_apply_mk, GridRectangleBetween.swapSides_toGridRectangle,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    Grid.left_mem_cIco R.left_ne_right, Grid.left_mem_cIco R.bottom_ne_top,
    Grid.right_notMem_cIco, ite_true, ite_false, one_mul, zero_mul] at h₁
  exact absurd h₁ one_ne_zero


end GridRectangleBetween

namespace GridDiagram

section RegionSystem

variable [NeZero n] (G : GridDiagram n)

/-- The multi-pointed genus-one Heegaard diagram of a grid diagram, as region incidence data. The
`α`-curves are the horizontal grid circles, oriented to the right, and the `β`-curves the
vertical grid circles, oriented upwards. The intersection point `(c, r)` lies on the vertical
circle `c` and the horizontal circle `r`, and the region `(c, r)` is the square whose lower-left
corner is that point. The basepoints `Sum.inl c` and `Sum.inr c` are the `O`- and `X`-markings in
the column of squares `c`. -/
def heegaardRegionSystem :
    HeegaardRegionSystem n (Fin n × Fin n) (Fin n × Fin n) (Fin n ⊕ Fin n) where
  pointFintype := inferInstance
  alpha p := p.2
  beta p := p.1
  alphaNext := Equiv.prodCongrLeft fun _ => finRotate n
  alphaNext_isCycleOn i := by
    convert isCycleOn_finRotate.prodCongrLeft (σ := fun _ => finRotate n) (b := i) using 1
    ext p
    simp
  betaNext := Equiv.prodCongrRight fun _ => finRotate n
  betaNext_isCycleOn j := by
    convert isCycleOn_finRotate.prodCongrRight (τ := fun _ => finRotate n) (a := j) using 1
    ext p
    simp
  alphaLeft p := p
  alphaRight p := (p.1, (finRotate n).symm p.2)
  betaLeft p := ((finRotate n).symm p.1, p.2)
  betaRight p := p
  regionNonempty := inferInstance
  crossingCompatible _ :=
    HeegaardRegionSystem.isCrossingCompatible_iff.mpr <| Or.inl ⟨rfl, rfl, rfl, rfl⟩
  regionCovered r := Or.inl ⟨r, Or.inl rfl⟩
  basepoint := Sum.elim (fun c => (c, G.O c)) fun c => (c, G.X c)

@[simp]
theorem heegaardRegionSystem_alpha (p : Fin n × Fin n) : G.heegaardRegionSystem.alpha p = p.2 :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_beta (p : Fin n × Fin n) : G.heegaardRegionSystem.beta p = p.1 :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_alphaNext_apply (p : Fin n × Fin n) :
    G.heegaardRegionSystem.alphaNext p = (finRotate n p.1, p.2) :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_alphaNext_symm_apply (p : Fin n × Fin n) :
    G.heegaardRegionSystem.alphaNext.symm p = ((finRotate n).symm p.1, p.2) :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_betaNext_apply (p : Fin n × Fin n) :
    G.heegaardRegionSystem.betaNext p = (p.1, finRotate n p.2) :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_betaNext_symm_apply (p : Fin n × Fin n) :
    G.heegaardRegionSystem.betaNext.symm p = (p.1, (finRotate n).symm p.2) :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_alphaLeft (p : Fin n × Fin n) :
    G.heegaardRegionSystem.alphaLeft p = p :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_alphaRight (p : Fin n × Fin n) :
    G.heegaardRegionSystem.alphaRight p = (p.1, (finRotate n).symm p.2) :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_betaLeft (p : Fin n × Fin n) :
    G.heegaardRegionSystem.betaLeft p = ((finRotate n).symm p.1, p.2) :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_betaRight (p : Fin n × Fin n) :
    G.heegaardRegionSystem.betaRight p = p :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_basepoint_inl (c : Fin n) :
    G.heegaardRegionSystem.basepoint (Sum.inl c) = (c, G.O c) :=
  (rfl)

@[simp]
theorem heegaardRegionSystem_basepoint_inr (c : Fin n) :
    G.heegaardRegionSystem.basepoint (Sum.inr c) = (c, G.X c) :=
  (rfl)

/-- Every region of a grid diagram is a square, so the Euler measure vanishes when every region
has Euler characteristic `1`. -/
@[simp]
theorem heegaardRegionSystem_eulerMeasure_const_one_eq_zero :
    G.heegaardRegionSystem.eulerMeasure 1 = 0 := by
  refine AddMonoidHom.ext fun D => ?_
  rw [AddMonoidHom.zero_apply]
  have hsum : ∀ e : Equiv.Perm (Fin n × Fin n), ∑ p, (D (e p) : ℚ) = ∑ p, (D p : ℚ) :=
    fun e => Equiv.sum_comp e fun p => (D p : ℚ)
  have h₁ := hsum ((finRotate n).symm.prodCongr (Equiv.refl (Fin n)))
  have h₂ := hsum ((finRotate n).symm.prodCongr (finRotate n).symm)
  have h₃ := hsum ((Equiv.refl (Fin n)).prodCongr (finRotate n).symm)
  simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply] at h₁ h₂ h₃
  rw [HeegaardRegionSystem.eulerMeasure_eq_sub_sum_pointMeasure]
  simp only [HeegaardRegionSystem.pointMeasure_apply, heegaardRegionSystem_alphaNext_symm_apply,
    heegaardRegionSystem_alphaLeft, heegaardRegionSystem_alphaRight, Pi.one_apply, Int.cast_one,
    one_mul, div_eq_mul_inv, add_mul, sum_add_distrib, ← sum_mul, h₁, h₂, h₃]
  ring

end RegionSystem

section Generators

variable [NeZero n] (G : GridDiagram n)

/-- The grid states of a grid diagram are the generators of its Heegaard diagram: the state `x`
occupies the intersection point `(c, x c)` of the vertical circle `c` with the horizontal circle
`x c`, and the generator matches the horizontal circle `r` with the vertical circle
`x⁻¹ r`. -/
def gridStateEquivGenerator : GridState n ≃ G.heegaardRegionSystem.Generator where
  toFun x := ⟨x.toPerm.symm, fun i => ⟨(x.toPerm.symm i, i), rfl, rfl⟩⟩
  invFun g := ⟨g.1.symm⟩
  left_inv _ := rfl
  right_inv g := G.heegaardRegionSystem.point_injective <| funext fun i => by
    rw [HeegaardIntersectionSystem.point_apply, HeegaardIntersectionSystem.point_apply]
    exact Prod.ext (g.2 i).property.2.symm (g.2 i).property.1.symm

/-- The generator of a grid state chooses the point `(x⁻¹ r, r)` on the horizontal circle `r`. -/
@[simp 1100]
theorem point_gridStateEquivGenerator (x : GridState n) (i : Fin n) :
    G.heegaardRegionSystem.point (G.gridStateEquivGenerator x) i = (x.toPerm.symm i, i) :=
  HeegaardIntersectionSystem.point_apply _ _ _

/-- The grid state of a generator sends each vertical circle to the horizontal circle it is
matched with. -/
@[simp]
theorem gridStateEquivGenerator_symm_toPerm (g : G.heegaardRegionSystem.Generator) :
    (G.gridStateEquivGenerator.symm g).toPerm = (G.heegaardRegionSystem.betaEquiv g).symm := by
  simp [gridStateEquivGenerator, HeegaardIntersectionSystem.betaEquiv_eq_fst]

/-- The generator of a grid state matches the horizontal circle `r` with the vertical circle
`x⁻¹ r`. -/
@[simp]
theorem betaEquiv_gridStateEquivGenerator (x : GridState n) :
    G.heegaardRegionSystem.betaEquiv (G.gridStateEquivGenerator x) = x.toPerm.symm :=
  Equiv.ext fun i => by
    rw [HeegaardIntersectionSystem.betaEquiv_apply, point_gridStateEquivGenerator,
      heegaardRegionSystem_beta]

/-- The `0`-chain of the generator of a grid state is the indicator of its occupied grid
points. -/
@[simp 1100]
theorem generatorChain_gridStateEquivGenerator (x : GridState n) (p : Fin n × Fin n) :
    G.heegaardRegionSystem.generatorChain (G.gridStateEquivGenerator x) p =
      if p ∈ x.pointSet then 1 else 0 := by
  rw [HeegaardIntersectionSystem.generatorChain_apply]
  simp only [heegaardRegionSystem_alpha, point_gridStateEquivGenerator, GridState.mem_pointSet]
  refine if_congr ?_ rfl rfl
  rw [Prod.ext_iff, Equiv.symm_apply_eq, eq_comm]
  simp

/-- The point measure at the generator of a grid state is the sum of the point measures at its
occupied grid points, indexed by the columns. -/
theorem generatorPointMeasure_gridStateEquivGenerator (x : GridState n)
    (D : Fin n × Fin n → ℤ) :
    G.heegaardRegionSystem.generatorPointMeasure (G.gridStateEquivGenerator x) D =
      ∑ c, G.heegaardRegionSystem.pointMeasure D (c, x c) := by
  rw [HeegaardRegionSystem.generatorPointMeasure_apply]
  simp only [point_gridStateEquivGenerator]
  exact (Equiv.sum_comp x.toPerm fun i =>
    G.heegaardRegionSystem.pointMeasure D (x.toPerm.symm i, i)).symm.trans
      (sum_congr rfl fun c _ => by simp)

end Generators

section Rectangles

variable [NeZero n] (G : GridDiagram n)

/-- The `α`-part of the boundary of the domain of a rectangle turns at its four corners: as a
`0`-chain it is `(right, bottom) - (right, top) - (left, bottom) + (left, top)`. -/
theorem alphaArcBoundary_alphaBoundary_domain (R : GridRectangle n) (q : Fin n × Fin n) :
    G.heegaardRegionSystem.alphaArcBoundary (G.heegaardRegionSystem.alphaBoundary R.domain) q =
      ((if q.1 = R.right then 1 else 0) - if q.1 = R.left then 1 else 0) *
        ((if q.2 = R.bottom then 1 else 0) - if q.2 = R.top then 1 else 0) := by
  obtain ⟨c, r⟩ := q
  have hr := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco R.bottom R.top ((finRotate n).symm r)
  have hc := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco R.left R.right ((finRotate n).symm c)
  simp only [Equiv.apply_symm_apply] at hr hc
  simp only [HeegaardRegionSystem.alphaArcBoundary_apply, HeegaardRegionSystem.alphaBoundary_apply,
    heegaardRegionSystem_alphaNext_symm_apply, heegaardRegionSystem_alphaLeft,
    heegaardRegionSystem_alphaRight, GridRectangle.domain_apply_mk]
  linear_combination
    (-((if c = R.left then 1 else 0 : ℤ) - if c = R.right then 1 else 0)) * hr -
      ((if r ∈ Grid.cIco R.bottom R.top then 1 else 0 : ℤ) -
        if (finRotate n).symm r ∈ Grid.cIco R.bottom R.top then 1 else 0) * hc

/-- The `β`-part of the boundary of the domain of a rectangle turns at its four corners: as a
`0`-chain it is `(right, top) - (right, bottom) - (left, top) + (left, bottom)`. -/
theorem betaArcBoundary_betaBoundary_domain (R : GridRectangle n) (q : Fin n × Fin n) :
    G.heegaardRegionSystem.betaArcBoundary (G.heegaardRegionSystem.betaBoundary R.domain) q =
      ((if q.1 = R.right then 1 else 0) - if q.1 = R.left then 1 else 0) *
        ((if q.2 = R.top then 1 else 0) - if q.2 = R.bottom then 1 else 0) := by
  obtain ⟨c, r⟩ := q
  have hr := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco R.bottom R.top ((finRotate n).symm r)
  have hc := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco R.left R.right ((finRotate n).symm c)
  simp only [Equiv.apply_symm_apply] at hr hc
  simp only [HeegaardRegionSystem.betaArcBoundary_apply, HeegaardRegionSystem.betaBoundary_apply,
    heegaardRegionSystem_betaNext_symm_apply, heegaardRegionSystem_betaLeft,
    heegaardRegionSystem_betaRight, GridRectangle.domain_apply_mk]
  linear_combination
    ((if c = R.left then 1 else 0 : ℤ) - if c = R.right then 1 else 0) * hr +
      ((if r ∈ Grid.cIco R.bottom R.top then 1 else 0 : ℤ) -
        if (finRotate n).symm r ∈ Grid.cIco R.bottom R.top then 1 else 0) * hc

/-- The `α`-boundary of the domain of a rectangle: going up across the horizontal circle `r` in a
covered column enters the rectangle at its bottom side and leaves it at its top side. -/
theorem alphaBoundary_domain (R : GridRectangle n) (c r : Fin n) :
    G.heegaardRegionSystem.alphaBoundary R.domain (c, r) =
      (if c ∈ Grid.cIco R.left R.right then 1 else 0) *
        ((if r = R.bottom then 1 else 0) - if r = R.top then 1 else 0) := by
  have h := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco R.bottom R.top ((finRotate n).symm r)
  simp only [Equiv.apply_symm_apply] at h
  simp only [HeegaardRegionSystem.alphaBoundary_apply, heegaardRegionSystem_alphaLeft,
    heegaardRegionSystem_alphaRight, GridRectangle.domain_apply_mk]
  linear_combination (if c ∈ Grid.cIco R.left R.right then 1 else 0 : ℤ) * h

/-- The `β`-boundary of the domain of a rectangle: going left across the vertical circle `c` in a
covered row enters the rectangle at its right side and leaves it at its left side. -/
theorem betaBoundary_domain (R : GridRectangle n) (c r : Fin n) :
    G.heegaardRegionSystem.betaBoundary R.domain (c, r) =
      (if r ∈ Grid.cIco R.bottom R.top then 1 else 0) *
        ((if c = R.right then 1 else 0) - if c = R.left then 1 else 0) := by
  have h := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco R.left R.right ((finRotate n).symm c)
  simp only [Equiv.apply_symm_apply] at h
  simp only [HeegaardRegionSystem.betaBoundary_apply, heegaardRegionSystem_betaLeft,
    heegaardRegionSystem_betaRight, GridRectangle.domain_apply_mk]
  linear_combination (-(if r ∈ Grid.cIco R.bottom R.top then 1 else 0 : ℤ)) * h

variable {x y : GridState n}

/-- The domain of an oriented rectangle from `x` to `y` is a domain from the generator of `x` to
the generator of `y`. -/
theorem isDomainBetween_domain (R : GridRectangleBetween x y) :
    G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) R.toGridRectangle.domain := by
  have hchain : ∀ q : Fin n × Fin n,
      G.heegaardRegionSystem.generatorChain (G.gridStateEquivGenerator y) q -
          G.heegaardRegionSystem.generatorChain (G.gridStateEquivGenerator x) q =
        ((if q.1 = R.right then 1 else 0) - if q.1 = R.left then 1 else 0) *
          ((if q.2 = R.bottom then 1 else 0) - if q.2 = R.top then 1 else 0) := by
    rintro ⟨c, r⟩
    simp only [generatorChain_gridStateEquivGenerator, GridState.mem_pointSet,
      GridRectangleBetween.bottom_def, GridRectangleBetween.top_def]
    by_cases hL : c = R.left
    · subst hL
      simp [R.map_left, R.left_ne_right, eq_comm (a := r)]
    by_cases hR : c = R.right
    · subst hR
      simp [R.map_right, R.left_ne_right.symm, eq_comm (a := r)]
    simp [R.map_of_ne c hL hR, hL, hR]
  rw [HeegaardRegionSystem.isDomainBetween_iff]
  constructor
  · funext q
    rw [alphaArcBoundary_alphaBoundary_domain, Pi.sub_apply, hchain]
    simp only [GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top]
  · funext q
    rw [betaArcBoundary_betaBoundary_domain, Pi.sub_apply]
    simp only [GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top]
    linear_combination hchain q

/-- The point measure of the domain of a nondegenerate rectangle at a grid point is a product of
a column weight and a row weight, each `2` strictly inside the rectangle, `1` on a side and `0`
outside. -/
theorem pointMeasure_domain (R : GridRectangle n) (hc : R.left ≠ R.right) (hr : R.bottom ≠ R.top)
    (c r : Fin n) :
    G.heegaardRegionSystem.pointMeasure R.domain (c, r) =
      (((2 * (if c ∈ Grid.cIoo R.left R.right then 1 else 0) + (if c = R.left then 1 else 0) +
          if c = R.right then 1 else 0 : ℤ) *
        (2 * (if r ∈ Grid.cIoo R.bottom R.top then 1 else 0) + (if r = R.bottom then 1 else 0) +
          if r = R.top then 1 else 0 : ℤ) : ℤ) : ℚ) / 4 := by
  have hr' := Grid.ite_mem_cIco_finRotate_add_ite_mem_cIco hr ((finRotate n).symm r)
  have hc' := Grid.ite_mem_cIco_finRotate_add_ite_mem_cIco hc ((finRotate n).symm c)
  simp only [Equiv.apply_symm_apply] at hr' hc'
  rw [HeegaardRegionSystem.pointMeasure_apply]
  simp only [heegaardRegionSystem_alphaNext_symm_apply, heegaardRegionSystem_alphaLeft,
    heegaardRegionSystem_alphaRight, GridRectangle.domain_apply_mk]
  rw [← hr', ← hc']
  push_cast
  ring

/-- At a grid point `(c, x c)` of the source state, the point measure of the domain of an
oriented rectangle is `1` strictly inside the rectangle, `1 / 4` at its two corners and `0`
elsewhere. -/
private theorem pointMeasure_domain_source (R : GridRectangleBetween x y) (c : Fin n) :
    G.heegaardRegionSystem.pointMeasure R.toGridRectangle.domain (c, x c) =
      (if (c, x c) ∈ R.toGridRectangle.interior then 1 else 0) +
        (if c = R.left then 4⁻¹ else 0) + if c = R.right then 4⁻¹ else 0 := by
  have hLR := R.left_ne_right
  rw [G.pointMeasure_domain R.toGridRectangle hLR R.bottom_ne_top]
  simp only [GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    GridRectangle.mem_interior, GridRectangle.mem_columnInterior, GridRectangle.mem_rowInterior,
    GridRectangleBetween.bottom_def, GridRectangleBetween.top_def]
  by_cases hL : c = R.left
  · subst hL
    simp [hLR]
  by_cases hR : c = R.right
  · subst hR
    simp [hLR.symm]
  have hb : x c ≠ x R.left := fun h => hL (x.toPerm.injective h)
  have ht : x c ≠ x R.right := fun h => hR (x.toPerm.injective h)
  by_cases h₁ : c ∈ Grid.cIoo R.left R.right <;>
    by_cases h₂ : x c ∈ Grid.cIoo (x R.left) (x R.right) <;>
    simp [hL, hR, hb, ht, h₁, h₂]

/-- The point measure of the domain of an oriented rectangle at the generator of its source is
the number of source points strictly inside it plus `1 / 2`, a quarter for each of the two
corners. -/
theorem generatorPointMeasure_domain_source (R : GridRectangleBetween x y) :
    G.heegaardRegionSystem.generatorPointMeasure (G.gridStateEquivGenerator x)
        R.toGridRectangle.domain =
      #(x.pointSet ∩ R.toGridRectangle.interior) + 1 / 2 := by
  rw [generatorPointMeasure_gridStateEquivGenerator]
  simp only [G.pointMeasure_domain_source R, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  rw [← x.sum_pointSet fun p => if p ∈ R.toGridRectangle.interior then (1 : ℚ) else 0, sum_boole,
    filter_mem_eq_inter]
  ring

/-- The point measure of the domain of an oriented rectangle at the generator of its target is
the number of source points strictly inside it plus `1 / 2`: the two states agree away from the
two corners where they differ. -/
theorem generatorPointMeasure_domain_target (R : GridRectangleBetween x y) :
    G.heegaardRegionSystem.generatorPointMeasure (G.gridStateEquivGenerator y)
        R.toGridRectangle.domain =
      #(x.pointSet ∩ R.toGridRectangle.interior) + 1 / 2 := by
  rw [← G.generatorPointMeasure_domain_source R, generatorPointMeasure_gridStateEquivGenerator,
    generatorPointMeasure_gridStateEquivGenerator]
  refine sum_congr rfl fun c _ => ?_
  have hLR := R.left_ne_right
  by_cases hL : c = R.left
  · subst hL
    rw [R.map_left, G.pointMeasure_domain _ hLR R.bottom_ne_top,
      G.pointMeasure_domain _ hLR R.bottom_ne_top]
    simp [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hLR, hLR.symm]
  by_cases hR : c = R.right
  · subst hR
    rw [R.map_right, G.pointMeasure_domain _ hLR R.bottom_ne_top,
      G.pointMeasure_domain _ hLR R.bottom_ne_top]
    simp [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hLR, hLR.symm]
  rw [R.map_of_ne c hL hR]

/-- **Lipshitz's index of a rectangle.** The domain of an oriented rectangle from `x` to `y` has
Maslov index `1 + 2 #(x ∩ Int(r))`, for Euler characteristic `1` on every square. -/
theorem maslovIndex_domain (R : GridRectangleBetween x y) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) R.toGridRectangle.domain =
      1 + 2 * #(x.pointSet ∩ R.toGridRectangle.interior) := by
  rw [HeegaardRegionSystem.maslovIndex_apply, heegaardRegionSystem_eulerMeasure_const_one_eq_zero,
    AddMonoidHom.zero_apply, generatorPointMeasure_domain_source,
    generatorPointMeasure_domain_target]
  ring

/-- The domain of an oriented rectangle has Maslov index one exactly when the rectangle is
empty. -/
theorem maslovIndex_domain_eq_one_iff (R : GridRectangleBetween x y) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) R.toGridRectangle.domain = 1 ↔ R.IsEmpty := by
  rw [maslovIndex_domain, GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
    GridRectangle.IsEmptyFor, disjoint_comm, disjoint_iff_inter_eq_empty, ← card_eq_zero]
  constructor
  · intro h
    exact_mod_cast (by linarith : (#(x.pointSet ∩ R.toGridRectangle.interior) : ℚ) = 0)
  · intro h
    rw [h]
    norm_num

/-- The multiplicity of the domain of a rectangle at the `O`-basepoints is the number of
`O`-markings in the squares it covers. -/
theorem sum_domain_basepoint_inl (R : GridRectangle n) :
    ∑ c, R.domain (G.heegaardRegionSystem.basepoint (Sum.inl c)) =
      #(G.OSet ∩ R.coveredSquares) := by
  simp only [heegaardRegionSystem_basepoint_inl, GridRectangle.domain_apply]
  rw [← G.O.sum_pointSet fun p => if p ∈ R.coveredSquares then (1 : ℤ) else 0, sum_boole,
    filter_mem_eq_inter, OSet_def]

/-- The multiplicity of the domain of a rectangle at the `X`-basepoints is the number of
`X`-markings in the squares it covers. -/
theorem sum_domain_basepoint_inr (R : GridRectangle n) :
    ∑ c, R.domain (G.heegaardRegionSystem.basepoint (Sum.inr c)) =
      #(G.XSet ∩ R.coveredSquares) := by
  simp only [heegaardRegionSystem_basepoint_inr, GridRectangle.domain_apply]
  rw [← G.X.sum_pointSet fun p => if p ∈ R.coveredSquares then (1 : ℤ) else 0, sum_boole,
    filter_mem_eq_inter, XSet_def]

/-- The Heegaard Floer grading `μ(D) - 2 n_O(D)` of the domain of a rectangle from `x` to `y` is
the difference `M_O(x) - M_O(y)` of the `O`-Maslov gradings of grid homology. -/
theorem maslovIndex_domain_sub_two_mul_sum_basepoint_inl (R : GridRectangleBetween x y) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
          (G.gridStateEquivGenerator y) R.toGridRectangle.domain -
        2 * ∑ c, (R.toGridRectangle.domain (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℚ) =
      G.maslovO x - G.maslovO y := by
  rw [← Int.cast_sum, sum_domain_basepoint_inl, maslovIndex_domain,
    G.maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card R,
    R.card_pointSet_inter_coveredSquares]
  push_cast
  ring

/-- The Heegaard Floer grading `μ(D) - 2 n_X(D)` of the domain of a rectangle from `x` to `y` is
the difference `M_X(x) - M_X(y)` of the `X`-Maslov gradings of grid homology. -/
theorem maslovIndex_domain_sub_two_mul_sum_basepoint_inr (R : GridRectangleBetween x y) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
          (G.gridStateEquivGenerator y) R.toGridRectangle.domain -
        2 * ∑ c, (R.toGridRectangle.domain (G.heegaardRegionSystem.basepoint (Sum.inr c)) : ℚ) =
      G.maslovX x - G.maslovX y := by
  rw [← Int.cast_sum, sum_domain_basepoint_inr, maslovIndex_domain,
    G.maslovX_sub_maslovX_eq_two_mul_card_sub_one_sub_two_mul_card R,
    R.card_pointSet_inter_coveredSquares]
  push_cast
  ring

/-- The Heegaard Floer Alexander grading `n_X(D) - n_O(D)` of the domain of a rectangle from `x`
to `y` is the difference `A(x) - A(y)` of the Alexander gradings of grid homology. -/
theorem sum_domain_basepoint_inr_sub_sum_domain_basepoint_inl (R : GridRectangleBetween x y) :
    ((∑ c, R.toGridRectangle.domain (G.heegaardRegionSystem.basepoint (Sum.inr c)) -
        ∑ c, R.toGridRectangle.domain (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℤ) : ℚ) =
      G.alexander x - G.alexander y := by
  rw [sum_domain_basepoint_inl, sum_domain_basepoint_inr,
    G.alexander_sub_alexander_eq_card_sub_card R]
  push_cast
  ring

/-- The domain of an empty rectangle covering no marking is counted by the hat differential of
the multi-pointed Heegaard diagram of a grid diagram: it is a nonnegative domain of Maslov index
one with multiplicity zero at every basepoint. -/
theorem domain_mem_hatDomains (R : GridRectangleBetween x y) (hR : R.IsEmpty)
    (hM : R.toGridRectangle.AvoidsMarkings G) :
    R.toGridRectangle.domain ∈ G.heegaardRegionSystem.hatDomains 1
      (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y) := by
  rw [HeegaardRegionSystem.mem_hatDomains_iff]
  refine ⟨G.isDomainBetween_domain R, ?_, R.toGridRectangle.domain_nonneg,
    (G.maslovIndex_domain_eq_one_iff R).2 hR⟩
  rw [GridRectangle.avoidsMarkings_iff_forall] at hM
  rintro (c | c) <;>
    simp only [heegaardRegionSystem_basepoint_inl, heegaardRegionSystem_basepoint_inr,
      GridRectangle.domain_apply, GridRectangle.mem_coveredSquares, ite_eq_right_iff,
      one_ne_zero, imp_false, not_and]
  · exact fun hc => (hM c hc).1
  · exact fun hc => (hM c hc).2

end Rectangles

end GridDiagram

end TauCeti
