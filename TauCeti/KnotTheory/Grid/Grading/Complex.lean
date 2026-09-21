/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Chain
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
import TauCeti.KnotTheory.Grid.Differential.Square.Zero

/-!
# The graded fully blocked grid complex

For each Alexander degree, the fully blocked differential restricts to a chain complex indexed
by the integer Maslov grading. Its objects are the homogeneous pieces of the grid chain module,
and its differential is the restriction of the rectangle-counting differential. Inclusion into
the total chain module intertwines the differentials, so square-zero follows from the total
complex. This supplies the graded fully blocked complex whose Euler characteristic agrees with
the Alexander-graded chain Euler characteristic.

The coefficient field is `ZMod 2`, as for the total fully blocked differential. The diagram has
an odd number of components so that its Alexander grading is integral. The differential lowers
Maslov degree by one and preserves Alexander degree.

## Main definitions

* `TauCeti.OddComponentGridDiagram.gradedFullyBlockedDifferential`: the differential between
  consecutive Maslov degrees at fixed Alexander degree.
* `TauCeti.OddComponentGridDiagram.gradedFullyBlockedComplex`: the resulting chain complex.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3--4.4.
-/

public section

open CategoryTheory

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

/-- A fully blocked empty rectangle lowers the bidegree by `(1, 0)`. -/
theorem bidegree_eq_sub_of_mem_fullyBlockedRectangles {x y : GridState n}
    {r : GridRectangleBetween x y} (hr : r ∈ G.1.fullyBlockedRectangles x y) :
    G.bidegree y = G.bidegree x - (1, 0) := by
  obtain ⟨he, ha⟩ := (G.1.mem_fullyBlockedRectangles x y r).mp hr
  have hO := r.disjoint_squares_OSet_of_avoidsMarkings ha
  have hX := r.disjoint_squares_XSet_of_avoidsMarkings ha
  rw [GridRectangle.squares_eq_coveredSquares] at hO hX
  have hM := G.1.maslovO_sub_maslovO_eq_one_of_disjoint_coveredSquares r he hO
  have hA := G.1.alexander_eq_alexander_of_disjoint_coveredSquares r
    (Finset.disjoint_union_right.mpr ⟨hO, hX⟩)
  rw [G.1.maslovO_eq_intCast, G.1.maslovO_eq_intCast] at hM
  rw [G.alexander_eq_intCast, G.alexander_eq_intCast] at hA
  have hM' : G.1.maslovOℤ x - G.1.maslovOℤ y = 1 := by exact_mod_cast hM
  have hA' : G.alexanderℤ x = G.alexanderℤ y := by exact_mod_cast hA
  apply Prod.ext
  · simp only [bidegree_fst, Prod.fst_sub]
    omega
  · simp only [bidegree_snd, Prod.snd_sub, sub_zero]
    exact hA'.symm

/-- A nonzero fully blocked rectangle count from `x` to `y` implies
`G.bidegree y = G.bidegree x - (1, 0)`. -/
theorem bidegree_eq_sub_of_fullyBlockedRectangleCount_ne_zero {x y : GridState n}
    (h : G.1.fullyBlockedRectangleCount x y ≠ 0) :
    G.bidegree y = G.bidegree x - (1, 0) := by
  have hc : (G.1.fullyBlockedRectangles x y).card ≠ 0 := by
    intro hc
    simp [GridDiagram.fullyBlockedRectangleCount_def, hc] at h
  obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp hc
  exact G.bidegree_eq_sub_of_mem_fullyBlockedRectangles hr

/-- The total differential of a homogeneous chain is supported in bidegree one lower in Maslov
and unchanged in Alexander. -/
theorem fullyBlockedDifferential_bigradedChainInclusion_apply_eq_zero_of_ne (g : ℤ × ℤ)
    (c : G.BigradedChainPiece (ZMod 2) g) {y : GridState n}
    (hy : G.bidegree y ≠ g - (1, 0)) :
    G.1.fullyBlockedDifferential (G.bigradedChainInclusion (ZMod 2) g c) y = 0 := by
  classical
  rw [GridDiagram.fullyBlockedDifferential_apply_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : G.bidegree x = g
  · have hz : G.1.fullyBlockedRectangleCount x y = 0 := by
      by_contra hz
      exact hy (hx ▸ G.bidegree_eq_sub_of_fullyBlockedRectangleCount_ne_zero hz)
    rw [hz, mul_zero]
  · simp [G.bigradedChainInclusion_apply, hx]

/-- The fully blocked differential from Maslov degree `m + 1` to `m` at Alexander degree `a`. -/
noncomputable def gradedFullyBlockedDifferential (a m : ℤ) :
    G.BigradedChainPiece (ZMod 2) (m + 1, a) →ₗ[ZMod 2]
      G.BigradedChainPiece (ZMod 2) (m, a) :=
  (G.bigradedChainProjection (ZMod 2) (m, a)).comp
    (G.1.fullyBlockedDifferential.comp (G.bigradedChainInclusion (ZMod 2) (m + 1, a)))

/-- The coefficient of the graded differential is the coefficient of the total differential. -/
@[simp]
theorem gradedFullyBlockedDifferential_apply (a m : ℤ)
    (c : G.BigradedChainPiece (ZMod 2) (m + 1, a))
    (y : {y : GridState n // G.bidegree y = (m, a)}) :
    G.gradedFullyBlockedDifferential a m c y =
      G.1.fullyBlockedDifferential (G.bigradedChainInclusion (ZMod 2) (m + 1, a) c) y := by
  simp [gradedFullyBlockedDifferential]

/-- Inclusion of the homogeneous pieces intertwines the graded and total differentials. -/
@[simp]
theorem bigradedChainInclusion_gradedFullyBlockedDifferential (a m : ℤ)
    (c : G.BigradedChainPiece (ZMod 2) (m + 1, a)) :
    G.bigradedChainInclusion (ZMod 2) (m, a) (G.gradedFullyBlockedDifferential a m c) =
      G.1.fullyBlockedDifferential (G.bigradedChainInclusion (ZMod 2) (m + 1, a) c) := by
  ext y
  rw [G.bigradedChainInclusion_apply]
  split_ifs with hy
  · exact G.gradedFullyBlockedDifferential_apply a m c ⟨y, hy⟩
  · exact (G.fullyBlockedDifferential_bigradedChainInclusion_apply_eq_zero_of_ne (m + 1, a) c
      (by simpa using hy)).symm

/-- Consecutive graded fully blocked differentials compose to zero. -/
theorem gradedFullyBlockedDifferential_comp_eq_zero (a m : ℤ) :
    (G.gradedFullyBlockedDifferential a m).comp
      (G.gradedFullyBlockedDifferential a (m + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply G.bigradedChainInclusion_injective (ZMod 2) (m, a)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero,
    bigradedChainInclusion_gradedFullyBlockedDifferential]
  exact LinearMap.congr_fun G.1.fullyBlockedDifferential_comp_self_eq_zero _

/-- The Maslov-graded fully blocked grid complex in Alexander degree `a`. -/
noncomputable def gradedFullyBlockedComplex (a : ℤ) : ChainComplex (ModuleCat (ZMod 2)) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of (ZMod 2) (G.BigradedChainPiece (ZMod 2) (m, a)))
    (fun m => ModuleCat.ofHom (G.gradedFullyBlockedDifferential a m)) (fun m => by
      rw [← ModuleCat.ofHom_comp, G.gradedFullyBlockedDifferential_comp_eq_zero,
        ModuleCat.ofHom_zero])

/-- The objects of the graded complex are the homogeneous grid-chain pieces. -/
@[simp]
theorem gradedFullyBlockedComplex_X (a m : ℤ) :
    (G.gradedFullyBlockedComplex a).X m =
      ModuleCat.of (ZMod 2) (G.BigradedChainPiece (ZMod 2) (m, a)) := by
  rfl

/-- The consecutive differential is the restriction of the total grid differential. -/
@[simp]
theorem gradedFullyBlockedComplex_d (a m : ℤ) :
    (G.gradedFullyBlockedComplex a).d (m + 1) m =
      eqToHom (G.gradedFullyBlockedComplex_X a (m + 1)) ≫
        ModuleCat.ofHom (G.gradedFullyBlockedDifferential a m) ≫
          eqToHom (G.gradedFullyBlockedComplex_X a m).symm := by
  simp only [gradedFullyBlockedComplex, ChainComplex.of_d]
  -- The object identifications act as identity maps on homogeneous chains.
  ext c
  rfl

end TauCeti.OddComponentGridDiagram
