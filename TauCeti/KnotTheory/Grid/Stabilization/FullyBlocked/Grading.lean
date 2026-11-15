/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.FullyBlocked.Basic
public import TauCeti.KnotTheory.Grid.Stabilization.Grading
public import TauCeti.KnotTheory.Grid.Grading.Complex

/-!
# Bigrading of the fully blocked stabilization comparison

The fully blocked stabilization comparison has two components. The center projection raises
both Maslov and Alexander degree by one, while the reduced off-center `X₂`-homotopy preserves
both degrees. Thus a stabilized chain in degree `(m, a)` maps to original chains in degrees
`(m + 1, a + 1)` and `(m, a)`. These are the shifts of the stabilization factor `W`, whose
summands have degrees `(-1,-1)` and `(0,0)`.

This file restricts the specified comparison to homogeneous chain pieces and proves that its
two components intertwine the graded differentials. It also shows that, on an arbitrary
stabilized chain, the center component sends the homogeneous part of degree `g` to the homogeneous
part of degree `g + (1,1)` of the image, and the off-center component preserves homogeneous parts.
These chain comparisons supply the grading input for the fully blocked homology stabilization
equivalence.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2.
* Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2.
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s : Fin n)

local notation "F" => ZMod 2

private theorem bidegree_eq_of_reducedHomotopy_ne_zero
    (y : G.1.StabilizeXOffCenterState s) (x : GridState n)
    (h : (G.1.stabilizeXOffCenterToCenter s F).constantCoeffReduction
      (Finsupp.single y 1) x ≠ 0) :
    G.bidegree x = (G.stabilizeX s).bidegree y := by
  classical
  rw [GridDiagram.constantCoeffReduction_stabilizeXOffCenterToCenter_single_apply] at h
  have hcard : ((((G.stabilizeX s).1.XHomotopyRectangles s.succ y.1
      (x.insertPoint s.succ (G.1.X s).succ)).filter fun r =>
        (G.stabilizeX s).1.OColumns r.toGridRectangle = ∅)).card ≠ 0 := by
    intro hz
    simp only [val_stabilizeX] at hz
    simp [hz] at h
  obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp hcard
  obtain ⟨hr, hO⟩ := Finset.mem_filter.mp hr
  rw [val_stabilizeX] at hr hO
  have hM := G.1.maslovOℤ_stabilizeX_eq_of_isEmpty s x
    ((GridDiagram.mem_XHomotopyRectangles _ _ r).mp hr).1
  have hA := G.1.alexander_stabilizeX_eq_of_mem_XHomotopyRectangles s x hr
  rw [hO, Finset.card_empty] at hM hA
  rw [← val_stabilizeX, alexander_eq_intCast, G.alexander_eq_intCast] at hA
  simp only [Nat.cast_zero, sub_zero] at hA
  apply Prod.ext
  · simpa [bidegree_fst] using hM.symm
  · simp only [bidegree_snd]
    exact Int.cast_inj.mp hA.symm

/-- On a homogeneous stabilized chain, the first comparison component is supported in degree
`g + (1,1)`, reflecting the degree `(-1,-1)` of the center summand of `W`. -/
theorem fullyBlockedStabilizeXMap_fst_bigradedChainInclusion_eq_zero_of_ne (g : ℤ × ℤ)
    (c : (G.stabilizeX s).BigradedChainPiece F g) {x : GridState n}
    (hx : G.bidegree x ≠ g + (1, 1)) :
    (G.1.fullyBlockedStabilizeXMap s ((G.stabilizeX s).bigradedChainInclusion F g c)).1 x = 0 := by
  rw [GridDiagram.fullyBlockedStabilizeXMap_fst,
    GridDiagram.constantCoeffReduction_stabilizeXCenterProjection_apply,
    bigradedChainInclusion_apply]
  have hne : (G.stabilizeX s).bidegree (x.insertPoint s.succ (G.1.X s).succ) ≠ g := by
    rw [bidegree_stabilizeX_insertPoint]
    exact fun h => hx (sub_eq_iff_eq_add.mp h)
  exact dite_eq_right hne

/-- On a homogeneous stabilized chain, the second comparison component is supported in the
same bidegree. Only rectangles carrying no `O`-marking survive coefficient reduction. -/
theorem fullyBlockedStabilizeXMap_snd_bigradedChainInclusion_eq_zero_of_ne (g : ℤ × ℤ)
    (c : (G.stabilizeX s).BigradedChainPiece F g) {x : GridState n} (hx : G.bidegree x ≠ g) :
    (G.1.fullyBlockedStabilizeXMap s ((G.stabilizeX s).bigradedChainInclusion F g c)).2 x = 0 := by
  classical
  rw [GridDiagram.fullyBlockedStabilizeXMap_snd,
    LinearMap.apply_apply_eq_finsuppSum_mul, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro y _
  rw [GridDiagram.constantCoeffReduction_stabilizeXOffCenterProjection_apply,
    bigradedChainInclusion_apply]
  by_cases hy : (G.stabilizeX s).bidegree y.1 = g
  · have hz : (G.1.stabilizeXOffCenterToCenter s F).constantCoeffReduction
        (Finsupp.single y 1) x = 0 := by
      by_contra hz
      exact hx ((G.bidegree_eq_of_reducedHomotopy_ne_zero s y x hz).trans hy)
    simp [hz]
  · simp [hy]

/-- The center component of fully blocked stabilization on homogeneous chains. Its target
bidegree is one higher in both coordinates. -/
noncomputable def gradedFullyBlockedStabilizeXCenter (g : ℤ × ℤ) :
    (G.stabilizeX s).BigradedChainPiece F g →ₗ[F] G.BigradedChainPiece F (g + (1, 1)) :=
  (G.bigradedChainProjection F (g + (1, 1))).comp
    ((LinearMap.fst F _ _).comp
      ((G.1.fullyBlockedStabilizeXMap s).comp ((G.stabilizeX s).bigradedChainInclusion F g)))

/-- The off-center homotopy component of fully blocked stabilization on homogeneous chains,
with no grading shift. -/
noncomputable def gradedFullyBlockedStabilizeXOffCenter (g : ℤ × ℤ) :
    (G.stabilizeX s).BigradedChainPiece F g →ₗ[F] G.BigradedChainPiece F g :=
  (G.bigradedChainProjection F g).comp
    ((LinearMap.snd F _ _).comp
      ((G.1.fullyBlockedStabilizeXMap s).comp ((G.stabilizeX s).bigradedChainInclusion F g)))

/-- At a state of the target degree, the graded center map reads the center coefficient. -/
@[simp]
theorem gradedFullyBlockedStabilizeXCenter_apply (g : ℤ × ℤ)
    (c : (G.stabilizeX s).BigradedChainPiece F g)
    (x : {x : GridState n // G.bidegree x = g + (1, 1)}) :
    G.gradedFullyBlockedStabilizeXCenter s g c x =
      (G.stabilizeX s).bigradedChainInclusion F g c
        (x.1.insertPoint s.succ (G.1.X s).succ) := by
  simp only [gradedFullyBlockedStabilizeXCenter, LinearMap.comp_apply,
    bigradedChainProjection_apply, LinearMap.fst_apply,
    GridDiagram.fullyBlockedStabilizeXMap_fst,
    GridDiagram.constantCoeffReduction_stabilizeXCenterProjection_apply]

/-- At a state of the target degree, the graded off-center map has the coefficient of the
specified total comparison. -/
@[simp]
theorem gradedFullyBlockedStabilizeXOffCenter_apply (g : ℤ × ℤ)
    (c : (G.stabilizeX s).BigradedChainPiece F g)
    (x : {x : GridState n // G.bidegree x = g}) :
    G.gradedFullyBlockedStabilizeXOffCenter s g c x =
      (G.1.fullyBlockedStabilizeXMap s
        ((G.stabilizeX s).bigradedChainInclusion F g c)).2 x := by
  simp [gradedFullyBlockedStabilizeXOffCenter]

/-- Inclusion of the graded center comparison recovers the specified total comparison. -/
@[simp]
theorem bigradedChainInclusion_gradedFullyBlockedStabilizeXCenter (g : ℤ × ℤ)
    (c : (G.stabilizeX s).BigradedChainPiece F g) :
    G.bigradedChainInclusion F (g + (1, 1)) (G.gradedFullyBlockedStabilizeXCenter s g c) =
      (G.1.fullyBlockedStabilizeXMap s ((G.stabilizeX s).bigradedChainInclusion F g c)).1 := by
  ext x
  rw [bigradedChainInclusion_apply]
  split_ifs with hx
  · simp [gradedFullyBlockedStabilizeXCenter]
  · exact (G.fullyBlockedStabilizeXMap_fst_bigradedChainInclusion_eq_zero_of_ne s g c hx).symm

/-- Inclusion of the graded off-center comparison recovers the specified total comparison. -/
@[simp]
theorem bigradedChainInclusion_gradedFullyBlockedStabilizeXOffCenter (g : ℤ × ℤ)
    (c : (G.stabilizeX s).BigradedChainPiece F g) :
    G.bigradedChainInclusion F g (G.gradedFullyBlockedStabilizeXOffCenter s g c) =
      (G.1.fullyBlockedStabilizeXMap s ((G.stabilizeX s).bigradedChainInclusion F g c)).2 := by
  ext x
  rw [bigradedChainInclusion_apply]
  split_ifs with hx
  · simp [gradedFullyBlockedStabilizeXOffCenter]
  · exact (G.fullyBlockedStabilizeXMap_snd_bigradedChainInclusion_eq_zero_of_ne s g c hx).symm

/-- The graded center comparison intertwines the differentials, with the `(-1,-1)` summand
shift on the original complex. -/
theorem gradedFullyBlockedStabilizeXCenter_differential (a m : ℤ)
    (c : (G.stabilizeX s).BigradedChainPiece F (m + 1, a)) :
    G.gradedFullyBlockedStabilizeXCenter s (m, a)
        ((G.stabilizeX s).gradedFullyBlockedDifferential a m c) =
      G.gradedFullyBlockedDifferential (a + 1) (m + 1)
        (G.gradedFullyBlockedStabilizeXCenter s (m + 1, a) c) := by
  apply G.bigradedChainInclusion_injective F (m + 1, a + 1)
  have hc (k : ℤ) (u : (G.stabilizeX s).BigradedChainPiece F (k, a)) :
      G.bigradedChainInclusion F (k + 1, a + 1)
          (G.gradedFullyBlockedStabilizeXCenter s (k, a) u) =
        (G.1.fullyBlockedStabilizeXMap s
          ((G.stabilizeX s).bigradedChainInclusion F (k, a) u)).1 := by
    simpa only [Prod.mk_add_mk] using
      G.bigradedChainInclusion_gradedFullyBlockedStabilizeXCenter s (k, a) u
  rw [hc, bigradedChainInclusion_gradedFullyBlockedDifferential,
    bigradedChainInclusion_gradedFullyBlockedDifferential, hc]
  have h := LinearMap.congr_fun (G.1.fullyBlockedStabilizeXMap_comp_differential s)
    ((G.stabilizeX s).bigradedChainInclusion F (m + 1, a) c)
  simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply, val_stabilizeX] using
    congrArg Prod.fst h

/-- The graded off-center comparison intertwines the differentials without a grading shift. -/
theorem gradedFullyBlockedStabilizeXOffCenter_differential (a m : ℤ)
    (c : (G.stabilizeX s).BigradedChainPiece F (m + 1, a)) :
    G.gradedFullyBlockedStabilizeXOffCenter s (m, a)
        ((G.stabilizeX s).gradedFullyBlockedDifferential a m c) =
      G.gradedFullyBlockedDifferential a m
        (G.gradedFullyBlockedStabilizeXOffCenter s (m + 1, a) c) := by
  apply G.bigradedChainInclusion_injective F (m, a)
  simp only [bigradedChainInclusion_gradedFullyBlockedStabilizeXOffCenter,
    bigradedChainInclusion_gradedFullyBlockedDifferential]
  have h := LinearMap.congr_fun (G.1.fullyBlockedStabilizeXMap_comp_differential s)
    ((G.stabilizeX s).bigradedChainInclusion F (m + 1, a) c)
  simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply, val_stabilizeX] using
    congrArg Prod.snd h

/-- The center component of the chain comparison sends the part of bidegree `g` of a stabilized
chain to the part of bidegree `g + (1, 1)` of its image. -/
theorem fst_fullyBlockedStabilizeXMap_bigradedChainInclusion (g : ℤ × ℤ)
    (c : GridChain F (n + 1)) :
    (G.1.fullyBlockedStabilizeXMap s ((G.stabilizeX s).bigradedChainInclusion F g
        ((G.stabilizeX s).bigradedChainProjection F g c))).1 =
      G.bigradedChainInclusion F (g + (1, 1))
        (G.bigradedChainProjection F (g + (1, 1)) (G.1.fullyBlockedStabilizeXMap s c).1) := by
  refine (G.stabilizeX s).map_bigradedChainInclusion_bigradedChainProjection G
    (LinearMap.fst F _ _ ∘ₗ G.1.fullyBlockedStabilizeXMap s) (1, 1) (fun x y hy => ?_) g c
  have h := G.fullyBlockedStabilizeXMap_fst_bigradedChainInclusion_eq_zero_of_ne s
    ((G.stabilizeX s).bidegree x)
    ((G.stabilizeX s).bigradedChainProjection F ((G.stabilizeX s).bidegree x) (Finsupp.single x 1))
    hy
  simpa only [bigradedChainInclusion_bigradedChainProjection_single, ↓reduceIte,
    LinearMap.comp_apply, LinearMap.fst_apply] using h

/-- The off-center component of the chain comparison preserves homogeneous parts. -/
theorem snd_fullyBlockedStabilizeXMap_bigradedChainInclusion (g : ℤ × ℤ)
    (c : GridChain F (n + 1)) :
    (G.1.fullyBlockedStabilizeXMap s ((G.stabilizeX s).bigradedChainInclusion F g
        ((G.stabilizeX s).bigradedChainProjection F g c))).2 =
      G.bigradedChainInclusion F g
        (G.bigradedChainProjection F g (G.1.fullyBlockedStabilizeXMap s c).2) := by
  have h := (G.stabilizeX s).map_bigradedChainInclusion_bigradedChainProjection G
    (LinearMap.snd F _ _ ∘ₗ G.1.fullyBlockedStabilizeXMap s) 0 (fun x y hy => ?_) g c
  · rw [add_zero] at h
    simpa only [LinearMap.comp_apply, LinearMap.snd_apply] using h
  have h := G.fullyBlockedStabilizeXMap_snd_bigradedChainInclusion_eq_zero_of_ne s
    ((G.stabilizeX s).bidegree x)
    ((G.stabilizeX s).bigradedChainProjection F ((G.stabilizeX s).bidegree x) (Finsupp.single x 1))
    (x := y) (by rwa [← add_zero ((G.stabilizeX s).bidegree x)])
  simpa only [bigradedChainInclusion_bigradedChainProjection_single, ↓reduceIte,
    LinearMap.comp_apply, LinearMap.snd_apply] using h

end TauCeti.OddComponentGridDiagram
