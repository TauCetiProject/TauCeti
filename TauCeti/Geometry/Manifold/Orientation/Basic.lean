/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.LinearAlgebra.Orientation
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Defs

/-!
# Manifold orientations

This file records the chart-sign data underlying an orientation of a finite-dimensional real
manifold.  An `OrientationLift` stores a model orientation and signs on the source of every
preferred chart, with local constancy and the transition-Jacobian compatibility law.  Quotienting
by the simultaneous sign flip gives `Manifold.Orientation`; `orientationAt` is its tangent-space
orientation and is independent of the chosen lift.

Tangent-space orientations provide the signs used to compare derivatives of maps and to evaluate
top forms, while the construction remains independent of integration and of a chosen orientation
of the atlas.

The conventions follow Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 15.
-/

public section

open Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} [Fintype ι] [FiniteDimensional ℝ E]

/-- A model orientation together with the signs of preferred charts.

The sign is indexed by the source of its chart, so no arbitrary values away from that source are
part of the data.  Its compatibility equation compares two charts through the determinant of the
transition derivative within `range I`, including boundary points. -/
structure OrientationLift (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (ι : Type*) [Fintype ι] [FiniteDimensional ℝ E] where
  /-- The orientation chosen on the model vector space. -/
  modelOrientation : Orientation ℝ E ι
  /-- The cardinality of the orientation index. -/
  card_eq : Fintype.card ι = Module.finrank ℝ E
  /-- The sign of the preferred chart at `x`, on its chart source. -/
  sign : (x : M) → (chartAt H x).source → ℤˣ
  /-- Chart signs are locally constant on each chart source. -/
  continuous_sign : ∀ x, Continuous (sign x)
  /-- On an overlap, the product of chart signs is the sign of the transition determinant. -/
  sign_mul_sign : ∀ x x' y (hy : y ∈ (chartAt H x).source)
    (hy' : y ∈ (chartAt H x').source),
    ((sign x ⟨y, hy⟩ * sign x' ⟨y, hy'⟩ : ℤˣ) : ℤ) =
      (SignType.sign (LinearMap.det
        (fderivWithin ℝ (extChartAt I x' ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x y) : E →ₗ[ℝ] E)) : ℤ)

namespace OrientationLift

/-- Extend a chart sign to a total function, using `1` off the chart source. -/
noncomputable def signAt (l : OrientationLift I M ι) (x y : M) : ℤˣ := by
  classical
  exact if hy : y ∈ (chartAt H x).source then l.sign x ⟨y, hy⟩ else 1

@[simp]
theorem signAt_of_mem (l : OrientationLift I M ι) (x y : M)
    (hy : y ∈ (chartAt H x).source) : l.signAt x y = l.sign x ⟨y, hy⟩ := by
  simp [signAt, hy]

/-- The tangent orientation induced by a lift at `x`. -/
noncomputable def tangentOrientation (l : OrientationLift I M ι) (x : M) :
    _root_.Orientation ℝ (TangentSpace I x) ι :=
  let o :=
    _root_.Orientation.map ι (tangentSpaceCastModel I x).symm.toLinearEquiv l.modelOrientation
  if l.sign x ⟨x, mem_chart_source H x⟩ = 1 then o else -o

end OrientationLift

/-- Two orientation lifts differ by the diagonal sign flip. -/
def OrientationLift.setoid : Setoid (OrientationLift I M ι) where
  r l l' := l' = l ∨
    (l'.modelOrientation = -l.modelOrientation ∧
      l'.sign = fun x y ↦ -l.sign x y)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro l
      exact Or.inl rfl
    · intro l l' h
      rcases h with rfl | ⟨hm, hs⟩
      · exact Or.inl rfl
      · right
        refine ⟨?_, ?_⟩
        · have hnn : -(-l.modelOrientation) = l.modelOrientation :=
            InvolutiveNeg.neg_neg l.modelOrientation
          calc
            l.modelOrientation = -(-l.modelOrientation) := hnn.symm
            _ = -l'.modelOrientation := by rw [hm]
        · funext x y
          simp [hs]
    · intro l l' l'' h h'
      rcases h with rfl | ⟨hm, hs⟩
      · exact h'
      · rcases h' with rfl | ⟨hm', hs'⟩
        · right
          exact ⟨hm, hs⟩
        · left
          cases l with
          | mk lm lc ls lcont lcomp =>
            cases l' with
            | mk lm' lc' ls' lcont' lcomp' =>
              cases l'' with
              | mk lm'' lc'' ls'' lcont'' lcomp'' =>
                have hm0 : lm' = -lm := by simpa using hm
                have hs0 : ls' = fun x y ↦ -ls x y := by simpa using hs
                have hm'0 : lm'' = -lm' := by simpa using hm'
                have hs'0 : ls'' = fun x y ↦ -ls' x y := by simpa using hs'
                have hlm : lm'' = lm := by
                  calc
                    lm'' = -lm' := hm'0
                    _ = -(-lm) := by rw [hm0]
                    _ = lm := by
                      exact InvolutiveNeg.neg_neg lm
                have hls : ls'' = ls := by
                  rw [hs'0, hs0]
                  funext x y
                  simp
                cases hlm
                cases hls
                rfl

/-- A manifold orientation is an orientation lift modulo the simultaneous sign flip. -/
def Manifold.Orientation (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (ι : Type*) [Fintype ι] : Type _ :=
  Quotient (OrientationLift.setoid (I := I) (M := M) (ι := ι))

namespace Manifold

/-- Flip the model orientation of a manifold orientation. -/
noncomputable def _root_.TauCeti.Manifold.Orientation.neg
    (o : Manifold.Orientation I M ι) : Manifold.Orientation I M ι :=
  Quotient.map (fun l ↦ { l with modelOrientation := -l.modelOrientation }) (by
    intro l l' h
    rcases h with rfl | ⟨hm, hs⟩
    · exact Or.inl rfl
    · right
      refine ⟨?_, ?_⟩
      · rw [hm]
      · exact hs) o

private theorem _root_.TauCeti.Manifold.Orientation.tangentOrientation_congr
    {l l' : OrientationLift I M ι}
    (h : OrientationLift.setoid.r l l') (x : M) :
    l.tangentOrientation x = l'.tangentOrientation x := by
  rcases h with rfl | ⟨hm, hs⟩
  · rfl
  · have hsign : l'.sign x ⟨x, mem_chart_source H x⟩ =
        -l.sign x ⟨x, mem_chart_source H x⟩ := by
      simp [hs]
    rcases Int.units_eq_one_or (l.sign x ⟨x, mem_chart_source H x⟩) with hone | hneg
    · have hsignneg : -l.sign x ⟨x, mem_chart_source H x⟩ ≠ (1 : ℤˣ) := by
        rw [hone]
        intro h
        have := congrArg ((↑) : ℤˣ → ℤ) h
        norm_num at this
      rw [OrientationLift.tangentOrientation, OrientationLift.tangentOrientation,
        hsign, ite_eq_left hone, ite_eq_right hsignneg, hm, Orientation.map_neg]
      have hnn : -(-(Orientation.map ι (tangentSpaceCastModel I x).symm.toLinearEquiv
          l.modelOrientation)) =
          (Orientation.map ι (tangentSpaceCastModel I x).symm.toLinearEquiv
            l.modelOrientation) := by
        exact @InvolutiveNeg.neg_neg (_root_.Orientation ℝ (TangentSpace I x) ι)
          inferInstance _
      exact hnn.symm
    · have hsignneg : l.sign x ⟨x, mem_chart_source H x⟩ ≠ (1 : ℤˣ) := by
        intro h
        rw [hneg] at h
        have := congrArg ((↑) : ℤˣ → ℤ) h
        norm_num at this
      have hsignpos : -l.sign x ⟨x, mem_chart_source H x⟩ = (1 : ℤˣ) := by
        rw [hneg]
        simp
      rw [OrientationLift.tangentOrientation, OrientationLift.tangentOrientation,
        hsign, ite_eq_right hsignneg, ite_eq_left hsignpos, hm, Orientation.map_neg]

end Manifold

/-- The quotient representative of an orientation lift. -/
def _root_.TauCeti.Manifold.Orientation.mk (l : OrientationLift I M ι) :
    Manifold.Orientation I M ι :=
  Quotient.mk _ l

/-- Eliminate a manifold orientation by choosing an orientation lift representative. -/
theorem _root_.TauCeti.Manifold.Orientation.inductionOn {p : Manifold.Orientation I M ι → Prop}
    (o : Manifold.Orientation I M ι) (h : ∀ l, p (Manifold.Orientation.mk l)) : p o :=
  Quotient.inductionOn o h

/-- Two representatives define the same manifold orientation exactly when they agree up to the
diagonal sign flip. -/
theorem _root_.TauCeti.Manifold.Orientation.mk_eq_mk_iff (l l' : OrientationLift I M ι) :
    Manifold.Orientation.mk l = Manifold.Orientation.mk l' ↔
      l' = l ∨
        (l'.modelOrientation = -l.modelOrientation ∧
          l'.sign = fun x y ↦ -l.sign x y) := by
  exact Quotient.eq'

/-- The tangent-space orientation induced by a quotient orientation. -/
noncomputable def _root_.TauCeti.Manifold.Orientation.orientationAt
    (o : Manifold.Orientation I M ι) (x : M) :
    _root_.Orientation ℝ (TangentSpace I x) ι :=
  Quotient.lift (fun l ↦ l.tangentOrientation x)
    (fun _l _l' h ↦ _root_.TauCeti.Manifold.Orientation.tangentOrientation_congr h x) o

/-- The characteristic equation for the tangent orientation represented by a lift. -/
@[simp]
theorem _root_.TauCeti.Manifold.Orientation.orientationAt_mk
    (l : OrientationLift I M ι) (x : M) :
    _root_.TauCeti.Manifold.Orientation.orientationAt
      (Manifold.Orientation.mk l) x =
      if l.sign x ⟨x, mem_chart_source H x⟩ = 1 then
        Orientation.map ι (tangentSpaceCastModel I x).symm.toLinearEquiv l.modelOrientation
      else
        -Orientation.map ι (tangentSpaceCastModel I x).symm.toLinearEquiv l.modelOrientation := by
  simp [Manifold.Orientation.orientationAt, Manifold.Orientation.mk,
    OrientationLift.tangentOrientation]

/-- Flipping the model orientation reverses every induced tangent orientation. -/
@[simp]
theorem _root_.TauCeti.Manifold.Orientation.orientationAt_neg
    (o : Manifold.Orientation I M ι) (x : M) :
    _root_.TauCeti.Manifold.Orientation.orientationAt o.neg x =
      -_root_.TauCeti.Manifold.Orientation.orientationAt o x := by
  refine Manifold.Orientation.inductionOn
    (p := fun o => Manifold.Orientation.orientationAt o.neg x =
      -Manifold.Orientation.orientationAt o x) o (fun l => ?_)
  let lneg : OrientationLift I M ι := { l with modelOrientation := -l.modelOrientation }
  have hneg : (Manifold.Orientation.mk l).neg = Manifold.Orientation.mk lneg := by
    rfl
  rw [hneg, Manifold.Orientation.orientationAt_mk,
    Manifold.Orientation.orientationAt_mk]
  simp only [lneg, Orientation.map_neg]
  by_cases hsign : l.sign x ⟨x, mem_chart_source H x⟩ = 1 <;> simp [hsign]

end TauCeti
