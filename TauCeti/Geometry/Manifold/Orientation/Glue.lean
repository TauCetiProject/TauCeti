/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Gluing orientations along local diffeomorphisms

Let `f : M → X` and `g : N → X` be injective `C^n` local diffeomorphisms, `n ≠ 0`, whose ranges
cover `X`, and let `o₁` and `o₂` be orientations of `M` and `N`. If, at every pair of points
`x : M` and `y : N` with `f x = g y`, the derivatives of `f` and `g` carry the tangent orientations
of `o₁` and `o₂` to the same orientation of the tangent space of `X`, then `X` carries an
orientation such that `f` and `g` preserve orientation everywhere, from `o₁` and `o₂` to it
(`TauCeti.Manifold.Orientation.glue`).

Its tangent orientation at a point of `X` is carried from `o₁` or `o₂` through a preimage under
`f` or `g`; the hypothesis makes this independent of the preimage, and the tangent orientations are
locally constant because near the image of a point they are carried from an orientation by a local
diffeomorphism (`IsLocalDiffeomorphAt.eventually_mapOrientation_eq`).

This is how manifolds glued from two oriented pieces, such as connected sums and composites of
cobordisms, are oriented.

## Main definitions

* `TauCeti.Manifold.Orientation.glue`: the orientation glued from orientations of the two pieces.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_glue_left`,
  `TauCeti.Manifold.Orientation.isOrientationPreservingAt_glue_right`: the two local
  diffeomorphisms preserve orientation from `o₁` and `o₂` to the glued orientation.
* `TauCeti.Manifold.Orientation.eq_glue_iff`: this property characterizes the glued orientation.
* `TauCeti.Manifold.Orientation.map_orientationAt_eq_of_comp_eventuallyEq`: the hypothesis of
  `glue` at a point of the overlap, when both pieces are read off a common oriented source by
  orientation-preserving maps.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer (2013), Chapter 15 (orientations, and their pullbacks along local
  diffeomorphisms).
-/

public section

noncomputable section

open Set Function Filter Module
open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞} [NeZero n]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
  {ι : Type*} [Fintype ι] {f : M → X} {g : N → X}
  (hf : IsLocalDiffeomorph I I n f) (hg : IsLocalDiffeomorph I I n g)
  (hf' : Injective f) (hg' : Injective g) (hfg : range f ∪ range g = univ)
  (o₁ : Orientation I M ι) (o₂ : Orientation I N ι)

/-- The tangent orientation of `X` at `h y`, carried from `o` by the derivative of `h` at `y`. -/
private def carry {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I 1 Y]
    {h : Y → X} (hh : IsLocalDiffeomorph I I n h) (o : Orientation I Y ι) (y : Y) :
    _root_.Orientation ℝ (TangentSpace I (h y)) ι :=
  _root_.Orientation.map ι ((hh y).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv
    (o.orientationAt y)

omit [IsManifold I 1 X] in
/-- An injective local diffeomorphism carries an orientation to the same tangent orientation at
two points with the same image. -/
private theorem carry_eq_of_eq {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
    [IsManifold I 1 Y] {h : Y → X} (hh : IsLocalDiffeomorph I I n h) (hh' : Injective h)
    (o : Orientation I Y ι) {y y' : Y} (hy : h y = h y') : carry hh o y = carry hh o y' := by
  obtain rfl := hh' hy
  rfl

open Classical in
/-- The tangent orientation of `X` at `p`, carried from `o₁` through a preimage under `f` if there
is one, and from `o₂` through a preimage under `g` otherwise. -/
private def glueAt (p : X) : _root_.Orientation ℝ (TangentSpace I p) ι :=
  if hp : p ∈ range f then carry hf o₁ hp.choose
  else if hq : p ∈ range g then carry hg o₂ hq.choose
  -- The ranges of `f` and `g` cover `X`, so this case does not occur.
  else ((finBasisOfFinrankEq ℝ E o₁.card_eq.symm).reindex (Fintype.equivFin ι).symm).orientation

variable {o₁ o₂}
  (h : ∀ x y, f x = g y →
    _root_.Orientation.map ι ((hf x).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv
        (o₁.orientationAt x) =
      _root_.Orientation.map ι ((hg y).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv
        (o₂.orientationAt y))

omit [IsManifold I 1 X] in
include hf' in
private theorem glueAt_left (x : M) : glueAt hf hg o₁ o₂ (f x) = carry hf o₁ x := by
  have hp : f x ∈ range f := mem_range_self x
  simp only [glueAt, hp, ↓reduceDIte]
  exact carry_eq_of_eq hf hf' o₁ hp.choose_spec

omit [IsManifold I 1 X] in
include hg' h in
private theorem glueAt_right (y : N) : glueAt hf hg o₁ o₂ (g y) = carry hg o₂ y := by
  have hq : g y ∈ range g := mem_range_self y
  by_cases hp : g y ∈ range f
  · simp only [glueAt, hp, ↓reduceDIte]
    exact h _ y hp.choose_spec
  · simp only [glueAt, hp, hq, ↓reduceDIte]
    exact carry_eq_of_eq hg hg' o₂ hq.choose_spec

open Classical in
/-- **Gluing orientations.** Let `f : M → X` and `g : N → X` be injective `C^n` local
diffeomorphisms, `n ≠ 0`, whose ranges cover `X`, and let `o₁` and `o₂` orient `M` and `N`. If at
any `x` and `y` with `f x = g y` the derivatives of `f` and `g` carry the tangent orientations of
`o₁` and `o₂` to the same orientation, then `X` carries the orientation whose tangent orientation is
carried from `o₁` along `f` and from `o₂` along `g`
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_glue_left`,
`TauCeti.Manifold.Orientation.isOrientationPreservingAt_glue_right`). -/
def glue : Orientation I X ι :=
  -- The model orientation only selects a representative lift, which the quotient forgets.
  ofVectorBundleOrientation
    (((finBasisOfFinrankEq ℝ E o₁.card_eq.symm).reindex (Fintype.equivFin ι).symm).orientation)
    o₁.card_eq
    ⟨glueAt hf hg o₁ o₂, fun b ↦ by
      -- Near the image of a point of `M` or `N`, the tangent orientations are carried from `o₁`
      -- or `o₂` by a local diffeomorphism, so they are locally constant.
      obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := hfg.symm ▸ mem_univ b
      · exact (hf x).eventually_mapOrientation_eq o₁ (glueAt hf hg o₁ o₂)
          (.of_forall fun x' ↦ ⟨(hf x').mfderivToContinuousLinearEquiv (NeZero.ne n), rfl,
            (glueAt_left hf hg hf' x').symm⟩)
      · exact (hg y).eventually_mapOrientation_eq o₂ (glueAt hf hg o₁ o₂)
          (.of_forall fun y' ↦ ⟨(hg y').mfderivToContinuousLinearEquiv (NeZero.ne n), rfl,
            (glueAt_right hf hg hg' h y').symm⟩)⟩

/-- `f` preserves orientation from `o₁` to the glued orientation. -/
theorem isOrientationPreservingAt_glue_left (x : M) :
    IsOrientationPreservingAt o₁ (glue hf hg hf' hg' hfg h) f x := by
  refine (isOrientationPreservingAt_iff_of_coe_eq _ _ _ x
    ((hf x).mfderivToContinuousLinearEquiv (NeZero.ne n)) rfl).2 ?_
  rw [glue, orientationAt_ofVectorBundleOrientation]
  exact (glueAt_left hf hg hf' x).symm

/-- `g` preserves orientation from `o₂` to the glued orientation. -/
theorem isOrientationPreservingAt_glue_right (y : N) :
    IsOrientationPreservingAt o₂ (glue hf hg hf' hg' hfg h) g y := by
  refine (isOrientationPreservingAt_iff_of_coe_eq _ _ _ y
    ((hg y).mfderivToContinuousLinearEquiv (NeZero.ne n)) rfl).2 ?_
  rw [glue, orientationAt_ofVectorBundleOrientation]
  exact (glueAt_right hf hg hg' h y).symm

/-- **The glued orientation is characterized by the pieces.** An orientation of `X` is the glued
orientation exactly when `f` and `g` preserve orientation from `o₁` and `o₂` to it. -/
theorem eq_glue_iff {o : Orientation I X ι} :
    o = glue hf hg hf' hg' hfg h ↔
      (∀ x, IsOrientationPreservingAt o₁ o f x) ∧ ∀ y, IsOrientationPreservingAt o₂ o g y := by
  refine ⟨?_, fun ⟨hl, hr⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨isOrientationPreservingAt_glue_left hf hg hf' hg' hfg h,
      isOrientationPreservingAt_glue_right hf hg hf' hg' hfg h⟩
  ext p
  obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := hfg.symm ▸ mem_univ p
  · exact (hl x).orientationAt_eq (isOrientationPreservingAt_glue_left hf hg hf' hg' hfg h x)
  · exact (hr y).orientationAt_eq (isOrientationPreservingAt_glue_right hf hg hf' hg' hfg h y)

omit [IsManifold I 1 X] in
/-- **Agreement through a common source.** Let `ρ₁ : P → M` and `ρ₂ : P → N` be differentiable at
`w` and preserve orientation there from an orientation `oP` of `P` to `o₁` and `o₂`. If
`f ∘ ρ₁ = g ∘ ρ₂` near `w`, then the derivatives of `f` and `g` carry `o₁` and `o₂` to the same
tangent orientation at `f (ρ₁ w) = g (ρ₂ w)`. This is how the hypothesis of
`TauCeti.Manifold.Orientation.glue` is checked on an overlap read off a common source. -/
theorem map_orientationAt_eq_of_comp_eventuallyEq {E' H' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
    [IsManifold I' 1 P] {oP : Orientation I' P ι}
    {ρ₁ : P → M} {ρ₂ : P → N} {w : P} (hρ₁ : IsOrientationPreservingAt oP o₁ ρ₁ w)
    (hρ₂ : IsOrientationPreservingAt oP o₂ ρ₂ w) (hρ₁' : MDifferentiableAt I' I ρ₁ w)
    (hρ₂' : MDifferentiableAt I' I ρ₂ w) (hρ : f ∘ ρ₁ =ᶠ[𝓝 w] g ∘ ρ₂) :
    _root_.Orientation.map ι
        ((hf (ρ₁ w)).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv
        (o₁.orientationAt (ρ₁ w)) =
      _root_.Orientation.map ι
        ((hg (ρ₂ w)).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv
        (o₂.orientationAt (ρ₂ w)) := by
  obtain ⟨A, hA, hAo⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 hρ₁
  obtain ⟨B, hB, hBo⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 hρ₂
  -- The two composites of derivatives are derivatives of the same map out of `P`.
  have hL : A.toLinearEquiv.trans
        ((hf (ρ₁ w)).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv =
      B.toLinearEquiv.trans
        ((hg (ρ₂ w)).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv := by
    have h₁ := mfderiv_comp w ((hf (ρ₁ w)).mdifferentiableAt (NeZero.ne n)) hρ₁'
    have h₂ := mfderiv_comp w ((hg (ρ₂ w)).mdifferentiableAt (NeZero.ne n)) hρ₂'
    rw [hρ.mfderiv_eq, h₂, ← hA, ← hB] at h₁
    ext v
    exact (congrArg (fun L ↦ L v) h₁).symm
  rw [← hAo, ← hBo, ← _root_.Orientation.map_trans, ← _root_.Orientation.map_trans]
  exact congrArg (fun L ↦ _root_.Orientation.map ι L (oP.orientationAt w)) hL

end TauCeti.Manifold.Orientation
