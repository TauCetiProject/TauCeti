/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Coordinate changes for Christoffel maps

This file proves the transformation law for the model-space Christoffel map of a covariant
derivative on the tangent bundle.  The law is stated for independent vector and direction
arguments, so its diagonal specialization is available for the geodesic spray.

## Main results

* `TauCeti.Manifold.christoffelMap_coordChange`: the Christoffel transformation law under a
  change of tangent trivialization.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The geodesic spray".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

public section

open Bundle CovariantDerivative Module Set
open scoped Manifold

noncomputable section

namespace TauCeti.Manifold

section CoordinateChange

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} (b : Basis ι 𝕜 E)
  {x x₀ y : M}
  {cov : (Π z : M, TangentSpace I z) → (Π z : M, TangentSpace I z →L[𝕜] TangentSpace I z)}

section Helpers

include b

variable [Fintype ι] [IsManifold I 2 M]
  {e₀ e₁ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)}
  [MemTrivializationAtlas e₀] [MemTrivializationAtlas e₁]

/-- The coefficients of the field `z ↦ e₁.symmL z V` in the frame of the trivialization `e₀` at `x₀`
are, near `x`, the coordinates of `tangentCoordChange I x x₀ z V`, so its flat derivative in that
frame at `x` is `e₀.symmL x` applied to the derivative of the tangent coordinate change. -/
private theorem frameCovariantDerivative_symmL_coordChange
    (he₀ : e₀ = trivializationAt E (TangentSpace I) x₀)
    (he₁ : e₁ = trivializationAt E (TangentSpace I) x)
    (hx₀ : x ∈ e₀.baseSet) (hx₁ : x ∈ e₁.baseSet)
    (hcmd : MDifferentiableAt I 𝓘(𝕜, E →L[𝕜] E) (tangentCoordChange I x x₀) x)
    (V : TangentSpace I x) :
    frameCovariantDerivative I b e₀ (fun z ↦ e₁.symmL 𝕜 z (V : E)) x =
      (e₀.symmL 𝕜 x).comp (mvfderiv I (fun z ↦ tangentCoordChange I x x₀ z V) x) := by
  have hgA : MDifferentiableAt I 𝓘(𝕜, E) (fun z ↦ tangentCoordChange I x x₀ z V) x :=
    MDifferentiableAt.clm_apply hcmd mdifferentiableAt_const
  refine frameCovariantDerivative_eq_symmL_comp b hgA.hasMFDerivAt (fun i ↦ ?_)
  filter_upwards [e₀.open_baseSet.mem_nhds hx₀, e₁.open_baseSet.mem_nhds hx₁] with z hz₀ hz₁
  rw [e₀.localFrameCoeff_eq_coeff (b := b) (s := fun z ↦ e₁.symmL 𝕜 z (V : E)) hz₀,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e₀ hz₀,
    ← Basis.coord_apply]
  subst he₀ he₁
  rw [continuousLinearMapAt_symmL_coordChange (I := I) (x := x) (x₀ := x₀) (y := z) hz₁ hz₀ V]

/-- The Christoffel forms of a covariant derivative in the frames at `x₀` and `x` differ at `x` by
the derivative of the tangent coordinate change. -/
private theorem christoffelForm_coordChange
    (he₀ : e₀ = trivializationAt E (TangentSpace I) x₀)
    (he₁ : e₁ = trivializationAt E (TangentSpace I) x)
    (hx₀ : x ∈ e₀.baseSet) (hx₁ : x ∈ e₁.baseSet)
    (hcmd : MDifferentiableAt I 𝓘(𝕜, E →L[𝕜] E) (tangentCoordChange I x x₀) x)
    (hcov : IsCovariantDerivativeOn E cov e₀.baseSet)
    (hcov' : IsCovariantDerivativeOn E cov e₁.baseSet) (V : TangentSpace I x) :
    christoffelForm b hcov x V = christoffelForm b hcov' x V
      - (e₀.symmL 𝕜 x).comp (mvfderiv I (fun z ↦ tangentCoordChange I x x₀ z V) x) := by
  have hσ : MDiffAt (T% (fun z ↦ e₁.symmL 𝕜 z (V : E))) x := by
    refine (((contMDiffOn_symm_baseSet (n := 1) (e := e₁) (V : E)).mdifferentiableOn
      one_ne_zero).mdifferentiableAt (e₁.open_baseSet.mem_nhds hx₁)).congr_of_eventuallyEq ?_
    filter_upwards [e₁.open_baseSet.mem_nhds hx₁] with z hz
    exact congrArg (TotalSpace.mk' E z) (e₁.symmL_apply hz _)
  have hσx : e₁.symmL 𝕜 x V = V := by
    subst he₁
    exact symmL_trivializationAt_self (I := I) x V
  have hp₀ := covariantDerivative_eq_add_christoffelForm b hcov hx₀ hσ
  have hp₁ := covariantDerivative_eq_add_christoffelForm b hcov' hx₁ hσ
  rw [frameCovariantDerivative_symmL_coordChange b he₀ he₁ hx₀ hx₁ hcmd V, hσx] at hp₀
  rw [frameCovariantDerivative_symmL_const b hx₁ (V : E), hσx] at hp₁
  linear_combination (norm := module) (hp₀.symm.trans hp₁)

/-- Reading the Christoffel form in the frame at `x` through the trivialization at `x₀` gives the
tangent coordinate change of the Christoffel map. -/
private theorem continuousLinearMapAt_christoffelForm
    (he₀ : e₀ = trivializationAt E (TangentSpace I) x₀)
    (he₁ : e₁ = trivializationAt E (TangentSpace I) x)
    (hx₀ : x ∈ e₀.baseSet) (hx₁ : x ∈ e₁.baseSet)
    (hcov' : IsCovariantDerivativeOn E cov e₁.baseSet) (U V : TangentSpace I x) :
    e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov' x V U) =
      tangentCoordChange I x x₀ x (christoffelMap b hcov' x V U) := by
  have hV : e₁.symmL 𝕜 x V = V := by
    subst he₁
    exact symmL_trivializationAt_self (I := I) x V
  have hU : e₁.symmL 𝕜 x U = U := by
    subst he₁
    exact symmL_trivializationAt_self (I := I) x U
  have h1 : e₁.symmL 𝕜 x (christoffelMap b hcov' x V U) = christoffelForm b hcov' x V U := by
    rw [christoffelMap_apply b hcov' hx₁ (V : E) (U : E),
      e₁.symmL_continuousLinearMapAt (R := 𝕜) hx₁]
    simp only [hV, hU]
  rw [← h1]
  subst he₀ he₁
  exact continuousLinearMapAt_symmL_coordChange (I := I) (x := x) (x₀ := x₀) (y := x)
    (mem_chart_source H x) hx₀ _

end Helpers

/-- **The Christoffel transformation law.**  The Christoffel map of a covariant derivative on the
tangent bundle, read in the trivialization centred at `x₀` and evaluated at the `x₀`-coordinates
of a tangent vector `V` and direction `U`, is the pushforward by
`tangentCoordChange I x x₀ x` of its value read in the trivialization centred at `x`, less the
derivative of the tangent coordinate change between the two charts along `U` applied to `V`. -/
theorem christoffelMap_coordChange [Fintype ι] [IsManifold I 2 M]
    : haveI : IsManifold I 1 M := IsManifold.of_le (n := 2) one_le_two
      ∀ (_hx₀ : x ∈ (extChartAt I x₀).source) (U V : TangentSpace I x)
        (hcov : IsCovariantDerivativeOn E cov
          (trivializationAt E (TangentSpace I) x₀).baseSet)
        (hcov' : IsCovariantDerivativeOn E cov
          (trivializationAt E (TangentSpace I) x).baseSet),
        christoffelMap b hcov x (tangentCoordChange I x x₀ x V)
            (tangentCoordChange I x x₀ x U)
          = tangentCoordChange I x x₀ x (christoffelMap b hcov' x V U)
            - mvfderiv I (fun z => tangentCoordChange I x x₀ z V) x U := by
  have hI : IsManifold I 1 M := IsManifold.of_le (n := 2) one_le_two
  intro hx₀ U V hcov hcov'
  set e₀ := trivializationAt E (TangentSpace I) x₀ with he₀
  set e₁ := trivializationAt E (TangentSpace I) x with he₁
  have hx₀c : x ∈ (chartAt H x₀).source := by
    rw [← OpenPartialHomeomorph.extend_source (f := chartAt H x₀) (I := I)]
    exact hx₀
  have hx₀' : x ∈ e₀.baseSet := hx₀c
  have hx₁' : x ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have hcmd : MDifferentiableAt I 𝓘(𝕜, E →L[𝕜] E) (tangentCoordChange I x x₀) x := by
    -- the `n + 1` regularity hypothesis of the polymorphic theorem, read at `n := 1`
    have : IsManifold I (1 + 1) M := inferInstanceAs (IsManifold I 2 M)
    exact (contMDiffAt_tangentCoordChange (I := I) (n := 1) (x := x) (y := x₀)
      hx₀).mdifferentiableAt one_ne_zero
  have hform := christoffelForm_coordChange b he₀ he₁ hx₀' hx₁' hcmd hcov hcov' V
  have hmap' := continuousLinearMapAt_christoffelForm b he₀ he₁ hx₀' hx₁' hcov' U V
  -- read both Christoffel forms in the model space
  have hw : ∀ u : E, e₀.continuousLinearMapAt 𝕜 x u = tangentCoordChange I x x₀ x u := by
    intro u
    simp only [he₀]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := I) (b₀ := x₀) (b := x) hx₀c]
    rfl
  have hsymmL : ∀ u : E, e₀.symmL 𝕜 x (tangentCoordChange I x x₀ x u) = u := by
    intro u
    rw [← hw u, e₀.symmL_continuousLinearMapAt (R := 𝕜) hx₀' u]
  have hfinal : e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov x V U)
      + mvfderiv I (fun z => tangentCoordChange I x x₀ z V) x U =
        e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov' x V U) := by
    rw [hform, sub_apply, map_sub, ContinuousLinearMap.comp_apply,
      e₀.continuousLinearMapAt_symmL (R := 𝕜) hx₀']
    abel
  calc christoffelMap b hcov x (tangentCoordChange I x x₀ x V)
        (tangentCoordChange I x x₀ x U) =
      e₀.continuousLinearMapAt 𝕜 x (christoffelForm b hcov x V U) := by
        rw [christoffelMap_apply b hcov hx₀', hsymmL (V : E), hsymmL (U : E)]
    _ = tangentCoordChange I x x₀ x (christoffelMap b hcov' x V U)
        - mvfderiv I (fun z => tangentCoordChange I x x₀ z V) x U := by
        rw [← hmap']
        exact eq_sub_iff_add_eq.mpr hfinal

end CoordinateChange

end TauCeti.Manifold
