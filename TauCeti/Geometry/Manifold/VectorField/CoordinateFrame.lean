/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Coordinate frames of manifold charts

The canonical trivialization of the tangent bundle at `x₀` is read off the chart at `x₀`, so the
local frame it induces from a basis `b` of the model space is the classical coordinate frame of
that chart.  This file identifies that frame with the pullback of constant model-space vector
fields and proves that its vector fields commute.

## Main results

* `TauCeti.Manifold.eqOn_localFrame_trivializationAt_mpullbackWithin`: over the chart source, the
  local frame of the canonical trivialization at `x₀` is the pullback along the extended chart of
  a constant model-space vector field.
* `TauCeti.Manifold.mlieBracket_localFrame_trivializationAt`: the coordinate frame commutes.
-/

public section

open Bundle Filter Manifold Module Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {x : M}

section Frame

variable [IsManifold I 1 M]

/-- **The local frame of the canonical trivialization is the coordinate frame of the chart.**  Over
the source of the chart at `x₀`, the `i`-th section of the local frame induced by a basis `b` is
the pullback, along the extended chart, of the constant model-space vector field with value
`b i`. -/
theorem eqOn_localFrame_trivializationAt_mpullbackWithin (b : Basis ι 𝕜 E) (x₀ : M) (i : ι) :
    EqOn ((trivializationAt E (TangentSpace I) x₀).localFrame b i)
      (mpullbackWithin I 𝓘(𝕜, E) (extChartAt I x₀)
        (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z) (extChartAt I x₀).source)
      (extChartAt I x₀).source := by
  intro y hy
  -- No rewrite reaches the pullback here: `TangentSpace 𝓘(𝕜, E) z` is only definitionally the
  -- model space, so the constant field makes the goal ill-typed at `implicit` transparency.
  have hpull : mpullbackWithin I 𝓘(𝕜, E) (extChartAt I x₀)
      (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z) (extChartAt I x₀).source y =
      (mfderiv[(extChartAt I x₀).source] (extChartAt I x₀) y).inverse (b i) := rfl
  rw [hpull, mfderivWithin_of_isOpen (isOpen_extChartAt_source x₀) hy,
    inverse_mfderiv_extChartAt x₀ hy]
  exact (symmL_basis_eq_localFrame b (by simpa using hy) i).symm

end Frame

variable [CompleteSpace E] [IsManifold I (minSmoothness 𝕜 2) M]

/-- **The coordinate frame of a chart commutes.**  The local frame that a basis of the model space
induces through the canonical tangent-bundle trivialization at `x₀` has vanishing Lie brackets on
the source of the chart at `x₀`. -/
theorem mlieBracket_localFrame_trivializationAt (b : Basis ι 𝕜 E) (x₀ : M)
    (hx : x ∈ (extChartAt I x₀).source) (i j : ι) :
    mlieBracket I ((trivializationAt E (TangentSpace I) x₀).localFrame b i)
      ((trivializationAt E (TangentSpace I) x₀).localFrame b j) x = 0 := by
  have hsopen : IsOpen (extChartAt I x₀).source := isOpen_extChartAt_source x₀
  -- Naturality of the manifold Lie bracket under the pullback along the chart at `x₀`.
  have key := mpullbackWithin_mlieBracketWithin (I := I) (I' := 𝓘(𝕜, E))
    (f := (extChartAt I x₀ : M → E))
    (V := (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z))
    (W := (fun _ ↦ b j : Π z : E, TangentSpace 𝓘(𝕜, E) z))
    (s := (extChartAt I x₀).source) (t := univ) (x₀ := x) (n := minSmoothness 𝕜 2)
    (hV := ((contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt (n := 1)).2
      contDiffWithinAt_const).mdifferentiableWithinAt one_ne_zero)
    (hW := ((contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt (n := 1)).2
      contDiffWithinAt_const).mdifferentiableWithinAt one_ne_zero)
    (hu := hsopen.uniqueMDiffOn)
    (hf := (contMDiffAt_extChartAt' (by simpa using hx)).contMDiffWithinAt)
    (hx₀ := hx) (hn := le_rfl) (hst := by simp)
    (h'x₀ := by rw [hsopen.interior_eq]; exact subset_closure hx)
  -- Constant vector fields on the model space commute.
  have hconst : mlieBracketWithin 𝓘(𝕜, E)
      (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z)
      (fun _ ↦ b j : Π z : E, TangentSpace 𝓘(𝕜, E) z) univ =
      (0 : Π z : E, TangentSpace 𝓘(𝕜, E) z) := by
    refine (mlieBracketWithin_univ (I := 𝓘(𝕜, E))
      (V := (fun _ ↦ b i : Π z : E, TangentSpace 𝓘(𝕜, E) z))
      (W := (fun _ ↦ b j : Π z : E, TangentSpace 𝓘(𝕜, E) z))).trans ?_
    funext z
    exact mlieBracket_const_model_space (𝕜 := 𝕜) (F := E) (b i) (b j) z
  rw [hconst] at key
  -- As above, the pullback of the zero field is reached definitionally rather than by rewriting.
  have hpull : mpullbackWithin I 𝓘(𝕜, E) (extChartAt I x₀)
      (0 : Π z : E, TangentSpace 𝓘(𝕜, E) z) (extChartAt I x₀).source x =
      (mfderiv[(extChartAt I x₀).source] (extChartAt I x₀) x).inverse 0 := rfl
  rw [hpull, map_zero] at key
  rw [← mlieBracketWithin_of_isOpen (I := I) hsopen hx,
    mlieBracketWithin_congr' (eqOn_localFrame_trivializationAt_mpullbackWithin b x₀ i)
      (eqOn_localFrame_trivializationAt_mpullbackWithin b x₀ j) hx]
  exact key.symm

end TauCeti.Manifold
