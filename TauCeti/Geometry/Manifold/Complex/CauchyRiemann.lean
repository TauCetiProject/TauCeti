/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.FDeriv
public import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# The Cauchy–Riemann criterion for manifold maps

A map between complex manifolds is holomorphic exactly when it is real-differentiable and
its real tangent map intertwines the canonical complex structures. Here those structures are
multiplication by `I`, transported through `tangentSpaceCastModel`. The criterion uses the
actual real manifold derivative, not a separately chosen coordinate derivative.

We give pointwise and global criteria, as well as the criterion on an open set. The pointwise
statement needs only real differentiability, not a neighbourhood of continuous derivatives.
No dimension, completeness, or separation assumptions are needed. Since the same charts are
used for the real and complex models, the pointwise criterion even holds on charted spaces
before imposing regularity of their coordinate changes.

The analytic input is the normed-space Cauchy–Riemann criterion and Mathlib's
`HasMFDerivAt` comparison with derivatives in charts.

## References

* D. Huybrechts, *Complex Geometry*, Chapter 1, §1.2.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  {f : M → N} {x : M} {s : Set M}

/-- A map is holomorphic at a point iff it is real-differentiable there and its real tangent
map commutes with multiplication by `I`, after identifying the tangent spaces with the models.
These identifications transport the canonical complex structures to the real tangent spaces. -/
theorem mdifferentiableAt_complex_iff_map_I :
    MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x ↔
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x ∧
        let D := (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x ∘L
          ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _)
        ∀ v, D (Complex.I • v) = Complex.I • D v := by
  have hchart {𝕜 : Type} [NontriviallyNormedField 𝕜]
      [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] :
      MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) f x ↔ ContinuousAt f x ∧
        DifferentiableAt 𝕜 (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x f)
          (extChartAt 𝓘(ℝ, E) x x) := by
    simp only [mdifferentiableAt_iff, mfld_simps, differentiableWithinAt_univ]
  have hD (hr : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x) :
      (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x ∘L
          ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _) =
        fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x f)
          (extChartAt 𝓘(ℝ, E) x x) :=
    (hr.hasMFDerivAt.2.hasFDerivAt (by simp)).fderiv.symm
  constructor
  · intro hf
    have hr := hf.restrictScalars ℝ
    refine ⟨hr, ?_⟩
    dsimp only
    rw [hD hr]
    exact (differentiableAt_complex_iff_map_I.mp ((hchart (𝕜 := ℂ)).mp hf).2).2
  · rintro ⟨hr, hI⟩
    rw [hD hr] at hI
    obtain ⟨hc, hd⟩ := (hchart (𝕜 := ℝ)).mp hr
    exact (hchart (𝕜 := ℂ)).mpr
      ⟨hc, differentiableAt_complex_iff_map_I.mpr ⟨hd, hI⟩⟩

/-- A real-differentiable map is holomorphic iff its real differential intertwines the
canonical complex structures at every point. -/
theorem mdifferentiable_complex_iff_map_I
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) f) :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f ↔ ∀ x,
      let D := (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x ∘L
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _)
      ∀ v, D (Complex.I • v) = Complex.I • D v :=
  ⟨fun h x ↦ (mdifferentiableAt_complex_iff_map_I.mp (h x)).2,
    fun h x ↦ mdifferentiableAt_complex_iff_map_I.mpr ⟨hf x, h x⟩⟩

/-- On an open set, a real-differentiable map is holomorphic iff its real differential
intertwines the canonical complex structures at every point of that set. -/
theorem mdifferentiableOn_complex_iff_map_I (hs : IsOpen s)
    (hf : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, F) f s) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, F) f s ↔ ∀ x ∈ s,
      let D := (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x ∘L
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _)
      ∀ v, D (Complex.I • v) = Complex.I • D v := by
  constructor
  · intro h x hx
    exact (mdifferentiableAt_complex_iff_map_I.mp
      ((h x hx).mdifferentiableAt (hs.mem_nhds hx))).2
  · intro h x hx
    exact (mdifferentiableAt_complex_iff_map_I.mpr
      ⟨(hf x hx).mdifferentiableAt (hs.mem_nhds hx), h x hx⟩).mdifferentiableWithinAt

end TauCeti
