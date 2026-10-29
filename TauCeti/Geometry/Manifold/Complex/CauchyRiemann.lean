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

We give within-set, pointwise, global, and setwise criteria. The within-set criterion requires
unique real derivatives, not openness. The pointwise statement needs only real differentiability,
not a neighbourhood of continuous derivatives.
No dimension, completeness, or separation assumptions are needed. Since the same charts are
used for the real and complex models, the pointwise criterion even holds on charted spaces
before imposing regularity of their coordinate changes.

The analytic input is the normed-space Cauchy–Riemann criterion and Mathlib's
`HasMFDerivWithinAt` comparison with derivatives in charts.

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

/-- Within a set with unique real derivatives, complex differentiability is equivalent to
real differentiability and the real tangent map commuting with multiplication by `I`, after
identifying tangent spaces with the models using `tangentSpaceCastModel`. -/
theorem mdifferentiableWithinAt_complex_iff_map_I_smul
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, E) s x) :
    MDifferentiableWithinAt 𝓘(ℂ, E) 𝓘(ℂ, F) f s x ↔
      MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, F) f s x ∧
        let D := (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
          mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, F) f s x ∘L
          ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _)
        ∀ v, D (Complex.I • v) = Complex.I • D v := by
  have hchart {𝕜 : Type} [NontriviallyNormedField 𝕜]
      [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] :
      MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) f s x ↔ ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x f)
          ((extChartAt 𝓘(ℝ, E) x).symm ⁻¹' s) (extChartAt 𝓘(ℝ, E) x x) := by
    simp only [mdifferentiableWithinAt_iff', mfld_simps]
  have hs' : UniqueDiffWithinAt ℝ ((extChartAt 𝓘(ℝ, E) x).symm ⁻¹' s)
      (extChartAt 𝓘(ℝ, E) x x) := by
    simpa only [UniqueMDiffWithinAt, mfld_simps] using hs
  have hD (hr : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, F) f s x) :
      (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
          mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, F) f s x ∘L
          ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _) =
        fderivWithin ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x f)
          ((extChartAt 𝓘(ℝ, E) x).symm ⁻¹' s) (extChartAt 𝓘(ℝ, E) x x) := by
    have h := hr.hasMFDerivWithinAt.2
    simp only [mfld_simps] at h
    exact (h.fderivWithin hs').symm
  constructor
  · intro hf
    have hr := hf.restrictScalars ℝ
    refine ⟨hr, ?_⟩
    dsimp only
    rw [hD hr]
    exact ((differentiableWithinAt_complex_iff_map_I_smul hs').mp
      ((hchart (𝕜 := ℂ)).mp hf).2).2
  · rintro ⟨hr, hI⟩
    rw [hD hr] at hI
    obtain ⟨hc, hd⟩ := (hchart (𝕜 := ℝ)).mp hr
    exact (hchart (𝕜 := ℂ)).mpr
      ⟨hc, (differentiableWithinAt_complex_iff_map_I_smul hs').mpr ⟨hd, hI⟩⟩

/-- A map is complex-differentiable at a point iff it is real-differentiable there and its
real tangent map commutes with multiplication by `I`, after identifying tangent spaces with
the models. These identifications transport the canonical complex structures to real tangents. -/
theorem mdifferentiableAt_complex_iff_map_I_smul :
    MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x ↔
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x ∧
        let D := (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x ∘L
          ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _)
        ∀ v, D (Complex.I • v) = Complex.I • D v := by
  simpa only [mdifferentiableWithinAt_univ, mfderivWithin_univ] using
    (mdifferentiableWithinAt_complex_iff_map_I_smul
      (f := f) (uniqueMDiffWithinAt_univ 𝓘(ℝ, E)))

/-- A real-differentiable map is holomorphic iff its real differential intertwines the
canonical complex structures at every point. -/
theorem mdifferentiable_complex_iff_map_I_smul
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) f) :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f ↔ ∀ x,
      let D := (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x ∘L
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _)
      ∀ v, D (Complex.I • v) = Complex.I • D v :=
  ⟨fun h x ↦ (mdifferentiableAt_complex_iff_map_I_smul.mp (h x)).2,
    fun h x ↦ mdifferentiableAt_complex_iff_map_I_smul.mpr ⟨hf x, h x⟩⟩

/-- On a set with unique real derivatives, a real-differentiable map is complex-differentiable
iff its real differential within the set intertwines the canonical complex structures. -/
theorem mdifferentiableOn_complex_iff_map_I_smul (hs : UniqueMDiffOn 𝓘(ℝ, E) s)
    (hf : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, F) f s) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, F) f s ↔ ∀ x ∈ s,
      let D := (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
        mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, F) f s x ∘L
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _)
      ∀ v, D (Complex.I • v) = Complex.I • D v :=
  ⟨fun h x hx ↦ (mdifferentiableWithinAt_complex_iff_map_I_smul (hs x hx)).mp (h x hx) |>.2,
    fun h x hx ↦ (mdifferentiableWithinAt_complex_iff_map_I_smul (hs x hx)).mpr
      ⟨hf x hx, h x hx⟩⟩

/-- On an open set, a real-differentiable map is holomorphic iff its real differential
intertwines the canonical complex structures at every point of that set. -/
theorem mdifferentiableOn_complex_iff_map_I_smul_of_isOpen (hs : IsOpen s)
    (hf : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, F) f s) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, F) f s ↔ ∀ x ∈ s,
      let D := (tangentSpaceCastModel 𝓘(ℝ, F) (f x) : _ →L[ℝ] F) ∘L
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x ∘L
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm : E →L[ℝ] _)
      ∀ v, D (Complex.I • v) = Complex.I • D v := by
  rw [mdifferentiableOn_complex_iff_map_I_smul hs.uniqueMDiffOn hf]
  apply forall₂_congr
  intro x hx
  rw [mfderivWithin_eq_mfderiv (hs.uniqueMDiffWithinAt hx)
    ((hf x hx).mdifferentiableAt (hs.mem_nhds hx))]

end TauCeti
