/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.MappingTorus.Orbit
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.VerticalArea

/-!
# Horizontal curves in a symplectic suspension lie in one leaf

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M`, let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus, with suspension flow
`[t, x] ↦ [t + s, x]` and vector field `T = ∂_t`, and let `X_φ = (ℝ / ℤ)_s × Y_φ`. The horizontal
plane field `H = span(∂_s, T)` of `X_φ` is integrable: its leaves are the products
`(ℝ / ℤ) × γ` of the `s`-circle with one orbit `γ` of the suspension flow.

This file proves that every connected curve tangent to `H` lies in a single leaf. If `u : C → X_φ`
is a differentiable map from a preconnected manifold whose tangent images all lie in `H`, then its
mapping torus component is tangent to `T`, so it stays in one orbit of the suspension flow
(`TauCeti.SmoothMappingTorus.range_subset_orbit_flow_of_mfderiv_mem_span`), and

`u(C) ⊆ (ℝ / ℤ) × γ`, where `γ` is the orbit of the mapping torus component of any value of `u`.

Combined with the classification of curves of zero vertical area as horizontal curves
(`TauCeti.SmoothMappingTorus.integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff`), this
places every compact connected pseudoholomorphic curve of zero `ω_v`-area, for an almost complex
structure of block form along it with vertically tamed restriction, inside one product
`(ℝ / ℤ) × γ`. This locates the curve for the classification of such curves as the tori
`(ℝ / ℤ) × γ` over closed orbits; it does not show that `γ` is closed or that the curve fills its
leaf. Neither compactness of `M` nor nondegeneracy or closedness of `σ` is used.

## Main results

All declarations are in the namespace `TauCeti.SmoothMappingTorus`.

* `range_subset_univ_prod_orbit_flow_of_mfderiv_mem_suspensionHorizontalSubspace`: a
  differentiable map from a preconnected manifold with horizontal tangent images lies in one leaf
  `(ℝ / ℤ) × γ`.
* `range_subset_univ_prod_orbit_flow_of_integralTopForm_eq_zero`: a compact connected
  pseudoholomorphic curve of zero vertical area lies in one leaf.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354 (holomorphic curves in `ℝ × Y_φ` on which `ω_φ`
  vanishes).
* Eleny-Nicoleta Ionel and Thomas H. Parker, *Gromov invariants and symplectic maps*,
  Mathematische Annalen 314 (1999), 127–158 (pseudoholomorphic tori over periodic orbits in
  `S¹ × Y_φ`).
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*} [TopologicalSpace C]
  [ChartedSpace H' C] {u : C → UnitAddCircle × SmoothMappingTorus φ}

/-- **Horizontal curves lie in one leaf.** Let `u` be a differentiable map from a preconnected
manifold into `X_φ = (ℝ / ℤ) × Y_φ` whose tangent images all lie in the horizontal plane
`span(∂_s, T)`. Then the image of `u` lies in the product `(ℝ / ℤ) × γ` of the circle with the
orbit `γ` of the suspension flow through the mapping torus component of any value of `u`. -/
theorem range_subset_univ_prod_orbit_flow_of_mfderiv_mem_suspensionHorizontalSubspace
    [IsManifold I' 1 C] [PreconnectedSpace C]
    (hu : MDifferentiable I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u)
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    (c : C) : range u ⊆ univ ×ˢ (flow φ).orbit (u c).2 := by
  -- The mapping torus component of `u` is tangent to `T`.
  have hT : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod I) (Prod.snd ∘ u) c e ∈ ℝ ∙ timeVectorField φ (u c).2 := by
    intro c e
    have h := mem_suspensionHorizontalSubspace_iff.1 (hH c e)
    rw [Manifold.tangentSpaceProdEquiv_apply] at h
    rwa [mfderiv_comp c mdifferentiableAt_snd (hu c), mfderiv_snd]
  rintro _ ⟨c', rfl⟩
  exact ⟨mem_univ _, range_subset_orbit_flow_of_mfderiv_mem_span
    (fun c ↦ mdifferentiableAt_snd.comp c (hu c)) hT c ⟨c', rfl⟩⟩

variable [IsManifold I' ∞ C] [FiniteDimensional ℝ E'] {σ : SmoothTwoForm I M}
  {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
  {J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
    (UnitAddCircle × SmoothMappingTorus φ)}
  {j : SmoothAlmostComplexStructure I' C} {o : Manifold.Orientation I' C (Fin 2)}

/-- **Curves of zero vertical area lie in one leaf.** Let `u` be a smooth pseudoholomorphic map
from a compact connected surface `C`, oriented so that the frames `(e, j e)` are positive, into
`X_φ` with an almost complex structure of block form along the image of `u` whose vertical
restriction is tamed by `ω_v`. If the vertical area `∫_C u^* ω_v` vanishes, then the image of `u`
lies in the product `(ℝ / ℤ) × γ` of the circle with the orbit `γ` of the suspension flow through
the mapping torus component of any value of `u`. -/
theorem range_subset_univ_prod_orbit_flow_of_integralTopForm_eq_zero [CompactSpace C]
    [PreconnectedSpace C]
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c),
      J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (htame : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) (u c) v (J (u c) v))
    (h0 : integralTopForm o (SmoothForm.mpullback u hu
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 = 0)
    (c : C) : range u ⊆ univ ×ˢ (flow φ).orbit (u c).2 :=
  range_subset_univ_prod_orbit_flow_of_mfderiv_mem_suspensionHorizontalSubspace
    (hu.mdifferentiable (by simp))
    ((integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff hu ho hhol hS hV htame).1 h0) c

end SmoothMappingTorus

end TauCeti
