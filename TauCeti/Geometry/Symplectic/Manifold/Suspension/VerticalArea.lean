/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Horizontal

/-!
# The vertical area of pseudoholomorphic curves in a symplectic suspension

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M` preserving a
two-form `σ`, let `X_φ = (ℝ / ℤ)_s × Y_φ` be the product of a circle with the smooth mapping torus
of `φ`, and let `ω_v` be the fiber form `σ_v` pulled back to `X_φ`. Let `u : (C, j) → (X_φ, J)` be
a smooth pseudoholomorphic map from a surface, where along the image of `u` the almost complex
structure `J` has block form (`J ∂_s = T`, and `J` preserves the vertical space `V`) and its
vertical restriction is tamed by `ω_v`. Orient `C` so that every frame `(e, j e)` is positive.

Pointwise, `(u^* ω_v)(e, j e) = ω_v((du e)_V, J (du e)_V) ≥ 0`, with equality exactly when `du e`
lies in the horizontal plane `span(∂_s, T)`
(`TauCeti.SmoothMappingTorus.eval₂_mpullback_mpullback_snd_fiberForm_apply_eq_zero_iff`). On a
positively oriented frame `(a, b)` of a tangent plane of `C`, the top form `u^* ω_v` is
`(u^* ω_v)(a, j a)` times the positive determinant of `(a, b)` in the frame `(a, j a)`. So
`u^* ω_v` is a nonnegative top form
(`TauCeti.SmoothMappingTorus.mpullback_mpullback_snd_fiberForm_apply_basis_nonneg`), and the
*vertical area* `∫_C u^* ω_v` is nonnegative. When `C` is compact, the integral of a continuous
nonnegative top form is positive as soon as the form is positive somewhere, so

`∫_C u^* ω_v = 0 ↔ du (T_c C) ⊆ span(∂_s, T)` for every `c ∈ C`.

Thus a compact pseudoholomorphic curve of zero vertical area is tangent to the horizontal plane
everywhere, and its tangent plane at each immersed point is exactly `span(∂_s, T)`. Conversely,
`ω_v` pulls back to zero along every map with horizontal tangent images
(`TauCeti.SmoothMappingTorus.mpullback_mpullback_snd_fiberForm_eq_zero`).
This is the integration step in the classification of compact pseudoholomorphic curves in `X_φ`
with zero `ω_v`-area as the tori `(ℝ / ℤ) × γ` over closed orbits `γ` of the suspension flow.
Neither compactness of `M` nor nondegeneracy or closedness of `σ` is used.

## Main results

* `TauCeti.SmoothMappingTorus.integralTopForm_mpullback_mpullback_snd_fiberForm_nonneg`: the
  vertical area is nonnegative.
* `TauCeti.SmoothMappingTorus.integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff`: for a
  compact source, the vertical area vanishes exactly when every tangent image is horizontal.
* `TauCeti.SmoothMappingTorus.range_mfderiv_eq_suspensionHorizontalSubspace`: for a compact source
  of zero vertical area, the tangent image at every immersed point is the horizontal plane.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354 (nonnegativity of `ω_φ` on holomorphic curves in
  `ℝ × Y_φ`, and the curves on which it vanishes).
* Eleny-Nicoleta Ionel and Thomas H. Parker, *Gromov invariants and symplectic maps*,
  Mathematische Annalen 314 (1999), 127–158 (pseudoholomorphic tori over periodic orbits in
  `S¹ × Y_φ`).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 16.6 (positivity of the integral).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C] {u : C → UnitAddCircle × SmoothMappingTorus φ}

variable [FiniteDimensional ℝ E'] {σ : SmoothTwoForm I M}
  {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
  {J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
    (UnitAddCircle × SmoothMappingTorus φ)}
  {j : SmoothAlmostComplexStructure I' C} {o : Manifold.Orientation I' C (Fin 2)}

/-- **Nonnegativity of the vertical area.** Let `u` be a smooth pseudoholomorphic map from a
surface `C`, oriented so that the frames `(e, j e)` are positive, into `X_φ` with an almost complex
structure of block form along the image of `u` whose vertical restriction is tamed by `ω_v`. Then
the vertical area `∫_C u^* ω_v` is nonnegative. -/
theorem integralTopForm_mpullback_mpullback_snd_fiberForm_nonneg
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c),
      J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (htame : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) (u c) v (J (u c) v)) :
    0 ≤ integralTopForm o (SmoothForm.mpullback u hu
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 :=
  integralTopForm_nonneg o fun c b hb ↦
    mpullback_mpullback_snd_fiberForm_apply_basis_nonneg hu ho (hhol c) (hS c) (hV c) (htame c) b hb

/-- **Curves of zero vertical area are horizontal.** Let `u` be a smooth pseudoholomorphic map
from a compact surface `C`, oriented so that the frames `(e, j e)` are positive, into `X_φ` with an
almost complex structure of block form along the image of `u` whose vertical restriction is tamed
by `ω_v`. Then the vertical area `∫_C u^* ω_v` vanishes exactly when every tangent image
`du (T_c C)` lies in the horizontal plane `span(∂_s, T)`. -/
theorem integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff [CompactSpace C]
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c),
      J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (htame : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) (u c) v (J (u c) v)) :
    integralTopForm o (SmoothForm.mpullback u hu
        (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 = 0 ↔
      ∀ c (e : TangentSpace I' c),
        mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c) := by
  refine ⟨fun h0 ↦ ?_, fun hH ↦ ?_⟩
  · by_contra hne
    push Not at hne
    obtain ⟨c, e, he⟩ := hne
    have he0 : e ≠ 0 := by
      rintro rfl
      exact he (by simp)
    -- The density is positive on the frame `b₀ = (e, j e)`, which is positively oriented.
    set b₀ := basisOfLinearIndependentOfCardEqFinrank
      ((j.almostComplexStructureAt c).linearIndependent_pair he0)
      (by simpa using (o.finrank_tangentSpace_eq c).symm)
    have hb₀ : ⇑b₀ = ![e, j c e] := by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank,
        SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    have hpos : 0 < (SmoothForm.mpullback u hu
        (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 c b₀ := by
      rw [hb₀, ← SmoothBundleForm.eval₂_apply]
      exact (eval₂_mpullback_mpullback_snd_fiberForm_apply_nonneg (hhol c) hu (hS c) (hV c)
        (htame c) e).lt_of_ne' (mt (eval₂_mpullback_mpullback_snd_fiberForm_apply_eq_zero_iff
          (hhol c) hu (hS c) (hV c) (htame c) e).1 he)
    refine (integralTopForm_pos o ((SmoothForm.isSmoothForm _).of_le (by simp))
      (isClosed_tsupport _).isCompact (fun c b hb ↦
        mpullback_mpullback_snd_fiberForm_apply_basis_nonneg hu ho (hhol c) (hS c) (hV c)
          (htame c) b hb)
      ⟨c, b₀, ho c b₀ (by rw [hb₀]; simp), hpos⟩).ne' h0
  · rw [mpullback_mpullback_snd_fiberForm_eq_zero hu hH]
    exact integralTopForm_zero o

/-- **The tangent planes of a curve of zero vertical area are horizontal.** Let `u` be a smooth
pseudoholomorphic map from a compact surface `C`, oriented so that the frames `(e, j e)` are
positive, into `X_φ` with an almost complex structure of block form along the image of `u` whose
vertical restriction is tamed by `ω_v`. If the vertical area `∫_C u^* ω_v` vanishes, then at every
point where `u` is an immersion its tangent image is the horizontal plane `span(∂_s, T)`. -/
theorem range_mfderiv_eq_suspensionHorizontalSubspace [CompactSpace C]
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
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
    {c : C} (hc : Function.Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c)) :
    (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c).range = suspensionHorizontalSubspace φ (u c) := by
  have hle : (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c).range ≤
      suspensionHorizontalSubspace φ (u c) := by
    rintro _ ⟨e, rfl⟩
    exact (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff hu ho hhol hS hV
      htame).1 h0 c e
  have : FiniteDimensional ℝ (suspensionHorizontalSubspace φ (u c)) := by
    rw [suspensionHorizontalSubspace_eq_span]
    exact FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  -- The plane `span(∂_s, T)` has dimension at most two, the dimension of the image of `du`.
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [LinearMap.finrank_range_of_inj hc, o.finrank_tangentSpace_eq c, Fintype.card_fin,
    suspensionHorizontalSubspace_eq_span]
  exact (finrank_span_le_ncard _ (Set.toFinite _)).trans
    ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))

end SmoothMappingTorus

end TauCeti
