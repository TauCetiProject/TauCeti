/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Torus
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Cross.Period
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Orientation

/-!
# Pseudoholomorphic tori in the cross summand of a symplectic suspension

Let `φ` be a diffeomorphism of a Hausdorff `σ`-compact smooth manifold `M`, modelled on a
finite-dimensional space, preserving a closed two-form `σ`. Let `Y_φ` be its smooth mapping torus,
with suspension vector field `T = ∂_t`, and let `X_φ = (ℝ / ℤ)_s × Y_φ` carry
`Ω = ds ∧ dt + ω_v`, where `ω_v` is the fiber form `σ_v` pulled back along the projection
`X_φ → Y_φ`. The second integral homology of `X_φ` contains the cross summand
`[S¹_s] × H₁(Y_φ; ℤ)`.

This file classifies the pseudoholomorphic tori whose class lies in that summand. Let
`u : ℝ / pℤ × ℝ / qℤ → X_φ` be a smooth map from a torus, oriented as the product of the positive
orientations of its two circles, and suppose that the image `u_*[T]` of the class of the torus is a
cross product `α × a` of a class `α` of positive degree of the circle `ℝ / ℤ`, such as its
fundamental class, with a class `a` of `Y_φ`.

Pairing closed two-forms with `u_*[T]` computes integrals over the torus
(`TauCeti.closedFormHomologyPeriod_singularHomologyMap_addCircleProdFundamentalClass`), and `ω_v`
has zero period on cross products
(`closedFormHomologyPeriod_verticalForm_singularHomologyCrossBilinear_eq_zero`). So the vertical
area `∫_T u^* ω_v` vanishes, and the `Ω`-area `∫_T u^* Ω` is the period of `ds ∧ dt` on `α × a`.

Now let `u` be pseudoholomorphic for an almost complex structure `j` on the torus, positive for
its orientation, and an almost complex structure `J` on `X_φ` of block form along the image of `u`
(`J ∂_s = T`, `J` preserves the vertical subbundle `V`, and `ω_v` tames `J` on `V`). Since the
vertical area vanishes, every tangent image of `u` is horizontal. If `u` is not constant, its image
is exactly the orbit torus `(ℝ / ℤ) × γ` over one primitive closed orbit `γ` of the suspension
flow, `u` factors through the orbit torus by a map of positive degree `m`, and its `Ω`-area is
`m d`, where `d` is the least period of `γ`. If `u` is an embedding, its `Ω`-area is `d`.

Together these classify the compact embedded pseudoholomorphic curves of a symplectic suspension
whose class lies in the cross summand, for curves parametrized by a torus. The
comparison of the de Rham pairing with integration is used only on the torus, where it holds by
`TauCeti.closedFormHomologyPeriod_addCircleProdFundamentalClass`. Neither compactness of `M` nor
nondegeneracy of `σ` is needed.

## Main results

All declarations are in the namespace `TauCeti.SmoothMappingTorus`.

* `integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq`: a torus
  whose class lies in the cross summand has zero vertical area.
* `integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_eq`: its `Ω`-area is the period
  of `ds ∧ dt` on its class.
* `range_eq_range_orbitTorus_of_singularHomologyMap_eq`: the image of a nonconstant
  pseudoholomorphic torus whose class lies in the cross summand is an orbit torus over a primitive
  closed orbit.
* `exists_degree_pos_orbitTorus_comp_eq_of_singularHomologyMap_eq`: such a torus factors through
  the orbit torus by a map of positive degree `m`, and its `Ω`-area is `m d`.
* `integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_eq_of_injective`: an embedded
  pseudoholomorphic torus whose class lies in the cross summand has `Ω`-area the least period of its
  closed orbit.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2.
* Eleny-Nicoleta Ionel and Thomas H. Parker, *Gromov invariants and symplectic maps*,
  Mathematische Annalen 314 (1999), 127–158 (pseudoholomorphic tori over periodic orbits in
  `S¹ × Y_φ`).
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] [SigmaCompactSpace M]
  {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
  {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)]
  {u : AddCircle p × AddCircle q → UnitAddCircle × SmoothMappingTorus φ}
  {i k : ℕ} {α : ((singularChains ℤ).obj (TopCat.of UnitAddCircle)).homology i}
  {a : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology k}

/-! ### Areas of a torus in the cross summand -/

/-- **A torus in the cross summand has zero vertical area.** Let `u` be a smooth map from the torus
`ℝ / pℤ × ℝ / qℤ`, oriented as the product of the positive orientations of its circles, to
`X_φ`, and suppose that the image `u_*[T]` of the class of the torus is the cross product `α × a`
of a class `α` of positive degree of the circle with a class `a` of the mapping torus. Then the
vertical area `∫_T u^* ω_v` vanishes. -/
theorem integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq
    (hσc : σ.IsClosed) (hu : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (h : i + k = 2) (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩
        (addCircleProdFundamentalClass p q) =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a) :
    integralTopForm ((AddCircle.orientation p).prod (AddCircle.orientation q))
      (SmoothForm.mpullback u hu
        (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).val = 0 := by
  rw [← coe_verticalForm hσc,
    ← closedFormHomologyPeriod_singularHomologyMap_addCircleProdFundamentalClass hu, hu₂]
  exact closedFormHomologyPeriod_verticalForm_singularHomologyCrossBilinear_eq_zero hσc h hi α a

/-- **The `Ω`-area of a torus in the cross summand is a period of `ds ∧ dt`.** Let `u` be a smooth
map from the torus `ℝ / pℤ × ℝ / qℤ`, oriented as the product of the positive orientations of its
circles, to `X_φ`, and suppose that `u_*[T]` is the cross product `α × a` of a class `α` of positive
degree of the circle with a class `a` of the mapping torus. Then the `Ω`-area `∫_T u^* Ω` is the
period of the closed form `ds ∧ dt` on `α × a`. -/
theorem integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_eq
    (hσc : σ.IsClosed) (hu : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (h : i + k = 2) (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩
        (addCircleProdFundamentalClass p q) =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a) :
    integralTopForm ((AddCircle.orientation p).prod (AddCircle.orientation q))
        (SmoothForm.mpullback u hu (suspensionForm φ σ hσ)).val =
      closedFormHomologyPeriod (wedgeTimeForm φ)
        (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
          (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a) := by
  rw [← coe_suspensionClosedForm hσc,
    ← closedFormHomologyPeriod_singularHomologyMap_addCircleProdFundamentalClass hu, hu₂,
    closedFormHomologyPeriod_suspensionClosedForm_singularHomologyCrossBilinear hσc h hi]

/-! ### Pseudoholomorphic tori in the cross summand -/

variable [I.Boundaryless]
  {J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
    (UnitAddCircle × SmoothMappingTorus φ)}
  {j : SmoothAlmostComplexStructure (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q)}

/-- **A nonconstant pseudoholomorphic torus in the cross summand fills one orbit torus.** Let `u` be
a smooth pseudoholomorphic map from the torus `ℝ / pℤ × ℝ / qℤ`, with an almost complex structure
`j` positive for the product of the positive orientations of its circles, into `X_φ` with an almost
complex structure of block form along the image of `u` whose vertical restriction is tamed by
`ω_v`. Suppose that `u_*[T]` is the cross product `α × a` of a class `α` of positive degree of the
circle with a class `a` of the mapping torus, and that `u` is not constant. Then for every value
`(s, [t, x])` of `u`, the image of `u` is exactly the image `(ℝ / ℤ) × γ` of the orbit torus of the
primitive closed orbit `γ` through `[0, x]`. -/
theorem range_eq_range_orbitTorus_of_singularHomologyMap_eq
    (hσc : σ.IsClosed) (hu : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (h : i + k = 2) (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩
        (addCircleProdFundamentalClass p q) =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) c)),
      b 1 = j c (b 0) →
        b.orientation = ((AddCircle.orientation p).prod (AddCircle.orientation q)).orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c),
      J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (htame : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) (u c) v (J (u c) v))
    {c₀ : AddCircle p × AddCircle q}
    (hne : mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : AddCircle p × AddCircle q} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    range u = range (orbitTorus φ (isPeriodicPt_minimalPeriod φ x)) :=
  range_eq_range_orbitTorus_of_integralTopForm_eq_zero_of_mfderiv_ne_zero hu ho hhol hS hV htame
    (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq hσc hu h
      hi hu₂) hne hc

/-- **A nonconstant pseudoholomorphic torus in the cross summand covers one orbit torus.** Under
the hypotheses of `range_eq_range_orbitTorus_of_singularHomologyMap_eq`, let `(s, [t, x])` be a
value of `u`, where `x` has least period `d`. Then `u = τ ∘ v` for the orbit torus `τ` of `x` and a
smooth map `v` of positive degree `m` between the two tori, oriented as the products of the
positive orientations of their circles, and the `Ω`-area of `u` is `m d`. By
`integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_eq`, `m d` is also the period of
`ds ∧ dt` on the class `α × a` of `u`. -/
theorem exists_degree_pos_orbitTorus_comp_eq_of_singularHomologyMap_eq
    (hσc : σ.IsClosed) (hu : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (h : i + k = 2) (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩
        (addCircleProdFundamentalClass p q) =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) c)),
      b 1 = j c (b 0) →
        b.orientation = ((AddCircle.orientation p).prod (AddCircle.orientation q)).orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c),
      J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (htame : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) (u c) v (J (u c) v))
    {c₀ : AddCircle p × AddCircle q}
    (hne : mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : AddCircle p × AddCircle q} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) {d : ℕ}
    [Fact (0 < (d : ℝ))] (hx : IsPeriodicPt φ d x) (hd : minimalPeriod φ x = d) :
    ∃ v : AddCircle p × AddCircle q → UnitAddCircle × AddCircle (d : ℝ),
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v ∧ orbitTorus φ hx ∘ v = u ∧
      0 < degree ((AddCircle.orientation p).prod (AddCircle.orientation q))
        ((AddCircle.orientation 1).prod (AddCircle.orientation (d : ℝ))) v ∧
      integralTopForm ((AddCircle.orientation p).prod (AddCircle.orientation q))
          (SmoothForm.mpullback u hu (suspensionForm φ σ hσ)).val =
        degree ((AddCircle.orientation p).prod (AddCircle.orientation q))
          ((AddCircle.orientation 1).prod (AddCircle.orientation (d : ℝ))) v * d := by
  have hH := (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff hu ho hhol hS hV
    htame).1 (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq
      hσc hu h hi hu₂)
  obtain ⟨v, hv, -, hτv, hdeg⟩ :=
    exists_degree_pos_orbitTorus_comp_eq_of_isPseudoholomorphicAt hu ho hhol hS hH hne hc hx hd
  exact ⟨v, hv, hτv, hdeg, integralTopForm_mpullback_suspensionForm_eq_degree_mul hu hv hx hτv⟩

/-- **The `Ω`-area of an embedded pseudoholomorphic torus in the cross summand.** Under the
hypotheses of `range_eq_range_orbitTorus_of_singularHomologyMap_eq`, let `u` moreover be an
embedding: injective, with injective differential. Then for every value `(s, [t, x])` of `u`, the
`Ω`-area of `u` is the least period of `x`, the period of the primitive closed orbit `γ` whose
orbit torus `(ℝ / ℤ) × γ` is the image of `u`. -/
theorem integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_eq_of_injective
    (hσc : σ.IsClosed) (hu : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (hu₁ : Injective u) (h : i + k = 2) (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩
        (addCircleProdFundamentalClass p q) =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) c)),
      b 1 = j c (b 0) →
        b.orientation = ((AddCircle.orientation p).prod (AddCircle.orientation q)).orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c),
      J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (htame : ∀ c, ∀ v ∈ suspensionVerticalSubspace φ (u c), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) (u c) v (J (u c) v))
    (hinj : ∀ c, Injective (mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : AddCircle p × AddCircle q} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    integralTopForm ((AddCircle.orientation p).prod (AddCircle.orientation q))
        (SmoothForm.mpullback u hu (suspensionForm φ σ hσ)).val =
      minimalPeriod φ x :=
  integralTopForm_mpullback_suspensionForm_of_integralTopForm_eq_zero hu hu₁ ho hhol hS hV htame
    (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq hσc hu h
      hi hu₂) hinj hc

end TauCeti.SmoothMappingTorus
