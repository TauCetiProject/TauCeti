/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.FundamentalClass
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Cross.Period
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Orientation

/-!
# Pseudoholomorphic curves in the cross summand of a symplectic suspension

Let `φ` be a diffeomorphism of a Hausdorff `σ`-compact smooth manifold `M`, modelled on a
finite-dimensional space, preserving a closed two-form `σ`. Let `Y_φ` be its smooth mapping torus,
with suspension vector field `T = ∂_t`, and let `X_φ = (ℝ / ℤ)_s × Y_φ` carry
`Ω = ds ∧ dt + ω_v`, where `ω_v` is the fiber form `σ_v` pulled back along the projection
`X_φ → Y_φ`. The second integral homology of `X_φ` contains the cross summand
`[S¹_s] × H₁(Y_φ; ℤ)`.

This file classifies the compact pseudoholomorphic curves whose class lies in that summand. Let
`C` be a compact connected boundaryless smooth surface with an orientation `o` and an integral
fundamental class `μ ∈ H₂(C; ℤ)` (`TauCeti.IsFundamentalClass`), and let `u : C → X_φ` be a smooth
map such that `u_* μ` is a cross product `α × a` of a class `α` of positive degree of the circle
`ℝ / ℤ`, such as its fundamental class, with a class `a` of `Y_φ`.

Pairing a closed two-form `β` with `u_* μ` computes `± ∫_C u^* β`, with one sign for all `β`
(`TauCeti.exists_closedFormHomologyPeriod_singularHomologyMap_eq_mul_integralTopForm`), and `ω_v`
has zero period on cross products
(`closedFormHomologyPeriod_verticalForm_singularHomologyCrossBilinear_eq_zero`). So the vertical
area `∫_C u^* ω_v` vanishes, and the `Ω`-area `∫_C u^* Ω` is `±` the period of `ds ∧ dt` on
`α × a`. When `C` is the torus `ℝ / pℤ × ℝ / qℤ`, oriented as the product of its circles, and `μ`
is its class `[ℝ / pℤ] × [ℝ / qℤ]`, the sign is `+`, by
`integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_addCircleProdFundamentalClass_eq`.

Now let `u` be pseudoholomorphic for an almost complex structure `j` on `C`, positive for `o`, and
an almost complex structure `J` on `X_φ` of block form along the image of `u` (`J ∂_s = T`, `J`
preserves the vertical subbundle `V`, and `ω_v` tames `J` on `V`). Since the vertical area
vanishes, every tangent image of `u` is horizontal. If `u` is not constant, its image is exactly
the orbit torus `(ℝ / ℤ) × γ` over one primitive closed orbit `γ` of the suspension flow. When `C`
is modelled on the plane, `u` factors through the orbit torus by a map of positive degree `m`, and
its `Ω`-area is `m d`, where `d` is the least period of `γ`. If `u` is an embedding, it is
`τ ∘ Φ` for the orbit torus `τ` and an orientation-preserving diffeomorphism `Φ` of `C` onto the
parameter torus `(ℝ / ℤ) × (ℝ / dℤ)`, and its `Ω`-area is `d`.

Together these classify the compact embedded pseudoholomorphic curves of a symplectic suspension
whose class lies in the cross summand: each is an orbit torus over a primitive closed orbit, with
`Ω`-area the period of the orbit and `ω_v`-area zero. Neither compactness of `M` nor
nondegeneracy of `σ` is needed.

## Main results

All declarations are in the namespace `TauCeti.SmoothMappingTorus`.

* `integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq`: a closed
  surface whose class lies in the cross summand has zero vertical area.
* `exists_closedFormHomologyPeriod_wedgeTimeForm_eq_mul_integralTopForm`: its `Ω`-area is `±` the
  period of `ds ∧ dt` on its class.
* for a torus with its product class, the `Ω`-area is that period:
`integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_addCircleProdFundamentalClass_eq`.
* `range_eq_range_orbitTorus_of_singularHomologyMap_eq`: the image of a nonconstant
  pseudoholomorphic closed surface whose class lies in the cross summand is an orbit torus over a
  primitive closed orbit.
* `exists_degree_pos_orbitTorus_comp_eq_of_singularHomologyMap_eq`: such a surface modelled on the
  plane factors through the orbit torus by a map of positive degree `m`, and its `Ω`-area is
  `m d`.
* `exists_diffeomorph_orbitTorus_comp_eq_of_singularHomologyMap_eq`: an embedded one is
  parametrized by the orbit torus through an orientation-preserving diffeomorphism.
* `integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_eq_of_injective`: an embedded
  one has `Ω`-area the least period of its closed orbit.

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
  {i k : ℕ} {α : ((singularChains ℤ).obj (TopCat.of UnitAddCircle)).homology i}
  {a : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology k}

/-! ### Areas of a closed surface in the cross summand -/

section Area

variable {E' H' C : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  {o : Manifold.Orientation I' C (Fin 2)} {μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2}
  {u : C → UnitAddCircle × SmoothMappingTorus φ}

/-- **A closed surface in the cross summand has zero vertical area.** Let `u` be a smooth map from
a compact connected oriented boundaryless surface `C` to `X_φ`, and suppose that the image `u_* μ`
of an integral fundamental class `μ` of `C` is the cross product `α × a` of a class `α` of positive
degree of the circle with a class `a` of the mapping torus. Then the vertical area `∫_C u^* ω_v`
vanishes. -/
theorem integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq
    (hσc : σ.IsClosed) (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ)
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (h : i + k = 2) (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a) :
    integralTopForm o (SmoothForm.mpullback u hu
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).val = 0 := by
  rw [← coe_verticalForm hσc, SmoothForm.coe_mpullback,
    ← closedFormHomologyPeriod_singularHomologyMap_eq_zero_iff
      (by rw [← o.card_eq, Fintype.card_fin]) o hμ hu, hu₂]
  exact closedFormHomologyPeriod_verticalForm_singularHomologyCrossBilinear_eq_zero hσc h hi α a

/-- **The `Ω`-area of a closed surface in the cross summand is a period of `ds ∧ dt` up to sign.**
Let `u` be a smooth map from a compact connected oriented boundaryless surface `C` to `X_φ`, and
suppose that the image `u_* μ` of an integral fundamental class `μ` of `C` is the cross product
`α × a` of a class `α` of positive degree of the circle with a class `a` of the mapping torus. Then
the period of the closed form `ds ∧ dt` on `α × a` is `s ∫_C u^* Ω` for a sign `s = ±1`, the sign
comparing `μ` with the orientation of `C`. -/
theorem exists_closedFormHomologyPeriod_wedgeTimeForm_eq_mul_integralTopForm
    (hσc : σ.IsClosed) (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ)
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (h : i + k = 2) (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      closedFormHomologyPeriod (wedgeTimeForm φ)
          (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
            (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a) =
        s * integralTopForm o (SmoothForm.mpullback u hu (suspensionForm φ σ hσ)).val := by
  obtain ⟨s, hs, hper⟩ := exists_closedFormHomologyPeriod_singularHomologyMap_eq_mul_integralTopForm
    (by rw [← o.card_eq, Fintype.card_fin]) o hμ hu
  refine ⟨s, hs, ?_⟩
  rw [← closedFormHomologyPeriod_suspensionClosedForm_singularHomologyCrossBilinear hσc h hi, ← hu₂,
    hper, coe_suspensionClosedForm, SmoothForm.coe_mpullback]

end Area

/-- **The `Ω`-area of a torus in the cross summand is a period of `ds ∧ dt`.** Let `u` be a smooth
map from the torus `ℝ / pℤ × ℝ / qℤ`, oriented as the product of the positive orientations of its
circles, to `X_φ`, and suppose that the image `u_*[T]` of the class of the torus is the cross
product `α × a` of a class `α` of positive degree of the circle with a class `a` of the mapping
torus. Then the `Ω`-area `∫_T u^* Ω` is the period of the closed form `ds ∧ dt` on `α × a`, with no
sign: the class of the torus is positive for its product orientation. -/
theorem
    integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_addCircleProdFundamentalClass_eq
    {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)]
    {u : AddCircle p × AddCircle q → UnitAddCircle × SmoothMappingTorus φ}
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

/-! ### Pseudoholomorphic closed surfaces in the cross summand -/

section Pseudoholomorphic

variable [I.Boundaryless]
  {J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
    (UnitAddCircle × SmoothMappingTorus φ)}
  {E' H' C : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  {o : Manifold.Orientation I' C (Fin 2)} {μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2}
  {u : C → UnitAddCircle × SmoothMappingTorus φ} {j : SmoothAlmostComplexStructure I' C}

/-- **A nonconstant pseudoholomorphic closed surface in the cross summand fills one orbit torus.**
Let `u` be a smooth pseudoholomorphic map from a compact connected boundaryless surface `C`,
oriented so that the frames `(e, j e)` are positive, into `X_φ` with an almost complex structure of
block form along the image of `u` whose vertical restriction is tamed by `ω_v`. Suppose that the
image `u_* μ` of an integral fundamental class `μ` of `C` is the cross product `α × a` of a class
`α` of positive degree of the circle with a class `a` of the mapping torus, and that `u` is not
constant. Then for every value `(s, [t, x])` of `u`, the image of `u` is exactly the image
`(ℝ / ℤ) × γ` of the orbit torus of the primitive closed orbit `γ` through `[0, x]`. -/
theorem range_eq_range_orbitTorus_of_singularHomologyMap_eq
    (hσc : σ.IsClosed) (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ)
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (h : i + k = 2) (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a)
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
    {c₀ : C} (hne : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    range u = range (orbitTorus φ (isPeriodicPt_minimalPeriod φ x)) :=
  range_eq_range_orbitTorus_of_integralTopForm_eq_zero_of_mfderiv_ne_zero hu ho hhol hS hV htame
    (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq hσc hμ hu
      h hi hu₂) hne hc

/-- **The oriented parametrization of an embedded pseudoholomorphic closed surface in the cross
summand.** Under the hypotheses of `range_eq_range_orbitTorus_of_singularHomologyMap_eq`, let `u`
moreover be an embedding: injective, with injective differential. Let `(s, [t, x])` be a value of
`u`, where `x` has least period `d`. Then `u = τ ∘ Φ` for the orbit torus `τ` of `x` and a
diffeomorphism `Φ : C ≃ (ℝ / ℤ) × (ℝ / dℤ)` that preserves orientation at every point, for the
product of the positive orientations of the two circles. -/
theorem exists_diffeomorph_orbitTorus_comp_eq_of_singularHomologyMap_eq
    (hσc : σ.IsClosed) (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ)
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (hu₁ : Injective u) (h : i + k = 2)
    (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a)
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
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} {x : M} {d : ℕ} [Fact (0 < (d : ℝ))] (hx : IsPeriodicPt φ d x)
    (hc : (u c).2 = mk φ t x) (hd : minimalPeriod φ x = d) :
    ∃ Φ : C ≃ₘ⟮I', 𝓘(ℝ).prod 𝓘(ℝ)⟯ UnitAddCircle × AddCircle (d : ℝ),
      orbitTorus φ hx ∘ Φ = u ∧ ∀ c, Manifold.Orientation.IsOrientationPreservingAt o
        ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) Φ c :=
  exists_diffeomorph_orbitTorus_comp_eq_of_integralTopForm_eq_zero hx hu hu₁ ho hhol hS hV htame
    (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq hσc hμ hu
      h hi hu₂) hinj hc hd

/-- **The `Ω`-area of an embedded pseudoholomorphic closed surface in the cross summand.** Under
the hypotheses of `range_eq_range_orbitTorus_of_singularHomologyMap_eq`, let `u` moreover be an
embedding: injective, with injective differential. Then for every value `(s, [t, x])` of `u`, the
`Ω`-area of `u` is the least period of `x`, the period of the primitive closed orbit `γ` whose
orbit torus `(ℝ / ℤ) × γ` is the image of `u`. -/
theorem integralTopForm_mpullback_suspensionForm_of_singularHomologyMap_eq_of_injective
    (hσc : σ.IsClosed) (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ)
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (hu₁ : Injective u) (h : i + k = 2)
    (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a)
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
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    integralTopForm o (SmoothForm.mpullback u hu (suspensionForm φ σ hσ)).val =
      minimalPeriod φ x :=
  integralTopForm_mpullback_suspensionForm_of_integralTopForm_eq_zero hu hu₁ ho hhol hS hV htame
    (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq hσc hμ hu
      h hi hu₂) hinj hc

end Pseudoholomorphic

/-! ### The covering degree of a pseudoholomorphic closed surface in the cross summand -/

section Degree

variable [I.Boundaryless]
  {J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
    (UnitAddCircle × SmoothMappingTorus φ)}
  {H' C : Type} [TopologicalSpace H'] {I' : ModelWithCorners ℝ (ℝ × ℝ) H'} [I'.Boundaryless]
  [TopologicalSpace C] [ChartedSpace H' C] [IsManifold I' ∞ C] [T2Space C] [CompactSpace C]
  [ConnectedSpace C] {o : Manifold.Orientation I' C (Fin 2)}
  {μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2}
  {u : C → UnitAddCircle × SmoothMappingTorus φ} {j : SmoothAlmostComplexStructure I' C}

/-- **A nonconstant pseudoholomorphic closed surface in the cross summand covers one orbit
torus.** Under the hypotheses of `range_eq_range_orbitTorus_of_singularHomologyMap_eq`, with `C`
modelled on the plane `ℝ × ℝ`, let `(s, [t, x])` be a value of `u`, where `x` has least period `d`.
Then `u = τ ∘ v` for the orbit torus `τ` of `x` and a smooth map `v` of positive degree `m` from
`C` to the parameter torus `(ℝ / ℤ) × (ℝ / dℤ)`, oriented as the product of the positive
orientations of its circles, and the `Ω`-area of `u` is `m d`. By
`exists_closedFormHomologyPeriod_wedgeTimeForm_eq_mul_integralTopForm`, `± m d` is also the period
of `ds ∧ dt` on the class `α × a` of `u`. -/
theorem exists_degree_pos_orbitTorus_comp_eq_of_singularHomologyMap_eq
    (hσc : σ.IsClosed) (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ)
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (h : i + k = 2) (hi : i ≠ 0)
    (hu₂ : ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ =
      TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) i k 2 h α a)
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
    {c₀ : C} (hne : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) {d : ℕ}
    [Fact (0 < (d : ℝ))] (hx : IsPeriodicPt φ d x) (hd : minimalPeriod φ x = d) :
    ∃ v : C → UnitAddCircle × AddCircle (d : ℝ),
      ContMDiff I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v ∧ orbitTorus φ hx ∘ v = u ∧
      0 < degree o ((AddCircle.orientation 1).prod (AddCircle.orientation (d : ℝ))) v ∧
      integralTopForm o (SmoothForm.mpullback u hu (suspensionForm φ σ hσ)).val =
        degree o ((AddCircle.orientation 1).prod (AddCircle.orientation (d : ℝ))) v * d := by
  have hH := (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff hu ho hhol hS hV
    htame).1 (integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_of_singularHomologyMap_eq
      hσc hμ hu h hi hu₂)
  obtain ⟨v, hv, -, hτv, hdeg⟩ :=
    exists_degree_pos_orbitTorus_comp_eq_of_isPseudoholomorphicAt hu ho hhol hS hH hne hc hx hd
  exact ⟨v, hv, hτv, hdeg, integralTopForm_mpullback_suspensionForm_eq_degree_mul hu hv hx hτv⟩

end Degree

end TauCeti.SmoothMappingTorus
