/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Orientation

/-!
# The covering multiplicity of a horizontal curve over its orbit torus

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M`, let `Y_φ` be its
smooth mapping torus and `X_φ = (ℝ / ℤ)_s × Y_φ`, with the closed two-form `Ω = ds ∧ dt + σ_v`. A
nonconstant compact connected pseudoholomorphic curve `u : C → X_φ` whose tangent planes are
horizontal lies over a closed orbit of `φ`: if `x` is a point of that orbit and `d` its least
period, then `u = τ ∘ v` for the orbit torus `τ : (ℝ / ℤ) × (ℝ / dℤ) → X_φ`,
`(s, θ) ↦ (s, [θ, x])`, and a surjective pseudoholomorphic map `v`
(`exists_surjective_orbitTorus_comp_eq_of_isPseudoholomorphicAt`).
Several integers attached to such a curve must be kept apart: the least period `d` of the orbit,
the number of times `v` covers the orbit torus, and the pairing of `u` with `Ω`. This file computes
how they are related.

Take `C` modelled on `ℝ × ℝ`, like the torus, compact and boundaryless, and orient `C` so that the
frames `(e, j e)` are positive and the torus as the product of the positive orientations of its two
circles. The **covering multiplicity** of `u` is the mapping degree `m = deg v` (`TauCeti.degree`).
The degree formula along `v` computes every integral over `C` of a two-form pulled back from `X_φ`:

`∫_C u^* β = m ∫_{(ℝ / ℤ) × (ℝ / dℤ)} τ^* β`

(`integralTopForm_mpullback_eq_degree_mul_of_orbitTorus_comp_eq`), so `u` represents `m` times the
orbit torus for de Rham pairings. Since `τ^* Ω = ds ∧ dt_d` has integral `d` over the torus, the
`Ω`-area of `u` is `m d` (`integralTopForm_mpullback_suspensionForm_eq_degree_mul`). For a
nonconstant pseudoholomorphic horizontal curve the multiplicity is positive
(`degree_pos_of_orbitTorus_comp_eq`), because the area of the pseudoholomorphic map `v` is.

When `u` is moreover immersed, `v` is a local diffeomorphism that preserves orientation at every
point, so all orientation signs in the degree are `+1`. Then every point of the orbit torus has
exactly `m` preimages under `v` (`ncard_preimage_eq_degree_of_orbitTorus_comp_eq`): the
multiplicity is the number of sheets of `C` over the embedded torus `(ℝ / ℤ) × γ`. Since `τ` is
injective, `u` is injective exactly when `m = 1`
(`injective_iff_degree_eq_one_of_orbitTorus_comp_eq`), the embedded case, whose `Ω`-area is the
least period `d` (`integralTopForm_mpullback_suspensionForm_of_integralTopForm_eq_zero`).

## Main results

* `integralTopForm_mpullback_eq_degree_mul_of_orbitTorus_comp_eq`: integrals of pulled back
  two-forms over a curve `u = τ ∘ v` are `deg v` times the integrals over the orbit torus.
* `integralTopForm_mpullback_suspensionForm_eq_degree_mul`: such a curve has `Ω`-area `deg v · d`.
* `degree_pos_of_orbitTorus_comp_eq`: a nonconstant compact connected pseudoholomorphic horizontal
  curve covers its orbit torus with positive multiplicity.
* `ncard_preimage_eq_degree_of_orbitTorus_comp_eq`: if the curve is immersed, every point of the
  orbit torus has `deg v` preimages.
* `injective_iff_degree_eq_one_of_orbitTorus_comp_eq`: an immersed such curve is injective exactly
  when its covering multiplicity is one.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (multiply covered tori and their multiplicities).
* Eleny-Nicoleta Ionel and Thomas H. Parker, *Gromov invariants and symplectic maps*,
  Mathematische Annalen 314 (1999), 127–158 (pseudoholomorphic tori over periodic orbits in
  `S¹ × Y_φ`).
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  {x : M} {d : ℕ} [Fact (0 < (d : ℝ))] (h : IsPeriodicPt φ d x)
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ (ℝ × ℝ) H'} [I'.Boundaryless]
  {C : Type*} [TopologicalSpace C] [ChartedSpace H' C] [IsManifold I' ∞ C] [T2Space C]
  [CompactSpace C] {o : Manifold.Orientation I' C (Fin 2)}
  {u : C → UnitAddCircle × SmoothMappingTorus φ} {v : C → UnitAddCircle × AddCircle (d : ℝ)}

/-- **Integrals over a curve through an orbit torus are multiplied by the covering degree.** Let
`u = τ ∘ v` for the orbit torus `τ` of a point of period `d` and a smooth map `v` from a compact
boundaryless surface modelled on `ℝ × ℝ`. Then for every smooth two-form `β` on `X_φ`, the integral
of `u^* β` over `C` is `deg v` times the integral of `τ^* β` over the torus, for the product of the
positive orientations of the two circles. -/
theorem integralTopForm_mpullback_eq_degree_mul_of_orbitTorus_comp_eq
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (hv : ContMDiff I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hτv : orbitTorus φ h ∘ v = u)
    (β : SmoothForm (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (UnitAddCircle × SmoothMappingTorus φ) ℝ 2) :
    integralTopForm o (SmoothForm.mpullback u hu β).1 =
      degree o ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v *
        integralTopForm ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ)))
          (SmoothForm.mpullback (orbitTorus φ h) (contMDiff_orbitTorus h) β).1 := by
  subst hτv
  rw [← SmoothForm.mpullback_mpullback _ _ hv (contMDiff_orbitTorus h), SmoothForm.coe_mpullback]
  exact integralTopForm_mpullback_eq_degree_mul _ _ hv (SmoothForm.isSmoothForm _)
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

variable {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- **The `Ω`-area of a curve through an orbit torus.** Let `u = τ ∘ v` for the orbit torus `τ` of
a point of period `d` and a smooth map `v` from a compact boundaryless surface modelled on
`ℝ × ℝ`. Then the suspension form `Ω = ds ∧ dt + σ_v` integrates to `deg v · d` over `C`. -/
theorem integralTopForm_mpullback_suspensionForm_eq_degree_mul
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (hv : ContMDiff I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hτv : orbitTorus φ h ∘ v = u) :
    integralTopForm o (SmoothForm.mpullback u hu (suspensionForm φ σ hσ)).1 =
      degree o ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v * d := by
  rw [integralTopForm_mpullback_eq_degree_mul_of_orbitTorus_comp_eq h hu hv hτv,
    mpullback_orbitTorus_suspensionForm, AddCircle.integralTopForm_wedge_timeForm, one_mul]

variable [I.Boundaryless] [FiniteDimensional ℝ E] [PreconnectedSpace C]
  {J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
    (UnitAddCircle × SmoothMappingTorus φ)}
  {j : SmoothAlmostComplexStructure I' C}

/-- The factor through the orbit torus of a nonconstant pseudoholomorphic horizontal curve is
smooth and pseudoholomorphic: by the injectivity of the orbit torus over a primitive orbit, it is
the factor constructed in `exists_surjective_orbitTorus_comp_eq_of_isPseudoholomorphicAt`. -/
private theorem contMDiff_and_isPseudoholomorphicAt_of_orbitTorus_comp_eq
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    {c₀ : C} (hne : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : C} {t : ℝ} (hc : (u c).2 = mk φ t x) (hd : minimalPeriod φ x = d)
    (hτv : orbitTorus φ h ∘ v = u) :
    ContMDiff I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v ∧
      ∀ c', IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd 1 d) v c' := by
  obtain ⟨v', hv'd, hv'hol, -, hτv'⟩ :=
    exists_surjective_orbitTorus_comp_eq_of_isPseudoholomorphicAt hu ho hhol hS hH hne hc h hd
  have hv' : v' = v := ((injective_orbitTorus_iff h).2 hd).comp_left (hτv'.trans hτv.symm)
  exact hv' ▸ ⟨hv'd, hv'hol⟩

/-- **A nonconstant pseudoholomorphic horizontal curve covers its orbit torus with positive
multiplicity.** Let `u` be a smooth pseudoholomorphic map from a compact connected boundaryless
surface `C` modelled on `ℝ × ℝ`, oriented so that the frames `(e, j e)` are positive, into `X_φ`
with an almost complex structure of block form `J ∂_s = T` along the image of `u`, with horizontal
tangent images and nonzero differential somewhere. Let `(s, [t, x])` be a value of `u`, where `x`
has least period `d`, and let `u = τ ∘ v` for the orbit torus `τ` of `x` and a map `v`. Then
`deg v > 0`, for the product of the positive orientations of the two circles. -/
theorem degree_pos_of_orbitTorus_comp_eq
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    {c₀ : C} (hne : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : C} {t : ℝ} (hc : (u c).2 = mk φ t x) (hd : minimalPeriod φ x = d)
    (hτv : orbitTorus φ h ∘ v = u) :
    0 < degree o ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v := by
  obtain ⟨hv, hvhol⟩ :=
    contMDiff_and_isPseudoholomorphicAt_of_orbitTorus_comp_eq h hu ho hhol hS hH hne hc hd hτv
  refine degree_pos_of_isPseudoholomorphicAt_addCircleProd ho hv hvhol (c₀ := c₀) ?_
  -- `du = dτ ∘ dv`, so `dv` vanishes nowhere where `du` does not.
  intro hv₀
  apply hne
  rw [← hτv, mfderiv_comp c₀ ((contMDiff_orbitTorus h).mdifferentiableAt (by simp))
    (hv.mdifferentiableAt (by simp)), hv₀, ContinuousLinearMap.comp_zero]

omit [I'.Boundaryless] [IsManifold I' ∞ C] [T2Space C] [CompactSpace C] [I.Boundaryless]
  [FiniteDimensional ℝ E] [PreconnectedSpace C] in
/-- The factor through the orbit torus of an immersed curve is immersed: `du = dτ ∘ dv`. -/
private theorem injective_mfderiv_of_orbitTorus_comp_eq
    (hv : ContMDiff I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v) (hτv : orbitTorus φ h ∘ v = u)
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c)) (c : C) :
    Injective (mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c) := by
  have hc := hinj c
  rw [← hτv, mfderiv_comp c ((contMDiff_orbitTorus h).mdifferentiableAt (by simp))
    (hv.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp] at hc
  exact hc.of_comp

omit [IsManifold I ∞ M] [I'.Boundaryless] [IsManifold I' ∞ C] [T2Space C] [CompactSpace C]
  [I.Boundaryless] [FiniteDimensional ℝ E] [PreconnectedSpace C] in
/-- An immersion of a surface has nonzero differential at every point. -/
private theorem mfderiv_ne_zero_of_injective
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c)) (c : C) :
    mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c ≠ 0 := by
  -- The tangent space `ℝ × ℝ` is nontrivial, so the zero map is not injective.
  have : Nontrivial (TangentSpace I' c) := inferInstanceAs (Nontrivial (ℝ × ℝ))
  exact fun h0 ↦ LinearMap.ne_zero_of_injective (hinj c)
    (by rw [h0, ContinuousLinearMap.toLinearMap_zero])

/-- **An immersed pseudoholomorphic horizontal curve has `deg v` sheets over its orbit torus.**
Let `u` be a smooth pseudoholomorphic immersion of a compact connected boundaryless surface `C`
modelled on `ℝ × ℝ`, oriented so that the frames `(e, j e)` are positive, into `X_φ` with an almost
complex structure of block form `J ∂_s = T` along the image of `u`, with horizontal tangent images.
Let `(s, [t, x])` be a value of `u`, where `x` has least period `d`, and let `u = τ ∘ v` for the
orbit torus `τ` of `x` and a map `v`. Then every point of the torus `(ℝ / ℤ) × (ℝ / dℤ)` has
exactly `deg v` preimages under `v`. -/
theorem ncard_preimage_eq_degree_of_orbitTorus_comp_eq
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} (hc : (u c).2 = mk φ t x) (hd : minimalPeriod φ x = d)
    (hτv : orbitTorus φ h ∘ v = u) (y : UnitAddCircle × AddCircle (d : ℝ)) :
    ((v ⁻¹' {y}).ncard : ℤ) =
      degree o ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v :=
  have hv := contMDiff_and_isPseudoholomorphicAt_of_orbitTorus_comp_eq h hu ho hhol hS hH
    (mfderiv_ne_zero_of_injective hinj c) hc hd hτv
  ncard_preimage_eq_degree_of_injective_mfderiv ho hv.1 hv.2
    (injective_mfderiv_of_orbitTorus_comp_eq h hv.1 hτv hinj) y

/-- **An immersed pseudoholomorphic horizontal curve is embedded exactly when its covering
multiplicity is one.** Let `u` be a smooth pseudoholomorphic immersion of a compact connected
boundaryless surface `C` modelled on `ℝ × ℝ`, oriented so that the frames `(e, j e)` are positive,
into `X_φ` with an almost complex structure of block form `J ∂_s = T` along the image of `u`, with
horizontal tangent images. Let `(s, [t, x])` be a value of `u`, where `x` has least period `d`, and
let `u = τ ∘ v` for the orbit torus `τ` of `x` and a map `v`. Then `u` is injective if and only
if `deg v = 1`. -/
theorem injective_iff_degree_eq_one_of_orbitTorus_comp_eq
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} (hc : (u c).2 = mk φ t x) (hd : minimalPeriod φ x = d)
    (hτv : orbitTorus φ h ∘ v = u) :
    Injective u ↔
      degree o ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v = 1 := by
  have : Nonempty C := ⟨c⟩
  obtain ⟨hv, hvhol⟩ := contMDiff_and_isPseudoholomorphicAt_of_orbitTorus_comp_eq h hu ho hhol hS
    hH (mfderiv_ne_zero_of_injective hinj c) hc hd hτv
  rw [← injective_iff_degree_eq_one_of_injective_mfderiv ho hv hvhol
    (injective_mfderiv_of_orbitTorus_comp_eq h hv hτv hinj), ← hτv]
  -- The orbit torus over a primitive orbit is injective.
  exact ((injective_orbitTorus_iff h).2 hd).of_comp_iff v

end SmoothMappingTorus

end TauCeti
