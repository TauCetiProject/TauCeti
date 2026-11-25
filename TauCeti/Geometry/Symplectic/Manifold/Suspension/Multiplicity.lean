/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Orientation

import TauCeti.Geometry.Manifold.MFDeriv.Basic

/-!
# The covering multiplicity of a horizontal curve over its orbit torus

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M`, let `Y_φ` be its
smooth mapping torus, with suspension vector field `T = ∂_t`, and `X_φ = (ℝ / ℤ)_s × Y_φ`. A
`φ`-invariant closed two-form `σ` on `M` descends to the fiber form `σ_v` on `Y_φ`, and
`Ω = ds ∧ dt + σ_v` is the corresponding closed two-form on `X_φ` (`suspensionForm`). Let `J` be an
almost complex structure on `X_φ`, and let `u : C → X_φ` be a compact connected pseudoholomorphic
curve with nonzero differential somewhere, whose tangent planes are horizontal and along whose image
`J ∂_s = T`. Suppose `u` meets the suspension orbit of a point `x` of least period `d`, at a value
`(s, [t, x])`. Then `u = τ ∘ v` for the orbit torus `τ : (ℝ / ℤ) × (ℝ / dℤ) → X_φ`,
`(s, θ) ↦ (s, [θ, x])`, and a surjective pseudoholomorphic map `v`
(`exists_surjective_orbitTorus_comp_eq_of_isPseudoholomorphicAt`).
Several integers attached to such a curve must be kept apart: the least period `d` of the orbit,
the number of times `v` covers the orbit torus, and the pairing of `u` with `Ω`. This file computes
how they are related.

Take `C` modelled on `ℝ × ℝ`, like the torus, compact and boundaryless, and orient `C` so that the
frames `(e, j e)` are positive and the torus as the product of the positive orientations of its two
circles. The **covering multiplicity** of `u` is the mapping degree `m = deg v` (`TauCeti.degree`).
The degree formula along `v` (`TauCeti.integralTopForm_mpullback_comp_eq_degree_mul`) computes every
integral over `C` of a two-form pulled back from `X_φ`:

`∫_C u^* β = m ∫_{(ℝ / ℤ) × (ℝ / dℤ)} τ^* β`

(`integralTopForm_mpullback_eq_degree_mul_of_orbitTorus_comp_eq`), so `u` represents `m` times the
orbit torus for de Rham pairings. For `β = Ω` this is the `Ω`-area `m d`
(`integralTopForm_mpullback_suspensionForm_eq_degree_mul`), and for a nonconstant
pseudoholomorphic horizontal curve the multiplicity is positive
(`exists_degree_pos_orbitTorus_comp_eq_of_isPseudoholomorphicAt`).

When `u` is moreover immersed, `v` is a local diffeomorphism that preserves orientation at every
point, so all orientation signs in the degree are `+1`. Then every point of the orbit torus has
exactly `m` preimages under `v` (`degree_eq_ncard_of_orbitTorus_comp_eq`): the multiplicity is the
number of sheets of `C` over the embedded torus `(ℝ / ℤ) × γ`. Since `τ` is injective, `u` is
injective exactly when `m = 1` (`injective_iff_degree_eq_one_of_orbitTorus_comp_eq`), the embedded
case, whose `Ω`-area is the least period `d`
(`integralTopForm_mpullback_suspensionForm_eq_degree_mul` with `m = 1`).

## Main results

* `integralTopForm_mpullback_eq_degree_mul_of_orbitTorus_comp_eq`: integrals of pulled back
  two-forms over a curve `u = τ ∘ v` are `deg v` times the integrals over the orbit torus.
* `degree_eq_ncard_of_orbitTorus_comp_eq`: if a nonconstant compact connected pseudoholomorphic
  horizontal curve is immersed, every point of its orbit torus has `deg v` preimages.
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
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ (ℝ × ℝ) H'}
  {C : Type*} [TopologicalSpace C] [ChartedSpace H' C] [IsManifold I' ∞ C] [T2Space C]
  [CompactSpace C] {o : Manifold.Orientation I' C (Fin 2)}
  {u : C → UnitAddCircle × SmoothMappingTorus φ} {v : C → UnitAddCircle × AddCircle (d : ℝ)}

/-- **Integrals over a curve through an orbit torus are multiplied by the covering degree.** Let
`u = τ ∘ v` for the orbit torus `τ` of a point of period `d` and a smooth map `v` from a compact
boundaryless surface modelled on `ℝ × ℝ`. Then for every smooth two-form `β` on `X_φ`, the integral
of `u^* β` over `C` is `deg v` times the integral of `τ^* β` over the torus, for the product of the
positive orientations of the two circles. -/
theorem integralTopForm_mpullback_eq_degree_mul_of_orbitTorus_comp_eq
    [BoundarylessManifold I' C] (hv : ContMDiff I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v)
    (hτv : orbitTorus φ h ∘ v = u)
    (β : SmoothForm (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (UnitAddCircle × SmoothMappingTorus φ) ℝ 2) :
    integralTopForm o
        (SmoothForm.mpullback u (hτv ▸ (contMDiff_orbitTorus h).comp hv) β).val =
      degree o ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v *
        integralTopForm ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ)))
          (SmoothForm.mpullback (orbitTorus φ h) (contMDiff_orbitTorus h) β).val := by
  subst hτv
  exact integralTopForm_mpullback_comp_eq_degree_mul o _ hv hv.continuous.isProperMap
    (contMDiff_orbitTorus h) β

variable [I'.Boundaryless] [I.Boundaryless] [FiniteDimensional ℝ E] [PreconnectedSpace C]
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
    {c₀ : C} (hne : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0) (hd : minimalPeriod φ x = d)
    (hτv : orbitTorus φ h ∘ v = u) :
    ContMDiff I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v ∧
      ∀ c', IsPseudoholomorphicAt j (SmoothAlmostComplexStructure.addCircleProd 1 d) v c' := by
  -- A real representative `t` of the time coordinate of `v c₀` gives the value `(s, [t, x])`.
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (v c₀).2
  have hc : (u c₀).2 = mk φ t x := by
    rw [← hτv, comp_apply, orbitTorus_apply, ← closedOrbit_coe h, ← ht]
  obtain ⟨v', hv'd, hv'hol, -, hτv'⟩ :=
    exists_surjective_orbitTorus_comp_eq_of_isPseudoholomorphicAt hu ho hhol hS hH hne hc h hd
  have hv' : v' = v := ((injective_orbitTorus_iff h).2 hd).comp_left (hτv'.trans hτv.symm)
  exact hv' ▸ ⟨hv'd, hv'hol⟩

/-- **An immersed pseudoholomorphic horizontal curve has `deg v` sheets over its orbit torus.**
Let `u` be a smooth pseudoholomorphic immersion of a compact connected boundaryless surface `C`
modelled on `ℝ × ℝ`, oriented so that the frames `(e, j e)` are positive, into `X_φ` with an almost
complex structure of block form `J ∂_s = T` along the image of `u`, with horizontal tangent images.
Let `x` have least period `d`, and let `u = τ ∘ v` for the orbit torus `τ` of `x` and a map `v`.
Then every point of the torus `(ℝ / ℤ) × (ℝ / dℤ)` has exactly `deg v` preimages under `v`. -/
theorem degree_eq_ncard_of_orbitTorus_comp_eq
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    (hd : minimalPeriod φ x = d) (hτv : orbitTorus φ h ∘ v = u)
    (y : UnitAddCircle × AddCircle (d : ℝ)) :
    degree o ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v =
      (v ⁻¹' {y}).ncard := by
  cases isEmpty_or_nonempty C with
  | inl _ =>
    -- On an empty surface all hypotheses of the torus statement hold vacuously.
    exact degree_eq_ncard_of_isPseudoholomorphicAt_addCircleProd_of_injective_mfderiv ho
      (fun c ↦ isEmptyElim c) (fun c ↦ isEmptyElim c) (fun c ↦ isEmptyElim c) y
  | inr _ =>
    have hv := contMDiff_and_isPseudoholomorphicAt_of_orbitTorus_comp_eq h hu ho hhol hS hH
      (mfderiv_ne_zero_of_injective (hinj (Classical.arbitrary C))) hd hτv
    exact degree_eq_ncard_of_isPseudoholomorphicAt_addCircleProd_of_injective_mfderiv ho hv.1 hv.2
      (fun c ↦ injective_mfderiv_of_injective_mfderiv_comp
        ((contMDiff_orbitTorus h).mdifferentiableAt (by simp)) (hv.1.mdifferentiableAt (by simp))
        (hτv ▸ hinj c)) y

/-- **An immersed pseudoholomorphic horizontal curve is embedded exactly when its covering
multiplicity is one.** Let `u` be a smooth pseudoholomorphic immersion of a compact connected
boundaryless surface `C` modelled on `ℝ × ℝ`, oriented so that the frames `(e, j e)` are positive,
into `X_φ` with an almost complex structure of block form `J ∂_s = T` along the image of `u`, with
horizontal tangent images. Let `C` be nonempty, let `x` have least period `d`, and let `u = τ ∘ v`
for the orbit torus `τ` of `x` and a map `v`. Then `u` is injective if and only if `deg v = 1`. -/
theorem injective_iff_degree_eq_one_of_orbitTorus_comp_eq [Nonempty C]
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    (hd : minimalPeriod φ x = d) (hτv : orbitTorus φ h ∘ v = u) :
    Injective u ↔
      degree o ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v = 1 := by
  obtain ⟨hv, hvhol⟩ := contMDiff_and_isPseudoholomorphicAt_of_orbitTorus_comp_eq h hu ho hhol hS
    hH (mfderiv_ne_zero_of_injective (hinj (Classical.arbitrary C))) hd hτv
  rw [← injective_iff_degree_eq_one_of_isPseudoholomorphicAt_addCircleProd_of_injective_mfderiv ho
    hv hvhol fun c ↦ injective_mfderiv_of_injective_mfderiv_comp
      ((contMDiff_orbitTorus h).mdifferentiableAt (by simp)) (hv.mdifferentiableAt (by simp))
      (hτv ▸ hinj c), ← hτv]
  -- The orbit torus over a primitive orbit is injective.
  exact ((injective_orbitTorus_iff h).2 hd).of_comp_iff v

end SmoothMappingTorus

end TauCeti
