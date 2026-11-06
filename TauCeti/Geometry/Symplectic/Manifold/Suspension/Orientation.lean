/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.AddCircle
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Leaf

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Symplectic.Manifold.Suspension.PeriodicTorus

/-!
# Orientation of the orbit-torus parametrization of a horizontal curve

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M`, let `Y_φ` be its
smooth mapping torus, with suspension vector field `T = ∂_t`, and let `X_φ = (ℝ / ℤ)_s × Y_φ`. For
a point `x` of positive period `d`, the orbit torus
`τ : (ℝ / ℤ) × (ℝ / dℤ) → X_φ`, `(s, θ) ↦ (s, [θ, x])`
(`TauCeti.SmoothMappingTorus.orbitTorus`) agrees with the periodic torus
`TauCeti.SmoothMappingTorus.periodicTorus`, so it has injective differential
`dτ (a, b) = a ∂_s + b T` (`TauCeti.SmoothMappingTorus.mfderiv_periodicTorus`). Orient the torus as
the product of the positive orientations of its two circles (`AddCircle.orientation`), with the
`s`-direction first.

Let `J` be an almost complex structure on `X_φ` of block form at a point of the orbit torus,
`J ∂_s = T`, and let a map `u : (C, j) → (X_φ, J)` from a surface, pseudoholomorphic at `c`, factor
as `u = τ ∘ v`. The differential `dτ` is injective and carries the standard frame
`((1, 0), (0, 1))` of the torus to `(∂_s, T)`. So when `dv` is invertible at `c`, the frame
`(e, f)` of `T_c C` with `dv e = (1, 0)` and `dv f = (0, 1)` satisfies
`dτ (dv (j e)) = J (dτ (1, 0)) = J ∂_s = T = dτ (dv f)`, that is, `f = j e`. Hence, if `C` is
oriented so that every frame `(e, j e)` is positive, `v` is orientation preserving at `c`
(`TauCeti.SmoothMappingTorus.isOrientationPreservingAt_of_orbitTorus_comp_eq`).

For a compact connected immersed pseudoholomorphic curve of zero vertical area, with the block and
taming hypotheses of the leaf theorem, the factor `v` through the orbit torus of the primitive
closed orbit is a surjective local diffeomorphism. It is therefore orientation preserving
everywhere. When `u` is moreover injective, `v` is a diffeomorphism of `C` onto the torus
`(ℝ / ℤ) × (ℝ / dℤ)`, and an orientation-preserving one. This is the oriented parametrization of
the embedded image `(ℝ / ℤ) × γ`.

## Main results

* `mfderiv_apply_almostComplex_eq_of_orbitTorus_comp_eq`: for a factor `v` through the orbit
  torus of a pseudoholomorphic map, `dv e = (1, 0)` implies `dv (j e) = (0, 1)`.
* `isOrientationPreservingAt_of_orbitTorus_comp_eq`: a factor through the orbit torus of a
  pseudoholomorphic map preserves orientation wherever its differential is invertible.
* `exists_isLocalDiffeomorph_orbitTorus_comp_eq_of_integralTopForm_eq_zero`:
  a compact connected immersed pseudoholomorphic curve of zero vertical area factors through the
  orbit torus by a surjective orientation-preserving local diffeomorphism.
* `exists_diffeomorph_orbitTorus_comp_eq_of_integralTopForm_eq_zero`:
  if the curve is also injective, the factor is an orientation-preserving diffeomorphism.

## References

* Eleny-Nicoleta Ionel and Thomas H. Parker, *Gromov invariants and symplectic maps*,
  Mathematische Annalen 314 (1999), 127–158 (pseudoholomorphic tori over periodic orbits in
  `S¹ × Y_φ`).
* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354.
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
  {J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
    (UnitAddCircle × SmoothMappingTorus φ)}

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C] {j : SmoothAlmostComplexStructure I' C}
  {u : C → UnitAddCircle × SmoothMappingTorus φ} {v : C → UnitAddCircle × AddCircle (d : ℝ)}
  {c : C}

/-- **The Cauchy–Riemann equation on the standard frame of the orbit torus.** Let `u = τ ∘ v` be
a pseudoholomorphic map at `c` that factors through the orbit torus `τ` by a map `v`
differentiable at `c`, and let `J` have block form `J ∂_s = T` at `u c`. If `dv e = (1, 0)`, then
`dv (j e) = (0, 1)`. -/
theorem mfderiv_apply_almostComplex_eq_of_orbitTorus_comp_eq
    (hv : MDifferentiableAt I' (𝓘(ℝ).prod 𝓘(ℝ)) v c) (hτv : orbitTorus φ h ∘ v = u)
    (hhol : IsPseudoholomorphicAt j J u c)
    (hS : J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    {e : TangentSpace I' c} (he : mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c e = ((1 : ℝ), (0 : ℝ))) :
    mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c (j c e) = ((0 : ℝ), (1 : ℝ)) := by
  subst hτv
  have hτ : orbitTorus φ h = periodicTorus φ h :=
    funext fun p ↦ by rw [orbitTorus_apply, periodicTorus_apply]
  -- The differential of the orbit torus is `dτ (a, b) = a ∂_s + b T`.
  have hdτ (w : ℝ × ℝ) :
      mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (orbitTorus φ h) (v c) w =
        (Manifold.tangentSpaceProdEquiv _).symm
          (w.1, w.2 • timeVectorField φ (orbitTorus φ h (v c)).2) := by
    rw [hτ, mfderiv_periodicTorus, periodicTorus_apply]
  have hchain (w : TangentSpace I' c) :
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (orbitTorus φ h ∘ v) c w =
        mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (orbitTorus φ h) (v c)
          (mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c w) := by
    rw [mfderiv_comp c ((contMDiff_orbitTorus h).mdifferentiableAt (by simp)) hv,
      ContinuousLinearMap.comp_apply]
  -- Apply `dτ`, which is injective and sends `(1, 0)` to `∂_s` and `(0, 1)` to `T`.
  apply hτ ▸ injective_mfderiv_periodicTorus h (v c)
  calc mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (orbitTorus φ h) (v c)
        (mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c (j c e))
      = J (orbitTorus φ h (v c))
          (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (orbitTorus φ h ∘ v) c e) := by
        rw [← hchain]
        exact hhol.mfderiv_apply_commute e
    _ = J (orbitTorus φ h (v c))
          ((Manifold.tangentSpaceProdEquiv (orbitTorus φ h (v c))).symm ((1 : ℝ), 0)) := by
        rw [hchain, he, hdτ]
        simp only [zero_smul]
    _ = (Manifold.tangentSpaceProdEquiv _).symm
          ((0 : ℝ), timeVectorField φ (orbitTorus φ h (v c)).2) := hS
    _ = _ := by
        rw [hdτ]
        simp only [one_smul]

variable [FiniteDimensional ℝ E'] {o : Manifold.Orientation I' C (Fin 2)}

/-- **The factor through the orbit torus preserves orientation.** Let `u = τ ∘ v` be a
pseudoholomorphic map at `c` that factors through the orbit torus `τ` by a map `v` with invertible
differential at `c`, let `J` have block form `J ∂_s = T` at `u c`, and orient `C` so that the
frames `(e, j e)` at `c` are positive. Then `v` preserves orientation at `c`, for the product of
the positive orientations of the two circles of the torus. -/
theorem isOrientationPreservingAt_of_orbitTorus_comp_eq
    (hτv : orbitTorus φ h ∘ v = u) (hhol : IsPseudoholomorphicAt j J u c)
    (hS : J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hinv : (mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c).IsInvertible)
    (ho : ∀ b : Module.Basis (Fin 2) ℝ (TangentSpace I' c), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c) :
    Manifold.Orientation.IsOrientationPreservingAt o
      ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v c := by
  obtain ⟨L, hL⟩ := hinv
  have hLw (w : TangentSpace I' c) : L w = mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c w := by
    rw [← hL, ContinuousLinearEquiv.coe_coe]
  have hv : MDifferentiableAt I' (𝓘(ℝ).prod 𝓘(ℝ)) v c :=
    mdifferentiableAt_of_mfderiv_injective (hL ▸ L.injective)
  -- The standard frame `((1, 0), (0, 1))` of the torus, which is positive for the product
  -- orientation, pulls back along `dv` to a frame `(e, j e)`.
  let b : Module.Basis (Fin 2) ℝ (TangentSpace I' c) :=
    (Module.Basis.finTwoProd ℝ).map L.symm.toLinearEquiv
  have hLb (i : Fin 2) : L (b i) = Module.Basis.finTwoProd ℝ i :=
    L.apply_symm_apply (Module.Basis.finTwoProd ℝ i)
  have hb : b 1 = j c (b 0) := by
    apply L.injective
    rw [hLb, Module.Basis.finTwoProd_one, hLw]
    exact (mfderiv_apply_almostComplex_eq_of_orbitTorus_comp_eq h hv hτv hhol hS
      (by rw [← hLw, hLb, Module.Basis.finTwoProd_zero])).symm
  rw [Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ L hL, ← ho b hb,
    ← Module.Basis.orientation_map, AddCircle.orientationAt_orientation_prod_orientation]
  congr 1
  ext i
  exact hLb i

variable [I.Boundaryless] [FiniteDimensional ℝ E] [I'.Boundaryless] [CompactSpace C]
  [ConnectedSpace C] {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- **Oriented parametrization of a curve of zero vertical area.** Let `u` be a smooth
pseudoholomorphic map with injective differential from a compact connected boundaryless surface
`C`, oriented so that the frames `(e, j e)` are positive, into `X_φ` with an almost complex
structure of block form along the image of `u` whose vertical restriction is tamed by `ω_v`. If
the vertical area `∫_C u^* ω_v` vanishes, let `(s, [t, x])` be a value of `u`, where `x` has least
period `d`. Then `u = τ ∘ v` for the orbit torus `τ` of the primitive closed orbit through `x` and
a surjective local diffeomorphism `v : C → (ℝ / ℤ) × (ℝ / dℤ)` that preserves orientation at every
point, for the product of the positive orientations of the two circles. -/
theorem exists_isLocalDiffeomorph_orbitTorus_comp_eq_of_integralTopForm_eq_zero
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
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} (hc : (u c).2 = mk φ t x) (hd : minimalPeriod φ x = d) :
    ∃ v : C → UnitAddCircle × AddCircle (d : ℝ),
      IsLocalDiffeomorph I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v ∧ Surjective v ∧ orbitTorus φ h ∘ v = u ∧
        ∀ c, Manifold.Orientation.IsOrientationPreservingAt o
          ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) v c := by
  obtain ⟨v, hloc, hsurj, hτv⟩ :=
    exists_isLocalDiffeomorph_orbitTorus_comp_eq_of_mfderiv_mem_suspensionHorizontalSubspace
      (by rw [← o.card_eq, Fintype.card_fin]) hu
      ((integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff hu ho hhol hS hV htame).1 h0)
      hc h hd hinj
  exact ⟨v, hloc, hsurj, hτv, fun c' ↦ isOrientationPreservingAt_of_orbitTorus_comp_eq h hτv
    (hhol c') (hS c') (hloc.isInvertible_mfderiv (by simp) c') (ho c')⟩

/-- **Oriented parametrization of an embedded curve of zero vertical area.** Under the hypotheses
of `exists_isLocalDiffeomorph_orbitTorus_comp_eq_of_integralTopForm_eq_zero`, if `u` is moreover
injective, then `u = τ ∘ Φ` for an orientation-preserving diffeomorphism
`Φ : C ≃ (ℝ / ℤ) × (ℝ / dℤ)` onto the orbit torus of the primitive closed orbit. -/
theorem exists_diffeomorph_orbitTorus_comp_eq_of_integralTopForm_eq_zero
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (hu₁ : Injective u)
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
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} (hc : (u c).2 = mk φ t x) (hd : minimalPeriod φ x = d) :
    ∃ Φ : C ≃ₘ⟮I', 𝓘(ℝ).prod 𝓘(ℝ)⟯ UnitAddCircle × AddCircle (d : ℝ),
      orbitTorus φ h ∘ Φ = u ∧ ∀ c, Manifold.Orientation.IsOrientationPreservingAt o
        ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ))) Φ c := by
  obtain ⟨v, hloc, hsurj, hτv, hor⟩ :=
    exists_isLocalDiffeomorph_orbitTorus_comp_eq_of_integralTopForm_eq_zero h hu ho hhol hS hV
      htame h0 hinj hc hd
  have hvinj : Injective v := fun a b hab ↦ hu₁ (by rw [← hτv, comp_apply, hab, comp_apply])
  have hΦ : ⇑(hloc.diffeomorphOfBijective ⟨hvinj, hsurj⟩) = v := coe_diffeomorphOfBijective
  refine ⟨hloc.diffeomorphOfBijective ⟨hvinj, hsurj⟩,
    (congrArg (orbitTorus φ h ∘ ·) hΦ).trans hτv, fun c' ↦ ?_⟩
  rw [hΦ]
  exact hor c'

end SmoothMappingTorus

end TauCeti
