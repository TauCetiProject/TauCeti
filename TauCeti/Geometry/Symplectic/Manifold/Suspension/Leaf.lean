/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.MappingTorus.Orbit
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.VerticalArea

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Horizontal curves in a symplectic suspension lie in one leaf and fill it

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
`(ℝ / ℤ) × γ`. When `γ` is the orbit through `[0, x]`, this leaf is the image of the orbit torus
`(s, θ) ↦ (s, [θ, x])` parametrized with the least period of `x`.

For an immersed curve, the orbit `γ` is closed. Let `u` have injective differential, from a compact
connected boundaryless manifold `C` of dimension at least two. If the mapping torus component of
`u` had zero differential at some point, the image of the differential of `u` there would lie in
the line spanned by `∂_s`, which is impossible. So that component is a compact curve tangent to
`T` with nowhere vanishing differential, and it lies in a closed orbit
(`TauCeti.SmoothMappingTorus.minimalPeriod_pos_of_mfderiv_ne_zero`). Hence the leaf of `u` is the
embedded torus `(ℝ / ℤ) × γ` over a primitive closed orbit.

When `C` is a surface, the curve fills its leaf. The orbit torus `τ : (s, θ) ↦ (s, [θ, x])`, with
`θ ∈ ℝ / dℤ` for the least period `d` of `x`, is a smooth embedding, so `u` lifts through it to a
smooth map `v : C → (ℝ / ℤ) × (ℝ / dℤ)` with `u = τ ∘ v`. The differential of `v` is injective
because that of `u` is, so it is invertible between these two-dimensional tangent spaces, and the
inverse function theorem makes `v` a local diffeomorphism. Its image is then open, and compact,
in the connected torus, so `v` is surjective and the image of `u` is exactly `(ℝ / ℤ) × γ`.
Neither compactness of `M` nor nondegeneracy or closedness of `σ` is used.

## Main results

All declarations are in the namespace `TauCeti.SmoothMappingTorus`.

* `range_subset_univ_prod_orbit_flow_of_mfderiv_mem_suspensionHorizontalSubspace`: a
  differentiable map from a preconnected manifold with horizontal tangent images lies in one leaf
  `(ℝ / ℤ) × γ`.
* `range_subset_range_orbitTorus_of_mfderiv_mem_suspensionHorizontalSubspace`: that leaf is the
  image of an orbit torus.
* `minimalPeriod_pos_of_mfderiv_mem_suspensionHorizontalSubspace`: for a compact immersed
  horizontal curve, the orbit is closed.
* `exists_isLocalDiffeomorph_orbitTorus_comp_eq_of_mfderiv_mem_suspensionHorizontalSubspace`: a
  compact connected immersed horizontal surface factors through the orbit torus by a surjective
  local diffeomorphism.
* `range_eq_range_orbitTorus_of_mfderiv_mem_suspensionHorizontalSubspace`: its image is exactly
  the image of the orbit torus.
* `range_subset_univ_prod_orbit_flow_of_integralTopForm_eq_zero`: a compact connected
  pseudoholomorphic curve of zero vertical area lies in one leaf.
* `minimalPeriod_pos_of_integralTopForm_eq_zero`: for a compact connected immersed
  pseudoholomorphic curve of zero vertical area, that leaf lies over a closed orbit.
* `range_eq_range_orbitTorus_of_integralTopForm_eq_zero`: the image of such a curve is exactly
  the orbit torus `(ℝ / ℤ) × γ` over that primitive closed orbit.

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

open Set Function
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
  rintro _ ⟨c', rfl⟩
  exact ⟨mem_univ _, range_subset_orbit_flow_of_mfderiv_mem_span
    (fun c ↦ mdifferentiableAt_snd.comp c (hu c))
    (fun c e ↦ mfderiv_snd_comp_mem_span_of_mem_suspensionHorizontalSubspace (hu c) (hH c e)) c
    ⟨c', rfl⟩⟩

/-- **Horizontal curves lie in one orbit torus.** Let `u` be a differentiable map from a
preconnected manifold into `X_φ = (ℝ / ℤ) × Y_φ` whose tangent images all lie in the horizontal
plane `span(∂_s, T)`, and let `(s, [t, x])` be one of its values. Then the image of `u` lies in
the image `(ℝ / ℤ) × γ` of the orbit torus of the orbit `γ` through `[0, x]`, parametrized with
the least period of `x`. When `x` is not periodic, that least period is zero and `γ` is the whole
orbit line. -/
theorem range_subset_range_orbitTorus_of_mfderiv_mem_suspensionHorizontalSubspace
    [IsManifold I' 1 C] [PreconnectedSpace C]
    (hu : MDifferentiable I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u)
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    range u ⊆ range (orbitTorus φ (isPeriodicPt_minimalPeriod φ x)) := by
  let := (flow φ).toAddAction
  have horbit : (flow φ).orbit (mk φ 0 x) = (flow φ).orbit (u c).2 :=
    AddAction.orbit_eq_iff.2 ((flow φ).mem_orbit_iff.2 ⟨-t, by rw [hc, flow_mk, add_neg_cancel]⟩)
  rw [range_orbitTorus, range_closedOrbit, horbit]
  exact range_subset_univ_prod_orbit_flow_of_mfderiv_mem_suspensionHorizontalSubspace hu hH c

/-- **Compact immersed horizontal curves lie over closed orbits.** Let `u` be a differentiable
map with injective differential from a compact connected boundaryless manifold of dimension at
least two into `X_φ = (ℝ / ℤ) × Y_φ`, whose tangent images all lie in the horizontal plane
`span(∂_s, T)`. Then for every value `(s, [t, x])` of `u`, the point `x` is periodic for `φ`:
its least period is positive. So the orbit torus containing the image of `u`
(`range_subset_range_orbitTorus_of_mfderiv_mem_suspensionHorizontalSubspace`) is the embedded
torus `(ℝ / ℤ) × γ` over a primitive closed orbit `γ`. -/
theorem minimalPeriod_pos_of_mfderiv_mem_suspensionHorizontalSubspace [IsManifold I' 1 C]
    [I'.Boundaryless] [CompactSpace C] [PreconnectedSpace C] (h2 : 2 ≤ Module.finrank ℝ E')
    (hu : MDifferentiable I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u)
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) : 0 < minimalPeriod φ x := by
  refine minimalPeriod_pos_of_mfderiv_ne_zero (fun c ↦ mdifferentiableAt_snd.comp c (hu c))
    (fun c e ↦ mfderiv_snd_comp_mem_span_of_mem_suspensionHorizontalSubspace (hu c) (hH c e))
    (fun c h0 ↦ ?_) hc
  -- The two components of the differential of `u`.
  have hfst : ∀ e, mfderiv I' 𝓘(ℝ) (Prod.fst ∘ u) c e =
      (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e).1 := fun e ↦ by
    rw [mfderiv_comp c mdifferentiableAt_fst (hu c), mfderiv_fst]
    -- The tangent space of `X_φ` is the product of the tangent spaces of its factors only up to
    -- definitional unfolding of `TangentSpace`, so `ContinuousLinearMap.comp_apply` cannot
    -- rewrite here; both sides are the first component of `du e`.
    rfl
  have hsnd : ∀ e, (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e).2 = 0 := fun e ↦ by
    have h := DFunLike.congr_fun h0 e
    rwa [mfderiv_comp c mdifferentiableAt_snd (hu c), mfderiv_snd] at h
  -- If the mapping torus component has zero differential, the circle component has injective
  -- differential, into a line.
  let L : E' →L[ℝ] ℝ := mfderiv I' 𝓘(ℝ) (Prod.fst ∘ u) c
  have hinj' : Injective L := fun e₁ e₂ he ↦
    hinj c (Prod.ext ((hfst e₁).symm.trans (he.trans (hfst e₂))) ((hsnd e₁).trans (hsnd e₂).symm))
  have hle := LinearMap.finrank_le_finrank_of_injective (f := L.toLinearMap) hinj'
  rw [Module.finrank_self] at hle
  omega

/-- **Compact immersed horizontal surfaces cover an orbit torus.** Let `u` be a smooth map with
injective differential from a compact connected boundaryless surface `C` into
`X_φ = (ℝ / ℤ) × Y_φ`, whose tangent images all lie in the horizontal plane `span(∂_s, T)`, and
let `(s, [t, x])` be one of its values, where `x` has least period `d`. Then `u` factors as
`u = τ ∘ v` through the orbit torus `τ : (ℝ / ℤ) × (ℝ / dℤ) → X_φ`, `(s, θ) ↦ (s, [θ, x])`, by a
surjective smooth local diffeomorphism `v`. In particular `u` maps onto the whole torus
`(ℝ / ℤ) × γ`. -/
theorem exists_isLocalDiffeomorph_orbitTorus_comp_eq_of_mfderiv_mem_suspensionHorizontalSubspace
    [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I' ∞ C] [I'.Boundaryless]
    [CompactSpace C] [ConnectedSpace C] (h2 : Module.finrank ℝ E' = 2)
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) {d : ℕ} [Fact (0 < (d : ℝ))]
    (h : IsPeriodicPt φ d x) (hd : minimalPeriod φ x = d)
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c)) :
    ∃ v : C → UnitAddCircle × AddCircle (d : ℝ),
      IsLocalDiffeomorph I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v ∧ Surjective v ∧ orbitTorus φ h ∘ v = u := by
  have : FiniteDimensional ℝ E' := .of_finrank_eq_succ h2
  -- The image of `u` lies in the image of the orbit torus, so `u` lifts through it.
  have hrange : range u ⊆ range (orbitTorus φ h) := by
    have := range_subset_range_orbitTorus_of_mfderiv_mem_suspensionHorizontalSubspace
      (hu.mdifferentiable (by simp)) hH hc
    rw [range_orbitTorus, range_closedOrbit] at this ⊢
    exact this
  choose v hv using fun c' ↦ hrange (mem_range_self c')
  have hτv : orbitTorus φ h ∘ v = u := funext hv
  -- The orbit torus is a smooth embedding, so the lift is continuous and then smooth.
  have hemb := (isSmoothEmbedding_orbitTorus_iff h (by simp)).2 hd
  have hvcont : Continuous v := hemb.isEmbedding.continuous_iff.2 (hτv ▸ hu.continuous)
  have hvsmooth : ContMDiff I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v := fun c' ↦
    (ContMDiffAt.iff_comp_isImmersionAt (hemb.isImmersion.isImmersionAt (v c'))).2
      ⟨hvcont.continuousAt, hτv ▸ hu c'⟩
  -- Its differential is injective, between spaces of dimension two, hence invertible.
  have hloc : IsLocalDiffeomorph I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v := by
    refine isLocalDiffeomorph_of_mfderiv_eq hvsmooth (by simp) fun c' ↦ ?_
    have hchain : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c' =
        (mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (orbitTorus φ h) (v c')).comp
          (mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c') := by
      rw [← hτv]
      exact mfderiv_comp c' (hemb.contMDiff.mdifferentiableAt (by simp))
        (hvsmooth.mdifferentiableAt (by simp))
    have hvinj : Injective (mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c') := fun a b hab ↦
      hinj c' ((DFunLike.congr_fun hchain a).trans
        ((congrArg (mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (orbitTorus φ h) (v c'))
          hab).trans (DFunLike.congr_fun hchain b).symm))
    -- The tangent spaces of `C` and of the torus are the model spaces `E'` and `ℝ × ℝ`, by the
    -- definition of `TangentSpace`; the dimension count and the equivalence below use this.
    have hrank : Module.finrank ℝ E' = Module.finrank ℝ (ℝ × ℝ) := by
      rw [h2, Module.finrank_prod, Module.finrank_self]
    have hbij : Bijective (mfderiv I' (𝓘(ℝ).prod 𝓘(ℝ)) v c') :=
      ⟨hvinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hvinj⟩
    exact ⟨(LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv, rfl⟩
  -- Its image is open and compact in the connected torus, hence everything.
  refine ⟨v, hloc, range_eq_univ.1 ?_, hτv⟩
  exact IsClopen.eq_univ ⟨(isCompact_range hvcont).isClosed, hloc.isOpen_range⟩ (range_nonempty v)

/-- **Compact immersed horizontal surfaces fill one leaf.** Let `u` be a smooth map with
injective differential from a compact connected boundaryless surface `C` into
`X_φ = (ℝ / ℤ) × Y_φ`, whose tangent images all lie in the horizontal plane `span(∂_s, T)`, and
let `(s, [t, x])` be one of its values. Then the image of `u` is exactly the image
`(ℝ / ℤ) × γ` of the orbit torus of the closed orbit `γ` through `[0, x]`, parametrized with the
least period of `x`, which is positive. -/
theorem range_eq_range_orbitTorus_of_mfderiv_mem_suspensionHorizontalSubspace
    [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I' ∞ C] [I'.Boundaryless]
    [CompactSpace C] [ConnectedSpace C] (h2 : Module.finrank ℝ E' = 2)
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    range u = range (orbitTorus φ (isPeriodicPt_minimalPeriod φ x)) := by
  have hpos := minimalPeriod_pos_of_mfderiv_mem_suspensionHorizontalSubspace h2.ge
    (hu.mdifferentiable (by simp)) hH hinj hc
  have : Fact (0 < (minimalPeriod φ x : ℝ)) := ⟨Nat.cast_pos.2 hpos⟩
  obtain ⟨v, -, hsurj, hτv⟩ :=
    exists_isLocalDiffeomorph_orbitTorus_comp_eq_of_mfderiv_mem_suspensionHorizontalSubspace h2 hu
      hH hc (isPeriodicPt_minimalPeriod φ x) rfl hinj
  rw [← hτv, range_comp, hsurj.range_eq, image_univ]

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

/-- **Compact immersed curves of zero vertical area lie over closed orbits.** Let `u` be a smooth
pseudoholomorphic map with injective differential from a compact connected boundaryless surface
`C`, oriented so that the frames `(e, j e)` are positive, into `X_φ` with an almost complex
structure of block form along the image of `u` whose vertical restriction is tamed by `ω_v`. If
the vertical area `∫_C u^* ω_v` vanishes, then for every value `(s, [t, x])` of `u`, the point `x`
is periodic for `φ`: its least period is positive. -/
theorem minimalPeriod_pos_of_integralTopForm_eq_zero [I'.Boundaryless] [CompactSpace C]
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
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) : 0 < minimalPeriod φ x :=
  minimalPeriod_pos_of_mfderiv_mem_suspensionHorizontalSubspace
    (by rw [← o.card_eq, Fintype.card_fin]) (hu.mdifferentiable (by simp))
    ((integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff hu ho hhol hS hV htame).1 h0)
    hinj hc

/-- **Compact immersed curves of zero vertical area fill one leaf.** Let `u` be a smooth
pseudoholomorphic map with injective differential from a compact connected boundaryless surface
`C`, oriented so that the frames `(e, j e)` are positive, into `X_φ` with an almost complex
structure of block form along the image of `u` whose vertical restriction is tamed by `ω_v`. If
the vertical area `∫_C u^* ω_v` vanishes, then for every value `(s, [t, x])` of `u`, the image of
`u` is exactly the image `(ℝ / ℤ) × γ` of the orbit torus of the primitive closed orbit `γ`
through `[0, x]`. -/
theorem range_eq_range_orbitTorus_of_integralTopForm_eq_zero [I.Boundaryless]
    [FiniteDimensional ℝ E] [I'.Boundaryless] [CompactSpace C] [ConnectedSpace C]
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
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    range u = range (orbitTorus φ (isPeriodicPt_minimalPeriod φ x)) :=
  range_eq_range_orbitTorus_of_mfderiv_mem_suspensionHorizontalSubspace
    (by rw [← o.card_eq, Fintype.card_fin]) hu
    ((integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff hu ho hhol hS hV htame).1 h0)
    hinj hc

end SmoothMappingTorus

end TauCeti
