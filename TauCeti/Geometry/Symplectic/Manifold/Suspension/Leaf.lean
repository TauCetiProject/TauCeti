/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.MappingTorus.Orbit
public import TauCeti.Geometry.Symplectic.Manifold.Harmonic
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

A pseudoholomorphic curve may have critical points, and for those the orbit is closed as soon as
the curve is not constant. Suppose `J ∂_s = T` along `u`, and that `x` is not periodic. Then
`u = (σ, [τ, x])` for a circle-valued `σ` and a smooth real time coordinate `τ`
(`TauCeti.SmoothMappingTorus.exists_contMDiff_eq_mk_of_minimalPeriod_eq_zero`), and the
Cauchy–Riemann equation says `dτ (j e) = dσ e`. So `τ` is a harmonic function on the compact
surface `C`, whose conjugate differential is the closed one-form `dσ`. Hence `τ` is constant
(`TauCeti.SmoothAlmostComplexStructure.mvfderiv_eq_zero_of_isClosed`), then `dσ = dτ ∘ j = 0`,
and `u` is constant. A nonconstant curve therefore lies over a primitive closed orbit of least
period `d > 0`, and it lifts to a smooth map `v` into the orbit torus `(ℝ / ℤ) × (ℝ / dℤ)`. Whether
`v` is surjective, and with which degree it covers the torus, is not decided here.

## Main results

All declarations are in the namespace `TauCeti.SmoothMappingTorus`.

* `range_subset_univ_prod_orbit_flow_of_mfderiv_mem_suspensionHorizontalSubspace`: a
  differentiable map from a preconnected manifold with horizontal tangent images lies in one leaf
  `(ℝ / ℤ) × γ`.
* `range_subset_range_orbitTorus_of_mfderiv_mem_suspensionHorizontalSubspace`: that leaf is the
  image of an orbit torus.
* `minimalPeriod_pos_of_mfderiv_mem_suspensionHorizontalSubspace`: for a compact immersed
  horizontal curve, the orbit is closed.
* `exists_contMDiff_orbitTorus_comp_eq_of_mfderiv_mem_suspensionHorizontalSubspace`: a horizontal
  curve over a closed orbit lifts smoothly to its orbit torus.
* `exists_isLocalDiffeomorph_orbitTorus_comp_eq_of_mfderiv_mem_suspensionHorizontalSubspace`: a
  compact connected immersed horizontal surface factors through the orbit torus by a surjective
  local diffeomorphism.
* `range_eq_range_orbitTorus_of_mfderiv_mem_suspensionHorizontalSubspace`: its image is exactly
  the image of the orbit torus.
* `range_subset_univ_prod_orbit_flow_of_integralTopForm_eq_zero`: a compact connected
  pseudoholomorphic curve of zero vertical area lies in one leaf.
* `mfderiv_eq_zero_of_minimalPeriod_eq_zero`: a compact connected pseudoholomorphic horizontal
  curve over an orbit that is not closed is constant.
* `minimalPeriod_pos_of_mfderiv_ne_zero_of_isPseudoholomorphicAt`: a nonconstant compact connected
  pseudoholomorphic horizontal curve lies over a closed orbit.
* `minimalPeriod_pos_of_integralTopForm_eq_zero`: for a compact connected immersed
  pseudoholomorphic curve of zero vertical area, that leaf lies over a closed orbit.
* `minimalPeriod_pos_of_integralTopForm_eq_zero_of_mfderiv_ne_zero`: the same for every
  nonconstant curve of zero vertical area, without the immersion hypothesis.
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

/-- **Horizontal curves over a closed orbit lift to its orbit torus.** Let `u` be a smooth map from
a preconnected manifold into `X_φ = (ℝ / ℤ) × Y_φ`, whose tangent images all lie in the horizontal
plane `span(∂_s, T)`, and let `(s, [t, x])` be one of its values, where `x` has positive least
period `d`. Then `u` factors as `u = τ ∘ v` through the orbit torus
`τ : (ℝ / ℤ) × (ℝ / dℤ) → X_φ`, `(s, θ) ↦ (s, [θ, x])`, by a smooth map `v`. -/
theorem exists_contMDiff_orbitTorus_comp_eq_of_mfderiv_mem_suspensionHorizontalSubspace
    [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I' ∞ C] [PreconnectedSpace C]
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) {d : ℕ} [Fact (0 < (d : ℝ))]
    (h : IsPeriodicPt φ d x) (hd : minimalPeriod φ x = d) :
    ∃ v : C → UnitAddCircle × AddCircle (d : ℝ),
      ContMDiff I' (𝓘(ℝ).prod 𝓘(ℝ)) ∞ v ∧ orbitTorus φ h ∘ v = u := by
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
  exact ⟨v, fun c' ↦ (ContMDiffAt.iff_comp_isImmersionAt (hemb.isImmersion.isImmersionAt (v c'))).2
    ⟨hvcont.continuousAt, hτv ▸ hu c'⟩, hτv⟩

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
  obtain ⟨v, hvsmooth, hτv⟩ :=
    exists_contMDiff_orbitTorus_comp_eq_of_mfderiv_mem_suspensionHorizontalSubspace hu hH hc h hd
  have hemb := (isSmoothEmbedding_orbitTorus_iff h (by simp)).2 hd
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
  exact IsClopen.eq_univ ⟨(isCompact_range hvsmooth.continuous).isClosed, hloc.isOpen_range⟩
    (range_nonempty v)

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

omit [FiniteDimensional ℝ E'] in
/-- The differential of a map `u = (σ, [τ, x])` into one leaf `(ℝ / ℤ) × {[r, x]}`, with a
smooth time coordinate `τ`, in the frame `(∂_s, T)`: `du e = dσ(e) ∂_s + dτ(e) T`. Here
`dσ(e)` is the value of the pulled back time form `σ^* ds` of the circle. -/
private theorem mfderiv_apply_eq_of_forall_snd_eq_mk
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) {τ : C → ℝ}
    (hτ : ContMDiff I' 𝓘(ℝ) ∞ τ) {x : M} (hτx : ∀ c, (u c).2 = mk φ (τ c) x)
    (c : C) (e : TangentSpace I' c) :
    mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e =
      (SmoothForm.mpullback (Prod.fst ∘ u) (contMDiff_fst.comp hu) (AddCircle.timeForm 1)).1 c
          ![e] • (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) (u c)).symm
          ((1 : ℝ), 0) +
        mvfderiv I' τ c e • (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I)
          (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2) := by
  have hud := hu.mdifferentiable (by simp)
  -- The mapping torus component is the flow line `r ↦ [r, x]` after `τ`, so it moves along `T`
  -- at the rate `dτ`.
  have hγ : Prod.snd ∘ u = (fun r ↦ flow φ r (mk φ 0 x)) ∘ τ := funext fun c ↦ by
    rw [Function.comp_apply, Function.comp_apply, flow_mk, zero_add]
    exact hτx c
  have h2 : mfderiv I' (𝓘(ℝ).prod I) (Prod.snd ∘ u) c e =
      mvfderiv I' τ c e • timeVectorField φ (u c).2 := by
    have hpt : flow φ (τ c) (mk φ 0 x) = (u c).2 := by
      rw [flow_mk, zero_add]
      exact (hτx c).symm
    rw [hγ, ((isMIntegralCurve_flow φ (mk φ 0 x) (τ c)).comp c
      ((hτ.mdifferentiable (by simp)) c).hasMFDerivAt).mfderiv]
    -- The derivative of the flow line is `smulRight 1 T`, applied to `dτ e`; both differentials
    -- of `τ` are the same real number.
    calc _ = mvfderiv I' τ c e • timeVectorField φ (flow φ (τ c) (mk φ 0 x)) := rfl
      _ = _ := by rw [hpt]
  -- The two components of `du e`. Tangent vectors of the product are pairs by the definition of
  -- `TangentSpace`, as in `minimalPeriod_pos_of_mfderiv_mem_suspensionHorizontalSubspace`.
  have hfst : mfderiv I' 𝓘(ℝ) (Prod.fst ∘ u) c e =
      (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e).1 := by
    rw [mfderiv_comp c mdifferentiableAt_fst (hud c), mfderiv_fst]
    rfl
  have hsnd : mfderiv I' (𝓘(ℝ).prod I) (Prod.snd ∘ u) c e =
      (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e).2 := by
    rw [mfderiv_comp c mdifferentiableAt_snd (hud c), mfderiv_snd]
    rfl
  apply (Manifold.tangentSpaceProdEquiv (u c)).injective
  rw [map_add, map_smul, map_smul, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, Manifold.tangentSpaceProdEquiv_apply]
  -- The tangent line of the circle is `ℝ` by definition, but its scalar multiplication is not
  -- syntactically multiplication in `ℝ`, so `simp` cannot normalize these components; `change`
  -- restates them in `ℝ`.
  refine Prod.ext ?_ ?_
  · change (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e).1 =
      (SmoothForm.mpullback (Prod.fst ∘ u) (contMDiff_fst.comp hu) (AddCircle.timeForm 1)).1 c
        ![e] * 1 + mvfderiv I' τ c e * 0
    rw [mul_one, mul_zero, add_zero, SmoothForm.mpullback_apply, AddCircle.timeForm_apply]
    exact hfst.symm
  · change (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e).2 =
      (SmoothForm.mpullback (Prod.fst ∘ u) (contMDiff_fst.comp hu) (AddCircle.timeForm 1)).1 c
        ![e] • (0 : TangentSpace (𝓘(ℝ).prod I) (u c).2) +
        mvfderiv I' τ c e • timeVectorField φ (u c).2
    rw [smul_zero, zero_add, ← h2, hsnd]

omit [FiniteDimensional ℝ E'] in
/-- The Cauchy–Riemann equation for a map `u = (σ, [τ, x])` into one leaf, when `J ∂_s = T`:
since `J (a ∂_s + b T) = -b ∂_s + a T`, the identity `du (j e) = J (du e)` gives
`dτ (j e) = dσ(e)`, where `dσ(e)` is the value of the pulled back time form `σ^* ds`. -/
private theorem mvfderiv_apply_almostComplex_eq_of_forall_snd_eq_mk
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) {τ : C → ℝ}
    (hτ : ContMDiff I' 𝓘(ℝ) ∞ τ) {x : M} (hτx : ∀ c, (u c).2 = mk φ (τ c) x) {c : C}
    (hhol : IsPseudoholomorphicAt j J u c)
    (hS : J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (e : TangentSpace I' c) :
    mvfderiv I' τ c (j c e) =
      (SmoothForm.mpullback (Prod.fst ∘ u) (contMDiff_fst.comp hu) (AddCircle.timeForm 1)).1 c
        ![e] := by
  -- `J T = -∂_s`, since `J ∂_s = T` and `J² = -1`.
  have hJT : J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm
      ((0 : ℝ), timeVectorField φ (u c).2)) =
        -(Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0) := by
    rw [← hS, SmoothAlmostComplexStructure.apply_apply]
  have h := hhol.mfderiv_apply_commute e
  rw [mfderiv_apply_eq_of_forall_snd_eq_mk hu hτ hτx,
    mfderiv_apply_eq_of_forall_snd_eq_mk hu hτ hτx] at h
  -- Expose the linear map `J (u c)` to `map_add` and `map_smul`.
  beta_reduce at h hS hJT
  rw [map_add, map_smul, map_smul, hS, hJT] at h
  -- Compare the `T`-components through `dp (T) = 1`.
  have h2 := congrArg (fun w ↦ mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (u c).2
    (Manifold.tangentSpaceProdEquiv (u c) w).2) h
  simp only [map_add, map_smul, map_neg, ContinuousLinearEquiv.apply_symm_apply, Prod.snd_add,
    Prod.smul_snd, Prod.snd_neg, smul_zero, neg_zero, add_zero, zero_add,
    mfderiv_proj_timeVectorField] at h2
  -- `h2` reads `dτ (j e) • 1 = dσ(e) • 1` in the tangent line of the circle, which is `ℝ`.
  exact (mul_one (mvfderiv I' τ c (j c e))).symm.trans (h2.trans (mul_one (_ : ℝ)))

/-- **Pseudoholomorphic horizontal curves over orbits that are not closed are constant.** Let `u`
be a smooth pseudoholomorphic map from a compact connected boundaryless surface `C`, oriented so
that the frames `(e, j e)` are positive, into `X_φ` with an almost complex structure satisfying
`J ∂_s = T` along the image of `u`, and let every tangent image of `u` lie in the horizontal plane
`span(∂_s, T)`. If `(s, [t, x])` is a value of `u` with `x` not periodic for `φ`, then `u` has zero
differential everywhere.

Indeed `u = (σ, [τ, x])` for a circle-valued `σ` and a smooth real `τ`
(`exists_contMDiff_eq_mk_of_minimalPeriod_eq_zero`), and the Cauchy–Riemann equation with
`J ∂_s = T`, `J T = -∂_s` says `dτ (j e) = dσ e`. So the conjugate differential of `τ` is the
closed one-form `dσ`, and `τ` is constant
(`SmoothAlmostComplexStructure.mvfderiv_eq_zero_of_isClosed`); then `dσ = dτ ∘ j = 0` too. -/
theorem mfderiv_eq_zero_of_minimalPeriod_eq_zero [I'.Boundaryless] [T2Space C] [CompactSpace C]
    [PreconnectedSpace C] (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) (hx : minimalPeriod φ x = 0) (c' : C) :
    mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c' = 0 := by
  -- The mapping torus component is `[τ, x]` for a smooth real `τ`.
  obtain ⟨τ, hτ, hτx⟩ := exists_contMDiff_eq_mk_of_minimalPeriod_eq_zero
    (contMDiff_snd.comp hu) (by simp) (fun c e ↦
      mfderiv_snd_comp_mem_span_of_mem_suspensionHorizontalSubspace
        ((hu.mdifferentiable (by simp)) c) (hH c e)) hc hx
  -- `dτ ∘ j` is the closed one-form `σ^* ds`, so `τ` is constant, and then so is `σ`.
  have hCR (c : C) := mvfderiv_apply_almostComplex_eq_of_forall_snd_eq_mk hu hτ hτx (hhol c) (hS c)
  have hτ0 := j.mvfderiv_eq_zero_of_isClosed ho (hτ.of_le (by simp))
    ((AddCircle.isClosed_timeForm 1).mpullback _ _) hCR
  ext1 e
  rw [mfderiv_apply_eq_of_forall_snd_eq_mk hu hτ hτx, ← hCR, hτ0, zero_apply, zero_apply,
    zero_smul, zero_smul, add_zero]
  rfl

/-- **Nonconstant pseudoholomorphic horizontal curves lie over closed orbits.** Let `u` be a smooth
pseudoholomorphic map from a compact connected boundaryless surface `C`, oriented so that the
frames `(e, j e)` are positive, into `X_φ` with an almost complex structure satisfying `J ∂_s = T`
along the image of `u`, and let every tangent image of `u` lie in the horizontal plane
`span(∂_s, T)`. If the differential of `u` is nonzero somewhere, then for every value `(s, [t, x])`
of `u`, the point `x` is periodic for `φ`: its least period is positive. Unlike
`minimalPeriod_pos_of_mfderiv_mem_suspensionHorizontalSubspace`, `u` may have critical points. -/
theorem minimalPeriod_pos_of_mfderiv_ne_zero_of_isPseudoholomorphicAt [I'.Boundaryless]
    [T2Space C] [CompactSpace C] [PreconnectedSpace C]
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (hS : ∀ c, J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c))
    {c₀ : C} (hne : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) : 0 < minimalPeriod φ x :=
  Nat.pos_of_ne_zero fun hx ↦
    hne (mfderiv_eq_zero_of_minimalPeriod_eq_zero hu ho hhol hS hH hc hx c₀)

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

/-- **Nonconstant curves of zero vertical area lie over closed orbits.** Let `u` be a smooth
pseudoholomorphic map from a compact connected boundaryless surface `C`, oriented so that the
frames `(e, j e)` are positive, into `X_φ` with an almost complex structure of block form along the
image of `u` whose vertical restriction is tamed by `ω_v`. If the vertical area `∫_C u^* ω_v`
vanishes and `u` is not constant, then for every value `(s, [t, x])` of `u`, the point `x` is
periodic for `φ`: its least period is positive. No immersion hypothesis is needed. -/
theorem minimalPeriod_pos_of_integralTopForm_eq_zero_of_mfderiv_ne_zero [I'.Boundaryless]
    [T2Space C] [CompactSpace C] [PreconnectedSpace C]
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
    {c₀ : C} (hne : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) : 0 < minimalPeriod φ x :=
  minimalPeriod_pos_of_mfderiv_ne_zero_of_isPseudoholomorphicAt hu ho hhol hS
    ((integralTopForm_mpullback_mpullback_snd_fiberForm_eq_zero_iff hu ho hhol hS hV htame).1 h0)
    hne hc

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
