/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Flux
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Topology.Covering.Proper
import TauCeti.Topology.SeparatedMap

/-!
# Lifting asymptotically Euclidean ends to Riemannian coverings

Let `p : N → M` be a Riemannian covering map, that is a covering map which is a local Riemannian
isometry, and let `φ` be an asymptotically Euclidean end of `M` of order `t`, parametrized by the
exterior `U = {x : R < ‖x‖}` of a ball in `ℝⁿ`. For `n ≥ 3` the exterior `U` is simply connected,
so `φ` lifts through `p`: for every base point `x₀ ∈ U` and every point `y` of `N` over `φ x₀`
there is a lift `ψ` of `φ` on `U` with `ψ x₀ = y`. Each lift is an asymptotically Euclidean end of
`N` of the same order, with the same pulled-back metric coefficients, hence the same coordinate
ADM flux at every radius and the same mass. The lifts through distinct points of the fibre have
disjoint images, and together they cover the preimage `p⁻¹(φ U)`. So over a covering with fibres
of cardinality `d`, each end of `M` lifts to exactly `d` ends of `N`, each with the mass of the end
below.

Consequently a finite-ended asymptotically Euclidean structure on `M` lifts to one on any finite
Riemannian covering `N`: the ends of `N` are indexed by pairs of an end of `M` and a point of the
fibre over its base point, and the complement of their images is the preimage of the compact
complement downstairs, which is compact since a covering with finite fibres is proper. This is how
the positive mass theorem passes to finite covers, for instance to the orientation double cover.

## Main results

* `TauCeti.normalizedCoordinateFlux_pullbackMetricCoeff_eq_of_eqOn_comp` and
  `TauCeti.tendsto_normalizedCoordinateFlux_pullbackMetricCoeff_iff_of_eqOn_comp`: a lift of an end
  through a local Riemannian isometry has the coordinate flux, and so the mass, of the end below;
  `TauCeti.normalizedCoordinateFlux_pullbackMetricCoeff_comp` is the invariance of the flux under
  composition with a local Riemannian isometry.
* `TauCeti.IsAsymptoticallyEuclideanEnd.exists_continuousOn_lift` and
  `TauCeti.IsAsymptoticallyEuclideanEnd.exists_lift`: for `n ≥ 3`, an end lifts continuously
  through a covering map, and through a Riemannian covering map to an end of the same order,
  through any prescribed point over a base point.
* `TauCeti.IsAsymptoticallyEuclideanEnd.pairwise_disjoint_image_lift` and
  `TauCeti.IsAsymptoticallyEuclideanEnd.preimage_image_eq_iUnion_image_lift`: the lifts through the
  points of the fibre over a base point have pairwise disjoint images whose union is the preimage of
  the image of the end.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean.exists_lift`: a finite-ended asymptotically
  Euclidean structure lifts to a surjective Riemannian covering with finite fibres, with one end
  over each end and each point of the fibre over its base point.

## References

* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Theorem 9.6 and
  the remark after Theorem 10.3.
* A. Hatcher, *Algebraic Topology*, Propositions 1.33 and 1.34, for the lifting of maps out of
  simply connected spaces and the uniqueness of lifts.
-/

public section

open Bundle Function Manifold Metric Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {p : N → M} {t R : ℝ}

/-! ### The flux of a lift -/

/-- If `ψ`, differentiable on the exterior of the ball of radius `R`, lifts `φ` there through a
local Riemannian isometry `p`, then `ψ` and `φ` have the same coordinate ADM flux at every radius
`r > R`. -/
theorem normalizedCoordinateFlux_pullbackMetricCoeff_eq_of_eqOn_comp
    (hp : IsLocalRiemannianIsometry J I p) {ψ : EuclideanSpace ℝ (Fin n) → N}
    {φ : EuclideanSpace ℝ (Fin n) → M}
    (hψ : MDifferentiableOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ψ (closedBall 0 R)ᶜ)
    (h : EqOn (p ∘ ψ) φ (closedBall 0 R)ᶜ) {r : ℝ} (hr : R < r) :
    normalizedCoordinateFlux (pullbackMetricCoeff J ψ) r =
      normalizedCoordinateFlux (pullbackMetricCoeff I φ) r :=
  normalizedCoordinateFlux_congr_of_eqOn (fun x hx ↦
    pullbackMetricCoeff_eqOn_of_eqOn_comp hp isClosed_closedBall.isOpen_compl hψ h
      (by simpa using hx)) hr

/-- **A lift of an end has the mass of the end below.** If `ψ`, differentiable on the exterior of
the ball of radius `R`, lifts `φ` there through a local Riemannian isometry `p`, then the coordinate
ADM flux of `ψ` tends to `m` exactly when that of `φ` does. -/
theorem tendsto_normalizedCoordinateFlux_pullbackMetricCoeff_iff_of_eqOn_comp
    (hp : IsLocalRiemannianIsometry J I p) {ψ : EuclideanSpace ℝ (Fin n) → N}
    {φ : EuclideanSpace ℝ (Fin n) → M}
    (hψ : MDifferentiableOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ψ (closedBall 0 R)ᶜ)
    (h : EqOn (p ∘ ψ) φ (closedBall 0 R)ᶜ) {m : ℝ} :
    Tendsto (normalizedCoordinateFlux (pullbackMetricCoeff J ψ)) atTop (𝓝 m) ↔
      Tendsto (normalizedCoordinateFlux (pullbackMetricCoeff I φ)) atTop (𝓝 m) :=
  tendsto_congr' <| (eventually_gt_atTop R).mono fun _ hr ↦
    normalizedCoordinateFlux_pullbackMetricCoeff_eq_of_eqOn_comp hp hψ h hr

/-- **Invariance of the flux under isometries.** Composing a parametrization, differentiable on
the exterior of the ball of radius `R`, with a local Riemannian isometry does not change its
coordinate ADM flux at any radius `r > R`. -/
theorem normalizedCoordinateFlux_pullbackMetricCoeff_comp (hp : IsLocalRiemannianIsometry J I p)
    {ψ : EuclideanSpace ℝ (Fin n) → N}
    (hψ : MDifferentiableOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ψ (closedBall 0 R)ᶜ) {r : ℝ}
    (hr : R < r) :
    normalizedCoordinateFlux (pullbackMetricCoeff I (p ∘ ψ)) r =
      normalizedCoordinateFlux (pullbackMetricCoeff J ψ) r :=
  (normalizedCoordinateFlux_pullbackMetricCoeff_eq_of_eqOn_comp hp hψ (eqOn_refl _ _) hr).symm

/-! ### Lifting one end -/

/-- In dimension at least two, the exterior of a ball in `ℝⁿ` is preconnected. -/
private theorem isPreconnected_compl_closedBall_euclideanSpace (hn : 1 < n) (R : ℝ) :
    IsPreconnected (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
  refine (isPathConnected_compl_closedBall ?_ 0 R).isConnected.isPreconnected
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast hn

namespace IsAsymptoticallyEuclideanEnd

variable {φ : EuclideanSpace ℝ (Fin n) → M}

/-- For `n ≥ 3`, an asymptotically Euclidean end `φ` of `M`, on the exterior of the ball of radius
`R`, lifts continuously through any covering map `p : N → M`: for every point `x₀` of the exterior
and every `y₀` over `φ x₀` there is a map `ψ`, continuous on the exterior, with `ψ x₀ = y₀` and
`p ∘ ψ = φ` there. The exterior is simply connected because `n ≥ 3`. -/
theorem exists_continuousOn_lift (hcov : IsCoveringMap p) (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (hn : 3 ≤ n) {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ (closedBall 0 R)ᶜ) {y₀ : N}
    (hy₀ : p y₀ = φ x₀) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → N, ContinuousOn ψ (closedBall 0 R)ᶜ ∧ ψ x₀ = y₀ ∧
      EqOn (p ∘ ψ) φ (closedBall 0 R)ᶜ := by
  classical
  set U := (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ
  have : SimplyConnectedSpace U := by
    refine simplyConnectedSpace_compl_closedBall ?_ 0 R
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 2 < n)
  have : LocallyPathConnectedSpace U := isClosed_closedBall.isOpen_compl.locallyPathConnectedSpace
  -- Lift `φ`, restricted to the simply connected exterior, through `p`, then extend the lift by
  -- `y₀` inside the ball.
  obtain ⟨G, ⟨hG₀, hG⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    ⟨U.domRestrict φ, h.contMDiffOn.continuousOn.domRestrict⟩ ⟨x₀, hx₀⟩ y₀ hy₀
  refine ⟨fun x ↦ if hx : x ∈ U then G ⟨x, hx⟩ else y₀, ?_, by simp [hx₀, hG₀],
    fun x hx ↦ by simpa [hx] using congrFun hG ⟨x, hx⟩⟩
  rw [continuousOn_iff_continuous_domRestrict]
  convert G.continuous using 1
  ext ⟨x, hx⟩
  simp [hx]

/-- **Lifting an end to a Riemannian covering.** For `n ≥ 3`, an asymptotically Euclidean end `φ`
of order `t` of `M`, on the exterior of the ball of radius `R`, lifts through a Riemannian covering
map `p : N → M`: for every point `x₀` of the exterior and every `y₀` over `φ x₀` there is an end
`ψ` of `N` of order `t` on the same exterior with `ψ x₀ = y₀` and `p ∘ ψ = φ` there. -/
theorem exists_lift [CompleteSpace F] [BoundarylessManifold J N] [IsManifold J ∞ N]
    [IsManifold I ∞ M] (hcov : IsCoveringMap p) (hp : IsLocalRiemannianIsometry J I p)
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (hn : 3 ≤ n) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ (closedBall 0 R)ᶜ) {y₀ : N} (hy₀ : p y₀ = φ x₀) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → N, IsAsymptoticallyEuclideanEnd J t R ψ ∧ ψ x₀ = y₀ ∧
      EqOn (p ∘ ψ) φ (closedBall 0 R)ᶜ := by
  obtain ⟨ψ, hcont, hψ₀, hψp⟩ := h.exists_continuousOn_lift hcov hn hx₀ hy₀
  -- The continuous lift is smooth, since `p` is a local diffeomorphism.
  have hsmooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J ∞ ψ (closedBall 0 R)ᶜ :=
    .of_comp_isLocalDiffeomorph (hp.isLocalDiffeomorph (n := ∞) (by simp) le_rfl) hcont
      (h.contMDiffOn.congr hψp)
  exact ⟨ψ, (h.congr fun x hx ↦ (hψp hx).symm).of_comp hp hsmooth, hψ₀, hψp⟩

/-- The lifts of an end of `M` through the points `y` of the fibre of a covering map `p` over
`φ x₀`, each continuous on the exterior of the ball and taking the value `y` at `x₀`, have pairwise
disjoint images on the exterior, in dimension at least two. -/
theorem pairwise_disjoint_image_lift (hcov : IsCoveringMap p)
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (hn : 1 < n) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ (closedBall 0 R)ᶜ) {ψ : p ⁻¹' {φ x₀} → EuclideanSpace ℝ (Fin n) → N}
    (hψ : ∀ y, ContinuousOn (ψ y) (closedBall 0 R)ᶜ) (hψ₀ : ∀ y, ψ y x₀ = y)
    (hψp : ∀ y, EqOn (p ∘ ψ y) φ (closedBall 0 R)ᶜ) :
    Pairwise fun y y' ↦ Disjoint (ψ y '' (closedBall 0 R)ᶜ) (ψ y' '' (closedBall 0 R)ᶜ) :=
  fun y y' hyy' ↦ hcov.isSeparatedMap.disjoint_image_of_eqOn_comp
    hcov.isLocalHomeomorph.isLocallyInjective (isPreconnected_compl_closedBall_euclideanSpace hn R)
    h.injOn (hψ y) (hψ y') (hψp y) (hψp y') hx₀ (by rwa [hψ₀, hψ₀, Ne, ← Subtype.ext_iff])

/-- **The preimage of an end is covered by its lifts.** For `n ≥ 3` and a covering map `p`, the
lifts of an end `φ` of `M` through the points `y` of the fibre over `φ x₀`, each
continuous on the exterior of the ball and taking the value `y` at `x₀`, have images on the exterior
whose union is the preimage under `p` of the image of `φ`. -/
theorem preimage_image_eq_iUnion_image_lift (hcov : IsCoveringMap p)
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (hn : 3 ≤ n)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ (closedBall 0 R)ᶜ)
    {ψ : p ⁻¹' {φ x₀} → EuclideanSpace ℝ (Fin n) → N}
    (hψ : ∀ y, ContinuousOn (ψ y) (closedBall 0 R)ᶜ) (hψ₀ : ∀ y, ψ y x₀ = y)
    (hψp : ∀ y, EqOn (p ∘ ψ y) φ (closedBall 0 R)ᶜ) :
    p ⁻¹' (φ '' (closedBall 0 R)ᶜ) = ⋃ y, ψ y '' (closedBall 0 R)ᶜ := by
  refine Subset.antisymm ?_ (iUnion_subset fun y ↦ ?_)
  · rintro z ⟨x, hx, hxz⟩
    -- Lift `φ` through `z` at `x`; this lift passes at `x₀` through a point `y` of the fibre, so
    -- it is the lift `ψ y`, which therefore takes the value `z` at `x`.
    obtain ⟨χ, hχ, hχx, hχp⟩ := h.exists_continuousOn_lift hcov hn hx hxz.symm
    have hy : χ x₀ ∈ p ⁻¹' {φ x₀} := hχp hx₀
    have hEq := hcov.eqOn_of_comp_eqOn
      (isPreconnected_compl_closedBall_euclideanSpace (by omega) R) (hψ ⟨χ x₀, hy⟩)
      hχ ((hψp _).trans hχp.symm) hx₀ (hψ₀ _)
    exact mem_iUnion.2 ⟨⟨χ x₀, hy⟩, x, hx, (hEq hx).trans hχx⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hψp y hx).symm⟩

end IsAsymptoticallyEuclideanEnd

/-! ### Lifting a finite-ended structure -/

namespace IsFiniteEndedAsymptoticallyEuclidean

variable {ι : Type*} {R : ι → ℝ} {φ : ι → EuclideanSpace ℝ (Fin n) → M}

/-- **Lifting a finite-ended structure to a finite Riemannian covering.** Let `p : N → M` be a
surjective Riemannian covering map with finite fibres, and let the ends `φ e` of `M` form a
finite-ended asymptotically Euclidean structure of order `t`, `n ≥ 3`, with base points `x₀ e` in
the exteriors of their balls. Then `N` carries a finite-ended asymptotically Euclidean structure
of order `t` whose ends `ψ ⟨e, y⟩` are indexed by an end `e` of `M` and a point `y` of `N` over
`φ e (x₀ e)`: each `ψ ⟨e, y⟩` lifts `φ e` on the exterior of the same ball and takes the value `y`
at `x₀ e`. In particular every end of `M` lifts to as many ends of `N` as there are sheets. -/
theorem exists_lift [CompleteSpace F] [BoundarylessManifold J N] [IsManifold J ∞ N]
    [IsManifold I ∞ M] (hcov : IsCoveringMap p) (hp : IsLocalRiemannianIsometry J I p)
    (hfin : ∀ x, Finite (p ⁻¹' {x})) (hsurj : Surjective p)
    (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) (hn : 3 ≤ n)
    (x₀ : ι → EuclideanSpace ℝ (Fin n)) (hx₀ : ∀ e, x₀ e ∈ (closedBall 0 (R e))ᶜ) :
    ∃ ψ : (Σ e, p ⁻¹' {φ e (x₀ e)}) → EuclideanSpace ℝ (Fin n) → N,
      IsFiniteEndedAsymptoticallyEuclidean J t (fun a ↦ R a.1) ψ ∧
        ∀ a, ψ a (x₀ a.1) = a.2 ∧ EqOn (p ∘ ψ a) (φ a.1) (closedBall 0 (R a.1))ᶜ := by
  choose ψ hψ hψ₀ hψp using fun a : Σ e, p ⁻¹' {φ e (x₀ e)} ↦
    (h.isAsymptoticallyEuclideanEnd a.1).exists_lift hcov hp hn (hx₀ a.1) a.2.property
  have hcont (a : Σ e, p ⁻¹' {φ e (x₀ e)}) : ContinuousOn (ψ a) (closedBall 0 (R a.1))ᶜ :=
    (hψ a).contMDiffOn.continuousOn
  -- Over each end `e` of `M`, the lifts `ψ ⟨e, y⟩` cover the preimage of the image of `e`.
  have hpre (e : ι) :
      p ⁻¹' (φ e '' (closedBall 0 (R e))ᶜ) = ⋃ y, ψ ⟨e, y⟩ '' (closedBall 0 (R e))ᶜ :=
    (h.isAsymptoticallyEuclideanEnd e).preimage_image_eq_iUnion_image_lift hcov hn (hx₀ e)
      (fun y ↦ hcont ⟨e, y⟩) (fun y ↦ hψ₀ ⟨e, y⟩) fun y ↦ hψp ⟨e, y⟩
  have hsub (a : Σ e, p ⁻¹' {φ e (x₀ e)}) :
      ψ a '' (closedBall 0 (R a.1))ᶜ ⊆ p ⁻¹' (φ a.1 '' (closedBall 0 (R a.1))ᶜ) :=
    (subset_iUnion (fun y ↦ ψ ⟨a.1, y⟩ '' (closedBall 0 (R a.1))ᶜ) a.2).trans (hpre a.1).superset
  have := h.finite
  obtain ⟨e⟩ := h.nonempty
  refine ⟨ψ, ⟨inferInstance, ?_, hψ, ?_, ?_⟩, fun a ↦ ⟨hψ₀ a, hψp a⟩⟩
  · obtain ⟨y, hy⟩ := hsurj (φ e (x₀ e))
    exact ⟨⟨e, y, hy⟩⟩
  · rintro ⟨e, y⟩ ⟨e', y'⟩ hne
    rcases eq_or_ne e e' with rfl | hee'
    · exact (h.isAsymptoticallyEuclideanEnd e).pairwise_disjoint_image_lift hcov (by omega)
        (hx₀ e) (fun y ↦ hcont ⟨e, y⟩) (fun y ↦ hψ₀ ⟨e, y⟩) (fun y ↦ hψp ⟨e, y⟩)
        fun hyy' ↦ hne (by rw [hyy'])
    · exact ((h.pairwise_disjoint hee').preimage p).mono (hsub ⟨e, y⟩) (hsub ⟨e', y'⟩)
  · -- The complement of the images of the lifted ends is the preimage of the compact complement
    -- of the images of the ends of `M`, which is compact since `p` is proper.
    have hU : (⋃ a : Σ e, p ⁻¹' {φ e (x₀ e)}, ψ a '' (closedBall 0 (R a.1))ᶜ) =
        p ⁻¹' ⋃ e, φ e '' (closedBall 0 (R e))ᶜ := by
      rw [preimage_iUnion, iUnion_sigma]
      exact iUnion_congr fun e ↦ (hpre e).symm
    rw [hU, ← preimage_compl]
    exact (hcov.isProperMap hfin).isCompact_preimage h.isCompact_compl_iUnion

end IsFiniteEndedAsymptoticallyEuclidean

end TauCeti
