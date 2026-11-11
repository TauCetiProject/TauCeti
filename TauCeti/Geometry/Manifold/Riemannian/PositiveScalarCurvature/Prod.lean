/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Topology
public import TauCeti.Geometry.Manifold.Riemannian.Prod.Topology
public import Mathlib.Topology.Connected.PathConnected

/-!
# Products of families of positive scalar curvature metrics

The scalar curvature of a product metric is the sum of the scalar curvatures of the factors, and
the product of metrics is jointly continuous in the chart C² topology
(`Bundle.ContMDiffRiemannianMetric.continuous_prodTangentSpace`). This file gives the family
counterparts of the product laws for positive scalar curvature.

Isotopies, that is C²-continuous paths of metrics of positive scalar curvature, on two manifolds
assemble into an isotopy on their product (`JoinedIn.prodTangentSpace`); the path on the second
factor only needs nonnegative scalar curvature. Neither manifold needs to be compact.

On compact manifolds, shrinking a factor of positive scalar curvature dominates the scalar
curvature of a whole compact family of metrics on the other factor at once
(`IsCompact.exists_pos_forall_hasPositiveScalarCurvature_prodTangentSpace_rescale`). In
particular, for any path of metrics `g_t` on a compact manifold, of arbitrary scalar curvature, and
any metric `g₂` of positive scalar curvature on a compact manifold, `g_t × c g₂` is an isotopy of
metrics of positive scalar curvature for every sufficiently small `c > 0`
(`Joined.exists_pos_joinedIn_prodTangentSpace_rescale`).

These are the family counterparts of
`Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.prodTangentSpace_of_nonneg` and
`Bundle.ContMDiffRiemannianMetric.exists_pos_hasPositiveScalarCurvature_prodTangentSpace_rescale`.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
-/

public section

open Bundle Set
open scoped ContDiff Manifold TauCeti.MetricC2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- An isotopy through metrics of positive scalar curvature and a C²-continuous path through
metrics of nonnegative scalar curvature assemble into an isotopy through metrics of positive scalar
curvature on the product, with the given product metrics as its exact endpoints. -/
theorem JoinedIn.prodTangentSpace [J.Boundaryless]
    {g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {h₀ h₁ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
    (hg : JoinedIn {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) |
      g.HasPositiveScalarCurvature} g₀ g₁)
    (hh : JoinedIn {h : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y) |
      ∀ y, 0 ≤ h.scalarCurvature y} h₀ h₁) :
    JoinedIn {G : ContMDiffRiemannianMetric (I.prod J) ∞ (E × F)
        (fun p : M × N ↦ TangentSpace (I.prod J) p) | G.HasPositiveScalarCurvature}
      (g₀.prodTangentSpace h₀) (g₁.prodTangentSpace h₁) := by
  have hcont := ContMDiffRiemannianMetric.continuous_prodTangentSpace (I := I) (J := J)
    (M := M) (N := N) 2 continuous_fst continuous_snd
  refine ((hg.prod hh).map hcont.continuousOn).mono ?_
  rintro _ ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩
  exact hg.prodTangentSpace_of_nonneg hh

variable [CompactSpace M] [CompactSpace N]

open ContMDiffRiemannianMetric in
/-- **Shrinking a compact factor of positive scalar curvature, uniformly in a family.** On
compact manifolds, let `K` be a set of metrics on `M`, compact in the chart C² topology, and let
`g₂` be a metric of positive scalar curvature on `N`. Then there is `ε > 0` such that `g × c g₂`
has positive scalar curvature for every `g ∈ K` and every `0 < c < ε`. -/
theorem IsCompact.exists_pos_forall_hasPositiveScalarCurvature_prodTangentSpace_rescale
    {K : Set (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))} (hK : IsCompact K)
    {g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
    (h₂ : g₂.HasPositiveScalarCurvature) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (c : ℝ) (hc : 0 < c), c < ε → ∀ g ∈ K,
      (g.prodTangentSpace
        (g₂.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)).HasPositiveScalarCurvature := by
  -- The scalar curvature is jointly continuous on the compact set `K × M`, so bounded below.
  obtain ⟨m, hm⟩ := (hK.prod isCompact_univ).bddBelow_image
    continuous_scalarCurvature_chartC2.continuousOn
  obtain ⟨δ, hδ, hδg⟩ := h₂.exists_pos_le
  obtain ⟨ε, hε, hfε⟩ :=
    exists_pos_forall_hasPositiveScalarCurvature_prodTangentSpace_rescale_of_forall_le
      (f := fun g : K ↦ (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)))
      (fun g x ↦ hm ⟨(g, x), ⟨g.2, mem_univ x⟩, rfl⟩) hδ hδg
  exact ⟨ε, hε, fun c hc hcε g hg ↦ hfε c hc hcε ⟨g, hg⟩⟩

/-- **A small factor of positive scalar curvature turns paths into isotopies.** On compact
manifolds, let `g₀` and `g₁` be metrics on `M` joined by a C²-continuous path of metrics, of
arbitrary scalar curvature, and let `g₂` be a metric of positive scalar curvature on `N`. Then
for every sufficiently small `c > 0`, the product path with `c g₂` is an isotopy of metrics of
positive scalar curvature from `g₀ × c g₂` to `g₁ × c g₂`. -/
theorem Joined.exists_pos_joinedIn_prodTangentSpace_rescale [J.Boundaryless]
    {g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} (hg : Joined g₀ g₁)
    {g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
    (h₂ : g₂.HasPositiveScalarCurvature) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (c : ℝ) (hc : 0 < c), c < ε →
      JoinedIn {G : ContMDiffRiemannianMetric (I.prod J) ∞ (E × F)
          (fun p : M × N ↦ TangentSpace (I.prod J) p) | G.HasPositiveScalarCurvature}
        (g₀.prodTangentSpace (g₂.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc))
        (g₁.prodTangentSpace (g₂.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)) := by
  obtain ⟨γ⟩ := hg
  obtain ⟨ε, hε, hγε⟩ :=
    IsCompact.exists_pos_forall_hasPositiveScalarCurvature_prodTangentSpace_rescale
      (isCompact_range γ.continuous) h₂
  refine ⟨ε, hε, fun c hc hcε ↦ ⟨γ.map (ContMDiffRiemannianMetric.continuous_prodTangentSpace
    (I := I) (J := J) (M := M) (N := N) 2 continuous_id continuous_const), fun t ↦ ?_⟩⟩
  exact hγε c hc hcε (γ t) ⟨t, rfl⟩
