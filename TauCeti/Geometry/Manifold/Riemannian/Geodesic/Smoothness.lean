/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Spray
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# Smoothness of the geodesic spray

The geodesic spray of a smooth Riemannian manifold is a smooth vector field on its tangent
bundle. In tangent-bundle coordinates it is

`(x, v) ↦ (v, -Γₓ(v, v))`,

so this follows from smoothness of the Christoffel map of the Levi-Civita connection. This is the
regularity input needed to apply existence and uniqueness theorems for integral curves to the
geodesic equation.

## Main result

* `TauCeti.Manifold.contMDiff_geodesicSpray`: the geodesic spray is `C^n` when the manifold is
  `C^(n + 2)` and its Riemannian metric is `C^(n + 1)`.
* `IsMIntegralCurveOn.isGeodesicCurveOnFrom_proj`: a spray integral curve on an open set projects
  to a geodesic with the initial data encoded by its value at zero.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

public section

open Bundle CovariantDerivative Module Set
open scoped ContDiff Manifold Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {n m k : ℕ∞ω}

namespace TauCeti.Manifold

/-- In the trivialization of the iterated tangent bundle centred at `z₀`, the geodesic spray has
the Christoffel-coordinate formula associated to the tangent trivialization centred at `z₀.proj`.
This isolates the coordinate identification between the two tangent-space wrappers. -/
private theorem trivializationAt_geodesicSpray_coord [IsManifold I 2 M]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (z₀ z : TangentBundle I M) (hz : z.proj ∈ (chartAt H z₀.proj).source) :
    let e := trivializationAt E (TangentSpace I) z₀.proj
    let eT := trivializationAt (E × E) (TangentSpace I.tangent) z₀
    (eT (TotalSpace.mk' (E × E) z (geodesicSpray I M z))).2 =
      ((e z).2, -christoffelMap (finBasis ℝ E)
        ((leviCivitaConnection I M).isCovariantDerivativeOn (s := e.baseSet)) z.proj
        (e z).2 (e z).2) := by
  dsimp only
  have hbase : z.proj ∈ (extChartAt I z₀.proj).source := by
    rw [extChartAt_source I z₀.proj]
    exact hz
  have hze : z.proj ∈ (trivializationAt E (TangentSpace I) z₀.proj).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hz
  have hzT : z ∈ (trivializationAt (E × E) (TangentSpace I.tangent) z₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (TangentBundle.mem_chart_source_iff z z₀).2 hz
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hzT,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hze,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hz,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hzT]
  exact tangentCoordChange_geodesicSpray (I := I) (M := M) hbase z.2

/-- **The geodesic spray is a `C^n` vector field on the tangent bundle.** A `C^(n + 1)` metric
and `C^(n + 2)` manifold structure suffice. In particular, the spray of a smooth Riemannian
manifold is smooth. -/
theorem contMDiff_geodesicSpray [IsManifold I 2 M] [IsManifold I m M]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]
    (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) :
    ContMDiff I.tangent I.tangent.tangent n
      (fun z : TangentBundle I M ↦
        TotalSpace.mk' (E × E) z (geodesicSpray I M z)) := by
  let _ : IsManifold I (n + 2) M := IsManifold.of_le (n := m) hm
  let _ : IsManifold I (n + 1) M :=
    IsManifold.of_le (n := m) ((by gcongr; norm_num : n + 1 ≤ n + 2).trans hm)
  let _ : IsManifold I (n + 1 + 1) M :=
    IsManifold.of_le (n := m) (by rwa [add_assoc, one_add_one_eq_two])
  let _ : IsContMDiffRiemannianBundle I (n + 1) E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := k) hk
  let _ : ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let _ : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let _ : IsManifold I.tangent (n + 1) (TangentBundle I M) := inferInstance
  let _ : ContMDiffVectorBundle n (E × E)
      (TangentSpace I.tangent : TangentBundle I M → Type _) I.tangent :=
    TangentBundle.contMDiffVectorBundle
  intro z₀
  let e := trivializationAt E (TangentSpace I) z₀.proj
  let eT := trivializationAt (E × E) (TangentSpace I.tangent) z₀
  have hz₀ : z₀ ∈ eT.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  rw [eT.contMDiffAt_section_iff hz₀]
  have hz₀e : z₀ ∈ e.source := by
    simpa only [e, TangentBundle.trivializationAt_source, mem_preimage] using
      mem_chart_source H z₀.proj
  have hopen : IsOpen e.source := e.open_source
  suffices hcoord : ContMDiffOn I.tangent 𝓘(ℝ, E × E) n
      (fun z : TangentBundle I M ↦
        ((e z).2, -christoffelMap (finBasis ℝ E)
          ((leviCivitaConnection I M).isCovariantDerivativeOn (s := e.baseSet)) z.proj
          (e z).2 (e z).2)) e.source by
    refine (hcoord z₀ hz₀e).contMDiffAt (hopen.mem_nhds hz₀e) |>.congr_of_eventuallyEq ?_
    · filter_upwards [hopen.mem_nhds hz₀e] with z hz
      have hzbase : z.proj ∈ (chartAt H z₀.proj).source := by
        simpa only [e, TangentBundle.trivializationAt_source, mem_preimage] using hz
      exact trivializationAt_geodesicSpray_coord z₀ z hzbase
  have hv : ContMDiffOn I.tangent 𝓘(ℝ, E) n (fun z ↦ (e z).2) e.source := by
    intro z hz
    exact (e.contMDiffOn z hz).snd
  have hproj : ContMDiffOn I.tangent I n
      (fun z : TangentBundle I M ↦ z.proj) e.source := by
    exact Bundle.contMDiffOn_proj (E := fun x : M ↦ TangentSpace I x)
  have hmaps : MapsTo (fun z : TangentBundle I M ↦ z.proj) e.source e.baseSet := by
    intro z hz
    simpa only [e, TangentBundle.trivializationAt_source, mem_preimage,
      TangentBundle.trivializationAt_baseSet] using hz
  have hΓ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (christoffelMap (finBasis ℝ E)
        ((leviCivitaConnection I M).isCovariantDerivativeOn (s := e.baseSet))) e.baseSet :=
    contMDiffOn_christoffelMap_leviCivitaConnection (n := n) (m := m) (k := k)
      (finBasis ℝ E) hm hk
  have hΓ' : ContMDiffOn I.tangent 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun z : TangentBundle I M ↦ christoffelMap (finBasis ℝ E)
        ((leviCivitaConnection I M).isCovariantDerivativeOn (s := e.baseSet)) z.proj) e.source :=
    hΓ.comp hproj hmaps
  exact (contMDiffOn_prod_module_iff _).2
    ⟨hv, ((hΓ'.clm_apply hv).clm_apply hv).neg⟩

end TauCeti.Manifold

namespace IsMIntegralCurveOn

open TauCeti.Manifold

variable [I.Boundaryless] [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]

/-- The projection of an integral curve of the geodesic spray on an open set is the geodesic
whose initial data are encoded by the integral curve's value at zero. -/
theorem isGeodesicCurveOnFrom_proj
    {z : ℝ → TangentBundle I M} {s : Set ℝ} {w : TangentBundle I M}
    (hz : IsMIntegralCurveOn z (geodesicSpray I M) s) (hs : IsOpen s)
    (h0s : (0 : ℝ) ∈ s) (h0 : z 0 = w) :
    IsGeodesicCurveOnFrom I (fun t ↦ (z t).proj) s w.proj w.2 := by
  -- `C²` regularity of the curve is read in the tangent bundle, whose `C²` vector-bundle
  -- structure is exactly what `IsManifold I 3 M` supplies.
  have : IsManifold I (2 + 1) M := IsManifold.of_le (n := 3) (by norm_num)
  let _ : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hspray : CMDiff 1 (fun q : TangentBundle I M ↦
      (⟨q, geodesicSpray I M q⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
    contMDiff_geodesicSpray (I := I) (M := M) (n := (1 : ℕ∞ω)) (m := 3) (k := 2)
      (by norm_num) (by norm_num)
  have hbase : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 2
      (fun t ↦ (z t).proj) s := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro t ht
    have hcurveAt : IsMIntegralCurveAt z (geodesicSpray I M) t :=
      hz.isMIntegralCurveAt (hs.mem_nhds ht)
    have hcurveTwo : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I.tangent 2 z t :=
      IsMIntegralCurveAt.contMDiffAt_two hcurveAt hspray.contMDiffAt
    have hproj : ContMDiffAt I.tangent I 2 TotalSpace.proj (z t) :=
      Bundle.contMDiffAt_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := (2 : ℕ∞ω))
    have hbaseAt : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2
        ((fun q : TangentBundle I M ↦ q.proj) ∘ z) t :=
      hproj.comp t hcurveTwo
    obtain ⟨u, hu, hbaseu⟩ := contMDiffAt_iff_contMDiffOn_nhds (n := (2 : ℕ∞ω))
      (by norm_num) |>.mp hbaseAt
    obtain ⟨V, hVsub, hVopen, htV⟩ := mem_nhds_iff.mp hu
    refine ⟨V, hVopen, htV, ?_⟩
    exact (hbaseu.mono (inter_subset_right.trans hVsub)).congr (fun _ _ ↦ rfl)
  have hunique : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  refine ⟨isGeodesicCurveOn_proj_of_isMIntegralCurveOn hunique hz hbase, h0s, ?_⟩
  simpa only [curveVelocityLiftWithin_apply] using
    (eq_curveVelocityLiftWithin_of_isMIntegralCurveOn (hunique 0 h0s) hz h0s).symm.trans h0

end IsMIntegralCurveOn

end
