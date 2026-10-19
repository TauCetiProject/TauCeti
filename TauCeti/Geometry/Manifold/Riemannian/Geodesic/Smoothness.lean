/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Spray
public import TauCeti.Geometry.Manifold.IntegralCurve.Regularity
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
  `C^(n + 2)` and its Riemannian metric is `C^(n + 1)`, with
  `TauCeti.Manifold.contMDiff_one_geodesicSpray` the `C^1` case consumed by the integral-curve
  API and `TauCeti.Manifold.contMDiff_infty_geodesicSpray` the smooth case used for geodesic flows.
* `TauCeti.Manifold.isGeodesicCurveOn_proj_of_isMIntegralCurveOn`: every spray integral curve
  on a set with unique derivatives projects to a geodesic.
* `IsMIntegralCurveOn.isGeodesicCurveOnFrom_proj`: its initial data are encoded by its value
  at zero, including for nondegenerate closed parameter intervals.

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

/-- **The geodesic spray is a `C^1` vector field** on the tangent bundle of a `C^3` manifold with
a `C^2` Riemannian metric.  This is the regularity at which Mathlib's integral-curve existence,
uniqueness and extension theorems consume the spray. -/
theorem contMDiff_one_geodesicSpray [IsManifold I 3 M]
    [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)] :
    CMDiff 1 (fun z : TangentBundle I M ↦
      (⟨z, geodesicSpray I M z⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
  contMDiff_geodesicSpray (I := I) (M := M) (n := (1 : ℕ∞ω)) (m := 3) (k := 2)
    (by norm_num) (by norm_num)

/-- **The geodesic spray is a smooth vector field** on the tangent bundle of a smooth manifold
with a smooth Riemannian metric. -/
theorem contMDiff_infty_geodesicSpray [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    CMDiff ∞ (fun z : TangentBundle I M ↦
      (⟨z, geodesicSpray I M z⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
  contMDiff_geodesicSpray (I := I) (M := M) (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp)

/-- **The base curve of an integral curve of the geodesic spray is a geodesic.** The integral
curve equation supplies `C²` regularity within any parameter set with unique derivatives;
no regularity of the projection needs to be assumed separately. -/
theorem isGeodesicCurveOn_proj_of_isMIntegralCurveOn [I.Boundaryless] [IsManifold I 3 M]
    [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
    {z : ℝ → TangentBundle I M} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hz : IsMIntegralCurveOn z (geodesicSpray I M) s) :
    IsGeodesicCurveOn I (fun t ↦ (z t).proj) s := by
  have : IsManifold I (2 + 1) M := IsManifold.of_le (n := 3) (by norm_num)
  let _ : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hz2 := contMDiffOn_two_of_isMIntegralCurveOn hs hz
    (fun _ _ ↦ (contMDiff_one_geodesicSpray (I := I) (M := M)).contMDiffAt)
  have hbase : ContMDiffOn 𝓘(ℝ, ℝ) I 2 (fun t ↦ (z t).proj) s :=
    (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x)
      (IB := I) (n := (2 : ℕ∞ω))).comp_contMDiffOn hz2
  exact (isMIntegralCurveOn_curveVelocityLiftWithin_iff hs hbase).1
    (hz.congr fun t ht ↦ (eq_curveVelocityLiftWithin_of_isMIntegralCurveOn (hs t ht) hz ht).symm)

end TauCeti.Manifold

namespace IsMIntegralCurveOn

open TauCeti.Manifold

variable [I.Boundaryless] [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]

/-- The projection of an integral curve of the geodesic spray on a parameter set with unique
derivatives is the geodesic whose initial data are encoded by its value at zero. -/
theorem isGeodesicCurveOnFrom_proj
    {z : ℝ → TangentBundle I M} {s : Set ℝ} {w : TangentBundle I M}
    (hz : IsMIntegralCurveOn z (geodesicSpray I M) s) (hs : UniqueDiffOn ℝ s)
    (h0s : (0 : ℝ) ∈ s) (h0 : z 0 = w) :
    IsGeodesicCurveOnFrom I (fun t ↦ (z t).proj) s w.proj w.2 := by
  refine ⟨isGeodesicCurveOn_proj_of_isMIntegralCurveOn hs hz, h0s, ?_⟩
  simpa only [curveVelocityLiftWithin_apply] using
    (eq_curveVelocityLiftWithin_of_isMIntegralCurveOn (hs 0 h0s) hz h0s).symm.trans h0

end IsMIntegralCurveOn

end
