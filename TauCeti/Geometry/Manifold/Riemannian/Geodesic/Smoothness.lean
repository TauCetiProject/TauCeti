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

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

public section

open Bundle CovariantDerivative Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {n m k : ℕ∞ω}
  [IsManifold I 2 M] [IsManifold I m M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]

/-- **The geodesic spray is a `C^n` vector field on the tangent bundle.** A `C^(n + 1)` metric
and `C^(n + 2)` manifold structure suffice: one derivative forms the Christoffel map, while one
more makes the tangent-bundle coordinate changes `C^(n + 1)`. In particular, the spray of a
smooth Riemannian manifold is smooth. -/
theorem contMDiff_geodesicSpray (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) :
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
    change z₀.proj ∈ (chartAt H z₀.proj).source
    exact mem_chart_source _ _
  have hopen : IsOpen e.source := e.open_source
  suffices hcoord : ContMDiffOn I.tangent 𝓘(ℝ, E × E) n
      (fun z : TangentBundle I M ↦
        ((e z).2, -christoffelMap (finBasis ℝ E)
          ((leviCivita I M).isCovariantDerivativeOn (s := e.baseSet)) z.proj
          (e z).2 (e z).2)) e.source by
    refine (hcoord z₀ hz₀e).contMDiffAt (hopen.mem_nhds hz₀e) |>.congr_of_eventuallyEq ?_
    · filter_upwards [hopen.mem_nhds hz₀e] with z hz
      have hzbase : z.proj ∈ (chartAt H z₀.proj).source := hz
      have hbase : z.proj ∈ (extChartAt I z₀.proj).source := by
        rw [extChartAt_source I z₀.proj]
        exact hzbase
      have hze : z.proj ∈ e.baseSet := hz
      have hzT : z ∈ eT.baseSet := by
        change z ∈ (chartAt (ModelProd H E) z₀).source
        exact (TangentBundle.mem_chart_source_iff z z₀).2 hzbase
      rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ eT hzT,
        ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hze,
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hzbase,
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hzT]
      exact tangentCoordChange_geodesicSpray (I := I) (M := M) hbase z.2
  have hv : ContMDiffOn I.tangent 𝓘(ℝ, E) n (fun z ↦ (e z).2) e.source := by
    intro z hz
    exact (e.contMDiffOn z hz).snd
  have hproj : ContMDiffOn I.tangent I n
      (fun z : TangentBundle I M ↦ z.proj) e.source := by
    exact Bundle.contMDiffOn_proj (E := fun x : M ↦ TangentSpace I x)
  have hmaps : MapsTo (fun z : TangentBundle I M ↦ z.proj) e.source e.baseSet := by
    intro z hz
    exact hz
  have hΓ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (christoffelMap (finBasis ℝ E)
        ((leviCivita I M).isCovariantDerivativeOn (s := e.baseSet))) e.baseSet :=
    contMDiffOn_christoffelMap_leviCivita (n := n) (m := m) (k := k)
      (finBasis ℝ E) hm hk
  have hΓ' : ContMDiffOn I.tangent 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun z : TangentBundle I M ↦ christoffelMap (finBasis ℝ E)
        ((leviCivita I M).isCovariantDerivativeOn (s := e.baseSet)) z.proj) e.source :=
    hΓ.comp hproj hmaps
  exact (contMDiffOn_prod_module_iff _).2
    ⟨hv, ((hΓ'.clm_apply hv).clm_apply hv).neg⟩

end TauCeti.Manifold

end
