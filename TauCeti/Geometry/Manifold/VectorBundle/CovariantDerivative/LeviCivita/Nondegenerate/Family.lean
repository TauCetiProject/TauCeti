/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Family
public import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Regularity

/-!
# Joint smoothness of the Levi-Civita connections of a metric family

For a smooth nondegenerate metric family over a parameter manifold, the coordinate metrics and
Levi-Civita connection coefficients are jointly smooth in the parameter and base point. The
statements apply throughout base chart domains, including boundary and corner points.
Neither positivity nor a fixed signature is needed.

Coefficient regularity is intrinsic to the chart domain and requires no extension of the metric
beyond the model range.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Chapter 3, the coordinate Levi-Civita formula.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  (g : ContMDiffNondegenerateMetricFamily I M IP P)

variable [FiniteDimensional ℝ E] [IsManifold IP 1 P]

/-- Applying the connections of a smooth metric family to fixed smooth vector fields gives
jointly smooth tangent coordinates on the whole chart domain, including its corner points. -/
theorem contMDiffAt_leviCivitaConnection_apply_inCoordinates (a : M)
    {X Y : Π x : M, TangentSpace I x}
    (hX : ContMDiffOn I I.tangent ∞ (fun y ↦ TotalSpace.mk' E y (X y))
      (trivializationAt E (TangentSpace I) a).baseSet)
    (hY : ContMDiffOn I I.tangent ∞ (fun y ↦ TotalSpace.mk' E y (Y y))
      (trivializationAt E (TangentSpace I) a).baseSet)
    {q : P × M} (hq : q.2 ∈ (trivializationAt E (TangentSpace I) a).baseSet) :
    ContMDiffAt (IP.prod I) 𝓘(ℝ, E) ∞
      (fun q : P × M ↦ (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ q.2
        ((g.metric q.1).leviCivitaConnection Y q.2 (X q.2))) q := by
  let e := trivializationAt E (TangentSpace I) a
  have hCov := contMDiffOn_covariantDerivative_of_isLeviCivitaConnection
    (g := g) (cov := fun p ↦ (g.metric p).leviCivitaConnection) (n := ∞)
    (fun p ↦ (g.metric p).isLeviCivitaConnection_leviCivitaConnection) le_rfl
    e.open_baseSet (hY.of_le (by simp))
  have hX' : ContMDiffOn (IP.prod I) I.tangent ∞
      (fun r : P × M ↦ TotalSpace.mk' E (E := TangentSpace I) r.2 (X r.2))
      (univ ×ˢ e.baseSet) := hX.comp contMDiffOn_snd (fun _ hr ↦ hr.2)
  have hApply := (hCov q ⟨mem_univ q.1, hq⟩).clm_bundle_apply
    (hX' q ⟨mem_univ q.1, hq⟩)
  have hAt := hApply.contMDiffAt ((isOpen_univ.prod e.open_baseSet).mem_nhds
    ⟨mem_univ q.1, hq⟩)
  have hCoordinates := (e.contMDiffAt_iff (IB := I) (n := ∞)
    (e.mem_source.mpr hq)).1 hAt
  refine hCoordinates.2.congr_of_eventuallyEq ?_
  filter_upwards [continuousAt_snd.preimage_mem_nhds (e.open_baseSet.mem_nhds hq)] with r hr
  exact e.continuousLinearMapAt_apply_of_mem ℝ hr _

/-- The Christoffel map of each frozen metric's Levi-Civita connection is jointly smooth in the
parameter and base point throughout the canonical tangent trivialization at `a`, including
boundary and corner points. -/
theorem contMDiffAt_christoffelMap {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (a : M) {q : P × M} (hq : q.2 ∈ (extChartAt I a).source) :
    ContMDiffAt (IP.prod I) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) ∞
      (fun q : P × M ↦ christoffelMap b
        ((g.metric q.1).leviCivitaConnection.isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) a).baseSet)) q.2) q := by
  let e := trivializationAt E (TangentSpace I) a
  let : Trivialization.IsLinear ℝ e := inferInstanceAs
    (Trivialization.IsLinear ℝ (trivializationAt E (TangentSpace I) a))
  have hqe : q.2 ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hq
  apply TauCeti.contMDiffAt_clm_apply.mpr
  intro v
  apply TauCeti.contMDiffAt_clm_apply.mpr
  intro u
  have h := g.contMDiffAt_leviCivitaConnection_apply_inCoordinates a
    (contMDiffOn_symm_baseSet (I := I) (e := e) u)
    (contMDiffOn_symm_baseSet (I := I) (e := e) v) hqe
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [continuousAt_snd.preimage_mem_nhds (e.open_baseSet.mem_nhds hqe)] with r hr
  rw [covariantDerivative_symm_apply_symm b
    ((g.metric r.1).leviCivitaConnection.isCovariantDerivativeOn (s := e.baseSet)) hr v u]
  rw [← e.symmL_apply (R := ℝ) hr, e.continuousLinearMapAt_symmL hr]

/-- The native connection coefficients are jointly smooth on the whole open base chart domain. -/
theorem contMDiffOn_christoffelMap {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (a : M) :
    ContMDiffOn (IP.prod I) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) ∞
      (fun q : P × M ↦ christoffelMap b
        ((g.metric q.1).leviCivitaConnection.isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) a).baseSet)) q.2)
      (Prod.snd ⁻¹' (extChartAt I a).source) :=
  fun _ hq ↦ (g.contMDiffAt_christoffelMap b a hq).contMDiffWithinAt

/-- The scalar Christoffel coefficients are jointly smooth in parameter and base point
at every point of the base chart domain, including corner points. -/
theorem contMDiffAt_christoffelSymbol {ι : Type*} (b : Module.Basis ι ℝ E)
    (a : M) {q : P × M} (hq : q.2 ∈ (extChartAt I a).source)
    (i j k : ι) :
    ContMDiffAt (IP.prod I) 𝓘(ℝ) ∞
      (fun q : P × M ↦ christoffelSymbol I b (trivializationAt E (TangentSpace I) a)
        (g.metric q.1).leviCivitaConnection.toFun i j k q.2) q := by
  let := FiniteDimensional.fintypeBasisIndex b
  have h := ((g.contMDiffAt_christoffelMap b a hq).clm_apply
    (contMDiffAt_const (c := b j))).clm_apply (contMDiffAt_const (c := b i))
  refine ((b.coord k).toContinuousLinearMap.contDiff.contDiffAt.comp_contMDiffAt h)
    |>.congr_of_eventuallyEq ?_
  filter_upwards [continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_source a).mem_nhds hq)] with q' hq'
  exact (coord_christoffelMap_apply_basis b
    ((g.metric q'.1).leviCivitaConnection.isCovariantDerivativeOn
      (s := (trivializationAt E (TangentSpace I) a).baseSet))
    (by simpa using hq') i j k).symm

/-- The scalar coefficients of the metric family's Levi-Civita connections are jointly
smooth on the whole base chart domain, including corner points. -/
theorem contMDiffOn_christoffelSymbol {ι : Type*} (b : Module.Basis ι ℝ E)
    (a : M) (i j k : ι) :
    ContMDiffOn (IP.prod I) 𝓘(ℝ) ∞
      (fun q : P × M ↦ christoffelSymbol I b (trivializationAt E (TangentSpace I) a)
        (g.metric q.1).leviCivitaConnection.toFun i j k q.2)
      (Prod.snd ⁻¹' (extChartAt I a).source) :=
  fun _ hq ↦ (g.contMDiffAt_christoffelSymbol b a hq i j k).contMDiffWithinAt

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily
