/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Chart
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Inhomogeneous terms from coordinate expressions

Let `q = (p, x) ∈ P × M` and write `U` and `V` for the sources of the charts of `P` at `p` and of
`M` at `x`. A `Cⁿ` map `A : EP × E → (EP →L[ℝ] E)` on the target of the extended product chart at
`q` defines a domain-dependent Hom section over `U × V`
(`TauCeti.DomainDependentHomSection.ofChart`): at `r ∈ U × V` it is `A` evaluated at the chart
value of `r`, conjugated by the tangent frames of the chart sources. If `A` is antilinear for the
coordinate expressions of a `Cⁿ` almost complex structure `j` on `U` and of a domain-dependent
structure `J` over `U × V`, read at the centre of the chart sources, this section is an
inhomogeneous term for `j` and `J` (`TauCeti.InhomogeneousTerm.ofChart`).

This is the converse of reading an inhomogeneous term in charts, and the analogue for inhomogeneous
terms of `TauCeti.ContMDiffAlmostComplexStructureFamily.ofChart`: a coordinate map on a chart
domain of the product defines a term there.

## Main declarations

* `TauCeti.DomainDependentHomSection.ofChart`: the Hom section defined by a coordinate map.
* `TauCeti.DomainDependentHomSection.inCoordinates_ofChart_tangentHom`: read in the tangent
  coordinates at the centre of the chart sources, the section is the coordinate map.
* `TauCeti.DomainDependentHomSection.ofChart_mem_inhomogeneousTerms`: an antilinear coordinate map
  defines an antilinear Hom section.
* `TauCeti.InhomogeneousTerm.ofChart`: the inhomogeneous term defined by an antilinear coordinate
  map.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (inhomogeneous Cauchy--Riemann equations).
-/

public noncomputable section

open Bundle
open TangentBundle (chartFrame)
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P] {n : ℕ∞}

namespace DomainDependentHomSection

/-- The field underlying the Hom section defined by a coordinate map: at `r`, the coordinate map
at the chart value of `r`, conjugated by the tangent frames of the chart sources. -/
private def ofChartField (q : P × M) (A : EP × E → EP →L[ℝ] E)
    (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) :
    TangentSpace IP r.1 →L[ℝ] TangentSpace I r.2 :=
  ((chartFrame (I := I) q.2).symmL ℝ r.2).comp
    ((A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M)))).comp
      ((chartFrame (I := IP) q.1).continuousLinearMapAt ℝ r.1))

/-- A coordinate map which is `Cⁿ` on the extended product chart target defines a jointly `Cⁿ`
Hom section over the product of the chart sources. -/
private theorem contMDiff_ofChartField (q : P × M) (A : EP × E → EP →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt (IP.prod I) q).target) :
    ContMDiff (IP.prod I) ((IP.prod I).prod 𝓘(ℝ, EP →L[ℝ] E)) n
      (fun r : chartSource (H := HP) q.1 × chartSource (H := H) q.2 ↦
        TotalSpace.mk' (EP →L[ℝ] E)
          (E := fun r ↦ horizontalTangentBundle I (chartSource (H := H) q.2) IP
              (chartSource (H := HP) q.1) r →L[ℝ]
            verticalTangentBundle I (chartSource (H := H) q.2) IP (chartSource (H := HP) q.1) r)
          r (ofChartField q A r)) := by
  set U := chartSource (H := HP) q.1
  set V := chartSource (H := H) q.2
  refine (TauCeti.contMDiff_hom_bundle_iff (E₁ := horizontalTangentBundle I V IP U)
    (E₂ := verticalTangentBundle I V IP U) (ofChartField q A)).2 ?_
  have hmP := TangentBundle.mem_chartFrame_baseSet (I := IP) q.1
  have hmM := TangentBundle.mem_chartFrame_baseSet (I := I) q.2
  have hbase : ContMDiff ((IP.prod I).prod 𝓘(ℝ, EP)) (IP.prod I) n
      (fun w : TotalSpace EP (horizontalTangentBundle I V IP U) ↦ w.proj) :=
    contMDiff_proj _
  -- The horizontal vector as a tangent vector of `U`, and its coordinates in the frame.
  have hlift : ContMDiff ((IP.prod I).prod 𝓘(ℝ, EP)) IP.tangent n
      (fun w : TotalSpace EP (horizontalTangentBundle I V IP U) ↦
        (⟨w.proj.1, w.snd⟩ : TangentBundle IP U)) :=
    Bundle.Pullback.contMDiff_lift (ContMDiffMap.fst : C^∞⟮IP.prod I, U × V; IP, U⟯)
      contMDiff_fst
  have hcoord := (((chartFrame (I := IP) q.1).contMDiff_iff
    fun w ↦ (chartFrame (I := IP) q.1).mem_source.2 (hmP _)).1 hlift).2
  -- The chart value of the base point.
  have hmem := mem_extChartAt_prod_source (I := IP) (I' := I) q
  have hg : ContMDiff (IP.prod I) 𝓘(ℝ, EP × E) n
      (fun r : U × V ↦ extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M))) :=
    (contMDiffOn_extChartAt (I := IP.prod I) (x := q) (n := n)).comp_contMDiff
      ((contMDiff_subtypeVal (I := IP)).prodMap (contMDiff_subtypeVal (I := I)))
      (fun r ↦ by simpa only [extChartAt_source] using hmem r)
  have hAg := (hA.contMDiffOn.comp_contMDiff hg fun r ↦
    (extChartAt (IP.prod I) q).map_source (hmem r)).comp hbase
  -- Read the image vector in the frame of `V` and return to the vertical bundle.
  refine (Bundle.Pullback.contMDiff_iff (ContMDiffMap.snd : C^∞⟮IP.prod I, U × V; I, V⟯)
    contMDiff_snd).2 ⟨hbase, ?_⟩
  refine ((chartFrame (I := I) q.2).contMDiff_iff
    fun w ↦ (chartFrame (I := I) q.2).mem_source.2 (hmM _)).2
      ⟨contMDiff_snd.comp hbase, (hAg.clm_apply hcoord).congr fun w ↦ ?_⟩
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ (hmM _)]
  -- The vertical lift of a point of the pulled-back bundle has the same fibre value, and the
  -- horizontal fibre at `w.proj` is the tangent space of `U` at `w.proj.1`; these are type
  -- synonyms, which `rw` cannot see through, so restate the goal with the field unfolded.
  change (chartFrame (I := I) q.2).continuousLinearMapAt ℝ w.proj.2
      ((chartFrame (I := I) q.2).symmL ℝ w.proj.2
        (A (extChartAt (IP.prod I) q ((w.proj.1 : P), (w.proj.2 : M)))
          ((chartFrame (I := IP) q.1).continuousLinearMapAt ℝ w.proj.1 w.snd))) = _
  rw [(chartFrame (I := I) q.2).continuousLinearMapAt_symmL (hmM _)]
  exact congrArg (A _) (Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ (hmP w.proj.1)
    (w.snd : TangentSpace IP w.proj.1))

/-- The Hom section over the product of the chart sources at `q` defined by a coordinate map `A`
which is `Cⁿ` on the extended product chart target: at `r` it is `A` at the chart value of `r`,
conjugated by the tangent frames of the chart sources. -/
def ofChart (q : P × M) (A : EP × E → EP →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt (IP.prod I) q).target) :
    DomainDependentHomSection I (chartSource (H := H) q.2) IP (chartSource (H := HP) q.1) n :=
  ⟨ofChartField q A, contMDiff_ofChartField q A hA⟩

/-- The section defined by a coordinate map conjugates it through the tangent frames. -/
@[simp]
theorem ofChart_tangentHom (q : P × M) (A : EP × E → EP →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt (IP.prod I) q).target)
    (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) :
    (ofChart q A hA).tangentHom r =
      ((chartFrame (I := I) q.2).symmL ℝ r.2).comp
        ((A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M)))).comp
          ((chartFrame (I := IP) q.1).continuousLinearMapAt ℝ r.1)) := by
  ext v
  rw [tangentHom_apply]
  rfl

/-- **Reading back the coordinate map.** In the tangent coordinates at the centre of the chart
sources, the section defined by a coordinate map `A` is `A` at the chart value. -/
theorem inCoordinates_ofChart_tangentHom (q : P × M) (A : EP × E → EP →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt (IP.prod I) q).target)
    (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) :
    ContinuousLinearMap.inCoordinates EP (TangentSpace IP) E (TangentSpace I)
        (chartSourceCentre (H := HP) (H' := H) q).1 r.1
        (chartSourceCentre (H := HP) (H' := H) q).2 r.2 ((ofChart q A hA).tangentHom r) =
      A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M))) := by
  have hP : r.1 ∈ (chartFrame (I := IP) q.1).baseSet :=
    TangentBundle.mem_chartFrame_baseSet (I := IP) q.1 _
  have hM : r.2 ∈ (chartFrame (I := I) q.2).baseSet :=
    TangentBundle.mem_chartFrame_baseSet (I := I) q.2 _
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ofChart_tangentHom,
    ContinuousLinearMap.comp_apply]
  rw [(chartFrame (I := I) q.2).continuousLinearMapAt_symmL hM,
    (chartFrame (I := IP) q.1).continuousLinearMapAt_symmL hP]

end DomainDependentHomSection

namespace InhomogeneousTerm

variable (q : P × M) (j : ContMDiffAlmostComplexStructure IP n (chartSource (H := HP) q.1))
  (J : ContMDiffAlmostComplexStructureFamily I (chartSource (H := H) q.2) IP
    (chartSource (H := HP) q.1) n)
  (A : EP × E → EP →L[ℝ] E) (hA : ContDiffOn ℝ n A (extChartAt (IP.prod I) q).target)
  (hAj : ∀ (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) (v : EP),
    A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M)))
        (j.inChart (chartSourceCentre (H := HP) (H' := H) q).1
          (extChartAt IP (chartSourceCentre (H := HP) (H' := H) q).1 r.1) v) =
      -J.inChart (chartSourceCentre (H := HP) (H' := H) q)
        (extChartAt (IP.prod I) (chartSourceCentre (H := HP) (H' := H) q) r)
        (A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M))) v))

include hAj in
/-- A coordinate map which is `Cⁿ` on the extended product chart target at `q` and antilinear for
the coordinate expressions of `j` and `J` at the centre of the chart sources defines a Hom section
which is antilinear for `j` and `J` at every point. -/
theorem _root_.TauCeti.DomainDependentHomSection.ofChart_mem_inhomogeneousTerms :
    DomainDependentHomSection.ofChart q A hA ∈ inhomogeneousTerms j J := by
  refine (mem_inhomogeneousTerms_iff_tangentHom _ _ _).2 fun r v ↦ ?_
  have hP : r.1 ∈ (chartFrame (I := IP) q.1).baseSet :=
    TangentBundle.mem_chartFrame_baseSet (I := IP) q.1 _
  have hM : r.2 ∈ (chartFrame (I := I) q.2).baseSet :=
    TangentBundle.mem_chartFrame_baseSet (I := I) q.2 _
  have h := hAj r ((chartFrame (I := IP) q.1).continuousLinearMapAt ℝ r.1 v)
  rw [ContMDiffAlmostComplexStructure.inChart_chartSource,
    ContMDiffAlmostComplexStructureFamily.inChart_chartSourceCentre] at h
  simp only [ContinuousLinearMap.comp_apply,
    (chartFrame (I := IP) q.1).symmL_continuousLinearMapAt hP] at h
  have h' := congrArg ((chartFrame (I := I) q.2).symmL ℝ r.2) h
  rw [map_neg, (chartFrame (I := I) q.2).symmL_continuousLinearMapAt hM] at h'
  rw [DomainDependentHomSection.ofChart_tangentHom]
  exact h'

/-- **Inhomogeneous terms from coordinate expressions.** Let `j` be a `Cⁿ` almost complex
structure on the chart source `U` at `q.1` and `J` a domain-dependent structure over `U × V`, with
`V` the chart source at `q.2`. A coordinate map `A`, `Cⁿ` on the extended product chart target at
`q` and antilinear for the coordinate expressions of `j` and `J` at the centre of the chart
sources, defines an inhomogeneous term for `j` and `J` over `U × V`. -/
def ofChart : InhomogeneousTerm j J :=
  ⟨DomainDependentHomSection.ofChart q A hA,
    DomainDependentHomSection.ofChart_mem_inhomogeneousTerms q j J A hA hAj⟩

@[simp]
theorem ofChart_val : (ofChart q j J A hA hAj).val = DomainDependentHomSection.ofChart q A hA :=
  (rfl)

/-- In the tangent coordinates at the centre of the chart sources, the term defined by a
coordinate map `A` is `A` at the chart value. -/
theorem inCoordinates_ofChart_val_tangentHom
    (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) :
    ContinuousLinearMap.inCoordinates EP (TangentSpace IP) E (TangentSpace I)
        (chartSourceCentre (H := HP) (H' := H) q).1 r.1
        (chartSourceCentre (H := HP) (H' := H) q).2 r.2
        ((ofChart q j J A hA hAj).val.tangentHom r) =
      A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M))) :=
  DomainDependentHomSection.inCoordinates_ofChart_tangentHom q A hA r

end InhomogeneousTerm

end TauCeti
