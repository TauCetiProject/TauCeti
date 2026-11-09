/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Domain-dependent almost complex structures in product charts

Let `J` be a jointly `Cⁿ` domain-dependent almost complex structure over `P × M`. Read along the
inverse of the extended product chart at `q = (p, x)`, and in the tangent trivialization of `M` at
`x`, the family becomes a map `(w, z) ↦ J(w, z)` from `EP × E` to `E →L[ℝ] E`. It is `Cⁿ` on the
whole extended product chart target, squares to minus the identity there, and equals `J q` at the
chart centre. Each slice with the domain coordinate fixed is the chart field of the frozen target
structure, and chart fields at two centres are conjugated by the target tangent transition.
Conversely, a `Cⁿ` field on the extended product chart target squaring to minus the identity
there defines a family on the product of the intrinsic chart sources, whose coordinate expression
is the prescribed field.

## Main declarations

* `ContMDiffAlmostComplexStructureFamily.inChart`: the coordinate expression of a family.
* `ContMDiffAlmostComplexStructureFamily.contDiffOn_inChart`: its joint regularity on the target.
* `ContMDiffAlmostComplexStructureFamily.inChart_mk`: slices are chart fields of frozen structures.
* `ContMDiffAlmostComplexStructureFamily.inChart_extChartAt_eq_conj`: conjugation on overlaps.
* `ContMDiffAlmostComplexStructureFamily.ofChart`, `inChart_ofChart`: reconstruction on the
  product of the intrinsic chart sources from a field on the product chart target.
* `ContMDiffAlmostComplexStructureFamily.inChart_ofModel`: on a model target, the coordinate
  expression of `ofModel A` is `A` read in the domain chart.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (finite-regularity domain-dependent almost complex structures).
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace ContMDiffAlmostComplexStructureFamily

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {n m : ℕ∞}

/-- Read a domain-dependent structure through the inverse extended product chart at `q` and the
tangent trivialization of the target at `q.2`. The formula is total; the square and regularity
assertions concern the actual product chart target. -/
def inChart (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M) (z : EP × E) :
    E →L[ℝ] E :=
  ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) q.2
    ((extChartAt (IP.prod I) q).symm z).2 q.2 ((extChartAt (IP.prod I) q).symm z).2
      (J.tangentEndomorphism ((extChartAt (IP.prod I) q).symm z))

omit [IsManifold I ∞ M] in
/-- The inverse extended product chart is the product of the inverse extended charts. -/
private theorem extChartAt_prod_symm_apply (q : P × M) (z : EP × E) :
    (extChartAt (IP.prod I) q).symm z =
      ((extChartAt IP q.1).symm z.1, (extChartAt I q.2).symm z.2) := by
  rw [extChartAt_prod]
  rfl

/-- With the domain coordinate fixed, the coordinate expression is the chart field of the
target structure frozen at the corresponding domain point. -/
theorem inChart_mk (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M)
    (w : EP) (z : E) :
    J.inChart q (w, z) = (J.freeze ((extChartAt IP q.1).symm w)).inChart q.2 z := by
  rw [inChart, ContMDiffAlmostComplexStructure.inChart_def, extChartAt_prod_symm_apply]
  congr 1
  ext v
  exact (J.freeze_apply _ _ v).symm

/-- The coordinate expression of a family is jointly `Cⁿ` on the whole extended product chart
target. For models with corners this is regularity within that target. -/
theorem contDiffOn_inChart [IsManifold IP ∞ P]
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M) :
    ContDiffOn ℝ n (J.inChart q) (extChartAt (IP.prod I) q).target := by
  let e := trivializationAt E (TangentSpace I) q.2
  let eh := trivializationAt (E →L[ℝ] E)
    (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
  have hG : ContMDiffOn (IP.prod I) 𝓘(ℝ, E →L[ℝ] E) n
      (fun q' : P × M ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        q.2 q'.2 q.2 q'.2 (J.tangentEndomorphism q')) (Prod.snd ⁻¹' e.baseSet) := by
    have h := (eh.contMDiffOn_iff (IM := IP.prod I) (n := n)
      (f := fun q' : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q'.2
        (J.tangentEndomorphism q'))
      (s := Prod.snd ⁻¹' e.baseSet) fun q' hq' ↦ eh.mem_source.2 ⟨hq', hq'⟩).1
        J.contMDiff_tangentEndomorphism.contMDiffOn
    -- The Hom trivialization at `q.2` is coordinate conjugation through the tangent frame.
    exact h.2
  have hmaps : Set.MapsTo (extChartAt (IP.prod I) q).symm (extChartAt (IP.prod I) q).target
      (Prod.snd ⁻¹' e.baseSet) := fun z hz ↦ by
    rw [extChartAt_prod_target] at hz
    rw [Set.mem_preimage, extChartAt_prod_symm_apply]
    exact TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz.2
  exact contMDiffOn_iff_contDiffOn.1 (hG.comp (contMDiffOn_extChartAt_symm q) hmaps)

/-- On the product chart target the coordinate expression squares to minus the identity. -/
theorem inChart_inChart (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M)
    {z : EP × E} (hz : z ∈ (extChartAt (IP.prod I) q).target) (v : E) :
    J.inChart q z (J.inChart q z v) = -v := by
  rw [extChartAt_prod_target] at hz
  obtain ⟨w, z⟩ := z
  rw [inChart_mk]
  exact (J.freeze _).inChart_inChart q.2 hz.2 v

/-- At the chart centre the coordinate expression is the family at that point. -/
theorem inChart_extChartAt_self (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (q : P × M) : J.inChart q (extChartAt (IP.prod I) q q) = J.tangentEndomorphism q := by
  rw [extChartAt_prod]
  change J.inChart q (extChartAt IP q.1 q.1, extChartAt I q.2 q.2) = _
  rw [inChart_mk, extChartAt_to_inv, ContMDiffAlmostComplexStructure.inChart_extChartAt_self]
  ext v
  exact J.freeze_apply q.1 q.2 v

/-- At the image of a chart point, a slice is the frozen chart field at that domain point. -/
theorem inChart_extChartAt_mk (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (q : P × M) {p : P} (hp : p ∈ (chartAt HP q.1).source) (z : E) :
    J.inChart q (extChartAt IP q.1 p, z) = (J.freeze p).inChart q.2 z := by
  rw [inChart_mk, (extChartAt IP q.1).left_inv (by rwa [extChartAt_source])]

/-- Coordinate expressions at two chart centres are conjugated by the actual derivative of the
target chart transition. The domain chart transition does not act on the fibre. -/
theorem inChart_extChartAt_eq_conj (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    {q q' : P × M} {p : P} (hp : p ∈ (chartAt HP q.1).source)
    (hp' : p ∈ (chartAt HP q'.1).source) {y : M} (hy : y ∈ (chartAt H q.2).source)
    (hy' : y ∈ (chartAt H q'.2).source) :
    J.inChart q' (extChartAt (IP.prod I) q' (p, y)) =
      (tangentCoordChange I q.2 q'.2 y).comp
        ((J.inChart q (extChartAt (IP.prod I) q (p, y))).comp
          (tangentCoordChange I q'.2 q.2 y)) := by
  rw [extChartAt_prod, extChartAt_prod]
  change J.inChart q' (extChartAt IP q'.1 p, extChartAt I q'.2 y) =
    (tangentCoordChange I q.2 q'.2 y).comp
      ((J.inChart q (extChartAt IP q.1 p, extChartAt I q.2 y)).comp
        (tangentCoordChange I q'.2 q.2 y))
  rw [J.inChart_extChartAt_mk q hp, J.inChart_extChartAt_mk q' hp']
  exact (J.freeze p).inChart_extChartAt_eq_conj q.2 hy hy'

@[simp]
theorem inChart_ofLE (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (hmn : m ≤ n)
    (q : P × M) : (J.ofLE hmn).inChart q = J.inChart q := by
  funext z
  obtain ⟨w, z⟩ := z
  rw [inChart_mk, inChart_mk, freeze_ofLE, ContMDiffAlmostComplexStructure.inChart_ofLE]

@[simp]
theorem inChart_neg (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M) :
    (-J).inChart q = -J.inChart q := by
  funext z
  obtain ⟨w, z⟩ := z
  rw [Pi.neg_apply, inChart_mk, inChart_mk, freeze_neg,
    ContMDiffAlmostComplexStructure.inChart_neg, Pi.neg_apply]

/-- A domain-independent family reads, in every product chart, as the target chart field. -/
@[simp]
theorem inChart_const (J : ContMDiffAlmostComplexStructure I n M) (q : P × M) (z : EP × E) :
    (const (IP := IP) (P := P) J).inChart q z = J.inChart q.2 z.2 := by
  obtain ⟨w, z⟩ := z
  rw [inChart_mk, freeze_const]

section Reconstruction

variable [IsManifold IP ∞ P]

/-- The intrinsic open chart source of a manifold at a point. -/
abbrev chartSource {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (x : M) : TopologicalSpace.Opens M :=
  ⟨(chartAt H x).source, (chartAt H x).open_source⟩

/-- The tangent frame of the intrinsic chart source at its centre; it covers the whole source. -/
abbrev chartFrame (x : M) :=
  trivializationAt E (TangentSpace I : chartSource (H := H) x → Type _)
    (⟨x, mem_chart_source H x⟩ : chartSource (H := H) x)

omit [IsManifold I ∞ M] [IsManifold IP ∞ P] in
private theorem mem_extChartAt_prod_source (q : P × M) (r : chartSource (H := HP) q.1 ×
    chartSource (H := H) q.2) : ((r.1 : P), (r.2 : M)) ∈ (extChartAt (IP.prod I) q).source := by
  rw [extChartAt_prod, PartialEquiv.prod_source, extChartAt_source, extChartAt_source]
  exact ⟨r.1.property, r.2.property⟩

/-- Reconstruct a domain-dependent structure on a product of intrinsic chart sources from a
normed-space field on the extended product chart target. Its finite regularity and square
identity are required only on that target. -/
def ofChart (q : P × M) (A : EP × E → E →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt (IP.prod I) q).target)
    (hAA : ∀ z ∈ (extChartAt (IP.prod I) q).target, ∀ v, A z (A z v) = -v) :
    ContMDiffAlmostComplexStructureFamily I (chartSource (H := H) q.2) IP
      (chartSource (H := HP) q.1) n :=
  ofContMDiff
    (fun r ↦ ((chartFrame (I := I) q.2).symmL ℝ r.2).comp
      ((A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M)))).comp
        ((chartFrame (I := I) q.2).continuousLinearMapAt ℝ r.2)))
    (by
      have hmem := mem_extChartAt_prod_source (I := I) (IP := IP) q
      have hbase := TangentBundle.trivializationAt_chartSource_baseSet (I := I) q.2
      let eh := trivializationAt (E →L[ℝ] E)
        (fun y : chartSource (H := H) q.2 ↦ TangentSpace I y →L[ℝ] TangentSpace I y)
        (⟨q.2, mem_chart_source H q.2⟩ : chartSource (H := H) q.2)
      refine (eh.contMDiff_iff fun r ↦ eh.mem_source.2 ?_).2 ⟨contMDiff_snd, ?_⟩
      · exact ⟨hbase.symm ▸ Set.mem_univ _, hbase.symm ▸ Set.mem_univ _⟩
      have hg : ContMDiff (IP.prod I) 𝓘(ℝ, EP × E) n
          (fun r : chartSource (H := HP) q.1 × chartSource (H := H) q.2 ↦
            extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M))) :=
        (contMDiffOn_extChartAt (I := IP.prod I) (x := q) (n := n)).comp_contMDiff
          ((contMDiff_subtype_val (I := IP)).prodMap (contMDiff_subtype_val (I := I)))
          (fun r ↦ by simpa only [extChartAt_source] using hmem r)
      refine (hA.contMDiffOn.comp_contMDiff hg fun r ↦
        (extChartAt (IP.prod I) q).map_source (hmem r)).congr fun r ↦ ?_
      have hr : r.2 ∈ (chartFrame (I := I) q.2).baseSet := hbase.symm ▸ Set.mem_univ _
      ext v
      simp only [eh, hom_trivializationAt, Trivialization.continuousLinearMap_apply,
        Function.comp_apply, ContinuousLinearMap.comp_apply]
      rw [(chartFrame (I := I) q.2).continuousLinearMapAt_symmL hr,
        (chartFrame (I := I) q.2).continuousLinearMapAt_symmL hr])
    (fun r v ↦ by
      have hr : r.2 ∈ (chartFrame (I := I) q.2).baseSet :=
        (TangentBundle.trivializationAt_chartSource_baseSet (I := I) q.2).symm ▸ Set.mem_univ _
      simp only [ContinuousLinearMap.comp_apply]
      rw [(chartFrame (I := I) q.2).continuousLinearMapAt_symmL hr,
        hAA _ ((extChartAt (IP.prod I) q).map_source
          (mem_extChartAt_prod_source (I := I) (IP := IP) q r)), map_neg,
        (chartFrame (I := I) q.2).symmL_continuousLinearMapAt hr])

/-- The reconstructed family conjugates the prescribed field through the source tangent frame. -/
theorem ofChart_toEndomorphism_apply (q : P × M) (A : EP × E → E →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt (IP.prod I) q).target)
    (hAA : ∀ z ∈ (extChartAt (IP.prod I) q).target, ∀ v, A z (A z v) = -v)
    (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) :
    (ofChart q A hA hAA).toEndomorphism r =
      ((chartFrame (I := I) q.2).symmL ℝ r.2).comp
        ((A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M)))).comp
          ((chartFrame (I := I) q.2).continuousLinearMapAt ℝ r.2)) := by
  unfold ofChart
  exact ofContMDiff_toEndomorphism_apply _ _ _ r

/-- The reconstructed family, read on the original target tangent spaces of the chart source. -/
theorem ofChart_tangentEndomorphism (q : P × M) (A : EP × E → E →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt (IP.prod I) q).target)
    (hAA : ∀ z ∈ (extChartAt (IP.prod I) q).target, ∀ v, A z (A z v) = -v)
    (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) :
    (ofChart q A hA hAA).tangentEndomorphism r =
      ((chartFrame (I := I) q.2).symmL ℝ r.2).comp
        ((A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M)))).comp
          ((chartFrame (I := I) q.2).continuousLinearMapAt ℝ r.2)) := by
  ext v
  rw [tangentEndomorphism_apply]
  exact DFunLike.congr_fun (ofChart_toEndomorphism_apply q A hA hAA r) v

/-- The centre of the product of intrinsic chart sources. -/
abbrev chartSourceCentre (q : P × M) : chartSource (H := HP) q.1 × chartSource (H := H) q.2 :=
  (⟨q.1, mem_chart_source HP q.1⟩, ⟨q.2, mem_chart_source H q.2⟩)

omit [IsManifold I ∞ M] [IsManifold IP ∞ P] in
private theorem mem_extChartAt_chartSourceCentre_source (q : P × M)
    (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) :
    r ∈ (extChartAt (IP.prod I) (chartSourceCentre q)).source := by
  rw [extChartAt_prod, PartialEquiv.prod_source, extChartAt_source, extChartAt_source]
  simp only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
    Set.mem_prod, Set.mem_preimage]
  exact ⟨r.1.property, r.2.property⟩

/-- Reading the reconstructed family in the product chart at the centre of the chart sources
recovers the prescribed field at the ambient chart value. -/
theorem inChart_ofChart (q : P × M) (A : EP × E → E →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt (IP.prod I) q).target)
    (hAA : ∀ z ∈ (extChartAt (IP.prod I) q).target, ∀ v, A z (A z v) = -v)
    (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) :
    (ofChart q A hA hAA).inChart (chartSourceCentre q)
        (extChartAt (IP.prod I) (chartSourceCentre q) r) =
      A (extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M))) := by
  have hr : r.2 ∈ (chartFrame (I := I) q.2).baseSet :=
    (TangentBundle.trivializationAt_chartSource_baseSet (I := I) q.2).symm ▸ Set.mem_univ _
  rw [inChart, (extChartAt (IP.prod I) (chartSourceCentre q)).left_inv
    (mem_extChartAt_chartSourceCentre_source q r), ofChart_tangentEndomorphism]
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [(chartFrame (I := I) q.2).continuousLinearMapAt_symmL hr,
    (chartFrame (I := I) q.2).continuousLinearMapAt_symmL hr]

end Reconstruction

section Model

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- On a model target, the coordinate expression of `ofModel A` is `A` with the domain point
read in the domain chart. Together with `ofModel` this reconstructs a family from a jointly
regular field squaring to minus the identity. -/
@[simp]
theorem inChart_ofModel (A : P × V → V →L[ℝ] V)
    (hA : ContMDiff (IP.prod 𝓘(ℝ, V)) 𝓘(ℝ, V →L[ℝ] V) n A)
    (hsq : ∀ q v, A q (A q v) = -v) (q : P × V) (z : EP × V) :
    (ofModel A hA hsq).inChart q z = A ((extChartAt IP q.1).symm z.1, z.2) := by
  obtain ⟨w, z⟩ := z
  rw [inChart_mk, ContMDiffAlmostComplexStructure.inChart_def, extChartAt_model_space_eq_id]
  simp only [PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq]
  have h : ((ofModel A hA hsq).freeze ((extChartAt IP q.1).symm w)).toEndomorphism z =
      A ((extChartAt IP q.1).symm w, z) :=
    (freeze_toEndomorphism_apply _ _ _).trans (ofModel_toEndomorphism_apply A hA hsq _)
  exact (inCoordinates_tangent_bundle_core_model_space (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, V))
    q.2 z q.2 z _).trans h

end Model

end ContMDiffAlmostComplexStructureFamily

end TauCeti
