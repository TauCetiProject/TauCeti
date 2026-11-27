/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.ExtChartAt.ChartSource

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
* `ContMDiffAlmostComplexStructureFamily.inChart_mk`: slices are chart fields of frozen structures;
  over a normed space, of the frozen smooth structures
  (`ContMDiffAlmostComplexStructureFamily.inChart_mk_eq_inChart_freezeSmooth`), which are therefore
  jointly smooth (`ContMDiffAlmostComplexStructureFamily.contDiffOn_inChart_freezeSmooth`).
* `ContMDiffAlmostComplexStructureFamily.inChart_extChartAt_eq_conj`: conjugation on overlaps.
* `ContMDiffAlmostComplexStructureFamily.inChart_chartSourceCentre`: on a product of chart sources,
  the coordinate expression at the centre is conjugation by the target tangent frame.
* `ContMDiffAlmostComplexStructureFamily.ofChart`, `inChart_ofChart`: reconstruction on the
  product of the intrinsic chart sources from a field on the product chart target.
* `ContMDiffAlmostComplexStructureFamily.inChart_ofModel`: on a model target, the coordinate
  expression of `ofModel A` is `A` read in the domain chart.
* `ContMDiffAlmostComplexStructureFamily.chartField`: the family read in a chart `φ` of the
  domain and a chart `ψ` of the target with values in a normed space, as the pushforward
  `dψ ∘ J(φ⁻¹ z, ψ⁻¹ v) ∘ dψ⁻¹`; this is the coefficient of coordinate Cauchy–Riemann equations.
  Reparametrizing along `g` with `g ∘ φ'⁻¹ = φ⁻¹` does not change it
  (`ContMDiffAlmostComplexStructureFamily.chartField_comp`).
* `ContMDiffAlmostComplexStructureFamily.chartField_symm_trans_comp_fderiv`: the derivative of a
  transition between two charts of the target intertwines the structures read in them.
* `ContMDiffAlmostComplexStructureFamily.chartField_comp_symm_chartAt`: over a domain with any
  model `IP`, possibly with boundary, in the preferred charts and on a boundaryless target, the
  structure read in charts along `IP.symm` is the coordinate expression `inChart`; hence it is
  jointly `Cⁿ` on the product of the extended chart targets
  (`ContMDiffAlmostComplexStructureFamily.contDiffOn_chartField_comp_symm_chartAt`), up to the
  boundary for a Riemann surface with boundary, and squares to minus the identity there
  (`ContMDiffAlmostComplexStructureFamily.chartField_comp_symm_chartAt_apply_apply`).
  `ContMDiffAlmostComplexStructureFamily.chartField_chartAt`,
  `ContMDiffAlmostComplexStructureFamily.contDiffOn_chartField_chartAt` and
  `ContMDiffAlmostComplexStructureFamily.chartField_chartAt_apply_apply` are the case of a domain
  modelled on `ℂ`.
* `ContMDiffAlmostComplexStructureFamily.contDiffOn_chartField_chartAt_refl`,
  `ContMDiffAlmostComplexStructureFamily.chartField_refl_mul_self`: with values in a normed space
  read in its identity chart, the structure read in a preferred chart is jointly `Cⁿ` on the
  product of the chart target with the whole space, and it squares to minus the identity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (finite-regularity domain-dependent almost complex structures).
-/

public noncomputable section

open Bundle
open TangentBundle (chartFrame)
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

/-- With the domain coordinate fixed, the coordinate expression is the chart field of the
target structure frozen at the corresponding domain point. -/
theorem inChart_mk (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M)
    (w : EP) (z : E) :
    J.inChart q (w, z) = (J.freeze ((extChartAt IP q.1).symm w)).inChart q.2 z := by
  rw [inChart, ContMDiffAlmostComplexStructure.inChart_def, extChartAt_prod_symm_apply]
  congr 1
  ext v
  exact (J.freeze_apply _ _ v).symm

/-- On a product of chart sources, a domain-dependent structure read in the product chart at the
centre is the structure conjugated by the tangent frame of the target chart source. -/
theorem inChart_chartSourceCentre (q : P × M)
    (J : ContMDiffAlmostComplexStructureFamily I (chartSource (H := H) q.2) IP
      (chartSource (H := HP) q.1) n)
    (r : chartSource (H := HP) q.1 × chartSource (H := H) q.2) :
    J.inChart (chartSourceCentre (H := HP) (H' := H) q)
        (extChartAt (IP.prod I) (chartSourceCentre (H := HP) (H' := H) q) r) =
      ((chartFrame (I := I) q.2).continuousLinearMapAt ℝ r.2).comp
        ((J.tangentEndomorphism r).comp ((chartFrame (I := I) q.2).symmL ℝ r.2)) := by
  rw [extChartAt_prod_apply, inChart_mk, (extChartAt IP _).left_inv,
    ContMDiffAlmostComplexStructure.inChart_chartSource, freeze_toEndomorphism_apply]
  · congr 2
    ext v
    exact (tangentEndomorphism_apply J r v).symm
  · exact mem_extChartAt_chartSource_source q.1 r.1

/-- The coordinate expression of a family is jointly `Cⁿ` on the whole extended product chart
target. For models with corners this is regularity within that target. -/
theorem contDiffOn_inChart [IsManifold IP n P]
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
  rw [extChartAt_prod_apply, inChart_mk, extChartAt_to_inv,
    ContMDiffAlmostComplexStructure.inChart_extChartAt_self]
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
  rw [extChartAt_prod_apply, extChartAt_prod_apply, J.inChart_extChartAt_mk q hp,
    J.inChart_extChartAt_mk q' hp']
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

variable [IsManifold IP n P]

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
      have hmem := mem_extChartAt_prod_source (I := IP) (I' := I) q
      let eh := trivializationAt (E →L[ℝ] E)
        (fun y : chartSource (H := H) q.2 ↦ TangentSpace I y →L[ℝ] TangentSpace I y)
        (⟨q.2, mem_chart_source H q.2⟩ : chartSource (H := H) q.2)
      refine (eh.contMDiff_iff fun r ↦ eh.mem_source.2 ?_).2 ⟨contMDiff_snd, ?_⟩
      · exact ⟨TangentBundle.mem_chartFrame_baseSet q.2 _,
          TangentBundle.mem_chartFrame_baseSet q.2 _⟩
      have hg : ContMDiff (IP.prod I) 𝓘(ℝ, EP × E) n
          (fun r : chartSource (H := HP) q.1 × chartSource (H := H) q.2 ↦
            extChartAt (IP.prod I) q ((r.1 : P), (r.2 : M))) :=
        (contMDiffOn_extChartAt (I := IP.prod I) (x := q) (n := n)).comp_contMDiff
          ((contMDiff_subtypeVal (I := IP)).prodMap (contMDiff_subtypeVal (I := I)))
          (fun r ↦ by simpa only [extChartAt_source] using hmem r)
      refine (hA.contMDiffOn.comp_contMDiff hg fun r ↦
        (extChartAt (IP.prod I) q).map_source (hmem r)).congr fun r ↦ ?_
      have hr := TangentBundle.mem_chartFrame_baseSet (I := I) q.2 r.2
      ext v
      simp only [eh, hom_trivializationAt, Trivialization.continuousLinearMap_apply,
        Function.comp_apply, ContinuousLinearMap.comp_apply]
      rw [(chartFrame (I := I) q.2).continuousLinearMapAt_symmL hr,
        (chartFrame (I := I) q.2).continuousLinearMapAt_symmL hr])
    (fun r v ↦ by
      have hr : r.2 ∈ (chartFrame (I := I) q.2).baseSet :=
        TangentBundle.mem_chartFrame_baseSet (I := I) q.2 _
      simp only [ContinuousLinearMap.comp_apply]
      rw [(chartFrame (I := I) q.2).continuousLinearMapAt_symmL hr,
        hAA _ ((extChartAt (IP.prod I) q).map_source
          (mem_extChartAt_prod_source (I := IP) (I' := I) q r)), map_neg,
        (chartFrame (I := I) q.2).symmL_continuousLinearMapAt hr])

/-- The reconstructed family conjugates the prescribed field through the source tangent frame. -/
@[simp]
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
@[simp]
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
    TangentBundle.mem_chartFrame_baseSet (I := I) q.2 _
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

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a smooth family over a normed space, whose chart is the identity, the slice of the
coordinate expression at the parameter `w` is the chart field of the smooth structure frozen at
`w`. -/
theorem inChart_mk_eq_inChart_freezeSmooth
    (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, F) F ⊤) (q : F × M) (w : F) (y : E) :
    J.inChart q (w, y) = (J.freezeSmooth w).inChart q.2 y := by
  simp [inChart_mk, ContMDiffAlmostComplexStructure.inChart_def,
    SmoothAlmostComplexStructure.inChart_def]

/-- For a smooth family over a normed space, the chart fields of the frozen smooth structures are
jointly smooth in the parameter and the chart coordinate on the chart target. -/
theorem contDiffOn_inChart_freezeSmooth
    (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, F) F ⊤) (x : M) :
    ContDiffOn ℝ ∞ (fun q : F × E ↦ (J.freezeSmooth q.1).inChart x q.2)
      (Set.univ ×ˢ (extChartAt I x).target) := by
  have h := J.contDiffOn_inChart ((0 : F), x)
  rw [extChartAt_prod_target, extChartAt_model_space_eq_id, PartialEquiv.refl_target] at h
  exact h.congr fun q _ ↦ (J.inChart_mk_eq_inChart_freezeSmooth (0, x) q.1 q.2).symm

end NormedSpace

section ChartField

variable {D G : Type*} [TopologicalSpace D] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A domain-dependent structure read in a chart `φ` of `P` and a chart `ψ` of `M` with values in
a normed space `G`: at `(z, v)`, the structure `J(φ⁻¹ z, ψ⁻¹ v)` pushed forward along `ψ`, that
is `dψ ∘ J(φ⁻¹ z, ψ⁻¹ v) ∘ dψ⁻¹`. -/
def chartField (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (φ : OpenPartialHomeomorph P D) (ψ : OpenPartialHomeomorph M G) (z : D) (v : G) :
    G →L[ℝ] G :=
  (J.freeze (φ.symm z)).chartPushforward ψ v

/-- Evaluate a structure read in charts. -/
theorem chartField_apply (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (φ : OpenPartialHomeomorph P D) (ψ : OpenPartialHomeomorph M G) (z : D) (v : G) :
    J.chartField φ ψ z v = (J.freeze (φ.symm z)).chartPushforward ψ v :=
  (rfl)

/-- **Changing the chart of the target.** For two charts `ψ₁` and `ψ₂` of `M` with values in
normed spaces and a point `w` of the source of the transition `Θ = ψ₂ ∘ ψ₁⁻¹`, the derivative of
`Θ` at `w` intertwines the structure read in `φ` and `ψ₁` at `(z, w)` with the structure read in
`φ` and `ψ₂` at `(z, Θ w)`, provided `ψ₁` is differentiable at `ψ₁⁻¹ w`, `ψ₂⁻¹` at `Θ w` and `Θ`
at `w`. -/
theorem chartField_symm_trans_comp_fderiv (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (φ : OpenPartialHomeomorph P D) (z : D) {G' : Type*} [NormedAddCommGroup G']
    [NormedSpace ℝ G'] {ψ₁ : OpenPartialHomeomorph M G} {ψ₂ : OpenPartialHomeomorph M G'} {w : G}
    (hw : w ∈ (ψ₁.symm.trans ψ₂).source) (hψ₁ : MDifferentiableAt I 𝓘(ℝ, G) ψ₁ (ψ₁.symm w))
    (hψ₂s : MDifferentiableAt 𝓘(ℝ, G') I ψ₂.symm (ψ₁.symm.trans ψ₂ w))
    (hΘ : DifferentiableAt ℝ (ψ₁.symm.trans ψ₂) w) :
    (J.chartField φ ψ₂ z (ψ₁.symm.trans ψ₂ w)).comp (fderiv ℝ (ψ₁.symm.trans ψ₂) w) =
      (fderiv ℝ (ψ₁.symm.trans ψ₂) w).comp (J.chartField φ ψ₁ z w) := by
  rw [chartField_apply, chartField_apply]
  exact (J.freeze (φ.symm z)).chartPushforward_symm_trans_comp_fderiv hw hψ₁ hψ₂s hΘ

/-- A structure independent of the domain point reads in charts as its pushforward along the
chart of `M`. -/
@[simp]
theorem chartField_const (J : ContMDiffAlmostComplexStructure I n M)
    (φ : OpenPartialHomeomorph P D) (ψ : OpenPartialHomeomorph M G) :
    (const (IP := IP) J).chartField φ ψ = fun _ v ↦ J.chartPushforward ψ v := by
  funext z v
  rw [chartField_apply, freeze_const]

/-- Forgetting regularity does not change a structure read in charts. -/
@[simp]
theorem chartField_ofLE (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (hmn : m ≤ n)
    (φ : OpenPartialHomeomorph P D) (ψ : OpenPartialHomeomorph M G) :
    (J.ofLE hmn).chartField φ ψ = J.chartField φ ψ := by
  funext z v
  rw [chartField_apply, chartField_apply, freeze_ofLE,
    ContMDiffAlmostComplexStructure.chartPushforward_ofLE]

/-- The negated structure reads in charts as the negated chart field. -/
@[simp]
theorem chartField_neg (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (φ : OpenPartialHomeomorph P D) (ψ : OpenPartialHomeomorph M G) :
    (-J).chartField φ ψ = -J.chartField φ ψ := by
  funext z v
  simp [chartField_apply]

/-- **Transport in charts.** If `φ'` is a chart of `Q` and `φ` a chart of `P` with
`g ∘ φ'⁻¹ = φ⁻¹`, the reparametrized family `J ∘ g` read in `φ'` is `J` read in `φ`. -/
theorem chartField_comp {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
    [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q]
    [ChartedSpace HQ Q] (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (g : C^n⟮IQ, Q; IP, P⟯) {φ' : OpenPartialHomeomorph Q D} {φ : OpenPartialHomeomorph P D}
    (hφ : g ∘ φ'.symm = φ.symm) (ψ : OpenPartialHomeomorph M G) :
    (J.comp g).chartField φ' ψ = J.chartField φ ψ := by
  funext z v
  rw [chartField_apply, chartField_apply, freeze_comp, ← hφ, Function.comp_apply]

/-- On a normed space, read in the identity chart, a structure is its value at the domain point
`φ⁻¹ z`. -/
@[simp]
theorem chartField_refl {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, F) F IP P n)
    (φ : OpenPartialHomeomorph P D) :
    J.chartField φ (OpenPartialHomeomorph.refl F) =
      fun z v ↦ (J.freeze (φ.symm z)).toEndomorphism v := by
  funext z v
  rw [chartField_apply, ContMDiffAlmostComplexStructure.chartPushforward_refl]

end ChartField

section PreferredCharts

variable [I.Boundaryless]

/-- In the preferred charts of a domain with any model `IP`, possibly with boundary, and of a
boundaryless target, a domain-dependent structure read through `chartField` along the inverse of
the model is the coordinate expression `inChart` on the extended product chart target. -/
theorem chartField_comp_symm_chartAt (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (x : P) (y : M) (w : EP) {v : E} (hv : v ∈ (extChartAt I y).target) :
    (J.chartField (chartAt HP x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) ∘ IP.symm) w
        v = J.inChart (x, y) (w, v) := by
  rw [Function.comp_apply, chartField_apply, inChart_mk, extChartAt_coe_symm, Function.comp_apply,
    ContMDiffAlmostComplexStructure.chartPushforward_eq_pullbackEnd_inChart _ y _
      (OpenPartialHomeomorph.refl E) hv ?_ ?_ differentiableAt_id differentiableAt_id]
  · ext w
    simp
  · refine Filter.EventuallyEq.of_eq ?_
    rw [OpenPartialHomeomorph.coe_extendTrans_refl]
    funext w
    simp [extChartAt]
  · refine Filter.EventuallyEq.of_eq ?_
    rw [OpenPartialHomeomorph.coe_symm_extendTrans_refl]
    funext w
    simp [extChartAt]

/-- In the preferred charts of a domain with any model `IP`, possibly with boundary, a
domain-dependent structure read through `chartField` along the inverse of the model is jointly
`Cⁿ` on the product of the extended chart targets. Over the closed upper half-plane this is
regularity up to the boundary. -/
theorem contDiffOn_chartField_comp_symm_chartAt [IsManifold IP n P]
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (x : P) (y : M) :
    ContDiffOn ℝ n (fun q : EP × E ↦
        (J.chartField (chartAt HP x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) ∘
          IP.symm) q.1 q.2)
      ((extChartAt IP x).target ×ˢ (extChartAt I y).target) := by
  have h := J.contDiffOn_inChart (x, y)
  rw [extChartAt_prod_target] at h
  exact h.congr fun q hq ↦ J.chartField_comp_symm_chartAt x y q.1 hq.2

/-- In the preferred charts of a domain with any model `IP`, a domain-dependent structure read
through `chartField` along the inverse of the model squares to minus the identity on the target
of the chart of `M`. -/
theorem chartField_comp_symm_chartAt_apply_apply
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (x : P) (y : M) (w : EP)
    {v : E} (hv : v ∈ (extChartAt I y).target) (u : E) :
    (J.chartField (chartAt HP x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) ∘ IP.symm) w
        v ((J.chartField (chartAt HP x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) ∘
          IP.symm) w v u) = -u := by
  rw [J.chartField_comp_symm_chartAt x y w hv, inChart_mk]
  exact (J.freeze _).inChart_inChart y hv u

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- In the preferred charts, a domain-dependent structure read through `chartField` is its
coordinate expression `inChart` on the extended product chart target. -/
theorem chartField_chartAt (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) Y n)
    (x : Y) (y : M) (z : ℂ) {v : E} (hv : v ∈ (extChartAt I y).target) :
    J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) z v =
      J.inChart (x, y) (z, v) := by
  simpa using J.chartField_comp_symm_chartAt x y z hv

/-- In the preferred charts, a domain-dependent structure read through `chartField` is jointly
`Cⁿ` on the product of the chart targets. -/
theorem contDiffOn_chartField_chartAt [IsManifold 𝓘(ℝ, ℂ) n Y]
    (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) Y n) (x : Y) (y : M) :
    ContDiffOn ℝ n (fun q : ℂ × E ↦
        J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) q.1 q.2)
      ((chartAt ℂ x).target ×ˢ (extChartAt I y).target) := by
  simpa using J.contDiffOn_chartField_comp_symm_chartAt x y

/-- In the preferred charts, a domain-dependent structure read through `chartField` squares to
minus the identity on the target of the chart of `M`. -/
theorem chartField_chartAt_apply_apply
    (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) Y n) (x : Y) (y : M) (z : ℂ)
    {v : E} (hv : v ∈ (extChartAt I y).target) (w : E) :
    J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) z v
        (J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)) z v w) =
      -w := by
  simpa using J.chartField_comp_symm_chartAt_apply_apply x y z hv w

end PreferredCharts

section IdentityChart

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a normed space, read in the identity chart, a structure squares to minus the identity. -/
theorem chartField_refl_mul_self {D : Type*} [TopologicalSpace D]
    (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, F) F IP P n) (φ : OpenPartialHomeomorph P D)
    (z : D) (v : F) :
    J.chartField φ (OpenPartialHomeomorph.refl F) z v *
      J.chartField φ (OpenPartialHomeomorph.refl F) z v = -1 := by
  rw [chartField_refl]
  exact (J.freeze _).toEndomorphism_mul_self v

/-- In a preferred chart of a domain modelled on `ℂ` and the identity chart of a normed space, a
domain-dependent structure read through `chartField` is jointly `Cⁿ` on the product of the chart
target with the whole space. -/
theorem contDiffOn_chartField_chartAt_refl {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℝ, ℂ) n Y] (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, F) F 𝓘(ℝ, ℂ) Y n)
    (x : Y) :
    ContDiffOn ℝ n
      (fun q : ℂ × F ↦ J.chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl F) q.1 q.2)
      ((chartAt ℂ x).target ×ˢ Set.univ) := by
  simpa only [OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl, chartAt_self_eq,
    extChartAt_model_space_eq_id, PartialEquiv.refl_target] using
    J.contDiffOn_chartField_chartAt x (0 : F)

end IdentityChart

end ContMDiffAlmostComplexStructureFamily

end TauCeti
