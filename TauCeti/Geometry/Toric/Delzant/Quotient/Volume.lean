/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.DuistermaatHeckman
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
public import TauCeti.Geometry.Toric.Delzant.Quotient.Darboux
public import TauCeti.Geometry.Toric.Delzant.Volume

/-!
# The Duistermaat–Heckman measure and the volume of the Delzant quotient

Let `i : N →+ V` be an integral lattice, `(u, c)` the facet presentation of a Delzant polytope
`Δ ⊆ V*` of dimension `n = dim V`, and `(M_Δ, ω_Δ)` its Delzant quotient
(`TauCeti.Toric.DelzantQuotient i u c`, `TauCeti.Toric.IsDelzant.delzantQuotientSymplecticForm`), a
compact symplectic manifold of dimension `2n` with moment map `μ_Δ : M_Δ → V*`
(`TauCeti.Toric.DelzantQuotient.reducedMomentMap`). This file computes its Duistermaat–Heckman
measure, the pushforward by `μ_Δ` of the Liouville measure `|ω_Δⁿ / n!|`
(`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure`):

`(μ_Δ)_* |ω_Δⁿ / n!| = (2π)ⁿ vol|_Δ`

(`TauCeti.Toric.IsDelzant.duistermaatHeckmanMeasure_delzantQuotientSymplecticForm`), where `vol` is
the lattice-normalized Lebesgue measure on `V*`, for which the weight lattice has covolume one
(`TauCeti.Toric.IsIntegralLattice.dualMeasure`). Taking total masses, the symplectic volume of
`M_Δ` is `(2π)ⁿ vol(Δ)`
(`TauCeti.Toric.IsDelzant.liouvilleMeasure_univ_delzantQuotientSymplecticForm`).

The proof is local over `Δ`. At a vertex `v` with set `A` of active facets, the vertex chart
(`TauCeti.Toric.IsDelzant.vertexDarbouxChart`) identifies the points of `M_Δ` whose moment values
lie in the open set `O_v = {y | c j < ⟨y, u j⟩ for every j ∉ A}` with an open subset `W` of `ℂ^A`.
It pulls `ω_Δ` back to the standard form, so it carries the Liouville measure there to Lebesgue
measure on `W`. In the chart the moment map is the weight model translated to `v`,
`w ↦ v + Σ_k ½ |w_k|² ε_k` for the edge basis `ε` dual to the active normals, which pushes Lebesgue
measure to `(2π)ⁿ` times the Haar measure of `ε` on the cone `v + Σ_k ℝ_(≥0) ε_k`
(`Module.Basis.map_volume_weightMomentMap_neg`). That Haar measure is the lattice-normalized one,
since the active normals form a lattice basis, and on `O_v` the cone agrees with `Δ`. The sets
`O_v` cover `Δ`, as the facets active at a point of `Δ` are active at some vertex, and both
measures vanish off `Δ`.

For the standard examples this gives the symplectic volumes `(2π)ⁿ aⁿ / n!` of `ℂPⁿ`, from the
simplex of size `a`, `2π a` of the two-sphere, from the interval `[0, a]`, and
`(2π)² (a b - k b² / 2)` of the Hirzebruch surfaces, in particular `(2π)² a b` of `S² × S²`.

## Main results

* `TauCeti.Toric.IsDelzant.duistermaatHeckmanMeasure_delzantQuotientSymplecticForm`: the
  Duistermaat–Heckman measure of `M_Δ` is `(2π)ⁿ` times the lattice-normalized measure on `Δ`.
* `TauCeti.Toric.IsDelzant.liouvilleMeasure_univ_delzantQuotientSymplecticForm`: the symplectic
  volume of `M_Δ` is `(2π)ⁿ vol(Δ)`.
* `TauCeti.Toric.liouvilleMeasure_univ_delzantQuotientSymplecticForm_simplex`,
  `TauCeti.Toric.liouvilleMeasure_univ_delzantQuotientSymplecticForm_interval`,
  `TauCeti.Toric.liouvilleMeasure_univ_delzantQuotientSymplecticForm_hirzebruch`: the volumes of
  `ℂPⁿ`, of the two-sphere and of the Hirzebruch surfaces.

## References

* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 29 and 30.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 2.
-/

public section

noncomputable section

open Module MeasureTheory Set Real
open scoped Manifold ContDiff ENNReal

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {i : N →+ V} {u : ι → N} {c : ι → ℝ} {v : StrongDual ℝ V}

namespace IsDelzant

open DelzantQuotient

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i) (hv : IsSmoothVertex i u c v)
  (hvP : v ∈ facetPolyhedron i u c) [Fintype (activeSet (facetPairing i u) c v)]

/-- The inverse vertex chart, restricted to the open target of the chart. -/
private theorem contMDiff_vertexChart_symm_restrict :
    letI := hΔ.delzantQuotientChartedSpace hi
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ∞
      (fun w : (⟨_, (vertexChart hv hi hvP).open_target⟩ : TopologicalSpace.Opens
          (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
            EuclideanSpace ℝ (activeSet (facetPairing i u) c v))) ↦
        (vertexChart hv hi hvP).symm w) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  intro w
  exact ((hΔ.contMDiffOn_vertexChart_symm hi hv hvP w w.property).contMDiffAt
    ((vertexChart hv hi hvP).open_target.mem_nhds w.property)).comp w
      contMDiff_subtypeVal.contMDiffAt

/-- The inverse vertex chart, restricted to the open target `W` of the chart, pulls the symplectic
form of the Delzant quotient back to the restriction to `W` of the standard symplectic form. -/
private theorem mpullback_vertexChart_symm_restrict :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    SmoothForm.mpullback _ (hΔ.contMDiff_vertexChart_symm_restrict hi hv hvP)
        (hΔ.delzantQuotientSymplecticForm hi) =
      SmoothForm.mpullback (Subtype.val : (⟨_, (vertexChart hv hi hvP).open_target⟩ :
          TopologicalSpace.Opens (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
            EuclideanSpace ℝ (activeSet (facetPairing i u) c v))) → _) contMDiff_subtypeVal
        (stdSymplecticForm (V := EuclideanSpace ℝ (activeSet (facetPairing i u) c v))).constSmooth
        := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  set e := vertexChart hv hi hvP
  set W : TopologicalSpace.Opens (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) := ⟨_, e.open_target⟩
  refine SmoothBundleForm.ext_eval₂ fun w a b ↦ ?_
  have hd : MDifferentiableAt _ _ e.symm w :=
    ((hΔ.contMDiffOn_vertexChart_symm hi hv hvP w w.property).contMDiffAt
      (e.open_target.mem_nhds w.property)).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
      𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) (Subtype.val : W → _) w :=
    contMDiff_subtypeVal.mdifferentiable one_ne_zero w
  -- The restricted inverse chart is by definition the inclusion of `W` followed by `e.symm`.
  rw [SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback,
    show (fun w : W ↦ e.symm w) = e.symm ∘ Subtype.val from rfl, mfderiv_comp_apply w hd hval,
    mfderiv_comp_apply w hd hval, TauCeti.Manifold.mfderiv_subtype_val_apply,
    TauCeti.Manifold.mfderiv_subtype_val_apply]
  exact (hΔ.eval₂_delzantQuotientSymplecticForm_mfderiv_vertexChart_symm hi hv hvP w.property a
    b).trans (SymplecticForm.constSmooth_apply _ _ _ _).symm

/-- **The Liouville measure on the source of a vertex chart.** The inverse vertex chart carries
Lebesgue measure on the target `W ⊆ ℂ^A` of the chart to the Liouville measure of `ω_Δ` on the
source of the chart: it pulls `ω_Δ` back to the standard form, whose Liouville measure is Lebesgue
measure. -/
private theorem map_vertexChart_symm_volume_restrict
    [MeasurableSpace (DelzantQuotient i u c)] [BorelSpace (DelzantQuotient i u c)]
    {n : ℕ} [Fact (finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) = 2 * n)]
    (hn : Fintype.card (activeSet (facetPairing i u) c v) = n) :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := compactSpace_delzantQuotient (u := u) (c := c) hΔ.isBounded
    (volume.restrict (vertexChart hv hi hvP).target).map (vertexChart hv hi hvP).symm =
      ((hΔ.delzantQuotientSymplecticForm hi).liouvilleMeasure n).restrict
          (vertexChart hv hi hvP).source := by
  subst hn
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := compactSpace_delzantQuotient (u := u) (c := c) hΔ.isBounded
  set e := vertexChart hv hi hvP
  set W : TopologicalSpace.Opens (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) := ⟨_, e.open_target⟩
  set g : W → DelzantQuotient i u c := fun w ↦ e.symm w
  have hg : ContMDiff _ _ ∞ g := hΔ.contMDiff_vertexChart_symm_restrict hi hv hvP
  have hemb : MeasurableEmbedding g := e.symm.isOpenEmbedding_restrict.measurableEmbedding
  -- The inverse chart pulls `ω_Δ` back to the standard form restricted to `W`.
  have hpull' := congrArg Subtype.val (hΔ.mpullback_vertexChart_symm_restrict hi hv hvP)
  rw [SmoothForm.coe_mpullback] at hpull'
  have : Fact (finrank ℝ (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) =
        2 * Fintype.card (activeSet (facetPairing i u) c v)) :=
    ⟨by rw [finrank_prod, finrank_euclideanSpace, two_mul]⟩
  have hmap := hemb.map_measure_mpullback (hg.mdifferentiable (by simp))
    ((hΔ.delzantQuotientSymplecticForm hi).volumeForm
      (Fintype.card (activeSet (facetPairing i u) c v))).val
  rw [SmoothTwoForm.mpullback_volumeForm hpull'] at hmap
  have hrange : range g = e.source := by
    rw [← e.symm_image_target_eq_source, ← Subtype.range_coe (s := e.target), ← range_comp]
    -- The points of `W` are those of `e.target`, and `g` is `e.symm` on them.
    rfl
  rw [← SmoothTwoForm.liouvilleMeasure_def, ← SmoothTwoForm.liouvilleMeasure_def, hrange] at hmap
  -- Push the Liouville measure of `W` forward to `ℂ^A`, where it is Lebesgue measure on `W`.
  rw [← hmap, show g = e.symm ∘ Subtype.val from rfl, ← AEMeasurable.map_map_of_aemeasurable,
    SmoothTwoForm.map_liouvilleMeasure_mpullback_subtypeVal,
    SymplecticForm.liouvilleMeasure_constSmooth_stdSymplecticForm]
  · -- The open set `W` has the target of the chart as its underlying set.
    rfl
  · rw [SmoothTwoForm.map_liouvilleMeasure_mpullback_subtypeVal,
      SymplecticForm.liouvilleMeasure_constSmooth_stdSymplecticForm]
    exact e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  · exact measurable_subtypeVal.aemeasurable

omit [Fintype ι] [FiniteDimensional ℝ V] [Fintype (activeSet (facetPairing i u) c v)] in
/-- **The cone of a smooth vertex agrees with `Δ` near the vertex.** Translated to the vertex `v`,
the lattice-normalized measure on the cone `{y | 0 ≤ ⟨y, u_k⟩ for every active facet k}` agrees
with the lattice-normalized measure on `Δ` over the open set of covectors satisfying strictly every
facet inequality not active at `v`. -/
private theorem map_add_dualMeasure_restrict_cone [Finite ι]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] :
    ((hi.dualMeasure.restrict {y | ∀ k, 0 ≤ (hv.edgeBasis hi).repr y k}).map (v + ·)).restrict
        {y | ∀ j ∉ activeSet (facetPairing i u) c v, c j < y (i (u j))} =
      (hi.dualMeasure.restrict (facetPolyhedron i u c)).restrict
        {y | ∀ j ∉ activeSet (facetPairing i u) c v, c j < y (i (u j))} := by
  set O := {y : StrongDual ℝ V | ∀ j ∉ activeSet (facetPairing i u) c v, c j < y (i (u j))}
  set K := {y : StrongDual ℝ V | ∀ k, 0 ≤ (hv.edgeBasis hi).repr y k}
  have hO : MeasurableSet O := by
    refine IsOpen.measurableSet ?_
    simp only [O, ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const (continuous_eval_const _)
  have hK : (v + ·) ⁻¹' ((fun y ↦ -v + y) ⁻¹' K) = K := by
    ext y
    simp
  rw [← hK, ← (measurableEmbedding_addLeft v).restrict_map, map_add_left_eq_self,
    Measure.restrict_restrict hO, Measure.restrict_restrict hO]
  congr 1
  have hvk (k : activeSet (facetPairing i u) c v) : v (i (u k)) = c k := by
    simpa using mem_activeSet.1 k.property
  ext y
  simp only [mem_inter_iff, mem_preimage, K, O, mem_ofPred_eq, IsSmoothVertex.edgeBasis_repr,
    add_apply, neg_apply, mem_facetPolyhedron]
  refine and_congr_right fun hy ↦ ⟨fun h j ↦ ?_, fun h k ↦ by linarith [h k, hvk k]⟩
  by_cases hj : j ∈ activeSet (facetPairing i u) c v
  · linarith [h ⟨j, hj⟩, hvk ⟨j, hj⟩]
  · exact (hy j hj).le

include hv hvP in
/-- **The Duistermaat–Heckman measure near a vertex.** On the open set of covectors satisfying
strictly every facet inequality not active at a smooth vertex `v`, the pushforward of the Liouville
measure of `ω_Δ` by the moment map is `(2π)^n` times the lattice-normalized measure of `Δ`: in the
vertex chart the moment map is the weight model translated to `v`. -/
private theorem map_liouvilleMeasure_restrict_vertexStar
    [MeasurableSpace (DelzantQuotient i u c)] [BorelSpace (DelzantQuotient i u c)]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {n : ℕ} [Fact (finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) = 2 * n)]
    (hn : Fintype.card (activeSet (facetPairing i u) c v) = n)
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j))) :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := compactSpace_delzantQuotient (u := u) (c := c) hΔ.isBounded
    (((hΔ.delzantQuotientSymplecticForm hi).liouvilleMeasure n).map (reducedMomentMap hβ)).restrict
          {y | ∀ j ∉ activeSet (facetPairing i u) c v, c j < y (i (u j))} =
      (ENNReal.ofReal (2 * π) ^ n •
        hi.dualMeasure.restrict (facetPolyhedron i u c)).restrict
          {y | ∀ j ∉ activeSet (facetPairing i u) c v, c j < y (i (u j))} := by
  subst hn
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := compactSpace_delzantQuotient (u := u) (c := c) hΔ.isBounded
  set e := vertexChart hv hi hvP
  set O := {y : StrongDual ℝ V | ∀ j ∉ activeSet (facetPairing i u) c v, c j < y (i (u j))}
  set m : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v) → StrongDual ℝ V :=
    weightMomentMap fun k ↦ -hv.edgeBasis hi k
  have hO : MeasurableSet O := by
    refine IsOpen.measurableSet ?_
    simp only [O, ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const (continuous_eval_const _)
  have hμ : Measurable (reducedMomentMap (u := u) (c := c) hβ) :=
    (continuous_reducedMomentMap hβ).measurable
  have hm : Measurable fun w ↦ v + m w :=
    (continuous_const.add (continuous_weightMomentMap _)).measurable
  -- In the vertex chart the moment map is the weight model translated to `v`.
  -- The source and the target of the chart are the preimages of `O` under the moment map and the
  -- translated weight model; both sides unfold to the same strict facet inequalities.
  have hsrc : reducedMomentMap hβ ⁻¹' O = e.source := by
    rw [vertexChart_source]
    rfl
  have htgt : e.target = (fun w ↦ v + m w) ⁻¹' O := by
    rw [vertexChart_target]
    rfl
  have hedge : hv.edgeBasis hi = hi.dualBasis hv.basis :=
    Module.Basis.eq_ofRepr_eq_repr fun y k ↦ by
      rw [IsSmoothVertex.edgeBasis_repr, IsIntegralLattice.dualBasis_repr, hv.basis_apply]
  have hae : reducedMomentMap hβ ∘ e.symm =ᵐ[volume.restrict e.target] fun w ↦ v + m w :=
    (ae_restrict_mem e.open_target.measurableSet).mono fun w hw ↦
      reducedMomentMap_vertexChart_symm hv hi hvP (le_of_mem_vertexChart_target hv hi hvP hw)
  rw [Measure.restrict_map hμ hO, hsrc,
    ← hΔ.map_vertexChart_symm_volume_restrict hi hv hvP rfl,
    AEMeasurable.map_map_of_aemeasurable hμ.aemeasurable
      (e.continuousOn_symm.aemeasurable e.open_target.measurableSet),
    Measure.map_congr hae,
    htgt, ← Measure.restrict_map hm hO,
    -- Split off the translation, and write the weights `-ε_k` as the negated basis `-ε`.
    show (fun w ↦ v + m w) = (v + ·) ∘ m from rfl,
    ← Measure.map_map (measurable_const_add v) (continuous_weightMomentMap _).measurable,
    show (weightMomentMap fun k ↦ -hv.edgeBasis hi k) = weightMomentMap (-⇑(hv.edgeBasis hi))
      from rfl, Module.Basis.map_volume_weightMomentMap_neg, hedge, hi.addHaar_dualBasis,
    ← hedge, Measure.map_smul]
  swap
  · exact (measurable_const_add v).aemeasurable
  -- Translating the cone of the weight model to `v` gives `Δ` near `v`.
  rw [Measure.restrict_smul, Measure.restrict_smul,
    map_add_dualMeasure_restrict_cone hi hv]

/-- **The Duistermaat–Heckman measure of a symplectic toric manifold.** Let `Δ` be a Delzant
polytope in `V*`, of dimension `n`, and `(M_Δ, ω_Δ)` its Delzant quotient, of dimension `2n`. The
pushforward by the moment map `μ_Δ` of the Liouville measure `|ω_Δⁿ / n!|` is `(2π)ⁿ` times the
lattice-normalized Lebesgue measure on `Δ`, for which the weight lattice has covolume one. -/
theorem duistermaatHeckmanMeasure_delzantQuotientSymplecticForm
    [MeasurableSpace (DelzantQuotient i u c)] [BorelSpace (DelzantQuotient i u c)]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {n : ℕ} [Fact (finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) = 2 * n)]
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j))) :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := compactSpace_delzantQuotient (u := u) (c := c) hΔ.isBounded
    (hΔ.delzantQuotientSymplecticForm hi).duistermaatHeckmanMeasure n (reducedMomentMap hβ) =
      ENNReal.ofReal (2 * π) ^ n • hi.dualMeasure.restrict (facetPolyhedron i u c) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := compactSpace_delzantQuotient (u := u) (c := c) hΔ.isBounded
  have hn : finrank ℝ V = n := by
    have h : finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) = 2 * n := Fact.out
    rw [hΔ.finrank_delzantQuotientModelSpace hi] at h
    omega
  have hμ : Measurable (reducedMomentMap (u := u) (c := c) hβ) :=
    (continuous_reducedMomentMap hβ).measurable
  have hP : MeasurableSet (facetPolyhedron i u c) := measurableSet_facetPolyhedron
  -- The open stars of the vertices and the complement of `Δ` cover `V*`.
  set O : StrongDual ℝ V → Set (StrongDual ℝ V) :=
    fun v ↦ {y | ∀ j ∉ activeSet (facetPairing i u) c v, c j < y (i (u j))}
  rw [SmoothTwoForm.duistermaatHeckmanMeasure_def]
  refine (Measure.ext_iff_of_sUnion_eq_univ
    (S := insert (facetPolyhedron i u c)ᶜ (O '' (facetPolyhedron i u c).extremePoints ℝ))
    ((finite_extremePoints_facetPolyhedron.image O).insert _).countable ?_).2 ?_
  · refine eq_univ_of_forall fun y ↦ ?_
    by_cases hy : y ∈ facetPolyhedron i u c
    · obtain ⟨v, hv, hsub⟩ := exists_mem_extremePoints_activeSet_subset
        (isCompact_facetPolyhedron_of_isBounded hΔ.isBounded) hy
      refine mem_sUnion.2 ⟨O v, mem_insert_of_mem _ (mem_image_of_mem O hv), fun j hj ↦ ?_⟩
      refine lt_of_le_of_ne (mem_facetPolyhedron.1 hy j) fun h ↦ hj (hsub ?_)
      rw [mem_activeSet, facetPairing_apply, h]
    · exact mem_sUnion.2 ⟨_, mem_insert _ _, hy⟩
  rintro s (rfl | ⟨v, hv, rfl⟩)
  · -- Both measures vanish off `Δ`, which contains the image of the moment map.
    have hpre : reducedMomentMap hβ ⁻¹' (facetPolyhedron i u c)ᶜ = ∅ :=
      eq_empty_of_forall_notMem fun q hq ↦ hq (reducedMomentMap_mem_facetPolyhedron hβ q)
    rw [Measure.restrict_smul, Measure.restrict_restrict hP.compl, compl_inter_self,
      Measure.restrict_empty, smul_zero, Measure.restrict_eq_zero, Measure.map_apply hμ hP.compl,
      hpre, measure_empty]
  · have hsv := hΔ.isSmoothVertex v hv
    have := Fintype.ofFinite (activeSet (facetPairing i u) c v)
    refine hΔ.map_liouvilleMeasure_restrict_vertexStar hi hsv hv.1 ?_ hβ
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hsv.ncard_activeSet, hi.finrank_eq, hn]

/-- **The symplectic volume of a symplectic toric manifold.** The Delzant quotient `(M_Δ, ω_Δ)` of a
Delzant polytope `Δ ⊆ V*` of dimension `n` has Liouville volume `(2π)ⁿ vol(Δ)`, where `vol` is the
lattice-normalized Lebesgue measure, for which the weight lattice has covolume one. -/
theorem liouvilleMeasure_univ_delzantQuotientSymplecticForm
    [MeasurableSpace (DelzantQuotient i u c)] [BorelSpace (DelzantQuotient i u c)]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {n : ℕ} [Fact (finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) = 2 * n)] :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := compactSpace_delzantQuotient (u := u) (c := c) hΔ.isBounded
    (hΔ.delzantQuotientSymplecticForm hi).liouvilleMeasure n univ =
      ENNReal.ofReal (2 * π) ^ n * hi.dualMeasure (facetPolyhedron i u c) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := compactSpace_delzantQuotient (u := u) (c := c) hΔ.isBounded
  have hβ := surjective_linearCombination_real hi.span_range_eq_top hΔ.surjective_linearCombination
  rw [← SmoothTwoForm.duistermaatHeckmanMeasure_univ (continuous_reducedMomentMap hβ).measurable,
    hΔ.duistermaatHeckmanMeasure_delzantQuotientSymplecticForm hi hβ, smul_apply,
    Measure.restrict_apply_univ, smul_eq_mul]

end IsDelzant

/-! ### Examples -/

/-- **The symplectic volume of `ℂPⁿ`.** The Delzant quotient of the standard simplex of size
`a > 0` in `ℝⁿ`, which is `ℂPⁿ` (`TauCeti.Toric.DelzantQuotient.simplexHomeomorph`), has symplectic
volume `(2π)ⁿ aⁿ / n!`. -/
theorem liouvilleMeasure_univ_delzantQuotientSymplecticForm_simplex (n : ℕ) [NeZero n] {a : ℝ}
    (ha : 0 < a)
    [MeasurableSpace (DelzantQuotient ((Int.castAddHom ℝ).compLeft (Fin n))
      (simplexNormal (Fin n)) (simplexSupport a))]
    [BorelSpace (DelzantQuotient ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a))] :
    letI := (isDelzant_simplex ha).delzantQuotientChartedSpace (isIntegralLattice_intCast n)
    haveI : Fact (finrank ℝ (ProperSMul.QuotientModelSpace
        (kernelTorusLieAlgebra ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n)))
        (Fin (Fintype.card (Option (Fin n)) + finrank ℝ (Fin n → ℝ)) → ℝ)) = 2 * n) :=
      ⟨by rw [(isDelzant_simplex ha).finrank_delzantQuotientModelSpace
        (isIntegralLattice_intCast n), Module.finrank_fin_fun]⟩
    haveI := (isDelzant_simplex ha).isManifold_delzantQuotient (isIntegralLattice_intCast n)
    haveI := compactSpace_delzantQuotient (isDelzant_simplex (κ := Fin n) ha).isBounded
    ((isDelzant_simplex ha).delzantQuotientSymplecticForm
        (isIntegralLattice_intCast n)).liouvilleMeasure n univ =
      ENNReal.ofReal (2 * π) ^ n * ENNReal.ofReal (a ^ n / n.factorial) := by
  rw [(isDelzant_simplex ha).liouvilleMeasure_univ_delzantQuotientSymplecticForm,
    dualMeasure_facetPolyhedron_simplex n ha.le]

/-- **The symplectic area of the two-sphere.** The Delzant quotient of the interval `[0, a]`,
`a > 0`, the moment polytope of the two-sphere, has symplectic area `2π a`. -/
theorem liouvilleMeasure_univ_delzantQuotientSymplecticForm_interval {a : ℝ} (ha : 0 < a)
    [MeasurableSpace (DelzantQuotient (Int.castAddHom ℝ) ![1, -1] ![0, -a])]
    [BorelSpace (DelzantQuotient (Int.castAddHom ℝ) ![1, -1] ![0, -a])] :
    letI := (isDelzant_interval ha).delzantQuotientChartedSpace isIntegralLattice_castAddHom
    haveI : Fact (finrank ℝ (ProperSMul.QuotientModelSpace
        (kernelTorusLieAlgebra (Int.castAddHom ℝ) ![(1 : ℤ), -1])
        (Fin (Fintype.card (Fin 2) + finrank ℝ ℝ) → ℝ)) = 2 * 1) :=
      ⟨by rw [(isDelzant_interval ha).finrank_delzantQuotientModelSpace
        isIntegralLattice_castAddHom, Module.finrank_self]⟩
    haveI := (isDelzant_interval ha).isManifold_delzantQuotient isIntegralLattice_castAddHom
    haveI := compactSpace_delzantQuotient (isDelzant_interval ha).isBounded
    ((isDelzant_interval ha).delzantQuotientSymplecticForm
        isIntegralLattice_castAddHom).liouvilleMeasure 1 univ =
      ENNReal.ofReal (2 * π * a) := by
  rw [(isDelzant_interval ha).liouvilleMeasure_univ_delzantQuotientSymplecticForm,
    dualMeasure_facetPolyhedron_interval, pow_one, ← ENNReal.ofReal_mul two_pi_pos.le]

/-- **The symplectic volume of a Hirzebruch surface.** The Delzant quotient of the Hirzebruch
trapezoid `{0 ≤ x(e₁), 0 ≤ x(e₂) ≤ b, x(e₁) + k x(e₂) ≤ a}`, for `0 < b` and `k b < a`, has
symplectic volume `(2π)² (a b - k b² / 2)`. For `k = 0` the trapezoid is the rectangle
`[0, a] × [0, b]`, the moment polytope of `S² × S²`, and the volume is `(2π)² a b`. -/
theorem liouvilleMeasure_univ_delzantQuotientSymplecticForm_hirzebruch {k : ℤ} {a b : ℝ}
    (hb : 0 < b) (ha : 0 < a) (hab : k * b < a)
    [MeasurableSpace (DelzantQuotient ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
      (hirzebruchSupport a b))]
    [BorelSpace (DelzantQuotient ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
      (hirzebruchSupport a b))] :
    letI := (isDelzant_hirzebruch hb ha hab).delzantQuotientChartedSpace
      (isIntegralLattice_intCast 2)
    haveI : Fact (finrank ℝ (ProperSMul.QuotientModelSpace
        (kernelTorusLieAlgebra ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
        (Fin (Fintype.card (Fin 4) + finrank ℝ (Fin 2 → ℝ)) → ℝ)) = 2 * 2) :=
      ⟨by rw [(isDelzant_hirzebruch hb ha hab).finrank_delzantQuotientModelSpace
        (isIntegralLattice_intCast 2), Module.finrank_fin_fun]⟩
    haveI := (isDelzant_hirzebruch hb ha hab).isManifold_delzantQuotient
      (isIntegralLattice_intCast 2)
    haveI := compactSpace_delzantQuotient (isDelzant_hirzebruch hb ha hab).isBounded
    ((isDelzant_hirzebruch hb ha hab).delzantQuotientSymplecticForm
        (isIntegralLattice_intCast 2)).liouvilleMeasure 2 univ =
      ENNReal.ofReal (2 * π) ^ 2 * ENNReal.ofReal (a * b - k * b ^ 2 / 2) := by
  rw [(isDelzant_hirzebruch hb ha hab).liouvilleMeasure_univ_delzantQuotientSymplecticForm,
    dualMeasure_facetPolyhedron_hirzebruch ha.le hab.le]

end TauCeti.Toric
