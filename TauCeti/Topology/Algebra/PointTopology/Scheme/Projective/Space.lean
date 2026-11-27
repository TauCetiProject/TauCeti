/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.HomogeneousCoordinates
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Charts
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Points of projective space in homogeneous coordinates

Let `K` be a field and `ι` a finite type. The projective space `ℙ(K^ι)` is the projective
spectrum `Proj (Sym_K (ι → K))`, with the homogeneous coordinates `X_i` of
`TauCeti.projCoord`. A nonzero vector `v : ι → K` gives the `K`-point
`TauCeti.SchemePointTopology.projPoint v` with homogeneous coordinates `v`, the morphism
`Spec K ⟶ Proj (Sym_K (ι → K))` of Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections` for
the evaluation `X_i ↦ v i`. Every `K`-point has this form, and two nonzero vectors give the same
point exactly when they are proportional.

For a topological field `K`, with the chart topology `TauCeti.SchemePointTopology.topology` on
the points, `v ↦ projPoint v` is continuous on the nonzero vectors: on the standard chart
`D₊(X_k)` it is the chart map applied to the evaluation `X_i / X_k ↦ v i / v k`. So
`ℙ(K^ι)(K)` is a continuous image of the nonzero vectors of `K^ι`.

Over a nonarchimedean local field `K` every point has homogeneous coordinates in the valuation
ring with one coordinate equal to `1`: divide by a coordinate of largest valuation. These
coordinate vectors form a compact set, so `ℙ(K^ι)(K)` is compact. This is the projective case
of the compactness of the points of a proper scheme over a local field.

## Main declarations

* `TauCeti.SchemePointTopology.projPoint`: the `K`-point with given homogeneous coordinates.
* `TauCeti.SchemePointTopology.projPoint_eq_projPoint_iff`: two coordinate vectors give the
  same point exactly when they are proportional.
* `TauCeti.SchemePointTopology.exists_projPoint_eq`: every `K`-point has homogeneous
  coordinates, which may be chosen with a coordinate equal to `1`.
* `TauCeti.SchemePointTopology.continuous_projPoint`: over a topological field, the point
  depends continuously on its nonzero coordinate vector.
* `TauCeti.SchemePointTopology.compactSpace_points_projToSpec_of_isNonarchimedeanLocalField`:
  over a nonarchimedean local field `K`, the `K`-points of `Proj (Sym_K (ι → K))` form a compact
  space.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  proof of Prop. 4.4, p. 11, and Cor. 5.6, p. 16.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization TauCeti.SymmetricAlgebra
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {K : Type u} [Field K] {ι : Type u} [Fintype ι]

section Points

variable [DecidableEq ι]

/-- The morphism `Spec K ⟶ ℙ(K^ι)` with homogeneous coordinates `v` is the chart `D₊(X_k)`
applied to `projChartEval v hk`, for any `k` with `v k ≠ 0`. -/
private theorem fromOfGlobalSections_projEval_eq {v : ι → K} {k : ι} (hk : v k ≠ 0) :
    Proj.fromOfGlobalSections (homogeneousSubmodule K (ι → K))
        ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (projEval v : _ →+* K))
        (by exact map_irrelevant_comp_projEval_eq_top _ fun h ↦ hk (congrFun h k)) =
      Spec.map (CommRingCat.ofHom (projChartEval v hk).toRingHom) ≫
        Proj.awayι (homogeneousSubmodule K (ι → K)) (projCoord K k) (projCoord_mem k) one_pos := by
  rw [projChartEval_toRingHom]
  exact Proj.fromOfGlobalSections_Spec_eq_awayLift _ (map_irrelevant_projEval_eq_top hk) one_pos
    (projCoord_mem k) _

/-- The `K`-point of `ℙ(K^ι) = Proj (Sym_K (ι → K))` with homogeneous coordinates `v ≠ 0`: the
morphism `Spec K ⟶ ℙ(K^ι)` of `Proj.fromOfGlobalSections` for the evaluation `X_i ↦ v i`. -/
noncomputable def projPoint (v : ι → K) (hv : v ≠ 0) : Points (R := K) (projToSpec K (ι → K)) :=
  ⟨Proj.fromOfGlobalSections (homogeneousSubmodule K (ι → K))
      ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (projEval v : _ →+* K))
      (by exact map_irrelevant_comp_projEval_eq_top _ hv), by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
    have h := (chartPoint (projToSpec K (ι → K))
      (CommAlgCat.of K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k)))
      _ (awayι_projCoord_projToSpec k) (projChartEval v hk)).property
    rw [chartPoint_val] at h
    rw [fromOfGlobalSections_projEval_eq hk]
    exact h⟩

/-- The underlying morphism of `projPoint v` is `Proj.fromOfGlobalSections` of the evaluation
at `v`. -/
theorem projPoint_val (v : ι → K) (hv : v ≠ 0) :
    (projPoint v hv).val = Proj.fromOfGlobalSections (homogeneousSubmodule K (ι → K))
      ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (projEval v : _ →+* K))
      (by exact map_irrelevant_comp_projEval_eq_top _ hv) :=
  (rfl)

/-- On the standard chart `D₊(X_k)`, the point with homogeneous coordinates `v` is the chart
applied to the evaluation `X_i / X_k ↦ v i / v k`. -/
theorem projPoint_eq_chartPoint {v : ι → K} (hv : v ≠ 0) {k : ι} (hk : v k ≠ 0) :
    projPoint v hv = chartPoint (projToSpec K (ι → K))
      (CommAlgCat.of K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k)))
      _ (awayι_projCoord_projToSpec k) (projChartEval v hk) :=
  Subtype.ext <| by
    rw [chartPoint_val, projPoint_val]
    exact fromOfGlobalSections_projEval_eq hk

/-- **Homogeneous coordinates are defined up to a scalar.** Rescaling the coordinates by a
nonzero scalar does not change the point. -/
theorem projPoint_smul {v : ι → K} (hv : v ≠ 0) {c : K} (hc : c ≠ 0) :
    projPoint (c • v) (smul_ne_zero hc hv) = projPoint v hv :=
  Subtype.ext <| TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling _ _ _
    (Units.map (Scheme.ΓSpecIso (.of K)).inv.hom.toMonoidHom (Units.mk0 c hc))
    (fun n a ha ↦ by simp [projEval_smul_of_mem c v ha]) _

/-- The point with homogeneous coordinates `v` pulls the standard chart `D₊(X_k)` back to the
basic open of `v k` in `Spec K`. -/
theorem projPoint_preimage_basicOpen (v : ι → K) (hv : v ≠ 0) (k : ι) :
    (projPoint v hv).val ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule K (ι → K)) (projCoord K k) =
      (Spec (.of K)).basicOpen ((Scheme.ΓSpecIso (.of K)).inv.hom (v k)) := by
  rw [projPoint_val, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos (projCoord_mem k),
    RingHom.comp_apply, RingHom.coe_coe, projEval_projCoord]

/-- The point with homogeneous coordinates `v` lies on the standard chart `D₊(X_k)` exactly when
`v k ≠ 0`. -/
theorem projPoint_mem_basicOpen_iff (v : ι → K) (hv : v ≠ 0) (k : ι) :
    (projPoint v hv).val (IsLocalRing.closedPoint K) ∈
        Proj.basicOpen (homogeneousSubmodule K (ι → K)) (projCoord K k) ↔ v k ≠ 0 := by
  rw [← Scheme.Hom.mem_preimage (projPoint v hv).val (x := IsLocalRing.closedPoint K),
    projPoint_preimage_basicOpen]
  by_cases hk : v k = 0
  · rw [hk, map_zero, Scheme.basicOpen_zero]
    exact iff_of_false id (not_not_intro rfl)
  · rw [Scheme.basicOpen_of_isUnit _ ((IsUnit.mk0 _ hk).map _)]
    exact iff_of_true trivial hk

/-- **Homogeneous coordinates are unique up to a scalar.** Two nonzero coordinate vectors give
the same point exactly when they are proportional. -/
theorem projPoint_eq_projPoint_iff {v w : ι → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    projPoint v hv = projPoint w hw ↔ ∃ c : K, c ≠ 0 ∧ w = c • v := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
    -- The point lies on the chart `D₊(X_k)`, so `w k ≠ 0` as well.
    have hwk : w k ≠ 0 := by
      rw [← projPoint_mem_basicOpen_iff w hw k, ← h]
      exact (projPoint_mem_basicOpen_iff v hv k).2 hk
    rw [projPoint_eq_chartPoint hv hk, projPoint_eq_chartPoint hw hwk] at h
    have hα := chartPoint_injective _ _ _ _ h
    refine ⟨w k / v k, div_ne_zero hwk hk, funext fun i ↦ ?_⟩
    -- Compare the two evaluations at the chart coordinate `X_i / X_k`.
    have hi := congrArg (· (Away.mk _ (projCoord_mem k) 1 (projCoord K i)
      (by simpa using projCoord_mem i))) hα
    simp only [projChartEval_awayMk, projEval_projCoord, pow_one] at hi
    rw [div_eq_div_iff hk hwk] at hi
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hk]
    linear_combination -hi
  · rintro ⟨c, hc, rfl⟩
    exact (projPoint_smul hv hc).symm

/-- **Every point has homogeneous coordinates.** Every `K`-point of `ℙ(K^ι)` is `projPoint v` for
a coordinate vector `v` with some coordinate equal to `1`. -/
theorem exists_projPoint_eq (x : Points (R := K) (projToSpec K (ι → K))) :
    ∃ (v : ι → K) (hv : v ≠ 0) (k : ι), v k = 1 ∧ projPoint v hv = x := by
  have hspan : Submodule.span K (Set.range fun i : ι ↦ (Pi.single i 1 : ι → K)) = ⊤ := by
    rw [show (fun i : ι ↦ (Pi.single i 1 : ι → K)) = ⇑(Pi.basisFun K ι) from
      funext fun i ↦ (Pi.basisFun_apply K ι i).symm]
    exact (Pi.basisFun K ι).span_eq
  have hx : x.val (IsLocalRing.closedPoint K) ∈
      ⨆ i, Proj.basicOpen (homogeneousSubmodule K (ι → K)) (projCoord K i) := by
    rw [show (⨆ i, Proj.basicOpen (homogeneousSubmodule K (ι → K)) (projCoord K i)) = ⊤ by
      simpa only [projCoord_def] using iSup_basicOpen_ι_eq_top K (ι → K) _ hspan]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  rw [← Proj.opensRange_awayι _ _ (projCoord_mem k) one_pos] at hk
  obtain ⟨α, rfl⟩ := (mem_range_chartPoint_iff_closedPoint (projToSpec K (ι → K))
    (CommAlgCat.of K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k))) _
    (awayι_projCoord_projToSpec k) x).2 hk
  obtain ⟨v, hk0, hk1, rfl⟩ := exists_eq_projChartEval k α
  have hv : v ≠ 0 := fun h ↦ hk0 (congrFun h k)
  exact ⟨v, hv, k, hk1, projPoint_eq_chartPoint hv hk0⟩

end Points

section Topology

variable [TopologicalSpace K]

/-- A homogeneous polynomial depends continuously on the coordinate vector at which it is
evaluated. -/
theorem continuous_projEval [IsTopologicalRing K] (s : _root_.SymmetricAlgebra K (ι → K)) :
    Continuous fun v : ι → K ↦ projEval v s := by
  induction s using _root_.SymmetricAlgebra.induction with
  | algebraMap r => simpa only [AlgHom.commutes] using continuous_const
  | ι m =>
    simp only [projEval_ι]
    fun_prop
  | mul a b ha hb =>
    simp only [map_mul]
    exact ha.mul hb
  | add a b ha hb =>
    simp only [map_add]
    exact ha.add hb

variable [DecidableEq ι] [IsTopologicalDivisionRing K]

/-- On the coordinate vectors with `v k ≠ 0`, the chart evaluation `X_i / X_k ↦ v i / v k`
depends continuously on `v`. -/
theorem continuous_projChartEval (k : ι) :
    Continuous fun v : {v : ι → K // v k ≠ 0} ↦ projChartEval v.val v.property := by
  refine PointTopology.continuous_iff.2 fun z ↦ ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (projCoord_mem k) z
  simp only [projChartEval_awayMk]
  exact ((continuous_projEval a).comp continuous_subtypeVal).div
    (((continuous_apply k).comp continuous_subtypeVal).pow n) fun v ↦ pow_ne_zero n v.property

/-- **Homogeneous coordinates are continuous.** Over a topological field, the point with
homogeneous coordinates `v` depends continuously on the nonzero vector `v`, for the chart
topology on the points of `ℙ(K^ι)`. -/
theorem continuous_projPoint [T1Space K] :
    Continuous fun v : {v : ι → K // v ≠ 0} ↦ projPoint v.val v.property := by
  refine continuous_of_cover_nhds (s := fun k : ι ↦ {v : {v : ι → K // v ≠ 0} | v.val k ≠ 0})
    (fun v ↦ ?_) fun k ↦ ?_
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp v.property
    exact ⟨k, (isOpen_compl_singleton.preimage
      ((continuous_apply k).comp continuous_subtypeVal)).mem_nhds hk⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have h : Set.domRestrict {v : {v : ι → K // v ≠ 0} | v.val k ≠ 0}
        (fun v : {v : ι → K // v ≠ 0} ↦ projPoint v.val v.property) =
        chartPoint (projToSpec K (ι → K))
          (CommAlgCat.of K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k))) _
          (awayι_projCoord_projToSpec k) ∘
          (fun w : {v : {v : ι → K // v ≠ 0} | v.val k ≠ 0} ↦ projChartEval w.val.val w.property) :=
      funext fun w ↦ projPoint_eq_chartPoint w.val.property w.property
    rw [h]
    have hw : Continuous fun w : {v : {v : ι → K // v ≠ 0} | v.val k ≠ 0} ↦
        (⟨w.val.val, w.property⟩ : {v : ι → K // v k ≠ 0}) :=
      (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
    have h1 := continuous_chartPoint (R := K) (projToSpec K (ι → K))
      (CommAlgCat.of K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k))) _
      (awayι_projCoord_projToSpec k)
    have h2 := (continuous_projChartEval (K := K) k).comp hw
    exact h1.comp h2

end Topology

section LocalField

open ValuativeRel

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [Fintype ι] in
/-- **Projective space over a nonarchimedean local field is compact.** For a nonarchimedean local
field `K`, the `K`-points of `ℙ(K^ι) = Proj (Sym_K (ι → K))` form a compact space for the chart
topology. -/
instance compactSpace_points_projToSpec_of_isNonarchimedeanLocalField [Finite ι] :
    CompactSpace (Points (R := K) (projToSpec K (ι → K))) := by
  classical
  have := Fintype.ofFinite ι
  -- Every point has homogeneous coordinates in the valuation ring with one coordinate equal to
  -- `1`, obtained by dividing by a coordinate of largest valuation, and these coordinate vectors
  -- form a compact set `S`.
  let S : Set (ι → K) := (Set.univ.pi fun _ ↦ {x | valuation K x ≤ 1}) ∩
    ⋃ k, {v | v k = 1}
  have hS : IsCompact S := by
    refine (isCompact_univ_pi fun _ ↦
      IsNonarchimedeanLocalField.isCompact_closedBall K 1).inter_right
      (isClosed_iUnion_of_finite fun k ↦ isClosed_eq (continuous_apply k) continuous_const)
  have hS0 : S ⊆ {v | v ≠ 0} := by
    rintro v ⟨-, hv⟩ rfl
    obtain ⟨_, hk⟩ := Set.mem_iUnion.mp hv
    exact zero_ne_one hk
  have hT : IsCompact (Subtype.val ⁻¹' S : Set {v : ι → K // v ≠ 0}) := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff,
      Set.image_preimage_eq_of_subset (by rwa [Subtype.range_coe_subtype])]
    exact hS
  refine ⟨?_⟩
  convert hT.image (continuous_projPoint (K := K) (ι := ι))
  refine (Set.eq_univ_of_forall fun x ↦ ?_).symm
  obtain ⟨v, hv, -, -, rfl⟩ := exists_projPoint_eq x
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
  obtain ⟨k, -, hvk, hdiv⟩ := (valuation K).valuationSubring.exists_ne_zero_and_div_mem
    (s := Finset.univ) (g := v) ⟨i₀, Finset.mem_univ _, hi₀⟩
  have hc : (v k)⁻¹ ≠ 0 := inv_ne_zero hvk
  refine ⟨⟨(v k)⁻¹ • v, smul_ne_zero hc hv⟩, ⟨fun i _ ↦ ?_, Set.mem_iUnion.2 ⟨k, ?_⟩⟩,
    projPoint_smul hv hc⟩
  · simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (hdiv i (Finset.mem_univ _))
  · simp [hvk]

end LocalField

end TauCeti.SchemePointTopology
