/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Charts

/-!
# Points of projective space in homogeneous coordinates

Let `K` be a field and `ι` a finite type. The projective space `ℙ(K^ι)` is the projective
spectrum `Proj (Sym_K (ι → K))`, whose homogeneous coordinates `X_i` are the images of the
standard basis vectors. A nonzero vector `v : ι → K` gives the `K`-point
`TauCeti.SchemePointTopology.projPoint v` with homogeneous coordinates `v`, the morphism
`Spec K ⟶ Proj (Sym_K (ι → K))` of Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections` for
the evaluation `X_i ↦ v i`. Every `K`-point has this form, and rescaling `v` by a nonzero
scalar does not change the point.

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
* `TauCeti.SchemePointTopology.projPoint_smul`: rescaling the coordinates does not change the
  point.
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

@[expose] public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization TauCeti.SymmetricAlgebra
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {K : Type u} [Field K] {ι : Type u} [Fintype ι]

section Algebraic

variable [DecidableEq ι]

variable (K) in
/-- The homogeneous coordinate `X_i` of `ℙ(K^ι) = Proj (Sym_K (ι → K))`, the image of the
standard basis vector `Pi.single i 1`. -/
noncomputable def projCoord (i : ι) : _root_.SymmetricAlgebra K (ι → K) :=
  _root_.SymmetricAlgebra.ι K (ι → K) (Pi.single i 1)

omit [Fintype ι] in
/-- The homogeneous coordinate `X_i` has degree one. -/
theorem projCoord_mem (i : ι) : projCoord K i ∈ homogeneousSubmodule K (ι → K) 1 :=
  ι_mem_homogeneousSubmodule K (ι → K) _

/-- Evaluation of homogeneous polynomials at the coordinate vector `v`: the `K`-algebra map
`Sym_K (ι → K) → K` sending `X_i` to `v i`. -/
noncomputable def projEval (v : ι → K) : _root_.SymmetricAlgebra K (ι → K) →ₐ[K] K :=
  _root_.SymmetricAlgebra.lift (Fintype.linearCombination K v)

omit [DecidableEq ι] in
/-- The evaluation at `v` sends the linear form `m` to `∑ i, m i * v i`. -/
@[simp]
theorem projEval_ι (v : ι → K) (m : ι → K) :
    projEval v (_root_.SymmetricAlgebra.ι K (ι → K) m) = ∑ i, m i * v i := by
  simp [projEval, Fintype.linearCombination_apply]

/-- The evaluation at `v` sends the homogeneous coordinate `X_i` to `v i`. -/
@[simp]
theorem projEval_projCoord (v : ι → K) (i : ι) : projEval v (projCoord K i) = v i := by
  simp [projCoord, Pi.single_apply]

omit [DecidableEq ι] in
/-- Rescaling the coordinates by `c` multiplies the value of a homogeneous polynomial of degree
`n` by `cⁿ`. -/
theorem projEval_smul_of_mem (c : K) (v : ι → K) {n : ℕ} {s : _root_.SymmetricAlgebra K (ι → K)}
    (hs : s ∈ homogeneousSubmodule K (ι → K) n) :
    projEval (c • v) s = c ^ n * projEval v s := by
  have h : Fintype.linearCombination K (c • v) = c • Fintype.linearCombination K v := by
    ext m
    simp [Fintype.linearCombination_apply, Finset.mul_sum, mul_left_comm]
  rw [projEval, h, lift_smul_of_mem_homogeneousSubmodule K (ι → K) _ c hs, smul_eq_mul]
  rfl

omit [DecidableEq ι] in
/-- A nonzero coordinate vector sends the irrelevant ideal to the unit ideal. -/
theorem map_irrelevant_projEval {v : ι → K} {k : ι} (hk : v k ≠ 0) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule K (ι → K))).toIdeal.map
      (projEval v : _root_.SymmetricAlgebra K (ι → K) →+* K) = ⊤ := by
  classical
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (x := projCoord K k) ?_)
    (by simpa using hk)
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne _ (projCoord_mem k) one_ne_zero]

omit [Fintype ι] in
/-- The standard chart `D₊(X_k)` of `ℙ(K^ι)` lies over `Spec K`. -/
theorem awayι_projCoord_projToSpec (k : ι) :
    Proj.awayι (homogeneousSubmodule K (ι → K)) (projCoord K k) (projCoord_mem k) one_pos ≫
        projToSpec K (ι → K) =
      Spec.algebraMap K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k)) := by
  rw [awayι_projToSpec]

/-- The evaluation `X_i / X_k ↦ v i / v k` of the standard chart `D₊(X_k)` at a coordinate
vector `v` with `v k ≠ 0`. -/
noncomputable def projChartEval (v : ι → K) {k : ι} (hk : v k ≠ 0) :
    Away (homogeneousSubmodule K (ι → K)) (projCoord K k) →ₐ[K] K :=
  { Away.lift (homogeneousSubmodule K (ι → K)) (projEval v : _ →+* K)
      (f := projCoord K k) (by simpa using hk) with
    commutes' r := by
      change Away.lift _ _ _ (fromZeroRingHom _ _ (algebraMap K _ r)) = _
      rw [← HomogeneousLocalization.algebraMap_eq, Away.lift_algebraMap]
      exact (projEval v).commutes r }

/-- The chart evaluation is `Away.lift` of the evaluation at `v`. -/
theorem projChartEval_apply (v : ι → K) {k : ι} (hk : v k ≠ 0) (z) :
    projChartEval v hk z = Away.lift (homogeneousSubmodule K (ι → K)) (projEval v : _ →+* K)
      (f := projCoord K k) (by simpa using hk) z :=
  (rfl)

end Algebraic

section Points

variable [DecidableEq ι]

/-- The morphism `Spec K ⟶ ℙ(K^ι)` with homogeneous coordinates `v` is the chart `D₊(X_k)`
applied to `projChartEval v hk`, for any `k` with `v k ≠ 0`. -/
private theorem fromOfGlobalSections_projEval_eq {v : ι → K} {k : ι} (hk : v k ≠ 0) :
    Proj.fromOfGlobalSections (homogeneousSubmodule K (ι → K))
        ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (projEval v : _ →+* K))
        (by rw [← Ideal.map_map, map_irrelevant_projEval hk, Ideal.map_top]) =
      Spec.map (CommRingCat.ofHom (projChartEval v hk).toRingHom) ≫
        Proj.awayι (homogeneousSubmodule K (ι → K)) (projCoord K k) (projCoord_mem k) one_pos :=
  Proj.fromOfGlobalSections_Spec_eq_awayLift _ (map_irrelevant_projEval hk) one_pos
    (projCoord_mem k) _

/-- The `K`-point of `ℙ(K^ι) = Proj (Sym_K (ι → K))` with homogeneous coordinates `v ≠ 0`: the
morphism `Spec K ⟶ ℙ(K^ι)` of `Proj.fromOfGlobalSections` for the evaluation `X_i ↦ v i`. -/
noncomputable def projPoint (v : ι → K) (hv : v ≠ 0) : Points (R := K) (projToSpec K (ι → K)) :=
  ⟨Proj.fromOfGlobalSections (homogeneousSubmodule K (ι → K))
      ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (projEval v : _ →+* K))
      (by
        obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
        rw [← Ideal.map_map, map_irrelevant_projEval hk, Ideal.map_top]), by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
    have h := (chartPoint (projToSpec K (ι → K))
      (CommAlgCat.of K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k)))
      _ (awayι_projCoord_projToSpec k) (projChartEval v hk)).property
    rw [chartPoint_val] at h
    rw [fromOfGlobalSections_projEval_eq hk]
    exact h⟩

/-- On the standard chart `D₊(X_k)`, the point with homogeneous coordinates `v` is the chart
applied to the evaluation `X_i / X_k ↦ v i / v k`. -/
theorem projPoint_eq_chartPoint {v : ι → K} (hv : v ≠ 0) {k : ι} (hk : v k ≠ 0) :
    projPoint v hv = chartPoint (projToSpec K (ι → K))
      (CommAlgCat.of K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k)))
      _ (awayι_projCoord_projToSpec k) (projChartEval v hk) :=
  Subtype.ext <| by
    rw [chartPoint_val]
    exact fromOfGlobalSections_projEval_eq hk

/-- **Homogeneous coordinates are defined up to a scalar.** Rescaling the coordinates by a
nonzero scalar does not change the point. -/
theorem projPoint_smul {v : ι → K} (hv : v ≠ 0) {c : K} (hc : c ≠ 0) :
    projPoint (c • v) (smul_ne_zero hc hv) = projPoint v hv := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hck : (c • v) k ≠ 0 := by simpa using And.intro hc hk
  rw [projPoint_eq_chartPoint _ hk, projPoint_eq_chartPoint _ hck]
  congr 1
  refine AlgHom.toRingHom_injective ?_
  exact Away.lift_eq_of_forall_mem _ _ (Units.mk0 c hc)
    (fun n a ha ↦ projEval_smul_of_mem c v ha) (projCoord_mem k) _ _

/-- The coordinate functions `X_i / X_k` of the standard chart `D₊(X_k)`: the `K`-algebra map
`Sym_K (ι → K) → (Sym_K (ι → K))_(X_k)` sending `X_i` to `X_i / X_k`. -/
private noncomputable def chartCoordinates (k : ι) :
    _root_.SymmetricAlgebra K (ι → K) →ₐ[K] Away (homogeneousSubmodule K (ι → K)) (projCoord K k) :=
  _root_.SymmetricAlgebra.lift <|
    (Away.mkLinearMap (𝒜 := homogeneousSubmodule K (ι → K)) (projCoord_mem k) 1).comp <|
      (_root_.SymmetricAlgebra.ι K (ι → K)).codRestrict _ fun m ↦ by
        simp

omit [Fintype ι] in
/-- A homogeneous polynomial `s` of degree `n`, written in the chart coordinates `X_i / X_k`, is
the fraction `s / X_kⁿ`. -/
private theorem chartCoordinates_of_mem (k : ι) {n : ℕ} {s : _root_.SymmetricAlgebra K (ι → K)}
    (hs : s ∈ homogeneousSubmodule K (ι → K) n) :
    chartCoordinates k s = Away.mk _ (projCoord_mem k) n s (by simpa using hs) := by
  apply val_injective
  let L := Localization.Away (projCoord K k)
  let f : _root_.SymmetricAlgebra K (ι → K) →ₐ[K] L := IsScalarTower.toAlgHom K _ L
  let g : _root_.SymmetricAlgebra K (ι → K) →ₐ[K] L :=
    (IsScalarTower.toAlgHom K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k)) L).comp
      (chartCoordinates k)
  have hg : ∀ m, g (_root_.SymmetricAlgebra.ι K (ι → K) m) =
      Localization.mk 1 (⟨projCoord K k, 1, pow_one _⟩ : Submonoid.powers (projCoord K k)) *
        f (_root_.SymmetricAlgebra.ι K (ι → K) m) := by
    intro m
    simp only [g, f, chartCoordinates, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
      _root_.SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, Away.mkLinearMap_apply,
      LinearMap.codRestrict_apply]
    rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk,
      ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one]
    simp only [pow_one]
  have h := AlgHom.apply_eq_pow_mul_of_forall_ι_eq f g _ hg hs
  simp only [g, f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h
  rw [HomogeneousLocalization.algebraMap_apply] at h
  rw [h, Away.val_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow,
    Localization.mk_mul, one_pow, one_mul, mul_one]
  rfl

/-- A `K`-point of the standard chart `D₊(X_k)` is the evaluation at the coordinate vector of its
values on the chart coordinates `X_i / X_k`. -/
private theorem eq_projChartEval (k : ι)
    (α : Away (homogeneousSubmodule K (ι → K)) (projCoord K k) →ₐ[K] K) :
    (fun i ↦ α (chartCoordinates k (projCoord K i))) k = 1 ∧
      ∃ (hk : (fun i ↦ α (chartCoordinates k (projCoord K i))) k ≠ 0),
        α = projChartEval (fun i ↦ α (chartCoordinates k (projCoord K i))) hk := by
  set v := fun i ↦ α (chartCoordinates k (projCoord K i))
  have hk1 : v k = 1 := by
    have hself : Away.mk (homogeneousSubmodule K (ι → K)) (projCoord_mem k) 1 (projCoord K k)
        (by simpa using projCoord_mem k) = 1 := by
      apply val_injective
      rw [Away.val_mk, val_one]
      simpa only [pow_one] using Localization.mk_self
        (⟨projCoord K k ^ 1, 1, rfl⟩ : Submonoid.powers (projCoord K k))
    change α (chartCoordinates k (projCoord K k)) = 1
    rw [chartCoordinates_of_mem k (projCoord_mem k), hself, map_one]
  have hcomp : projEval v = α.comp (chartCoordinates k) := by
    ext i
    simp [v, projCoord, Pi.single_apply]
    rfl
  refine ⟨hk1, by simp [hk1], ?_⟩
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (projCoord_mem k) z
  have ha' : a ∈ homogeneousSubmodule K (ι → K) n := by simpa using ha
  rw [projChartEval_apply, Away.lift_mk, ← chartCoordinates_of_mem k ha',
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [RingHom.coe_coe, projEval_projCoord, hk1, one_pow, inv_one, mul_one, hcomp,
    AlgHom.comp_apply]

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
    rw [show (⨆ i, Proj.basicOpen (homogeneousSubmodule K (ι → K)) (projCoord K i)) = ⊤ from
      iSup_basicOpen_ι_eq_top K (ι → K) _ hspan]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  rw [← Proj.opensRange_awayι _ _ (projCoord_mem k) one_pos] at hk
  obtain ⟨α, rfl⟩ := (mem_range_chartPoint_iff_closedPoint (projToSpec K (ι → K))
    (CommAlgCat.of K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k))) _
    (awayι_projCoord_projToSpec k) x).2 hk
  obtain ⟨hk1, hk0, hα⟩ := eq_projChartEval k α
  refine ⟨fun i ↦ α (chartCoordinates k (projCoord K i)), fun h ↦ hk0 (congrFun h k), k, hk1, ?_⟩
  exact (projPoint_eq_chartPoint (v := fun i ↦ α (chartCoordinates k (projCoord K i))) _
    hk0).trans (congrArg _ hα.symm)

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
  have h (v : {v : ι → K // v k ≠ 0}) :
      projChartEval v.val v.property (Away.mk _ (projCoord_mem k) n a ha) =
        projEval v.val a * (v.val k ^ n)⁻¹ := by
    rw [projChartEval_apply, Away.lift_mk, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec, RingHom.coe_coe, projEval_projCoord]
  simp only [h]
  exact ((continuous_projEval a).comp continuous_subtypeVal).mul
    ((((continuous_apply k).comp continuous_subtypeVal).pow n).inv₀
      fun v ↦ pow_ne_zero n v.property)

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
topology. Every point has homogeneous coordinates in the valuation ring with one coordinate equal
to `1`, obtained by dividing by a coordinate of largest valuation, and these coordinate vectors
form a compact set. -/
instance compactSpace_points_projToSpec_of_isNonarchimedeanLocalField [Finite ι] :
    CompactSpace (Points (R := K) (projToSpec K (ι → K))) := by
  classical
  have := Fintype.ofFinite ι
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
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i ↦ valuation K (v i))
    ⟨i₀, Finset.mem_univ _⟩
  have hvk : v k ≠ 0 := by
    intro h
    have := hk i₀ (Finset.mem_univ _)
    rw [h, map_zero, nonpos_iff_eq_zero, map_eq_zero] at this
    exact hi₀ this
  have hc : (v k)⁻¹ ≠ 0 := inv_ne_zero hvk
  refine ⟨⟨(v k)⁻¹ • v, smul_ne_zero hc hv⟩, ⟨fun i _ ↦ ?_, Set.mem_iUnion.2 ⟨k, ?_⟩⟩,
    projPoint_smul hv hc⟩
  · simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have h0 : valuation K (v k) ≠ 0 := by simpa using hvk
    exact (inv_mul_le_iff₀' (pos_iff_ne_zero.2 h0)).2 (by simpa using hk i (Finset.mem_univ _))
  · simp [hvk]

end LocalField

end TauCeti.SchemePointTopology
