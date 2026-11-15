/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# The quotient manifold theorem

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on a
finite-dimensional boundaryless smooth manifold `M`. The **quotient manifold theorem** says that
the orbit space `M ⧸ G` is a smooth manifold of dimension `dim M - dim G` for which the orbit
projection `π : M → M ⧸ G` is a smooth submersion. This file proves it. Quotients of this kind
are the reduced spaces of symplectic reduction and the homogeneous spaces of Lie groups.

The charts come from transverse slices. At `x : M`, choose a complement `W` of the orbit tangent
space `𝔤 · x` in the model space of `M` and a linear isomorphism `e` of `ℝ^(dim M - dim G)`
with `W`. The slice through `x` is `τ v = φ⁻¹ (φ x + e v)` for the extended chart `φ` at `x`.
The slice map `(g, v) ↦ g • τ v` is a local diffeomorphism at `(1, 0)`
(`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`), hence at `(g, v)` for every `g` and every
`v` near `0`, and properness makes it injective on `G × U` for a small open neighbourhood `U` of
`0` (`ProperSMul.exists_mem_nhds_injOn_smul_slice`). The chart of `M ⧸ G` at the orbit of `x` is
the inverse of `v ↦ [τ v]` on `U` (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`). Its
transitions are smooth by `TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`.

The model space is `ℝ^(dim M - dim G)`, the Euclidean space
`ProperSMul.QuotientModelSpace E E'` for the model spaces `E` of `G` and `E'` of `M`. The charted
space is the definition `ProperSMul.orbitRelQuotientChartedSpace`, not an instance, because its
model depends on the model with corners of `G`, which instance search cannot recover from the
orbit space. Once it is in place, the manifold structure is found by instance search.

## Main results

* `ProperSMul.orbitRelQuotientChartedSpace`: the slice charts on `M ⧸ G`.
* `ProperSMul.instIsManifoldOrbitRelQuotient`: they form a smooth manifold.
* `ProperSMul.contMDiff_quotientMk`: the orbit projection is smooth.
* `ProperSMul.isSubmersion_quotientMk`: the orbit projection is a smooth submersion. So a map out
  of `M ⧸ G` is smooth exactly when its composite with the projection is
  (`Manifold.IsSubmersion.contMDiff_comp_iff`).
* `ProperSMul.ker_mfderiv_quotientMk`: the kernel of the differential of the orbit projection at
  `x` is the orbit tangent space `𝔤 · x`.

The orbit space is Hausdorff by the instance `t2Space_quotient_mulAction_of_properSMul`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.10 (the
  quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21.
-/

public section

noncomputable section

open Function Set Filter Manifold Module Topology TauCeti
open scoped ContDiff Manifold

namespace ProperSMul

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The model space `ℝ^(dim E' - dim E)` of the orbit space of a free proper action of a Lie group
modelled on `E` on a manifold modelled on `E'`. -/
abbrev QuotientModelSpace (E E' : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] : Type :=
  EuclideanSpace ℝ (Fin (finrank ℝ E' - finrank ℝ E))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [BoundarylessManifold I G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

section Slice

omit [BoundarylessManifold I G] in
variable (I G I') in
/-- A free action of a finite-dimensional Lie group is locally free. -/
private theorem isotropy_eq_bot (x : M) :
    (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  exact Lie.isotropy_eq_bot_of_stabilizer_eq_bot (IsCancelSMul.stabilizer_eq_bot x)

variable (I G I') in
/-- The complement of the orbit tangent space along which the slice through `x` runs. -/
private def sliceComplement (x : M) : Submodule ℝ E' :=
  (Submodule.exists_isCompl
    ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)).choose

omit [BoundarylessManifold I G] [I'.Boundaryless] [ProperSMul G M] [IsCancelSMul G M] in
private theorem isCompl_sliceComplement (x : M) :
    IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)
      (sliceComplement I G I' x : Submodule ℝ E') :=
  (Submodule.exists_isCompl
    ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)).choose_spec

omit [BoundarylessManifold I G] in
private theorem finrank_sliceComplement (x : M) :
    finrank ℝ (QuotientModelSpace E E') = finrank ℝ (sliceComplement I G I' x) := by
  have h1 : finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) +
      finrank ℝ (sliceComplement I G I' x) = finrank ℝ E' :=
    Submodule.finrank_add_eq_of_isCompl (isCompl_sliceComplement x)
  -- The Lie algebra `GroupLieAlgebra I G` is the model space `E` of `G`.
  have h2 : finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) =
      finrank ℝ E :=
    InfinitesimalAction.finrank_orbitTangent_of_isotropy_eq_bot _ _ (isotropy_eq_bot I G I' x)
  rw [finrank_euclideanSpace_fin]
  omega

variable (I G I') in
/-- Linear coordinates `ℝ^(dim M - dim G) ≃ W` on the complement along the slice through `x`. -/
private def sliceEquiv (x : M) : QuotientModelSpace E E' ≃L[ℝ] sliceComplement I G I' x :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_sliceComplement x)

variable (I G I') in
/-- The slice through `x`, `v ↦ φ⁻¹ (φ x + e v)`, for the extended chart `φ` at `x`. -/
private def slice (x : M) (v : QuotientModelSpace E E') : M :=
  (extChartAt I' x).symm (extChartAt I' x x + sliceEquiv I G I' x v)

omit [BoundarylessManifold I G] in
private theorem slice_zero (x : M) : slice I G I' x 0 = x := by
  simp [slice]

/-- The slice map of the slice through `x` is a local diffeomorphism at `(1, 0)`. -/
private theorem isLocalDiffeomorphAt_smul_slice (x : M) :
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, QuotientModelSpace E E')) I' ∞
      (fun p : G × QuotientModelSpace E E' ↦ p.1 • slice I G I' x p.2) (1, 0) := by
  have h := isLocalDiffeomorphAt_smul_extChartAt_symm (I := I) (G := G)
    (isotropy_eq_bot I G I' x) (isCompl_sliceComplement x)
  -- Precompose with the linear coordinates on the complement.
  let e := sliceEquiv I G I' x
  let T : (G × QuotientModelSpace E E') ≃ₘ^∞⟮I.prod 𝓘(ℝ, QuotientModelSpace E E'),
      I.prod 𝓘(ℝ, sliceComplement I G I' x)⟯ (G × sliceComplement I G I' x) :=
    { toEquiv := (Equiv.refl G).prodCongr e.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (e.contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (e.symm.contDiff.contMDiff.comp contMDiff_snd) }
  have hT : T (1, 0) = (1, 0) := Prod.ext rfl e.map_zero
  exact IsLocalDiffeomorphAt.comp (hf := T.isLocalDiffeomorph (1, 0)) (hg := hT ▸ h)

omit [BoundarylessManifold I G] in
/-- The slice through `x` is smooth where `φ x + e v` lies in the target of `φ`. -/
private theorem contMDiffOn_slice (x : M) :
    ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ (slice I G I' x)
      ((fun v ↦ extChartAt I' x x + (sliceEquiv I G I' x v : E')) ⁻¹'
        (extChartAt I' x).target) :=
  (contMDiffOn_extChartAt_symm x).comp
    (contDiff_const.add ((sliceComplement I G I' x).subtypeL.contDiff.comp
      (sliceEquiv I G I' x).contDiff)).contMDiff.contMDiffOn fun _ hv ↦ hv

/-- Properness and freeness give an open neighbourhood `U` of `0` on which the slice through `x` is
smooth and over which the slice map is injective and a local diffeomorphism on all of `G × U`. -/
private theorem exists_sliceDomain (x : M) :
    ∃ U : Set (QuotientModelSpace E E'), IsOpen U ∧ 0 ∈ U ∧
      ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ (slice I G I' x) U ∧
      InjOn (fun p : G × QuotientModelSpace E E' ↦ p.1 • slice I G I' x p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, QuotientModelSpace E E')) I' ∞
        (fun p : G × QuotientModelSpace E E' ↦ p.1 • slice I G I' x p.2) (univ ×ˢ U) := by
  have hloc := isLocalDiffeomorphAt_smul_slice (I := I) (G := G) (I' := I') x
  set B := (fun v ↦ extChartAt I' x x + (sliceEquiv I G I' x v : E')) ⁻¹'
    (extChartAt I' x).target
  have hB : IsOpen B := (isOpen_extChartAt_target x).preimage (continuous_const.add
    (continuous_subtype_val.comp (sliceEquiv I G I' x).continuous))
  have h0B : (0 : QuotientModelSpace E E') ∈ B := by simp [B]
  -- Properness upgrades local injectivity near `(1, 0)` to injectivity on a tube.
  obtain ⟨N, hN, hinjN⟩ := hloc.exists_mem_nhds_injOn
  obtain ⟨U₁, hU₁, hinj⟩ := exists_mem_nhds_injOn_smul_slice
    ((contMDiffOn_slice x).continuousOn.continuousAt (hB.mem_nhds h0B))
    (by rw [slice_zero]; exact IsCancelSMul.stabilizer_eq_bot x) hN hinjN
  refine ⟨interior (U₁ ∩ B ∩ {v | ∀ g : G, IsLocalDiffeomorphAt
      (I.prod 𝓘(ℝ, QuotientModelSpace E E')) I' ∞
      (fun p : G × QuotientModelSpace E E' ↦ p.1 • slice I G I' x p.2) (g, v)}),
    isOpen_interior, mem_interior_iff_mem_nhds.2 (inter_mem (inter_mem hU₁ (hB.mem_nhds h0B))
      hloc.eventually_forall_smul_slice),
    (contMDiffOn_slice x).mono fun v hv ↦ (interior_subset hv).1.2,
    hinj.mono (prod_mono_right fun v hv ↦ (interior_subset hv).1.1), ?_⟩
  rintro ⟨⟨g, v⟩, -, hv⟩
  exact (interior_subset hv).2 g

variable (I G I') in
/-- The domain of the slice chart at `x`. -/
private def sliceDomain (x : M) : Set (QuotientModelSpace E E') :=
  (exists_sliceDomain (I := I) (G := G) (I' := I') x).choose

private theorem isOpen_sliceDomain (x : M) : IsOpen (sliceDomain I G I' x) :=
  (exists_sliceDomain x).choose_spec.1

private theorem zero_mem_sliceDomain (x : M) : 0 ∈ sliceDomain I G I' x :=
  (exists_sliceDomain x).choose_spec.2.1

private theorem contMDiffOn_sliceDomain (x : M) :
    ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ (slice I G I' x) (sliceDomain I G I' x) :=
  (exists_sliceDomain x).choose_spec.2.2.1

private theorem injOn_sliceDomain (x : M) :
    InjOn (fun p : G × QuotientModelSpace E E' ↦ p.1 • slice I G I' x p.2)
      (univ ×ˢ sliceDomain I G I' x) :=
  (exists_sliceDomain x).choose_spec.2.2.2.1

private theorem isLocalDiffeomorphOn_sliceDomain (x : M) :
    IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, QuotientModelSpace E E')) I' ∞
      (fun p : G × QuotientModelSpace E E' ↦ p.1 • slice I G I' x p.2)
      (univ ×ˢ sliceDomain I G I' x) :=
  (exists_sliceDomain x).choose_spec.2.2.2.2

variable (I G I') in
/-- The slice chart at `x`: the inverse of `v ↦ [τ v]` on the slice domain. -/
private def sliceChart (x : M) :
    OpenPartialHomeomorph (MulAction.orbitRel.Quotient G M) (QuotientModelSpace E E') :=
  (OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((MulAction.injOn_quotientMk_slice
      (injOn_sliceDomain (I := I) (G := G) (I' := I') x)).toPartialEquiv _ _)
    (continuous_quot_mk.comp_continuousOn
      (contMDiffOn_sliceDomain (I := I) (G := G) (I' := I') x).continuousOn)
    (MulAction.isOpenEmbedding_quotientMk_slice (isOpen_sliceDomain x) (injOn_sliceDomain x)
      (isLocalDiffeomorphOn_sliceDomain (I := I) (G := G) (I' := I')
        x).isLocalHomeomorphOn).isOpenMap
    (isOpen_sliceDomain x)).symm

private theorem sliceChart_target (x : M) :
    (sliceChart I G I' x).target = sliceDomain I G I' x :=
  rfl

private theorem sliceChart_symm_apply (x : M) (v : QuotientModelSpace E E') :
    (sliceChart I G I' x).symm v = Quotient.mk _ (slice I G I' x v) :=
  rfl

private theorem mem_sliceChart_source (x : M) :
    Quotient.mk _ x ∈ (sliceChart I G I' x).source :=
  ⟨0, zero_mem_sliceDomain x, congrArg (Quotient.mk _) (slice_zero x)⟩

/-- In the slice chart at `x`, the orbit of `f z'` depends smoothly on `z'` wherever `f` does. -/
private theorem contMDiffAt_sliceChart_comp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Type*} [TopologicalSpace K] {L : ModelWithCorners ℝ F K} {P : Type*}
    [TopologicalSpace P] [ChartedSpace K P] {f : P → M} {z : P} (hf : ContMDiffAt L I' ∞ f z)
    (x : M) (hz : Quotient.mk _ (f z) ∈ (sliceChart I G I' x).source) :
    ContMDiffAt L 𝓘(ℝ, QuotientModelSpace E E') ∞
      (fun z' ↦ sliceChart I G I' x (Quotient.mk _ (f z'))) z := by
  set c := sliceChart I G I' x
  have hs : c (Quotient.mk _ (f z)) ∈ sliceDomain I G I' x := c.map_source hz
  obtain ⟨t, ht, -, hev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff (isOpen_sliceDomain x)
    (injOn_sliceDomain x) (isLocalDiffeomorphOn_sliceDomain x) hf hs (c.left_inv hz)
  refine ht.congr_of_eventuallyEq ?_
  filter_upwards [hev] with z' ⟨htU, hiff⟩
  -- The point `t z'` of the slice domain lies on the orbit of `f z'`.
  have h1 : c.symm (t z') = Quotient.mk _ (f z') := (hiff _ htU).2 rfl
  rw [← h1, c.right_inv htU]

end Slice

variable (I G I' M) in
/-- **The charts of the quotient manifold.** For a free proper smooth action of a
finite-dimensional Lie group `G` on a boundaryless manifold `M`, the orbit space `M ⧸ G` is
charted by transverse slices: the chart at an orbit `q` is the inverse of `v ↦ [τ v]` on a small
open neighbourhood of `0` in `ℝ^(dim M - dim G)`, for a slice `τ` through a representative of
`q` transverse to its orbit. -/
@[instance_reducible]
def orbitRelQuotientChartedSpace :
    ChartedSpace (QuotientModelSpace E E') (MulAction.orbitRel.Quotient G M) where
  atlas := range fun q : MulAction.orbitRel.Quotient G M ↦ sliceChart I G I' q.out
  chartAt q := sliceChart I G I' q.out
  mem_chart_source q := by
    have h := mem_sliceChart_source (I := I) (G := G) (I' := I') q.out
    rwa [Quotient.out_eq] at h
  chart_mem_atlas q := mem_range_self q

private theorem chartAt_orbitRelQuotient (q : MulAction.orbitRel.Quotient G M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    chartAt (QuotientModelSpace E E') q = sliceChart I G I' q.out :=
  rfl

/-- **The quotient manifold theorem.** The orbit space of a free proper smooth action of a
finite-dimensional Lie group `G` on a boundaryless smooth manifold `M` is a smooth manifold for
the slice charts `ProperSMul.orbitRelQuotientChartedSpace`. -/
instance instIsManifoldOrbitRelQuotient :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsManifold 𝓘(ℝ, QuotientModelSpace E E') ∞ (MulAction.orbitRel.Quotient G M) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ ?_
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id_eq,
    inter_univ, CompTriple.comp_eq]
  intro v hv
  rw [id_eq, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    sliceChart_target, mem_inter_iff, mem_preimage, sliceChart_symm_apply] at hv
  -- The transition sends `v` to the slice coordinate at `q'` of the orbit of `τ v`.
  have h := contMDiffAt_sliceChart_comp
    ((contMDiffOn_sliceDomain q.out).contMDiffAt ((isOpen_sliceDomain q.out).mem_nhds hv.1))
    q'.out hv.2
  exact (contMDiffAt_iff_contDiffAt.1 h).contDiffWithinAt

/-- **The orbit projection is smooth** for the slice charts on `M ⧸ G`. -/
theorem contMDiff_quotientMk :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiff I' 𝓘(ℝ, QuotientModelSpace E E') ∞ (Quotient.mk (MulAction.orbitRel G M)) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  intro y
  rw [contMDiffAt_iff_target]
  refine ⟨continuous_quot_mk.continuousAt, ?_⟩
  -- In the chart at the orbit of `y`, the projection reads as a slice coordinate.
  have hy := mem_chart_source (QuotientModelSpace E E') (Quotient.mk (MulAction.orbitRel G M) y)
  rw [chartAt_orbitRelQuotient] at hy
  have h := contMDiffAt_sliceChart_comp (I := I) (G := G) contMDiffAt_id _ hy
  rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, chartAt_orbitRelQuotient]
  exact h

/-- The differential of the orbit projection is surjective: the slice through a representative,
moved to `y` by the action, is a smooth section whose composite with the projection is the inverse
of the chart at the orbit of `y`. -/
private theorem surjective_mfderiv_quotientMk (y : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    Surjective
      (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E') (Quotient.mk (MulAction.orbitRel G M)) y) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  set q := Quotient.mk (MulAction.orbitRel G M) y
  set x := q.out
  obtain ⟨g, hg⟩ : ∃ g : G, g • y = x :=
    MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq q)))
  set σ : QuotientModelSpace E E' → M := fun v ↦ g⁻¹ • slice I G I' x v
  have hσ0 : σ 0 = y := by simp [σ, slice_zero, ← hg]
  have hπσ : Quotient.mk (MulAction.orbitRel G M) ∘ σ =
      (extChartAt 𝓘(ℝ, QuotientModelSpace E E') q).symm := by
    funext v
    rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id]
    exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ _))
  have hq0 : extChartAt 𝓘(ℝ, QuotientModelSpace E E') q q = 0 := by
    have h0 : (sliceChart I G I' x).symm 0 = q := by
      rw [sliceChart_symm_apply, slice_zero, Quotient.out_eq]
    rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, chartAt_orbitRelQuotient]
    exact (congrArg (sliceChart I G I' x) h0.symm).trans
      ((sliceChart I G I' x).right_inv (zero_mem_sliceDomain x))
  have hderiv : mfderiv 𝓘(ℝ, QuotientModelSpace E E') 𝓘(ℝ, QuotientModelSpace E E')
      (Quotient.mk (MulAction.orbitRel G M) ∘ σ) 0 = ContinuousLinearMap.id ℝ _ := by
    rw [hπσ, ← hq0, ← mfderivWithin_univ, ← (𝓘(ℝ, QuotientModelSpace E E')).range_eq_univ]
    exact mfderivWithin_range_extChartAt_symm
  have hσ : MDifferentiableAt 𝓘(ℝ, QuotientModelSpace E E') I' σ 0 :=
    ((isLocalDiffeomorphOn_sliceDomain x ⟨(g⁻¹, 0), mem_univ _, zero_mem_sliceDomain x⟩
      ).contMDiffAt.mdifferentiableAt (by simp)).comp (0 : QuotientModelSpace E E')
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  -- The chain rule for the projection after the section, at the point `σ 0 = y`.
  have key : ∀ z, σ 0 = z → Surjective (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E')
      (Quotient.mk (MulAction.orbitRel G M)) z) := by
    rintro z rfl w
    refine ⟨mfderiv 𝓘(ℝ, QuotientModelSpace E E') I' σ 0 w, ?_⟩
    have h := mfderiv_comp (0 : QuotientModelSpace E E')
      ((contMDiff_quotientMk (I := I) (G := G) (σ 0)).mdifferentiableAt (by simp)) hσ
    rw [hderiv] at h
    exact (congrArg (· w) h).symm
  exact key y hσ0

/-- **The orbit projection is a smooth submersion** for the slice charts on `M ⧸ G`. In
particular a map out of `M ⧸ G` is smooth exactly when its composite with the projection is
(`Manifold.IsSubmersion.contMDiff_comp_iff`). -/
theorem isSubmersion_quotientMk :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsSubmersion I' 𝓘(ℝ, QuotientModelSpace E E') ∞ (Quotient.mk (MulAction.orbitRel G M)) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  exact (contMDiff_quotientMk.isSubmersionOfComplement_of_surjective_mfderiv (by simp)
    (surjective_mfderiv_quotientMk (I := I) (G := G))).isSubmersion

/-- **The vertical directions of the orbit projection are the orbit directions.** The kernel of
the differential at `y` of the projection `M → M ⧸ G` is the orbit tangent space `𝔤 · y`. -/
theorem ker_mfderiv_quotientMk (y : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E') (Quotient.mk (MulAction.orbitRel G M)) y).ker =
      (InfinitesimalAction.fundamental I G I' M).orbitTangent y := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  -- The projection is constant on the orbit of `y`, so orbit directions are vertical.
  have hconst : Quotient.mk (MulAction.orbitRel G M) ∘ (fun g : G ↦ g • y) =
      fun _ ↦ Quotient.mk _ y :=
    funext fun g ↦ Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ _))
  have key : ∀ z, (1 : G) • y = z → ∀ ξ : GroupLieAlgebra I G,
      mfderiv I' 𝓘(ℝ, QuotientModelSpace E E') (Quotient.mk (MulAction.orbitRel G M)) z
        (mfderiv I I' (fun g : G ↦ g • y) 1 ξ) = 0 := by
    rintro z rfl ξ
    have h := mfderiv_comp (f := fun g : G ↦ g • y) (g := Quotient.mk (MulAction.orbitRel G M))
      (1 : G) ((contMDiff_quotientMk (I := I) ((1 : G) • y)).mdifferentiableAt (by simp))
      ((ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) y).mdifferentiableAt
        (x := 1) (by simp))
    rw [hconst, mfderiv_const] at h
    exact (congrArg (· ξ) h).symm
  have hle : (InfinitesimalAction.fundamental I G I' M).orbitTangent y ≤
      (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E') (Quotient.mk (MulAction.orbitRel G M)) y).ker := by
    intro v hv
    obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ _).1 hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, InfinitesimalAction.fundamental_apply,
      fundamentalVectorField_apply]
    exact key y (one_smul G y) ξ
  -- Both have the dimension of `G`.
  have hrank : finrank ℝ (QuotientModelSpace E E') + finrank ℝ
      (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E') (Quotient.mk (MulAction.orbitRel G M)) y).ker =
        finrank ℝ E' := by
    have h := LinearMap.finrank_range_add_finrank_ker (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E')
      (Quotient.mk (MulAction.orbitRel G M)) y).toLinearMap
    rw [LinearMap.range_eq_top.2 (surjective_mfderiv_quotientMk y), finrank_top] at h
    exact h
  rw [finrank_euclideanSpace_fin] at hrank
  have horbit : finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent y) =
      finrank ℝ E :=
    InfinitesimalAction.finrank_orbitTangent_of_isotropy_eq_bot _ _ (isotropy_eq_bot I G I' y)
  have hdim : finrank ℝ E ≤ finrank ℝ E' :=
    horbit ▸ Submodule.finrank_le ((InfinitesimalAction.fundamental I G I' M).orbitTangent y)
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  omega

end ProperSMul
