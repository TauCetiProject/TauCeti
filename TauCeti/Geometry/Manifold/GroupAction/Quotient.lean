/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Algebra.TypeTags
public import TauCeti.Topology.Algebra.GroupAction.Quotient
public import TauCeti.Topology.Algebra.ProperAction.Basic
import TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap
import TauCeti.Geometry.Manifold.GroupAction.Orbit
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.LinearAlgebra.LinearMap.Comp
import TauCeti.Topology.Algebra.GroupAction.SliceChart

/-!
# The quotient manifold theorem

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on a
finite-dimensional boundaryless smooth manifold `M`. The **quotient manifold theorem** says that
the orbit space `M ⧸ G` (with its quotient topology) is a smooth manifold of dimension
`dim M - dim G` for which the orbit projection `π : M → M ⧸ G` is a smooth submersion with fibre
complement `E` (the model space of `G`) and vertical tangent space `ker dπ_x = 𝔤 · x`. This file
proves it, together with its smooth descent, universal property, uniqueness up to canonical
diffeomorphism, equivariant functoriality, and additive Lie group counterpart (for actions on
`AddAction.orbitRel.Quotient G M`, such as tori `(ℝ / 2πℤ)^k`). Quotients of this kind are the
reduced spaces of symplectic reduction, Delzant quotients, and the homogeneous spaces of Lie
groups.

The charts come from transverse slices. At `x : M`, choose a complement `W` of the orbit tangent
space `𝔤 · x` in the model space `E'` of `M` and a linear isomorphism `e` of `ℝ^(dim M - dim G)`
with `W`. The slice through `x` is `τ v = φ⁻¹ (φ x + e v)` for the extended chart `φ` at `x`.
The slice map `(g, v) ↦ g • τ v` is a local diffeomorphism at `(1, 0)`
(`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`), and properness with trivial stabilizer
shrinks the slice to an open neighbourhood `U` of `0` where it is injective and a smooth local
diffeomorphism on all of `G × U` (`IsLocalDiffeomorphAt.exists_isOpen_smul_slice`). The chart of
`M ⧸ G` at the orbit of `x` is the inverse of `v ↦ [τ v]` on `U`
(`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`). Its transitions are smooth by
`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`.

The model space is `ℝ^(dim M - dim G)`, the Euclidean space
`ProperSMul.QuotientModelSpace E E'` for the model spaces `E` of `G` and `E'` of `M`
(`ProperSMul.finrank_quotientModelSpace`). The charted space
`ProperSMul.orbitRelQuotientChartedSpace` (and its additive counterpart
`ProperVAdd.orbitRelQuotientChartedSpace`) is marked `@[instance_reducible]`, not a global
instance, because its model depends on the model with corners of `G`, which instance search cannot
recover from the orbit space, and because for discrete `G` a global instance would create a diamond
with `MulAction.instChartedSpaceQuotient`. Once it is in place, the manifold structure is found by
instance search.

Neither Hausdorffness nor second-countability needs to be assumed, and `M` may be empty:
`T2Space G` follows from the Lie group structure (`ModelWithCorners.t2Space_of_lieGroup`),
`T2Space M` and `T2Space (MulAction.orbitRel.Quotient G M)` follow from properness
(`t2Space_of_properSMul_of_t1Group`, `t2Space_quotient_mulAction_of_properSMul`), and when `M` is
nonempty `dim G ≤ dim M` (`TauCeti.finrank_le_of_properSMul_of_isCancelSMul`,
`TauCeti.finrank_le_of_properVAdd_of_isCancelVAdd`).

## Main definitions

* `ProperSMul.QuotientModelSpace`: the model space `EuclideanSpace ℝ (Fin (dim E' - dim E))`.
* `ProperSMul.orbitRelQuotientChartedSpace`: the slice charts on `M ⧸ G`.
* `ProperSMul.diffeomorphOfOrbitSubmersion`: for a free proper smooth Lie group action and `m ≤ ∞`,
  the canonical `C^m` diffeomorphism `(M ⧸ G) ≃ₘ^m Q` induced by any surjective `C^m` submersion
  `p : M → Q` whose fibres are the `G`-orbits.
* `ProperSMul.orbitRelQuotientDiffeomorph`: the `C^m` diffeomorphism of orbit manifolds induced by
  an equivariant `C^m` diffeomorphism (`m ≤ ∞`).
* `ProperVAdd.orbitRelQuotientChartedSpace`,
  `ProperVAdd.orbitRelQuotientDiffeomorphMultiplicative`,
  `ProperVAdd.diffeomorphOfOrbitSubmersion`,
  `ProperVAdd.orbitRelQuotientDiffeomorph`: the additive Lie group counterparts on
  `AddAction.orbitRel.Quotient G M`, pulled back from `Multiplicative G`.

## Main results

* `ProperSMul.instIsManifoldOrbitRelQuotient`, `ProperVAdd.instIsManifoldOrbitRelQuotient`: the
  slice charts form a smooth manifold.
* `ProperSMul.contMDiff_quotientMk`, `ProperSMul.surjective_mfderiv_quotientMk`,
  `ProperSMul.isSubmersionOfComplement_quotientMk`, `ProperSMul.isSubmersion_quotientMk`,
  `ProperSMul.exists_contMDiffOn_section_quotientMk`,
  `ProperSMul.exists_orbitRelQuotient_isSubmersion` (and their `ProperVAdd.*` counterparts): the
  orbit projection is a smooth submersion with fibre complement `E` and smooth local sections.
* `ProperSMul.ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt`,
  `ProperVAdd.ker_mfderiv_eq_orbitTangent_fundamental_multiplicative_of_isSubmersionAt`: for a
  proper smooth (multiplicative or additive) Lie group action and a point `x` with trivial
  stabilizer (no global freeness needed), identification of `ker dp_x` with `𝔤 · x` for any `C^m`
  (`m ≠ 0`) submersion at `x` that is locally invariant along the orbit of `x` and whose fibres
  near `(x, x)` lie in single orbits.
* `ProperSMul.ker_mfderiv_quotientMk`, `ProperVAdd.ker_mfderiv_quotientMk`: the kernel of the
  differential of the orbit projection at `y` is the orbit tangent space `𝔤 · y`.
* `ProperSMul.isLocalDiffeomorphAt_smul_section`: a smooth local section `s` of the orbit
  projection is a transverse slice, so `(g, q) ↦ g • s q` is a local diffeomorphism.
* `ProperSMul.contMDiffAt_orbitRelQuotientLift_iff`,
  `ProperSMul.contMDiff_orbitRelQuotientLift_iff`,
  `ProperSMul.existsUnique_contMDiff_comp_quotientMk_eq`,
  `ProperSMul.contMDiff_orbitRelQuotientMap` (and their `ProperVAdd.*` counterparts): smooth
  descent, universal property, and functoriality for `m ≤ ∞`.
* `ProperSMul.contMDiffSMul_orbitRelQuotient`, `ProperSMul.contMDiffConstSMul_orbitRelQuotient`
  (and their `ProperVAdd.*` counterparts): a smooth action commuting with that of `G`, or an action
  by smooth maps commuting with it, descends to one on `M ⧸ G`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 4.31
  (uniqueness of quotient manifold structures) and Theorem 21.10 (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21.
-/

public section

noncomputable section

open Function Set Filter Manifold Module Topology TauCeti
open scoped ContDiff Manifold

namespace ProperSMul

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- The model space `ℝ^(dim E' - dim E)` of the orbit space of a free proper action of a Lie group
modelled on `E` on a manifold modelled on `E'`. -/
abbrev QuotientModelSpace (E E' : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] : Type :=
  EuclideanSpace ℝ (Fin (finrank ℝ E' - finrank ℝ E))

/-- The model space of the orbit space has dimension `dim E' - dim E`. -/
theorem finrank_quotientModelSpace {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] :
    finrank ℝ (QuotientModelSpace E E') = finrank ℝ E' - finrank ℝ E :=
  finrank_euclideanSpace_fin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

section Slice

omit [I'.Boundaryless] [ProperSMul G M] [IsCancelSMul G M] in
variable (I G I') in
/-- The complement of the orbit tangent space along which the slice through `x` runs. -/
private def sliceComplement (x : M) : Submodule ℝ E' :=
  (Submodule.exists_isCompl
    ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)).choose

omit [I'.Boundaryless] [ProperSMul G M] [IsCancelSMul G M] in
private theorem isCompl_sliceComplement (x : M) :
    IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)
      (sliceComplement I G I' x : Submodule ℝ E') :=
  (Submodule.exists_isCompl
    ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)).choose_spec

omit [IsCancelSMul G M] in
private theorem finrank_sliceComplement {x : M} (hx : _root_.MulAction.stabilizer G x = ⊥) :
    finrank ℝ (QuotientModelSpace E E') = finrank ℝ (sliceComplement I G I' x) := by
  have h1 : finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) +
      finrank ℝ (sliceComplement I G I' x) = finrank ℝ E' :=
    Submodule.finrank_add_eq_of_isCompl (isCompl_sliceComplement x)
  have hiso := isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot
    (I := I) (I' := I') hx
  -- The Lie algebra `GroupLieAlgebra I G` is the model space `E` of `G`.
  have h2 : finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) =
      finrank ℝ E :=
    InfinitesimalAction.finrank_orbitTangent_of_isotropy_eq_bot _ _ hiso
  rw [finrank_euclideanSpace_fin]
  omega

omit [IsCancelSMul G M] in
variable (I G I') in
/-- Linear coordinates `ℝ^(dim M - dim G) ≃ W` on the complement along the slice through `x`. -/
private def sliceEquiv {x : M} (hx : _root_.MulAction.stabilizer G x = ⊥) :
    QuotientModelSpace E E' ≃L[ℝ] sliceComplement I G I' x :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_sliceComplement hx)

omit [IsCancelSMul G M] in
variable (I G I') in
/-- The slice through `x`, `v ↦ φ⁻¹ (φ x + e v)`, for the extended chart `φ` at `x`. -/
private def slice {x : M} (hx : _root_.MulAction.stabilizer G x = ⊥)
    (v : QuotientModelSpace E E') : M :=
  (extChartAt I' x).symm (extChartAt I' x x + sliceEquiv I G I' hx v)

omit [IsCancelSMul G M] in
private theorem slice_zero {x : M} (hx : _root_.MulAction.stabilizer G x = ⊥) :
    slice I G I' hx 0 = x := by
  simp [slice]

omit [IsCancelSMul G M] in
/-- The slice map of the slice through a free point `x` is a local diffeomorphism at `(1, 0)`. -/
private theorem isLocalDiffeomorphAt_smul_slice {x : M}
    (hx : _root_.MulAction.stabilizer G x = ⊥) :
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, QuotientModelSpace E E')) I' ∞
      (fun p : G × QuotientModelSpace E E' ↦ p.1 • slice I G I' hx p.2) (1, 0) := by
  have hiso := isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot
    (I := I) (I' := I') hx
  have h := isLocalDiffeomorphAt_smul_extChartAt_symm (I := I) (G := G)
    hiso (isCompl_sliceComplement x)
  -- Precompose with the linear coordinates on the complement.
  let e := sliceEquiv I G I' hx
  rw [← e.map_zero] at h
  exact IsLocalDiffeomorphAt.comp (hg := h) (hf :=
    ((Diffeomorph.refl I G ∞).isLocalDiffeomorph 1).prodMap (e.toDiffeomorph.isLocalDiffeomorph 0))

omit [IsCancelSMul G M] in
/-- The slice through `x` is smooth where `φ x + e v` lies in the target of `φ`. -/
private theorem contMDiffOn_slice {x : M} (hx : _root_.MulAction.stabilizer G x = ⊥) :
    ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ (slice I G I' hx)
      ((fun v ↦ extChartAt I' x x + (sliceEquiv I G I' hx v : E')) ⁻¹'
        (extChartAt I' x).target) :=
  (contMDiffOn_extChartAt_symm x).comp
    (contDiff_const.add ((sliceComplement I G I' x).subtypeL.contDiff.comp
      (sliceEquiv I G I' hx).contDiff)).contMDiff.contMDiffOn fun _ hv ↦ hv

omit [IsCancelSMul G M] in
/-- Properness and trivial stabilizer at `x` give an open neighbourhood `U` of `0` on which the
slice through `x` is smooth and over which the slice map is injective and a local diffeomorphism on
all of `G × U`. -/
private theorem exists_sliceDomain {x : M} (hx : _root_.MulAction.stabilizer G x = ⊥) :
    ∃ U : Set (QuotientModelSpace E E'), IsOpen U ∧ 0 ∈ U ∧
      ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ (slice I G I' hx) U ∧
      InjOn (fun p : G × QuotientModelSpace E E' ↦ p.1 • slice I G I' hx p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, QuotientModelSpace E E')) I' ∞
        (fun p : G × QuotientModelSpace E E' ↦ p.1 • slice I G I' hx p.2) (univ ×ˢ U) := by
  have hloc := isLocalDiffeomorphAt_smul_slice (I := I) (G := G) (I' := I') hx
  obtain ⟨U₁, hU₁, h0U₁, hinj, hlocOn⟩ :=
    hloc.exists_isOpen_smul_slice (by rwa [slice_zero])
  set B := (fun v ↦ extChartAt I' x x + (sliceEquiv I G I' hx v : E')) ⁻¹'
    (extChartAt I' x).target
  have hB : IsOpen B := (isOpen_extChartAt_target x).preimage (continuous_const.add
    (continuous_subtypeVal.comp (sliceEquiv I G I' hx).continuous))
  have h0B : (0 : QuotientModelSpace E E') ∈ B := by simp [B]
  exact ⟨U₁ ∩ B, hU₁.inter hB, ⟨h0U₁, h0B⟩,
    (contMDiffOn_slice hx).mono inter_subset_right,
    hinj.mono (prod_mono_right inter_subset_left),
    fun ⟨⟨g, v⟩, _, hv⟩ ↦ hlocOn ⟨(g, v), mem_univ _, hv.1⟩⟩

omit [IsCancelSMul G M] in
/-- Near a point `x : M` with trivial stabilizer, the transverse-slice coordinate
`t : M → QuotientModelSpace E E'` is smooth at `x`, identifies points on the same `G`-orbit near
`(x, x)`, and has vertical tangent kernel `(mfderiv I' _ t x).ker = 𝔤 · x`. -/
private theorem exists_contMDiffAt_ker_mfderiv_eq_orbitTangent {x : M}
    (hx : _root_.MulAction.stabilizer G x = ⊥) :
    ∃ t : M → QuotientModelSpace E E',
      ContMDiffAt I' 𝓘(ℝ, QuotientModelSpace E E') ∞ t x ∧
      (∀ᶠ yz : M × M in 𝓝 (x, x),
        Quotient.mk (_root_.MulAction.orbitRel G M) yz.1 = Quotient.mk _ yz.2 → t yz.1 = t yz.2) ∧
      (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E') t x).ker =
        (InfinitesimalAction.fundamental I G I' M).orbitTangent x := by
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := I) (I' := I') ∞
  obtain ⟨U, hU_open, h0U, hτ_on, hinj, hlocOn⟩ :=
    exists_sliceDomain (I := I) (G := G) (I' := I') hx
  let J0 := 𝓘(ℝ, QuotientModelSpace E E')
  obtain ⟨t, ht_diff, -, ht_ev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff hU_open hinj hlocOn
    (contMDiffAt_id (I := I') (x := x)) h0U
    (congrArg (Quotient.mk (_root_.MulAction.orbitRel G M)) (slice_zero hx))
  have ht_orb : ∀ᶠ yz : M × M in 𝓝 (x, x),
      Quotient.mk (_root_.MulAction.orbitRel G M) yz.1 = Quotient.mk _ yz.2 →
        t yz.1 = t yz.2 := by
    filter_upwards [prod_mem_nhds ht_ev ht_ev] with ⟨y, z⟩ ⟨⟨hty, hy⟩, ⟨_, hz⟩⟩ hyz
    exact (hz (t y) hty).1 (hyz ▸ (hy (t y) hty).2 rfl)
  have hx_iso := isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot
    (I := I) (I' := I') hx
  have ht_inv : ∀ᶠ g in 𝓝 (1 : G), t (g • x) = t x := by
    have hsmul : Tendsto (fun g : G ↦ (g • x, x)) (𝓝 1) (𝓝 (x, x)) := by
      have hgx : Tendsto (fun g : G ↦ g • x) (𝓝 1) (𝓝 x) := by
        simpa only [id_eq, one_smul] using
          (tendsto_id (x := 𝓝 (1 : G))).smul (tendsto_const_nhds (x := x))
      exact hgx.prodMk_nhds (tendsto_const_nhds (x := x))
    exact (hsmul.eventually ht_orb).mono fun g hg ↦
      hg _root_.MulAction.orbitRel.Quotient.quotient_smul_eq
  have ht_surj : Surjective (mfderiv I' J0 t x) := by
    have hτ_diff : ContMDiffAt J0 I' ∞ (slice I G I' hx) 0 :=
      hτ_on.contMDiffAt (hU_open.mem_nhds h0U)
    have hτ_tendsto : Tendsto (slice I G I' hx) (𝓝 0) (𝓝 x) := by
      simpa only [slice_zero hx] using hτ_diff.continuousAt.tendsto
    have hτ_ev : t ∘ slice I G I' hx =ᶠ[𝓝 0] id := by
      filter_upwards [hU_open.mem_nhds h0U, hτ_tendsto.eventually ht_ev] with u huU ⟨_, hu⟩
      exact ((hu u huU).1 rfl).symm
    have ht_diff_τ0 : MDifferentiableAt I' J0 t (slice I G I' hx 0) := by
      simpa only [slice_zero hx] using ht_diff.mdifferentiableAt (by simp)
    have hid : mfderiv J0 J0 (t ∘ slice I G I' hx) 0 = .id ℝ _ :=
      ((hasMFDerivAt_id (I := J0) 0).congr_of_eventuallyEq hτ_ev).mfderiv
    rw [mfderiv_comp 0 ht_diff_τ0 (hτ_diff.mdifferentiableAt (by simp)), slice_zero hx] at hid
    exact Function.RightInverse.surjective (DFunLike.congr_fun hid)
  have hle : finrank ℝ E ≤ finrank ℝ E' :=
    finrank_le_of_properSMul_of_stabilizer_eq_bot I I' hx
  refine ⟨t, ht_diff, ht_orb,
    ker_mfderiv_eq_orbitTangent_fundamental hx_iso ht_inv ht_surj ?_⟩
  rw [finrank_euclideanSpace_fin]
  omega

variable (I G I') in
/-- The domain of the slice chart at `x`. -/
private def sliceDomain (x : M) : Set (QuotientModelSpace E E') :=
  (exists_sliceDomain (I := I) (G := G) (I' := I') (IsCancelSMul.stabilizer_eq_bot x)).choose

private theorem isOpen_sliceDomain (x : M) : IsOpen (sliceDomain I G I' x) :=
  (exists_sliceDomain (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.1

private theorem zero_mem_sliceDomain (x : M) : 0 ∈ sliceDomain I G I' x :=
  (exists_sliceDomain (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.2.1

private theorem contMDiffOn_sliceDomain (x : M) :
    ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞
      (slice I G I' (IsCancelSMul.stabilizer_eq_bot x)) (sliceDomain I G I' x) :=
  (exists_sliceDomain (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.2.2.1

private theorem injOn_sliceDomain (x : M) :
    InjOn (fun p : G × QuotientModelSpace E E' ↦
      p.1 • slice I G I' (IsCancelSMul.stabilizer_eq_bot x) p.2)
      (univ ×ˢ sliceDomain I G I' x) :=
  (exists_sliceDomain (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.2.2.2.1

private theorem isLocalDiffeomorphOn_sliceDomain (x : M) :
    IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, QuotientModelSpace E E')) I' ∞
      (fun p : G × QuotientModelSpace E E' ↦
        p.1 • slice I G I' (IsCancelSMul.stabilizer_eq_bot x) p.2)
      (univ ×ˢ sliceDomain I G I' x) :=
  (exists_sliceDomain (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.2.2.2.2

variable (I G I') in
/-- The slice chart at `x`: the inverse of `v ↦ [τ v]` on the slice domain. -/
private def sliceChart (x : M) :
    OpenPartialHomeomorph (_root_.MulAction.orbitRel.Quotient G M) (QuotientModelSpace E E') :=
  (OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((TauCeti.MulAction.injOn_quotientMk_slice
      (injOn_sliceDomain (I := I) (G := G) (I' := I') x)).toPartialEquiv _ _)
    (continuous_quot_mk.comp_continuousOn
      (contMDiffOn_sliceDomain (I := I) (G := G) (I' := I') x).continuousOn)
    (TauCeti.MulAction.isOpenEmbedding_quotientMk_slice (isOpen_sliceDomain x) (injOn_sliceDomain x)
      (isLocalDiffeomorphOn_sliceDomain (I := I) (G := G) (I' := I')
        x).isLocalHomeomorphOn).isOpenMap
    (isOpen_sliceDomain x)).symm

private theorem sliceChart_target (x : M) :
    (sliceChart I G I' x).target = sliceDomain I G I' x :=
  rfl

private theorem sliceChart_symm_apply (x : M) (v : QuotientModelSpace E E') :
    (sliceChart I G I' x).symm v =
      Quotient.mk _ (slice I G I' (IsCancelSMul.stabilizer_eq_bot x) v) :=
  rfl

private theorem mem_sliceChart_source (x : M) :
    Quotient.mk _ x ∈ (sliceChart I G I' x).source :=
  ⟨0, zero_mem_sliceDomain x,
    congrArg (Quotient.mk _) (slice_zero (IsCancelSMul.stabilizer_eq_bot x))⟩

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
    ChartedSpace (QuotientModelSpace E E') (_root_.MulAction.orbitRel.Quotient G M) where
  atlas := range fun q : _root_.MulAction.orbitRel.Quotient G M ↦ sliceChart I G I' q.out
  chartAt q := sliceChart I G I' q.out
  mem_chart_source q := by
    have h := mem_sliceChart_source (I := I) (G := G) (I' := I') q.out
    rwa [Quotient.out_eq] at h
  chart_mem_atlas q := mem_range_self q

private theorem chartAt_orbitRelQuotient (q : _root_.MulAction.orbitRel.Quotient G M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    chartAt (QuotientModelSpace E E') q = sliceChart I G I' q.out :=
  rfl

private theorem extChartAt_orbitRelQuotient (q : _root_.MulAction.orbitRel.Quotient G M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    ⇑(extChartAt 𝓘(ℝ, QuotientModelSpace E E') q) = sliceChart I G I' q.out :=
  rfl

/-- **The quotient manifold theorem.** The orbit space of a free proper smooth action of a
finite-dimensional Lie group `G` on a boundaryless smooth manifold `M` is a smooth manifold for
the slice charts `ProperSMul.orbitRelQuotientChartedSpace`. -/
instance instIsManifoldOrbitRelQuotient :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsManifold 𝓘(ℝ, QuotientModelSpace E E') ∞ (_root_.MulAction.orbitRel.Quotient G M) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ ?_
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id_eq,
    inter_univ, CompTriple.comp_eq]
  intro v hv
  obtain ⟨hv₁, hv₂⟩ : v ∈ sliceDomain I G I' q.out ∧
      Quotient.mk _ (slice I G I' (IsCancelSMul.stabilizer_eq_bot q.out) v) ∈
        (sliceChart I G I' q'.out).source := by
    simpa [sliceChart_target, sliceChart_symm_apply] using hv
  -- The transition sends `v` to the slice coordinate at `q'` of the orbit of `τ v`.
  have h := contMDiffAt_sliceChart_comp
    ((contMDiffOn_sliceDomain q.out).contMDiffAt ((isOpen_sliceDomain q.out).mem_nhds hv₁))
    q'.out hv₂
  exact (contMDiffAt_iff_contDiffAt.1 h).contDiffWithinAt

/-- **The orbit projection is smooth** for the slice charts on `M ⧸ G`. -/
theorem contMDiff_quotientMk :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiff I' 𝓘(ℝ, QuotientModelSpace E E') ∞ (Quotient.mk (_root_.MulAction.orbitRel G M)) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  intro y
  rw [contMDiffAt_iff_target]
  refine ⟨continuous_quot_mk.continuousAt, ?_⟩
  -- In the chart at the orbit of `y`, the projection reads as a slice coordinate.
  have hy := mem_chart_source (QuotientModelSpace E E')
    (Quotient.mk (_root_.MulAction.orbitRel G M) y)
  rw [chartAt_orbitRelQuotient] at hy
  have h := contMDiffAt_sliceChart_comp (I := I) (G := G) contMDiffAt_id _ hy
  rw [extChartAt_orbitRelQuotient]
  exact h

/-- The differential of the orbit projection is surjective: the slice through a representative,
moved to `y` by the action, is a smooth section whose composite with the projection is the inverse
of the chart at the orbit of `y`. -/
theorem surjective_mfderiv_quotientMk (y : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    Surjective
      (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E')
        (Quotient.mk (_root_.MulAction.orbitRel G M)) y) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  set q := Quotient.mk (_root_.MulAction.orbitRel G M) y
  set x := q.out
  obtain ⟨g, hg⟩ : ∃ g : G, g • y = x :=
    _root_.MulAction.mem_orbit_iff.1
      (_root_.MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq q)))
  set σ : QuotientModelSpace E E' → M :=
    fun v ↦ g⁻¹ • slice I G I' (IsCancelSMul.stabilizer_eq_bot x) v
  have hσ0 : σ 0 = y := by simp [σ, slice_zero, ← hg]
  have hπσ : Quotient.mk (_root_.MulAction.orbitRel G M) ∘ σ =
      (extChartAt 𝓘(ℝ, QuotientModelSpace E E') q).symm := by
    funext v
    rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id,
      chartAt_orbitRelQuotient, sliceChart_symm_apply]
    exact Quotient.sound (_root_.MulAction.orbitRel_apply.2 (_root_.MulAction.mem_orbit _ _))
  have hq0 : extChartAt 𝓘(ℝ, QuotientModelSpace E E') q q = 0 := by
    have h0 : (sliceChart I G I' x).symm 0 = q := by
      rw [sliceChart_symm_apply, slice_zero, Quotient.out_eq]
    rw [extChartAt_orbitRelQuotient]
    exact (congrArg (sliceChart I G I' x) h0.symm).trans
      ((sliceChart I G I' x).right_inv (zero_mem_sliceDomain x))
  have hderiv : mfderiv 𝓘(ℝ, QuotientModelSpace E E') 𝓘(ℝ, QuotientModelSpace E E')
      (Quotient.mk (_root_.MulAction.orbitRel G M) ∘ σ) 0 = ContinuousLinearMap.id ℝ _ := by
    rw [hπσ, ← hq0, ← mfderivWithin_univ, ← (𝓘(ℝ, QuotientModelSpace E E')).range_eq_univ]
    exact mfderivWithin_range_extChartAt_symm
  have hσ : MDifferentiableAt 𝓘(ℝ, QuotientModelSpace E E') I' σ 0 :=
    ((isLocalDiffeomorphOn_sliceDomain x ⟨(g⁻¹, 0), mem_univ _, zero_mem_sliceDomain x⟩
      ).contMDiffAt.mdifferentiableAt (by simp)).comp (0 : QuotientModelSpace E E')
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  -- The chain rule for the projection after the section, at the point `σ 0 = y`.
  intro w
  refine ⟨mfderiv 𝓘(ℝ, QuotientModelSpace E E') I' σ 0 w, ?_⟩
  have h := mfderiv_comp_apply_of_eq (0 : QuotientModelSpace E E')
    ((contMDiff_quotientMk (I := I) (G := G) y).mdifferentiableAt (by simp)) hσ hσ0 w
  rw [hderiv] at h
  exact h.symm

/-- **The orbit projection is a smooth submersion with fibre complement `E`.** Even when `M` is
empty, the orbit projection has the submersion normal form with complement `E`, the model space
of `G`. -/
theorem isSubmersionOfComplement_quotientMk :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsSubmersionOfComplement E I' 𝓘(ℝ, QuotientModelSpace E E') ∞
      (Quotient.mk (_root_.MulAction.orbitRel G M)) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  by_cases hM : Nonempty M
  · have hle : finrank ℝ E ≤ finrank ℝ E' :=
      finrank_le_of_properSMul_of_isCancelSMul I G I' M
    have hsub := (contMDiff_quotientMk (I := I) (G := G) (I' := I')
      (M := M)).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
      (surjective_mfderiv_quotientMk (I := I) (G := G) (I' := I') (M := M))
    have hdim : finrank ℝ (Fin (finrank ℝ E' - finrank ℝ (QuotientModelSpace E E')) → ℝ) =
        finrank ℝ E := by
      simp only [Module.finrank_fin_fun, finrank_euclideanSpace_fin]
      omega
    exact (IsSubmersionOfComplement.congr_F (ContinuousLinearEquiv.ofFinrankEq hdim)).1 hsub
  · rw [not_nonempty_iff] at hM
    exact isSubmersionOfComplement_iff.2 fun x ↦ isEmptyElim x

/-- **The orbit projection is a smooth submersion** for the slice charts on `M ⧸ G`. In
particular a map out of `M ⧸ G` is smooth exactly when its composite with the projection is
(`Manifold.IsSubmersion.contMDiff_comp_iff`). -/
theorem isSubmersion_quotientMk :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsSubmersion I' 𝓘(ℝ, QuotientModelSpace E E') ∞
      (Quotient.mk (_root_.MulAction.orbitRel G M)) :=
  letI := orbitRelQuotientChartedSpace I G I' M
  (isSubmersionOfComplement_quotientMk (I := I) (G := G) (I' := I') (M := M)).isSubmersion

/-- Over an open neighbourhood of `[y]` in `M ⧸ G`, the orbit projection admits a smooth local
section sending `[y]` to `y`. -/
theorem exists_contMDiffOn_section_quotientMk (y : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    ∃ U : Set (_root_.MulAction.orbitRel.Quotient G M),
      IsOpen U ∧ Quotient.mk (_root_.MulAction.orbitRel G M) y ∈ U ∧
      ∃ s : _root_.MulAction.orbitRel.Quotient G M → M,
        s (Quotient.mk (_root_.MulAction.orbitRel G M) y) = y ∧
        ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ s U ∧
        ∀ q ∈ U, Quotient.mk (_root_.MulAction.orbitRel G M) (s q) = q :=
  letI := orbitRelQuotientChartedSpace I G I' M
  ((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).isSubmersionAt
    y).exists_contMDiffOn_section

omit [IsCancelSMul G M] in
/-- For a proper smooth action of a finite-dimensional real Lie group `G` on a boundaryless
manifold `M` and a point `x : M` with trivial stabilizer (no global freeness needed), if
`p : M → Q` is a `C^m` (`m ≠ 0`) submersion at `x` that is locally invariant along the orbit of
`x` and whose fibres near `(x, x)` lie in single `G`-orbits, then its vertical tangent space at
`x` is the orbit tangent space `ker dp_x = 𝔤 · x`. -/
theorem ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    {m : ℕ∞ω} {p : M → Q} {x : M} (hx : _root_.MulAction.stabilizer G x = ⊥)
    (hp : IsSubmersionAt I' JQ m p x) (hm₀ : m ≠ 0)
    (hinv : ∀ᶠ g in 𝓝 (1 : G), p (g • x) = p x)
    (hfib : ∀ᶠ yz : M × M in 𝓝 (x, x), p yz.1 = p yz.2 → ∃ g : G, g • yz.2 = yz.1) :
    (mfderiv I' JQ p x).ker = (InfinitesimalAction.fundamental I G I' M).orbitTangent x := by
  obtain ⟨t, ht_diff, ht_orb, ht_ker⟩ :=
    exists_contMDiffAt_ker_mfderiv_eq_orbitTangent (I := I) (G := G) (I' := I') hx
  have hp_diff : MDifferentiableAt I' JQ p x := hp.contMDiffAt.mdifferentiableAt hm₀
  refine le_antisymm ?_ (orbitTangent_fundamental_le_ker_mfderiv hinv)
  obtain ⟨U, hU, hxU, s, hsx, hs, hps⟩ := hp.exists_contMDiffOn_section
  have hs_cont : ContinuousAt s (p x) := (hs.contMDiffAt (hU.mem_nhds hxU)).continuousAt
  have hsp : Tendsto (fun y ↦ (s (p y), y)) (𝓝 x) (𝓝 (x, x)) := by
    have hspx : Tendsto (s ∘ p) (𝓝 x) (𝓝 x) := by
      simpa only [comp_apply, hsx] using (hs_cont.comp hp.contMDiffAt.continuousAt).tendsto
    exact hspx.prodMk_nhds tendsto_id
  have heq : ((t ∘ s) ∘ p) =ᶠ[𝓝 x] t := by
    filter_upwards [hp.contMDiffAt.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU),
      hsp.eventually (ht_orb.and hfib)] with y hyU ⟨ht_eq, hfib_y⟩
    obtain ⟨g, hg⟩ := hfib_y (hps (p y) hyU)
    exact ht_eq (Quotient.sound (_root_.MulAction.orbitRel_apply.2
      (_root_.MulAction.mem_orbit_iff.2 ⟨g, hg⟩)))
  have hs_diff : MDifferentiableAt JQ I' s (p x) :=
    (hs.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt hm₀
  have ht_s_diff : MDifferentiableAt I' 𝓘(ℝ, QuotientModelSpace E E') t (s (p x)) := by
    simpa only [hsx] using ht_diff.mdifferentiableAt (by simp)
  have ht_congr := ((ht_s_diff.hasMFDerivAt.comp (p x) hs_diff.hasMFDerivAt).comp x
    hp_diff.hasMFDerivAt).congr_of_eventuallyEq heq.symm
  rw [← ht_ker, ht_congr.mfderiv]
  exact (LinearMap.ker_le_ker_comp _ _).trans (LinearMap.ker_le_ker_comp _ _)

/-- **The vertical directions of the orbit projection are the orbit directions.** The kernel of
the differential at `y` of the projection `M → M ⧸ G` is the orbit tangent space `𝔤 · y`. -/
theorem ker_mfderiv_quotientMk (y : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E')
      (Quotient.mk (_root_.MulAction.orbitRel G M)) y).ker =
      (InfinitesimalAction.fundamental I G I' M).orbitTangent y := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  exact ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt (I := I) (G := G)
    (IsCancelSMul.stabilizer_eq_bot y)
    ((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).isSubmersionAt y) (by simp)
    (Eventually.of_forall fun _ ↦ _root_.MulAction.orbitRel.Quotient.quotient_smul_eq)
    (Eventually.of_forall fun _ h ↦
      _root_.MulAction.mem_orbit_iff.1 (_root_.MulAction.orbitRel_apply.1 (Quotient.exact h)))

/-- **Smooth local sections are slices.** Let `s` be a smooth section of the orbit projection over
an open set `U` of `M ⧸ G`. Then the slice map `(g, q) ↦ g • s q` is a smooth local
diffeomorphism at every point of `G × U`: the range of `ds` is a complement of the orbit tangent
space `𝔤 · s q`, the kernel of the differential of the projection. -/
theorem isLocalDiffeomorphAt_smul_section {U : Set (_root_.MulAction.orbitRel.Quotient G M)}
    {s : _root_.MulAction.orbitRel.Quotient G M → M} (hU : IsOpen U)
    (hs : letI := orbitRelQuotientChartedSpace I G I' M
      ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ s U)
    (hsec : ∀ q ∈ U, Quotient.mk _ (s q) = q) {q : _root_.MulAction.orbitRel.Quotient G M}
    (hq : q ∈ U) (g : G) :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, QuotientModelSpace E E')) I' ∞
      (fun p : G × _root_.MulAction.orbitRel.Quotient G M ↦ p.1 • s p.2) (g, q) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  set J := 𝓘(ℝ, QuotientModelSpace E E')
  have hsd : MDifferentiableAt J I' s q :=
    (hs.contMDiffAt (hU.mem_nhds hq)).mdifferentiableAt (by simp)
  have hπd : MDifferentiableAt I' J (Quotient.mk (_root_.MulAction.orbitRel G M)) (s q) :=
    (contMDiff_quotientMk (I := I) (G := G) (I' := I') (M := M) (s q)).mdifferentiableAt
      (by simp)
  -- The differential of the projection is a left inverse of that of the section.
  have hcomp : (mfderiv I' J (Quotient.mk (_root_.MulAction.orbitRel G M)) (s q)).toLinearMap ∘ₗ
      (mfderiv J I' s q).toLinearMap = LinearMap.id := by
    have hev : Quotient.mk (_root_.MulAction.orbitRel G M) ∘ s =ᶠ[𝓝 q] id :=
      eventually_of_mem (hU.mem_nhds hq) hsec
    have h : mfderiv J J (Quotient.mk (_root_.MulAction.orbitRel G M) ∘ s) q = mfderiv J J id q :=
      hev.mfderiv_eq
    rw [mfderiv_id, mfderiv_comp q hπd hsd] at h
    exact LinearMap.ext fun v ↦ DFunLike.congr_fun h v
  have hbij : Bijective
      ((mfderiv I' J (Quotient.mk (_root_.MulAction.orbitRel G M)) (s q)).toLinearMap ∘ₗ
        (mfderiv J I' s q).toLinearMap) := by
    rw [hcomp]
    exact bijective_id
  obtain ⟨hinj, hcompl, -⟩ := LinearMap.bijective_comp_iff.1 hbij
  have hslice := (isLocalDiffeomorphAt_smul_slice_iff (I := I) (G := G) hs hU hq).2
    ⟨isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot
      (IsCancelSMul.stabilizer_eq_bot (s q)), hinj, by
        rw [← ker_mfderiv_quotientMk (I := I) (G := G) (s q)]
        exact hcompl.symm⟩
  exact hslice.eventually_forall_smul_slice.self_of_nhds g

/-- **The quotient manifold theorem for free proper Lie group actions (existential form).** Let a
finite-dimensional real Lie group `G` act smoothly, freely and properly on a finite-dimensional
boundaryless smooth real manifold `M`. Then `MulAction.orbitRel.Quotient G M`, with its quotient
topology, admits a smooth (`C^∞`) manifold structure modelled on `QuotientModelSpace E E'` for
which the orbit projection is a smooth submersion. No explicit separation or countability
hypotheses are needed, and `M` may be empty. -/
theorem exists_orbitRelQuotient_isSubmersion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [I'.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
    [MulAction G M] [ProperSMul G M]
    (hsm : ContMDiff (I.prod I') I' ∞ (fun gx : G × M ↦ gx.1 • gx.2))
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    ∃ cs : ChartedSpace (QuotientModelSpace E E') (_root_.MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, QuotientModelSpace E E') ∞ (_root_.MulAction.orbitRel.Quotient G M) ∧
      IsSubmersion I' 𝓘(ℝ, QuotientModelSpace E E') ∞
        (Quotient.mk (_root_.MulAction.orbitRel G M)) := by
  let _ : ContMDiffSMul I I' ∞ G M := ⟨hsm⟩
  let _ : IsCancelSMul G M := isCancelSMul_iff_eq_one_of_smul_eq.2 hfree
  exact ⟨orbitRelQuotientChartedSpace I G I' M, instIsManifoldOrbitRelQuotient,
    isSubmersion_quotientMk (I := I) (G := G)⟩

/-! ### Smooth descent, universal property and equivariant maps -/

section Descent

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  {m : ℕ∞ω}

/-- For a free proper smooth Lie group action and `m ≤ ∞`, the descent
`TauCeti.MulAction.orbitRelQuotientLift f hf` of a `G`-invariant map `f : M → N` is `C^m` at `[x]`
exactly when `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_iff (hm : m ≤ ∞) {f : M → N}
    {hf : ∀ (g : G) (x : M), f (g • x) = f x} {x : M} :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffAt 𝓘(ℝ, QuotientModelSpace E E') IN m
      (TauCeti.MulAction.orbitRelQuotientLift f hf)
      (Quotient.mk (_root_.MulAction.orbitRel G M) x) ↔
      ContMDiffAt I' IN m f x := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  rw [← (((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).isSubmersionAt
    x).contMDiffAt_comp_iff hm), TauCeti.MulAction.orbitRelQuotientLift_comp_mk]

/-- **Smooth descent to the orbit space.** For a free proper smooth Lie group action and `m ≤ ∞`,
the descent `TauCeti.MulAction.orbitRelQuotientLift f hf` of a `G`-invariant map `f : M → N` is
`C^m` on `M ⧸ G` exactly when `f` is `C^m` on `M`. -/
theorem contMDiff_orbitRelQuotientLift_iff (hm : m ≤ ∞) {f : M → N}
    {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiff 𝓘(ℝ, QuotientModelSpace E E') IN m
      (TauCeti.MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I' IN m f := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  rw [← ((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).contMDiff_comp_iff
    Quotient.mk_surjective hm), TauCeti.MulAction.orbitRelQuotientLift_comp_mk]

/-- **Universal property of the quotient manifold.** For a free proper smooth Lie group action,
every `G`-invariant `C^m` map (`m ≤ ∞`) `f : M → N` factors uniquely through
`Quotient.mk (MulAction.orbitRel G M)` as a `C^m` map on `M ⧸ G`. -/
theorem existsUnique_contMDiff_comp_quotientMk_eq (hm : m ≤ ∞) {f : M → N}
    (hf_diff : ContMDiff I' IN m f) (hf_inv : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    ∃! f' : _root_.MulAction.orbitRel.Quotient G M → N,
      ContMDiff 𝓘(ℝ, QuotientModelSpace E E') IN m f' ∧
        f' ∘ Quotient.mk (_root_.MulAction.orbitRel G M) = f := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  refine (isSubmersion_quotientMk (I := I) (G := G) (I' := I')
    (M := M)).existsUnique_contMDiff_comp_eq Quotient.mk_surjective hm hf_diff ?_
  rintro x y hxy
  obtain ⟨g, rfl⟩ := _root_.MulAction.orbitRel_apply.1 (Quotient.exact hxy)
  exact hf_inv g y

/-- **Commuting actions descend smoothly to the orbit manifold.** For a free proper smooth Lie
group action of `G` on `M` and `m ≤ ∞`, a `C^m` action of `L` on `M` commuting with that of `G`
induces a `C^m` action `l • [x] = [l • x]` on `M ⧸ G`
(`MulAction.orbitRel.Quotient.instSMulOfSMulCommClass`), for a manifold `L` with boundaryless
model. -/
theorem contMDiffSMul_orbitRelQuotient (hm : m ≤ ∞) {EL HL L : Type*} [NormedAddCommGroup EL]
    [NormedSpace ℝ EL] [TopologicalSpace HL] {IL : ModelWithCorners ℝ EL HL} [IL.Boundaryless]
    [TopologicalSpace L] [ChartedSpace HL L] [IsManifold IL ∞ L] [SMul L M]
    [SMulCommClass L G M] [ContMDiffSMul IL I' m L M] :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffSMul IL 𝓘(ℝ, QuotientModelSpace E E') m L
      (_root_.MulAction.orbitRel.Quotient G M) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  have hπ := isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)
  refine ⟨((IsSubmersion.id.prodMap hπ).contMDiff_comp_iff
    (surjective_id.prodMap Quotient.mk_surjective) hm).1 ?_⟩
  rw [_root_.MulAction.orbitRel.Quotient.smul_comp_prodMap_mk]
  exact (hπ.contMDiff.of_le hm).comp ContMDiffSMul.contMDiff_smul

/-- **Commuting actions by smooth maps descend to the orbit manifold.** For a free proper smooth Lie
group action of `G` on `M` and `m ≤ ∞`, an action of `L` on `M` by `C^m` maps commuting with that
of `G` induces an action `l • [x] = [l • x]` on `M ⧸ G` by `C^m` maps. No topology on `L` is
needed. -/
theorem contMDiffConstSMul_orbitRelQuotient (hm : m ≤ ∞) {L : Type*} [SMul L M]
    [SMulCommClass L G M] [ContMDiffConstSMul I' m L M] :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffConstSMul 𝓘(ℝ, QuotientModelSpace E E') m L
      (_root_.MulAction.orbitRel.Quotient G M) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  have hπ := isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)
  refine ⟨fun l ↦ (hπ.contMDiff_comp_iff Quotient.mk_surjective hm).1 ?_⟩
  rw [_root_.MulAction.orbitRel.Quotient.smul_comp_mk]
  exact (hπ.contMDiff.of_le hm).comp (contMDiff_const_smul l)

variable (I) in
/-- **Canonical `C^m` diffeomorphism with any `C^m` orbit submersion.** For a free proper smooth
Lie group action of `G` on a boundaryless manifold `M` and `m ≤ ∞`, if `p : M → Q` is a surjective
`C^m` submersion whose fibres are the `G`-orbits (`p x = p y ↔ ∃ g : G, g • y = x`), then `p`
descends to a `C^m` diffeomorphism `(M ⧸ G) ≃ₘ^m Q` sending `[x]` to `p x`. -/
def diffeomorphOfOrbitSubmersion
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hm : m ≤ ∞) (p : M → Q) (hp : IsSubmersion I' JQ m p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • y = x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    _root_.MulAction.orbitRel.Quotient G M ≃ₘ^m⟮𝓘(ℝ, QuotientModelSpace E E'), JQ⟯ Q :=
  letI := orbitRelQuotientChartedSpace I G I' M
  let e : _root_.MulAction.orbitRel.Quotient G M ≃ Q :=
    (Quotient.congrRight fun x y ↦
      (_root_.MulAction.orbitRel_apply.trans _root_.MulAction.mem_orbit_iff).trans
        (hfib x y).symm).trans
      (Setoid.quotientKerEquivOfSurjective p hp_surj)
  e.diffeomorphOfSubmersions
    ((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).of_le hm)
    Quotient.mk_surjective hp (funext fun _ ↦ rfl)

variable (I) in
/-- `diffeomorphOfOrbitSubmersion` sends the orbit `[x]` to `p x`. -/
@[simp]
theorem diffeomorphOfOrbitSubmersion_mk
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hm : m ≤ ∞) (p : M → Q) (hp : IsSubmersion I' JQ m p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • y = x) (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    diffeomorphOfOrbitSubmersion I hm p hp hp_surj hfib
      (Quotient.mk (_root_.MulAction.orbitRel G M) x) = p x := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  rw [diffeomorphOfOrbitSubmersion, Equiv.diffeomorphOfSubmersions_apply]
  -- Both `Quotient.congrRight` and `Setoid.quotientKerEquivOfSurjective` compute on `Quotient.mk`
  -- by `Quot.lift_beta`, so `(e ∘ Quotient.mk _) x` is definitionally `p x`.
  rfl

variable (I) in
/-- Composing `diffeomorphOfOrbitSubmersion` with the orbit projection recovers `p`. -/
@[simp]
theorem diffeomorphOfOrbitSubmersion_comp_mk
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hm : m ≤ ∞) (p : M → Q) (hp : IsSubmersion I' JQ m p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • y = x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    ⇑(diffeomorphOfOrbitSubmersion I hm p hp hp_surj hfib) ∘
      Quotient.mk (_root_.MulAction.orbitRel G M) = p := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  ext x
  exact diffeomorphOfOrbitSubmersion_mk I hm p hp hp_surj hfib x

variable (I) in
/-- The inverse of `diffeomorphOfOrbitSubmersion` sends `p x` back to `[x]`. -/
@[simp]
theorem diffeomorphOfOrbitSubmersion_symm_apply
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hm : m ≤ ∞) (p : M → Q) (hp : IsSubmersion I' JQ m p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • y = x) (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    (diffeomorphOfOrbitSubmersion I hm p hp hp_surj hfib).symm (p x) =
      Quotient.mk (_root_.MulAction.orbitRel G M) x := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  exact (diffeomorphOfOrbitSubmersion I hm p hp hp_surj hfib).symm_apply_eq.2
    (diffeomorphOfOrbitSubmersion_mk I hm p hp hp_surj hfib x).symm

section Equivariant

variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {G₂ : Type*} [TopologicalSpace G₂] [ChartedSpace H₂ G₂] [Group G₂] [LieGroup I₂ ∞ G₂]
  {E₂' : Type*} [NormedAddCommGroup E₂'] [NormedSpace ℝ E₂'] [FiniteDimensional ℝ E₂']
  {H₂' : Type*} [TopologicalSpace H₂'] {I₂' : ModelWithCorners ℝ E₂' H₂'} [I₂'.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂' M₂] [IsManifold I₂' ∞ M₂] [MulAction G₂ M₂]
  [ContMDiffSMul I₂ I₂' ∞ G₂ M₂] [ProperSMul G₂ M₂] [IsCancelSMul G₂ M₂]

/-- **Smoothness of equivariant maps on orbit spaces.** For `m ≤ ∞`, a `C^m` map `φ : M →ₑ[σ] M₂`
between two free proper smooth Lie group actions descends to a `C^m` map `M ⧸ G → M₂ ⧸ G₂`. -/
theorem contMDiff_orbitRelQuotientMap (hm : m ≤ ∞) {σ : G → G₂} {φ : M →ₑ[σ] M₂}
    (hφ : ContMDiff I' I₂' m φ) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    ContMDiff 𝓘(ℝ, QuotientModelSpace E E') 𝓘(ℝ, QuotientModelSpace E₂ E₂') m
      (MulActionHom.orbitRelQuotientMap φ) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
  rw [← (isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_quotientMk (I := I₂) (G := G₂) (I' := I₂') (M := M₂)).of_le hm).comp hφ

variable (I I₂) in
/-- **An equivariant `C^m` diffeomorphism induces a `C^m` diffeomorphism of orbit manifolds.**
For `m ≤ ∞`, if `e : M ≃ₘ^m⟮I', I₂'⟯ M₂` intertwines two free proper smooth Lie group actions
along a group isomorphism `φ : G ≃* G₂`, then
`TauCeti.MulAction.orbitRelQuotientCongr φ e.toEquiv he` is a `C^m` diffeomorphism
`(M ⧸ G) ≃ₘ^m (M₂ ⧸ G₂)`. No smoothness assumption on `φ` is needed. -/
def orbitRelQuotientDiffeomorph (hm : m ≤ ∞) (φ : G ≃* G₂) (e : M ≃ₘ^m⟮I', I₂'⟯ M₂)
    (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    _root_.MulAction.orbitRel.Quotient G M ≃ₘ^m⟮𝓘(ℝ, QuotientModelSpace E E'),
      𝓘(ℝ, QuotientModelSpace E₂ E₂')⟯ _root_.MulAction.orbitRel.Quotient G₂ M₂ :=
  letI := orbitRelQuotientChartedSpace I G I' M
  letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
  { toEquiv := TauCeti.MulAction.orbitRelQuotientCongr φ e.toEquiv he
    contMDiff_toFun :=
      ((isSubmersion_quotientMk (I := I) (G := G)).contMDiff_comp_iff
        Quotient.mk_surjective hm).1 <|
        (((contMDiff_quotientMk (I := I₂) (G := G₂)).of_le hm).comp e.contMDiff).congr fun x ↦
          TauCeti.MulAction.orbitRelQuotientCongr_mk φ e.toEquiv he x
    contMDiff_invFun :=
      ((isSubmersion_quotientMk (I := I₂) (G := G₂)).contMDiff_comp_iff
        Quotient.mk_surjective hm).1 <|
        (((contMDiff_quotientMk (I := I) (G := G)).of_le hm).comp e.symm.contMDiff).congr fun y ↦
          TauCeti.MulAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y }

variable (I I₂) in
/-- The underlying equivalence of `orbitRelQuotientDiffeomorph` is
`TauCeti.MulAction.orbitRelQuotientCongr`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_toEquiv (hm : m ≤ ∞) (φ : G ≃* G₂)
    (e : M ≃ₘ^m⟮I', I₂'⟯ M₂) (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    (orbitRelQuotientDiffeomorph I I₂ hm φ e he).toEquiv =
      TauCeti.MulAction.orbitRelQuotientCongr φ e.toEquiv he :=
  (rfl)

variable (I I₂) in
/-- `orbitRelQuotientDiffeomorph` sends `[x]` to `[e x]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_mk (hm : m ≤ ∞) (φ : G ≃* G₂)
    (e : M ≃ₘ^m⟮I', I₂'⟯ M₂) (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    orbitRelQuotientDiffeomorph I I₂ hm φ e he
      (Quotient.mk (_root_.MulAction.orbitRel G M) x) =
      Quotient.mk (_root_.MulAction.orbitRel G₂ M₂) (e x) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
  exact TauCeti.MulAction.orbitRelQuotientCongr_mk φ e.toEquiv he x

variable (I I₂) in
/-- The inverse of `orbitRelQuotientDiffeomorph` sends `[y]` to `[e.symm y]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_symm_mk (hm : m ≤ ∞) (φ : G ≃* G₂)
    (e : M ≃ₘ^m⟮I', I₂'⟯ M₂) (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) (y : M₂) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    (orbitRelQuotientDiffeomorph I I₂ hm φ e he).symm
      (Quotient.mk (_root_.MulAction.orbitRel G₂ M₂) y) =
      Quotient.mk (_root_.MulAction.orbitRel G M) (e.symm y) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
  exact TauCeti.MulAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y

end Equivariant

end Descent

end ProperSMul

/-! ### Additive Lie group actions -/

namespace ProperVAdd

open ProperSMul (QuotientModelSpace)

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [AddGroup G] [LieAddGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [AddAction G M]
  [ContMDiffVAdd I I' ∞ G M] [ProperVAdd G M] [IsCancelVAdd G M]

variable (I G I' M) in
/-- **The transverse-slice atlas on `AddAction.orbitRel.Quotient G M`.** Pulled back from
`ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M` along
`TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative`, for a free proper smooth action of an
additive Lie group `G` (such as a torus `(ℝ / 2πℤ)^k` or a closed Lie subgroup thereof). -/
@[instance_reducible]
def orbitRelQuotientChartedSpace :
    ChartedSpace (QuotientModelSpace E E') (_root_.AddAction.orbitRel.Quotient G M) :=
  letI := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
  (TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative
    (G := G) (X := M)).pullbackChartedSpace

/-- **The additive quotient manifold theorem.** Equipped with
`ProperVAdd.orbitRelQuotientChartedSpace`, `AddAction.orbitRel.Quotient G M` is a smooth manifold.
-/
instance instIsManifoldOrbitRelQuotient :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsManifold 𝓘(ℝ, QuotientModelSpace E E') ∞ (_root_.AddAction.orbitRel.Quotient G M) := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
  exact (TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative
    (G := G) (X := M)).pullback_isManifold _ ∞

variable (I G I' M) in
/-- **Canonical `C^m` diffeomorphism between the additive orbit manifold and its `Multiplicative`
counterpart.** -/
def orbitRelQuotientDiffeomorphMultiplicative (m : ℕ∞ω) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
    _root_.AddAction.orbitRel.Quotient G M ≃ₘ^m⟮𝓘(ℝ, QuotientModelSpace E E'),
      𝓘(ℝ, QuotientModelSpace E E')⟯ _root_.MulAction.orbitRel.Quotient (Multiplicative G) M :=
  letI := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
  (TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative
    (G := G) (X := M)).pullbackDiffeomorph 𝓘(ℝ, QuotientModelSpace E E') m

variable (I G I' M) in
/-- The underlying homeomorphism of `orbitRelQuotientDiffeomorphMultiplicative` is
`TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphMultiplicative_toHomeomorph (m : ℕ∞ω) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
    (orbitRelQuotientDiffeomorphMultiplicative I G I' M m).toHomeomorph =
      TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative (G := G) (X := M) := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
  exact (TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative
    (G := G) (X := M)).pullbackDiffeomorph_toHomeomorph _ m

variable (I G I' M) in
/-- The underlying equivalence of `orbitRelQuotientDiffeomorphMultiplicative` is
`TauCeti.AddAction.orbitRelQuotientEquivMultiplicative`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphMultiplicative_toEquiv (m : ℕ∞ω) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
    (orbitRelQuotientDiffeomorphMultiplicative I G I' M m).toEquiv =
      TauCeti.AddAction.orbitRelQuotientEquivMultiplicative := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
  rw [← Diffeomorph.toHomeomorph_toEquiv,
    orbitRelQuotientDiffeomorphMultiplicative_toHomeomorph,
    TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative_toEquiv]

variable (I G I' M) in
/-- `orbitRelQuotientDiffeomorphMultiplicative` sends the additive orbit `[x]` to the
`Multiplicative G`-orbit `[x]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphMultiplicative_mk (m : ℕ∞ω) (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
    orbitRelQuotientDiffeomorphMultiplicative I G I' M m
      (Quotient.mk (_root_.AddAction.orbitRel G M) x) =
      Quotient.mk (_root_.MulAction.orbitRel (Multiplicative G) M) x := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
  rw [orbitRelQuotientDiffeomorphMultiplicative, Homeomorph.coe_pullbackDiffeomorph,
    TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative_mk]

variable (I G I' M) in
/-- The inverse of `orbitRelQuotientDiffeomorphMultiplicative` sends the `Multiplicative G`-orbit
`[x]` to the additive orbit `[x]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphMultiplicative_symm_mk (m : ℕ∞ω) (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
    (orbitRelQuotientDiffeomorphMultiplicative I G I' M m).symm
      (Quotient.mk (_root_.MulAction.orbitRel (Multiplicative G) M) x) =
      Quotient.mk (_root_.AddAction.orbitRel G M) x := by
  let _ := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
  rw [orbitRelQuotientDiffeomorphMultiplicative, Homeomorph.coe_pullbackDiffeomorph_symm,
    TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative_symm_mk]

/-- The additive orbit projection `M → AddAction.orbitRel.Quotient G M` is a smooth submersion with
fibre complement `E`. -/
theorem isSubmersionOfComplement_quotientMk :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsSubmersionOfComplement E I' 𝓘(ℝ, QuotientModelSpace E E') ∞
      (Quotient.mk (_root_.AddAction.orbitRel G M)) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
  let Φ := (orbitRelQuotientDiffeomorphMultiplicative I G I' M ∞).symm
  have hcomp : ⇑Φ ∘ Quotient.mk (_root_.MulAction.orbitRel (Multiplicative G) M) =
      Quotient.mk (_root_.AddAction.orbitRel G M) := by
    ext y
    simp [Φ]
  rw [← hcomp]
  exact isSubmersionOfComplement_iff.2 fun x ↦
    (Φ.isLocalDiffeomorph _).comp_isSubmersionAtOfComplement
      ((ProperSMul.isSubmersionOfComplement_quotientMk
        (I := I) (G := Multiplicative G) (I' := I') (M := M)).isSubmersionAt x)

/-- The additive orbit projection `M → AddAction.orbitRel.Quotient G M` is a smooth submersion. -/
theorem isSubmersion_quotientMk :
    letI := orbitRelQuotientChartedSpace I G I' M
    IsSubmersion I' 𝓘(ℝ, QuotientModelSpace E E') ∞
      (Quotient.mk (_root_.AddAction.orbitRel G M)) :=
  letI := orbitRelQuotientChartedSpace I G I' M
  (isSubmersionOfComplement_quotientMk (I := I) (G := G) (I' := I') (M := M)).isSubmersion

/-- The additive orbit projection `M → AddAction.orbitRel.Quotient G M` is smooth. -/
theorem contMDiff_quotientMk :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiff I' 𝓘(ℝ, QuotientModelSpace E E') ∞
      (Quotient.mk (_root_.AddAction.orbitRel G M)) :=
  letI := orbitRelQuotientChartedSpace I G I' M
  (isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).contMDiff

/-- At every `y : M`, the differential of the additive orbit projection is surjective. -/
theorem surjective_mfderiv_quotientMk (y : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    Surjective (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E')
      (Quotient.mk (_root_.AddAction.orbitRel G M)) y) :=
  letI := orbitRelQuotientChartedSpace I G I' M
  ((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).isSubmersionAt
    y).surjective_mfderiv (by simp)

/-- Over an open neighbourhood of `[y]` in `AddAction.orbitRel.Quotient G M`, the additive orbit
projection admits a smooth local section sending `[y]` to `y`. -/
theorem exists_contMDiffOn_section_quotientMk (y : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    ∃ U : Set (_root_.AddAction.orbitRel.Quotient G M),
      IsOpen U ∧ Quotient.mk (_root_.AddAction.orbitRel G M) y ∈ U ∧
      ∃ s : _root_.AddAction.orbitRel.Quotient G M → M,
        s (Quotient.mk (_root_.AddAction.orbitRel G M) y) = y ∧
        ContMDiffOn 𝓘(ℝ, QuotientModelSpace E E') I' ∞ s U ∧
        ∀ q ∈ U, Quotient.mk (_root_.AddAction.orbitRel G M) (s q) = q :=
  letI := orbitRelQuotientChartedSpace I G I' M
  ((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).isSubmersionAt
    y).exists_contMDiffOn_section

omit [IsCancelVAdd G M] in
/-- For a proper smooth action of a finite-dimensional additive real Lie group `G` on a
boundaryless manifold `M` and a point `x : M` with trivial stabilizer (no global freeness needed),
if `p : M → Q` is a `C^m` (`m ≠ 0`) submersion at `x` that is locally invariant along the additive
orbit of `x` and whose fibres near `(x, x)` lie in single additive `G`-orbits, then `ker dp_x` is
the orbit tangent space of `Multiplicative G` at `x`. -/
theorem ker_mfderiv_eq_orbitTangent_fundamental_multiplicative_of_isSubmersionAt
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    {m : ℕ∞ω} {p : M → Q} {x : M} (hx : _root_.AddAction.stabilizer G x = ⊥)
    (hp : IsSubmersionAt I' JQ m p x) (hm₀ : m ≠ 0)
    (hinv : ∀ᶠ g in 𝓝 (0 : G), p (g +ᵥ x) = p x)
    (hfib : ∀ᶠ yz : M × M in 𝓝 (x, x), p yz.1 = p yz.2 → ∃ g : G, g +ᵥ yz.2 = yz.1) :
    (mfderiv I' JQ p x).ker =
      (InfinitesimalAction.fundamental I (Multiplicative G) I' M).orbitTangent x :=
  ProperSMul.ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt
    (I := I) (G := Multiplicative G) (by simp [hx]) hp hm₀
    ((continuous_toAdd.tendsto (1 : Multiplicative G)).eventually hinv)
    (hfib.mono fun _ hyz h ↦ Multiplicative.ofAdd.exists_congr_left.1 (hyz h))

/-- At every `y : M`, the kernel of the differential of the additive orbit projection is the orbit
tangent space of `Multiplicative G` at `y`. -/
theorem ker_mfderiv_quotientMk (y : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    (mfderiv I' 𝓘(ℝ, QuotientModelSpace E E')
      (Quotient.mk (_root_.AddAction.orbitRel G M)) y).ker =
      (InfinitesimalAction.fundamental I (Multiplicative G) I' M).orbitTangent y := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  exact ker_mfderiv_eq_orbitTangent_fundamental_multiplicative_of_isSubmersionAt (I := I) (G := G)
    (IsCancelVAdd.stabilizer_eq_bot y)
    ((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).isSubmersionAt y) (by simp)
    (Eventually.of_forall fun _ ↦ _root_.AddAction.orbitRel.Quotient.quotient_vadd_eq)
    (Eventually.of_forall fun _ h ↦
      _root_.AddAction.mem_orbit_iff.1 (_root_.AddAction.orbitRel_apply.1 (Quotient.exact h)))

/-- **The additive quotient manifold theorem (existential form).** Let a finite-dimensional
additive real Lie group `G` act smoothly, freely and properly on a finite-dimensional boundaryless
smooth real manifold `M`. Then `AddAction.orbitRel.Quotient G M`, with its quotient topology,
admits a smooth (`C^∞`) manifold structure modelled on `QuotientModelSpace E E'` for which the
orbit projection is a smooth submersion. No explicit separation or countability hypotheses are
needed, and `M` may be empty. -/
theorem exists_orbitRelQuotient_isSubmersion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [AddGroup G] [LieAddGroup I ∞ G]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [I'.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
    [AddAction G M] [ProperVAdd G M]
    (hvadd : ContMDiff (I.prod I') I' ∞ (fun gx : G × M ↦ gx.1 +ᵥ gx.2))
    (hfree : ∀ (g : G) (x : M), g +ᵥ x = x → g = 0) :
    ∃ cs : ChartedSpace (QuotientModelSpace E E') (_root_.AddAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, QuotientModelSpace E E') ∞ (_root_.AddAction.orbitRel.Quotient G M) ∧
      IsSubmersion I' 𝓘(ℝ, QuotientModelSpace E E') ∞
        (Quotient.mk (_root_.AddAction.orbitRel G M)) := by
  let _ : ContMDiffVAdd I I' ∞ G M := ⟨hvadd⟩
  let _ : IsCancelVAdd G M := isCancelVAdd_iff_eq_zero_of_vadd_eq.2 hfree
  exact ⟨orbitRelQuotientChartedSpace I G I' M, instIsManifoldOrbitRelQuotient,
    isSubmersion_quotientMk (I := I) (G := G)⟩

section Descent

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  {m : ℕ∞ω}

/-- Pointwise smooth descent (`m ≤ ∞`) for a `G`-invariant map out of a free proper smooth additive
Lie group action. -/
theorem contMDiffAt_orbitRelQuotientLift_iff (hm : m ≤ ∞) {f : M → N}
    {hf : ∀ (g : G) (x : M), f (g +ᵥ x) = f x} {x : M} :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffAt 𝓘(ℝ, QuotientModelSpace E E') IN m
      (TauCeti.AddAction.orbitRelQuotientLift f hf)
      (Quotient.mk (_root_.AddAction.orbitRel G M) x) ↔
      ContMDiffAt I' IN m f x := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  rw [← (((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).isSubmersionAt
    x).contMDiffAt_comp_iff hm), TauCeti.AddAction.orbitRelQuotientLift_comp_mk]

/-- Smooth descent (`m ≤ ∞`) for a `G`-invariant map out of a free proper smooth additive Lie group
action. -/
theorem contMDiff_orbitRelQuotientLift_iff (hm : m ≤ ∞) {f : M → N}
    {hf : ∀ (g : G) (x : M), f (g +ᵥ x) = f x} :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiff 𝓘(ℝ, QuotientModelSpace E E') IN m
      (TauCeti.AddAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I' IN m f := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  rw [← ((isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).contMDiff_comp_iff
    Quotient.mk_surjective hm), TauCeti.AddAction.orbitRelQuotientLift_comp_mk]

/-- Universal property of the additive quotient manifold (`m ≤ ∞`). -/
theorem existsUnique_contMDiff_comp_quotientMk_eq (hm : m ≤ ∞) {f : M → N}
    (hf_diff : ContMDiff I' IN m f) (hf_inv : ∀ (g : G) (x : M), f (g +ᵥ x) = f x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    ∃! f' : _root_.AddAction.orbitRel.Quotient G M → N,
      ContMDiff 𝓘(ℝ, QuotientModelSpace E E') IN m f' ∧
        f' ∘ Quotient.mk (_root_.AddAction.orbitRel G M) = f := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  refine (isSubmersion_quotientMk (I := I) (G := G) (I' := I')
    (M := M)).existsUnique_contMDiff_comp_eq Quotient.mk_surjective hm hf_diff ?_
  rintro x y hxy
  obtain ⟨g, rfl⟩ := _root_.AddAction.orbitRel_apply.1 (Quotient.exact hxy)
  exact hf_inv g y

/-- For a free proper smooth additive Lie group action of `G` on `M` and `m ≤ ∞`, a `C^m` additive
action of `L` on `M` commuting with that of `G` induces a `C^m` additive action
`l +ᵥ [x] = [l +ᵥ x]` on `M ⧸ G`, for a manifold `L` with boundaryless model. -/
theorem contMDiffVAdd_orbitRelQuotient (hm : m ≤ ∞) {EL HL L : Type*} [NormedAddCommGroup EL]
    [NormedSpace ℝ EL] [TopologicalSpace HL] {IL : ModelWithCorners ℝ EL HL} [IL.Boundaryless]
    [TopologicalSpace L] [ChartedSpace HL L] [IsManifold IL ∞ L] [VAdd L M]
    [VAddCommClass L G M] [ContMDiffVAdd IL I' m L M] :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffVAdd IL 𝓘(ℝ, QuotientModelSpace E E') m L
      (_root_.AddAction.orbitRel.Quotient G M) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  have hπ := isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)
  refine ⟨((IsSubmersion.id.prodMap hπ).contMDiff_comp_iff
    (surjective_id.prodMap Quotient.mk_surjective) hm).1 ?_⟩
  rw [_root_.AddAction.orbitRel.Quotient.vadd_comp_prodMap_mk]
  exact (hπ.contMDiff.of_le hm).comp ContMDiffVAdd.contMDiff_vadd

/-- For a free proper smooth additive Lie group action of `G` on `M` and `m ≤ ∞`, an additive
action of `L` on `M` by `C^m` maps commuting with that of `G` induces an additive action
`l +ᵥ [x] = [l +ᵥ x]` on `M ⧸ G` by `C^m` maps. No topology on `L` is needed. -/
theorem contMDiffConstVAdd_orbitRelQuotient (hm : m ≤ ∞) {L : Type*} [VAdd L M]
    [VAddCommClass L G M] [ContMDiffConstVAdd I' m L M] :
    letI := orbitRelQuotientChartedSpace I G I' M
    ContMDiffConstVAdd 𝓘(ℝ, QuotientModelSpace E E') m L
      (_root_.AddAction.orbitRel.Quotient G M) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  have hπ := isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)
  refine ⟨fun l ↦ (hπ.contMDiff_comp_iff Quotient.mk_surjective hm).1 ?_⟩
  rw [_root_.AddAction.orbitRel.Quotient.vadd_comp_mk]
  exact (hπ.contMDiff.of_le hm).comp (contMDiff_const_vadd l)

variable (I) in
/-- For a free proper smooth action of an additive Lie group `G` on a boundaryless manifold `M` and
`m ≤ ∞`, the canonical `C^m` diffeomorphism between `AddAction.orbitRel.Quotient G M` and the
target of any surjective `C^m` submersion `p : M → Q` whose fibres are the additive `G`-orbits. -/
def diffeomorphOfOrbitSubmersion
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hm : m ≤ ∞) (p : M → Q) (hp : IsSubmersion I' JQ m p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g +ᵥ y = x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    _root_.AddAction.orbitRel.Quotient G M ≃ₘ^m⟮𝓘(ℝ, QuotientModelSpace E E'), JQ⟯ Q :=
  letI := orbitRelQuotientChartedSpace I G I' M
  letI := ProperSMul.orbitRelQuotientChartedSpace I (Multiplicative G) I' M
  (orbitRelQuotientDiffeomorphMultiplicative I G I' M m).trans
    (ProperSMul.diffeomorphOfOrbitSubmersion I (G := Multiplicative G) hm p hp hp_surj
      fun x y ↦ (hfib x y).trans Multiplicative.ofAdd.exists_congr_left)

variable (I) in
/-- `diffeomorphOfOrbitSubmersion` sends the additive orbit `[x]` to `p x`. -/
@[simp]
theorem diffeomorphOfOrbitSubmersion_mk
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hm : m ≤ ∞) (p : M → Q) (hp : IsSubmersion I' JQ m p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g +ᵥ y = x) (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    diffeomorphOfOrbitSubmersion I hm p hp hp_surj hfib
      (Quotient.mk (_root_.AddAction.orbitRel G M) x) = p x := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  simp [diffeomorphOfOrbitSubmersion]

variable (I) in
/-- Composing `diffeomorphOfOrbitSubmersion` with the additive orbit projection recovers `p`. -/
@[simp]
theorem diffeomorphOfOrbitSubmersion_comp_mk
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hm : m ≤ ∞) (p : M → Q) (hp : IsSubmersion I' JQ m p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g +ᵥ y = x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    ⇑(diffeomorphOfOrbitSubmersion I hm p hp hp_surj hfib) ∘
      Quotient.mk (_root_.AddAction.orbitRel G M) = p := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  ext x
  exact diffeomorphOfOrbitSubmersion_mk I hm p hp hp_surj hfib x

variable (I) in
/-- The inverse of `diffeomorphOfOrbitSubmersion` sends `p x` back to `[x]`. -/
@[simp]
theorem diffeomorphOfOrbitSubmersion_symm_apply
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hm : m ≤ ∞) (p : M → Q) (hp : IsSubmersion I' JQ m p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g +ᵥ y = x) (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    (diffeomorphOfOrbitSubmersion I hm p hp hp_surj hfib).symm (p x) =
      Quotient.mk (_root_.AddAction.orbitRel G M) x := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  exact (diffeomorphOfOrbitSubmersion I hm p hp hp_surj hfib).symm_apply_eq.2
    (diffeomorphOfOrbitSubmersion_mk I hm p hp hp_surj hfib x).symm

section Equivariant

variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {G₂ : Type*} [TopologicalSpace G₂] [ChartedSpace H₂ G₂] [AddGroup G₂] [LieAddGroup I₂ ∞ G₂]
  {E₂' : Type*} [NormedAddCommGroup E₂'] [NormedSpace ℝ E₂'] [FiniteDimensional ℝ E₂']
  {H₂' : Type*} [TopologicalSpace H₂'] {I₂' : ModelWithCorners ℝ E₂' H₂'} [I₂'.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂' M₂] [IsManifold I₂' ∞ M₂] [AddAction G₂ M₂]
  [ContMDiffVAdd I₂ I₂' ∞ G₂ M₂] [ProperVAdd G₂ M₂] [IsCancelVAdd G₂ M₂]

/-- **Smoothness of equivariant maps on additive orbit spaces.** For `m ≤ ∞`, a `C^m` equivariant
map `φ : AddActionHom σ M M₂` between two free proper smooth additive Lie group actions descends to
a `C^m` map of additive orbit spaces. -/
theorem contMDiff_orbitRelQuotientMap (hm : m ≤ ∞) {σ : G → G₂} {φ : AddActionHom σ M M₂}
    (hφ : ContMDiff I' I₂' m φ) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    ContMDiff 𝓘(ℝ, QuotientModelSpace E E') 𝓘(ℝ, QuotientModelSpace E₂ E₂') m
      (AddActionHom.orbitRelQuotientMap φ) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
  rw [← (isSubmersion_quotientMk (I := I) (G := G) (I' := I') (M := M)).contMDiff_comp_iff
    Quotient.mk_surjective hm, AddActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_quotientMk (I := I₂) (G := G₂) (I' := I₂') (M := M₂)).of_le hm).comp hφ

variable (I I₂) in
/-- **An equivariant `C^m` diffeomorphism induces a `C^m` diffeomorphism of additive orbit
manifolds.** For `m ≤ ∞`, if `e : M ≃ₘ^m⟮I', I₂'⟯ M₂` intertwines two free proper smooth additive
Lie group actions along an additive group isomorphism `φ : G ≃+ G₂`, then
`TauCeti.AddAction.orbitRelQuotientCongr φ e.toEquiv he` is a `C^m` diffeomorphism of additive
orbit spaces. No smoothness assumption on `φ` is needed. -/
def orbitRelQuotientDiffeomorph (hm : m ≤ ∞) (φ : G ≃+ G₂) (e : M ≃ₘ^m⟮I', I₂'⟯ M₂)
    (he : ∀ (g : G) (x : M), e (g +ᵥ x) = φ g +ᵥ e x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    _root_.AddAction.orbitRel.Quotient G M ≃ₘ^m⟮𝓘(ℝ, QuotientModelSpace E E'),
      𝓘(ℝ, QuotientModelSpace E₂ E₂')⟯ _root_.AddAction.orbitRel.Quotient G₂ M₂ :=
  letI := orbitRelQuotientChartedSpace I G I' M
  letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
  { toEquiv := TauCeti.AddAction.orbitRelQuotientCongr φ e.toEquiv he
    contMDiff_toFun :=
      ((isSubmersion_quotientMk (I := I) (G := G)).contMDiff_comp_iff
        Quotient.mk_surjective hm).1 <|
        (((contMDiff_quotientMk (I := I₂) (G := G₂)).of_le hm).comp e.contMDiff).congr fun x ↦
          TauCeti.AddAction.orbitRelQuotientCongr_mk φ e.toEquiv he x
    contMDiff_invFun :=
      ((isSubmersion_quotientMk (I := I₂) (G := G₂)).contMDiff_comp_iff
        Quotient.mk_surjective hm).1 <|
        (((contMDiff_quotientMk (I := I) (G := G)).of_le hm).comp e.symm.contMDiff).congr fun y ↦
          TauCeti.AddAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y }

variable (I I₂) in
/-- The underlying equivalence of `orbitRelQuotientDiffeomorph` is
`TauCeti.AddAction.orbitRelQuotientCongr`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_toEquiv (hm : m ≤ ∞) (φ : G ≃+ G₂)
    (e : M ≃ₘ^m⟮I', I₂'⟯ M₂) (he : ∀ (g : G) (x : M), e (g +ᵥ x) = φ g +ᵥ e x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    (orbitRelQuotientDiffeomorph I I₂ hm φ e he).toEquiv =
      TauCeti.AddAction.orbitRelQuotientCongr φ e.toEquiv he :=
  (rfl)

variable (I I₂) in
/-- `orbitRelQuotientDiffeomorph` sends `[x]` to `[e x]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_mk (hm : m ≤ ∞) (φ : G ≃+ G₂)
    (e : M ≃ₘ^m⟮I', I₂'⟯ M₂) (he : ∀ (g : G) (x : M), e (g +ᵥ x) = φ g +ᵥ e x) (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    orbitRelQuotientDiffeomorph I I₂ hm φ e he
      (Quotient.mk (_root_.AddAction.orbitRel G M) x) =
      Quotient.mk (_root_.AddAction.orbitRel G₂ M₂) (e x) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
  exact TauCeti.AddAction.orbitRelQuotientCongr_mk φ e.toEquiv he x

variable (I I₂) in
/-- The inverse of `orbitRelQuotientDiffeomorph` sends `[y]` to `[e.symm y]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorph_symm_mk (hm : m ≤ ∞) (φ : G ≃+ G₂)
    (e : M ≃ₘ^m⟮I', I₂'⟯ M₂) (he : ∀ (g : G) (x : M), e (g +ᵥ x) = φ g +ᵥ e x) (y : M₂) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
    (orbitRelQuotientDiffeomorph I I₂ hm φ e he).symm
      (Quotient.mk (_root_.AddAction.orbitRel G₂ M₂) y) =
      Quotient.mk (_root_.AddAction.orbitRel G M) (e.symm y) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelQuotientChartedSpace I₂ G₂ I₂' M₂
  exact TauCeti.AddAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y

end Equivariant

end Descent

end ProperVAdd
