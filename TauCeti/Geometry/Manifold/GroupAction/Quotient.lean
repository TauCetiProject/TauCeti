/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Lie.FundamentalVectorField

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Lie.Basic
import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.Orbit
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# Quotient manifolds of free proper Lie group actions

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on a
finite-dimensional boundaryless smooth real manifold `M`. This file proves the **quotient manifold
theorem**: the orbit space `MulAction.orbitRel.Quotient G M`, with its quotient topology, carries a
unique smooth manifold structure of dimension `dim M - dim G` for which the orbit projection
`M → M ⧸ G` is a smooth submersion.

## Construction

At any point `x ∈ M` with trivial stabilizer, the isotropy algebra `𝔤_x` vanishes
(`TauCeti.Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot`), so choosing a complement `W` of the
orbit tangent space `𝔤 · x` in `T_x M` gives a transverse chart slice
`σ : (Fin (dim M - dim G) → ℝ) → M` with `σ 0 = x` whose slice map `(g, u) ↦ g • σ u` is a
smooth local diffeomorphism at `(1, 0)` (`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`).
Equivariance extends local diffeomorphy to `G × U` for a small neighbourhood `U` of `0`
(`IsLocalDiffeomorphAt.eventually_forall_smul_slice`), and properness upgrades local injectivity at
`(1, 0)` to global injectivity on `G × U` (`ProperSMul.exists_mem_nhds_injOn_smul_slice`). This
produces a slice chart at every free point (`TauCeti.exists_slice_of_stabilizer_eq_bot`).

For a globally free proper action (`[IsCancelSMul G M]`), the slice maps descend to open embeddings
`u ↦ [σ_x u]` into `M ⧸ G` (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`) with smooth
overlap transitions (`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`). Gluing these open pieces
via `TauCeti.chartedSpaceOfIsOpenEmbedding` yields the named atlas
`TauCeti.freeProperQuotientChartedSpace` (deliberately not a global instance, to avoid conflicting
with Mathlib's `MulAction.instChartedSpaceQuotient` for discrete actions) and its `IsManifold`
structure (`TauCeti.isManifold_freeProperQuotient`).

Near any `x ∈ M`, the orbit projection reads through the local inverse of the slice map at
`(1, 0)` as the second projection followed by the slice chart embedding, so it is smooth with
surjective differential and therefore a smooth submersion with complement `E`, the model space of
`G` (`TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`). Dimension counting
identifies the kernel of its differential at `x` with the orbit tangent space `𝔤 · x`
(`TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`). Uniqueness of the smooth structure
(`TauCeti.maximalAtlas_freeProperQuotient_eq`) and smooth descent of invariant and equivariant maps
follow from the general theory of surjective submersions. Neither manifold needs separate Hausdorff
or second-countability assumptions (both `T2Space G` and `T2Space M` are derived from `LieGroup` and
`ProperSMul`, and Mathlib already supplies `T2Space` and `SecondCountableTopology` on the orbit
space when applicable), and `M` may be empty.

## Main results

* `TauCeti.exists_slice_of_stabilizer_eq_bot`: existence of an injective smooth transverse slice at
  any free point of a proper smooth Lie group action.
* `TauCeti.freeProperQuotientChartedSpace`: named, non-instance `ChartedSpace` on
  `MulAction.orbitRel.Quotient G M` modelled on `Fin (dim M - dim G) → ℝ`.
* `TauCeti.isManifold_freeProperQuotient`: the quotient is a smooth manifold.
* `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient` and
  `TauCeti.isSubmersion_quotientMk_freeProperQuotient`: the orbit projection is a smooth submersion
  with complement `E`.
* `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`: the kernel of the differential of the orbit
  projection at `x` is the orbit tangent space `𝔤 · x`.
* `TauCeti.maximalAtlas_freeProperQuotient_eq`: uniqueness of the maximal atlas making the orbit
  projection a smooth submersion.
* `TauCeti.contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`, and
  `TauCeti.isSubmersion_orbitRelQuotientMap_freeProperQuotient`: smooth descent of invariant maps
  and of equivariant maps and submersions.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: existential form of the quotient manifold
  theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 21.10
  (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21.
-/

public section

noncomputable section

open Function Module Set Filter Manifold Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### Transverse slices at free points -/

section Slice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ProperSMul G M] [ContMDiffSMul I I' ∞ G M]

/-- At a free point of a proper smooth action of a finite-dimensional real Lie group, the isotropy
algebra vanishes. -/
private theorem isotropy_eq_bot_of_stabilizer_eq_bot {x : M}
    (hx : MulAction.stabilizer G x = ⊥) :
    (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have : Subsingleton (MulAction.stabilizer G x) := by
    rw [hx]
    infer_instance
  exact (Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := I) (I' := I')).1 inferInstance

/-- At a free point of a proper smooth action of a finite-dimensional real Lie group, the orbit
tangent space has dimension `dim G`. -/
private theorem finrank_orbitTangent_of_stabilizer_eq_bot {x : M}
    (hx : MulAction.stabilizer G x = ⊥) :
    finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) = finrank ℝ E := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  have hsum := InfinitesimalAction.finrank_orbitTangent_add_finrank_isotropy
    (InfinitesimalAction.fundamental I G I' M) x
  have hbot : finrank ℝ ((InfinitesimalAction.fundamental I G I' M).isotropy x) = 0 := by
    rw [isotropy_eq_bot_of_stabilizer_eq_bot hx]
    have : Subsingleton (⊥ : LieSubalgebra ℝ (GroupLieAlgebra I G)) :=
      ⟨fun a b ↦ Subtype.ext
        (((LieSubalgebra.mem_bot _).1 a.2).trans ((LieSubalgebra.mem_bot _).1 b.2).symm)⟩
    exact finrank_zero_of_subsingleton
  rw [hbot, add_zero] at hsum
  exact hsum

/-- At a free point of a proper smooth action, choosing a complement of the orbit tangent space
produces a chart slice `σ : (Fin (dim M - dim G) → ℝ) → M` with `σ 0 = x` whose action map is a
local diffeomorphism at `(1, 0)`. -/
private theorem exists_localDiffeomorphAt_slice_of_stabilizer_eq_bot {x : M}
    (hx : MulAction.stabilizer G x = ⊥) :
    ∃ σ : (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) → M,
      σ 0 = x ∧
      IsLocalDiffeomorphAt
        (I.prod 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)) I' ∞
        (fun p : G × (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ↦ p.1 • σ p.2) (1, 0) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  have hiso : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ :=
    isotropy_eq_bot_of_stabilizer_eq_bot hx
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ E',
      IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) W :=
    Submodule.exists_isCompl _
  have hdimW : finrank ℝ (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) = finrank ℝ W := by
    have horb := finrank_orbitTangent_of_stabilizer_eq_bot (I := I) (I' := I') hx
    have hsum : finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) +
        finrank ℝ W = finrank ℝ E' := Submodule.finrank_add_eq_of_isCompl hW
    rw [horb] at hsum
    rw [finrank_fin_fun]
    omega
  let e : (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ≃L[ℝ] W :=
    ContinuousLinearEquiv.ofFinrankEq hdimW
  let σ : (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) → M :=
    fun u ↦ (extChartAt I' x).symm (extChartAt I' x x + (e u : E'))
  let T : (G × (Fin (finrank ℝ E' - finrank ℝ E) → ℝ)) ≃ₘ^∞⟮
      I.prod 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      I.prod 𝓘(ℝ, W)⟯ (G × W) :=
    { toEquiv := (Equiv.refl G).prodCongr e.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (e.contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (e.symm.contDiff.contMDiff.comp contMDiff_snd) }
  have hWloc := isLocalDiffeomorphAt_smul_extChartAt_symm (I := I) (G := G) (I' := I') hiso hW
  have hT0 : T (1, 0) = (1, 0) := Prod.ext rfl (map_zero e)
  exact ⟨σ, by simp [σ], (T.isLocalDiffeomorph (1, 0)).comp (hg := hT0.symm ▸ hWloc)⟩

/-- **Existence of a transverse slice at a free point of a proper action.** Let a
finite-dimensional real Lie group `G` act smoothly and properly on a finite-dimensional
boundaryless smooth real manifold `M`, and let `x ∈ M` have trivial stabilizer. Then there exist a
slice `σ : (Fin (dim M - dim G) → ℝ) → M` with `σ 0 = x` and an open neighbourhood `U` of `0`
such that the slice map `(g, u) ↦ g • σ u` is injective and a smooth local diffeomorphism on
`G × U`. -/
theorem exists_slice_of_stabilizer_eq_bot {x : M} (hx : MulAction.stabilizer G x = ⊥) :
    ∃ (σ : (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) → M)
      (U : TopologicalSpace.Opens (Fin (finrank ℝ E' - finrank ℝ E) → ℝ)),
      0 ∈ U ∧ σ 0 = x ∧
      InjOn (fun p : G × (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ↦ p.1 • σ p.2)
        (univ ×ˢ (U : Set _)) ∧
      IsLocalDiffeomorphOn
        (I.prod 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)) I' ∞
        (fun p : G × (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ↦ p.1 • σ p.2)
        (univ ×ˢ (U : Set _)) := by
  obtain ⟨σ, hσ0, hloc0⟩ :=
    exists_localDiffeomorphAt_slice_of_stabilizer_eq_bot (I := I) (I' := I') hx
  -- Local diffeomorphy extends along whole orbits, and properness gives tube injectivity.
  have hev_loc := hloc0.eventually_forall_smul_slice
  have hσcont : ContinuousAt σ 0 := by
    have h := hloc0.contMDiffAt.continuousAt.comp
      (f := fun u : Fin (finrank ℝ E' - finrank ℝ E) → ℝ ↦ ((1 : G), u))
      (continuous_const.prodMk continuous_id).continuousAt
    simpa only [Function.comp_def, one_smul] using h
  have hinj_loc : InjOn
      (fun p : G × (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ↦ p.1 • σ p.2)
      hloc0.localInverse.target := fun p hp q hq hpq ↦ by
    rw [← hloc0.localInverse_left_inv hp, ← hloc0.localInverse_left_inv hq]
    exact congrArg hloc0.localInverse hpq
  obtain ⟨U₁, hU₁, hinj₁⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice
    hσcont (by rwa [hσ0])
    (hloc0.localInverse.open_target.mem_nhds hloc0.localInverse_mem_target) hinj_loc
  obtain ⟨U, hU_sub, hU_open, h0U⟩ := mem_nhds_iff.1 (inter_mem hev_loc hU₁)
  refine ⟨σ, ⟨U, hU_open⟩, h0U, hσ0,
    hinj₁.mono (prod_mono_right (hU_sub.trans inter_subset_right)), ?_⟩
  rintro ⟨⟨g, u⟩, -, hu⟩
  exact (hU_sub hu).1 g

end Slice

/-! ### Quotient manifold structure and submersion projection -/

section QuotientManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ProperSMul G M] [IsCancelSMul G M] [ContMDiffSMul I I' ∞ G M]

private noncomputable def sliceMap (x : M) :
    (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) → M :=
  (exists_slice_of_stabilizer_eq_bot (I := I) (I' := I')
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose

private noncomputable def sliceDomain (x : M) :
    TopologicalSpace.Opens (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) :=
  (exists_slice_of_stabilizer_eq_bot (I := I) (I' := I')
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose

private theorem zero_mem_sliceDomain (x : M) :
    (0 : Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∈
      sliceDomain (I := I) (G := G) (I' := I') (M := M) x :=
  (exists_slice_of_stabilizer_eq_bot (I := I) (I' := I')
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose_spec.1

private theorem sliceMap_zero (x : M) :
    sliceMap (I := I) (G := G) (I' := I') (M := M) x 0 = x :=
  (exists_slice_of_stabilizer_eq_bot (I := I) (I' := I')
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose_spec.2.1

private theorem injOn_smul_sliceMap (x : M) :
    InjOn (fun p : G × (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ↦
        p.1 • sliceMap (I := I) (G := G) (I' := I') (M := M) x p.2)
      (univ ×ˢ (sliceDomain (I := I) (G := G) (I' := I') (M := M) x : Set _)) :=
  (exists_slice_of_stabilizer_eq_bot (I := I) (I' := I')
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose_spec.2.2.1

private theorem isLocalDiffeomorphOn_smul_sliceMap (x : M) :
    IsLocalDiffeomorphOn
      (I.prod 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)) I' ∞
      (fun p : G × (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ↦
        p.1 • sliceMap (I := I) (G := G) (I' := I') (M := M) x p.2)
      (univ ×ˢ (sliceDomain (I := I) (G := G) (I' := I') (M := M) x : Set _)) :=
  (exists_slice_of_stabilizer_eq_bot (I := I) (I' := I')
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose_spec.2.2.2

private noncomputable def sliceChartEmbedding (x : M) :
    sliceDomain (I := I) (G := G) (I' := I') (M := M) x → MulAction.orbitRel.Quotient G M :=
  fun u ↦ Quotient.mk (MulAction.orbitRel G M)
    (sliceMap (I := I) (G := G) (I' := I') (M := M) x u)

private theorem isOpenEmbedding_sliceChartEmbedding (x : M) :
    IsOpenEmbedding (sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M) x) :=
  TauCeti.MulAction.isOpenEmbedding_quotientMk_slice
    (sliceDomain (I := I) (G := G) (I' := I') (M := M) x).isOpen
    (injOn_smul_sliceMap (I := I) (G := G) (I' := I') (M := M) x)
    (isLocalDiffeomorphOn_smul_sliceMap (I := I) (G := G) (I' := I') (M := M) x).isLocalHomeomorphOn

private theorem cover_sliceChartEmbedding (q : MulAction.orbitRel.Quotient G M) :
    ∃ (x : M) (u : sliceDomain (I := I) (G := G) (I' := I') (M := M) x),
      sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M) x u = q :=
  Quotient.inductionOn q fun x ↦
    ⟨x, ⟨0, zero_mem_sliceDomain (I := I) (G := G) (I' := I') (M := M) x⟩,
      by simp [sliceChartEmbedding, sliceMap_zero]⟩

private theorem deck_sliceChartEmbedding (x y : M)
    (u : sliceDomain (I := I) (G := G) (I' := I') (M := M) x)
    (v : sliceDomain (I := I) (G := G) (I' := I') (M := M) y)
    (huv : sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M) x u =
      sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M) y v) :
    ∃ T : sliceDomain (I := I) (G := G) (I' := I') (M := M) x →
      sliceDomain (I := I) (G := G) (I' := I') (M := M) y,
      ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
        𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞ T u ∧
      sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M) y ∘ T =ᶠ[𝓝 u]
        sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M) x := by
  classical
  let K := 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
  have hσx : ContMDiffAt K I' ∞
      (sliceMap (I := I) (G := G) (I' := I') (M := M) x ∘ Subtype.val) u := by
    have h1 := (isLocalDiffeomorphOn_smul_sliceMap (I := I) (G := G) (I' := I') (M := M) x
      ⟨((1 : G), u.1), mem_univ (1 : G), u.2⟩).contMDiffAt
    have h2 : ContMDiffAt K I' ∞ (sliceMap (I := I) (G := G) (I' := I') (M := M) x) u.1 := by
      simpa only [Function.comp_def, one_smul] using
        h1.comp u.1 (contMDiffAt_const.prodMk contMDiffAt_id)
    exact h2.comp u contMDiff_subtype_val.contMDiffAt
  obtain ⟨t, ht_smooth, -, htev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff
    (sliceDomain (I := I) (G := G) (I' := I') (M := M) y).isOpen
    (injOn_smul_sliceMap (I := I) (G := G) (I' := I') (M := M) y)
    (isLocalDiffeomorphOn_smul_sliceMap (I := I) (G := G) (I' := I') (M := M) y)
    hσx v.2 huv.symm
  let T : sliceDomain (I := I) (G := G) (I' := I') (M := M) x →
      sliceDomain (I := I) (G := G) (I' := I') (M := M) y :=
    fun z ↦
      if hz : t z ∈ sliceDomain (I := I) (G := G) (I' := I') (M := M) y then ⟨t z, hz⟩ else v
  refine ⟨T, ?_, ?_⟩
  · refine (ContMDiffAt.subtypeVal_comp_iff _ T u).1 (ht_smooth.congr_of_eventuallyEq ?_)
    filter_upwards [htev] with z hz
    simp only [Function.comp_apply, T, dite_eq_left (SetLike.mem_coe.1 hz.1)]
  · filter_upwards [htev] with z hz
    simp only [Function.comp_apply, sliceChartEmbedding, T, dite_eq_left (SetLike.mem_coe.1 hz.1)]
    exact (hz.2 (t z) hz.1).2 rfl

variable (I G I' M) in
/-- **The quotient atlas of a free proper Lie group action.** Charts are obtained by gluing the
open embeddings of transverse slices of dimension `dim M - dim G` into
`MulAction.orbitRel.Quotient G M`. The quotient retains its quotient topology; this definition is
deliberately not a global instance, to avoid conflicting with Mathlib's
`MulAction.instChartedSpaceQuotient` for discrete actions. -/
@[instance_reducible]
noncomputable def freeProperQuotientChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding (H := Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
    (isOpenEmbedding_sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M))
    (cover_sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M))

variable (I G I' M) in
/-- The orbit space of a free proper smooth action of a finite-dimensional real Lie group on a
finite-dimensional boundaryless smooth real manifold is a smooth manifold of dimension
`dim M - dim G`. -/
theorem isManifold_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I G I' M
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding
    (isOpenEmbedding_sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M))
    (cover_sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M))
    (deck_sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M))

/-- Locally near `x`, the second component of the local inverse of the slice map defines a smooth
retraction `r` onto the slice domain with surjective differential through which the orbit projection
factors. -/
private theorem exists_localSliceProjection (x : M) :
    ∃ r : M → sliceDomain (I := I) (G := G) (I' := I') (M := M) x,
      ContMDiffAt I' 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞ r x ∧
      Surjective (mfderiv I' 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) r x) ∧
      Quotient.mk (MulAction.orbitRel G M) =ᶠ[𝓝 x]
        sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M) x ∘ r := by
  classical
  let K := 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
  let σ := sliceMap (I := I) (G := G) (I' := I') (M := M) x
  let U := sliceDomain (I := I) (G := G) (I' := I') (M := M) x
  have h0U : (0 : Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∈ U :=
    zero_mem_sliceDomain (I := I) (G := G) (I' := I') (M := M) x
  have hσ0 : (1 : G) • σ 0 = x := by
    rw [one_smul]
    exact sliceMap_zero (I := I) (G := G) (I' := I') (M := M) x
  have hloc := isLocalDiffeomorphOn_smul_sliceMap (I := I) (G := G) (I' := I') (M := M) x
    ⟨((1 : G), 0), mem_univ (1 : G), h0U⟩
  let Ψ := hloc.localInverse
  have hΨloc : IsLocalDiffeomorphAt I' (I.prod K) ∞ Ψ x :=
    hσ0 ▸ hloc.localInverse_isLocalDiffeomorphAt
  have hΨx : Ψ x = (1, 0) := by
    rw [← hσ0]
    exact hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hmemU : ∀ᶠ y in 𝓝 x, (Ψ y).2 ∈ U :=
    (continuous_snd.continuousAt.comp hΨloc.contMDiffAt.continuousAt).preimage_mem_nhds
      (U.isOpen.mem_nhds (by simpa [hΨx] using h0U))
  have hright : ∀ᶠ y in 𝓝 x, (Ψ y).1 • σ (Ψ y).2 = y := by
    have h := hloc.localInverse_eventuallyEq_right
    rw [hσ0] at h
    exact h
  let r : M → U := fun y ↦ if hy : (Ψ y).2 ∈ U then ⟨(Ψ y).2, hy⟩ else ⟨0, h0U⟩
  have hr_eq : (Subtype.val : U → _) ∘ r =ᶠ[𝓝 x] Prod.snd ∘ Ψ := by
    filter_upwards [hmemU] with y hy
    simp only [Function.comp_apply, r, dite_eq_left hy]
  have hr_smooth : ContMDiffAt I' K ∞ r x :=
    (ContMDiffAt.subtypeVal_comp_iff U r x).1
      ((contMDiffAt_snd.comp x hΨloc.contMDiffAt).congr_of_eventuallyEq hr_eq)
  have hvalinv := (isLocalDiffeomorph_subtype_val (I := K) (n := ∞) (U := U)
    (r x)).isInvertible_mfderiv (by simp)
  have hΨinv := hΨloc.isInvertible_mfderiv (by simp)
  refine ⟨r, hr_smooth, ?_, ?_⟩
  · refine (Surjective.of_comp_iff' hvalinv.bijective _).1 ?_
    rw [← ContinuousLinearMap.coe_comp,
      ← mfderiv_comp x ((contMDiff_subtype_val (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
        (hr_smooth.mdifferentiableAt (by simp)),
      hr_eq.mfderiv_eq,
      mfderiv_comp x mdifferentiableAt_snd (hΨloc.contMDiffAt.mdifferentiableAt (by simp)),
      mfderiv_snd]
    exact (tangentSpaceCast K _ _).surjective.comp (Prod.snd_surjective.comp hΨinv.surjective)
  · filter_upwards [hmemU, hright] with y hyU hyR
    simp only [Function.comp_apply, sliceChartEmbedding, r, dite_eq_left hyU]
    exact Quotient.sound ⟨(Ψ y).1, hyR⟩

/-- At every `x ∈ M`, the orbit projection is smooth and has surjective differential. -/
private theorem contMDiffAt_and_surjective_mfderiv_quotientMk (x : M) :
    letI := freeProperQuotientChartedSpace I G I' M
    ContMDiffAt I' 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) x ∧
    Surjective (mfderiv I' 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x) := by
  let := freeProperQuotientChartedSpace I G I' M
  have := isManifold_freeProperQuotient I G I' M
  let K := 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
  obtain ⟨r, hr_smooth, hr_surj, hπ_eq⟩ :=
    exists_localSliceProjection (I := I) (G := G) (I' := I') x
  have hφloc : IsLocalDiffeomorph K K ∞
      (sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M) x) :=
    isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
      (isOpenEmbedding_sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M))
      (cover_sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M))
      (deck_sliceChartEmbedding (I := I) (G := G) (I' := I') (M := M)) x
  refine ⟨((hφloc (r x)).contMDiffAt.comp x hr_smooth).congr_of_eventuallyEq hπ_eq, ?_⟩
  have hφinv := (hφloc (r x)).isInvertible_mfderiv (by simp)
  rw [hπ_eq.mfderiv_eq, mfderiv_comp x ((hφloc (r x)).contMDiffAt.mdifferentiableAt (by simp))
    (hr_smooth.mdifferentiableAt (by simp))]
  exact (tangentSpaceCast K _ _).surjective.comp (hφinv.surjective.comp hr_surj)

variable (I G I' M) in
/-- **The orbit projection is a smooth submersion with complement `E`.** Here `E` is the model
space of the Lie group `G`. This holds even when `M` is empty. -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I G I' M
    Manifold.IsSubmersionOfComplement E I'
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace I G I' M
  have := isManifold_freeProperQuotient I G I' M
  let K := 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
  have hsmooth : ContMDiff I' K ∞ (Quotient.mk (MulAction.orbitRel G M)) :=
    fun x ↦ (contMDiffAt_and_surjective_mfderiv_quotientMk (I := I) (G := G) (I' := I') x).1
  refine Manifold.isSubmersionOfComplement_iff.2 fun x ↦ ?_
  have hsurj := (contMDiffAt_and_surjective_mfderiv_quotientMk (I := I) (G := G) (I' := I') x).2
  have hsub := hsmooth.contMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv
    isOpen_univ (mem_univ x) (by simp) hsurj
  -- At any point `x ∈ M`, the orbit tangent space embeds `E` into `E'`, so `dim E ≤ dim E'` and
  -- the standard complement `Fin (dim E' - (dim E' - dim E)) → ℝ` is isomorphic to `E`.
  have hle : finrank ℝ E ≤ finrank ℝ E' := by
    rw [← finrank_orbitTangent_of_stabilizer_eq_bot (I := I) (I' := I')
      (IsCancelSMul.stabilizer_eq_bot (G := G) x)]
    exact Submodule.finrank_le _
  let e :
      (Fin (finrank ℝ E' - finrank ℝ (Fin (finrank ℝ E' - finrank ℝ E) → ℝ)) → ℝ) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_fin_fun, finrank_fin_fun]; omega)
  exact (Manifold.IsSubmersionAtOfComplement.congr_F e).mp hsub

variable (I G I' M) in
/-- **The orbit projection is a smooth submersion.** -/
theorem isSubmersion_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I G I' M
    Manifold.IsSubmersion I' 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) :=
  letI := freeProperQuotientChartedSpace I G I' M
  (isSubmersionOfComplement_quotientMk_freeProperQuotient I G I' M).isSubmersion

/-- **The vertical tangent space of a free proper quotient is the orbit tangent space.** At every
`x ∈ M`, the kernel of the differential of the orbit projection is `𝔤 · x`. -/
theorem ker_mfderiv_quotientMk_freeProperQuotient (x : M) :
    letI := freeProperQuotientChartedSpace I G I' M
    (mfderiv I' 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental I G I' M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I G I' M
  have := isManifold_freeProperQuotient I G I' M
  let K := 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
  have hsub := isSubmersion_quotientMk_freeProperQuotient I G I' M
  -- Every fundamental vector field is killed because the projection is constant along orbits.
  have hle_ker : (InfinitesimalAction.fundamental I G I' M).orbitTangent x ≤
      (mfderiv I' K (Quotient.mk (MulAction.orbitRel G M)) x).ker := by
    intro v hv
    obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ _).1 hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, InfinitesimalAction.fundamental_apply,
      fundamentalVectorField_apply]
    have hconst : Quotient.mk (MulAction.orbitRel G M) ∘ (fun g : G ↦ g • x) =
        fun _ : G ↦ Quotient.mk (MulAction.orbitRel G M) ((1 : G) • x) :=
      funext fun g ↦ Quotient.sound ⟨g, by rw [one_smul]⟩
    have hdiff_orb : MDifferentiableAt I I' (fun g : G ↦ g • x) (1 : G) :=
      (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) x).mdifferentiableAt
        (by simp)
    have hdiff_mk : MDifferentiableAt I' K (Quotient.mk (MulAction.orbitRel G M)) ((1 : G) • x) :=
      (hsub.contMDiff ((1 : G) • x)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp (1 : G) hdiff_mk hdiff_orb
    rw [hconst, mfderiv_const] at hcomp
    have h0 := congrArg (fun L ↦ L ξ) hcomp.symm
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at h0
    exact (congrArg (fun L : E' →L[ℝ] (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ↦
      L ((mfderiv I I' (fun g : G ↦ g • x) 1) ξ))
      (mfderiv_congr_point (I := I') (I' := K) (f := Quotient.mk (MulAction.orbitRel G M))
        (one_smul G x))).symm.trans h0
  -- Both subspaces have dimension `dim G`, so the inclusion is an equality.
  have hsurj : Surjective (mfderiv I' K (Quotient.mk (MulAction.orbitRel G M)) x) :=
    hsub.surjective_mfderiv (by simp) x
  have horb := finrank_orbitTangent_of_stabilizer_eq_bot (I := I) (I' := I')
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)
  have hle : finrank ℝ E ≤ finrank ℝ E' := horb ▸ Submodule.finrank_le _
  have hker_dim : finrank ℝ (mfderiv I' K (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      finrank ℝ E := by
    have h := (mfderiv I' K (Quotient.mk (MulAction.orbitRel G M)) x).toLinearMap
      |>.finrank_ker_eq_sub_of_surjective hsurj
    have hdimK : finrank ℝ (TangentSpace K (Quotient.mk (MulAction.orbitRel G M) x)) =
        finrank ℝ E' - finrank ℝ E := finrank_fin_fun ℝ
    have hdimM : finrank ℝ (TangentSpace I' x) = finrank ℝ E' := rfl
    rw [hdimK, hdimM] at h
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle_ker (by rw [horb, hker_dim])).symm

/-- **Uniqueness of the smooth structure on a free proper quotient.** Any smooth manifold structure
on `M ⧸ G` modelled on `Fin (dim M - dim G) → ℝ` for which the orbit projection is a smooth
submersion has the same maximal atlas as `TauCeti.freeProperQuotientChartedSpace`. -/
theorem maximalAtlas_freeProperQuotient_eq
    {c : ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      (MulAction.orbitRel.Quotient G M)}
    (hc : letI := c; IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M))
    (hsub : letI := c; Manifold.IsSubmersion I'
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M))) :
    (letI := freeProperQuotientChartedSpace I G I' M;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) =
      (letI := c;
        IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
          (MulAction.orbitRel.Quotient G M)) :=
  Manifold.maximalAtlas_eq_of_isSubmersion (isManifold_freeProperQuotient I G I' M) hc
    (isSubmersion_quotientMk_freeProperQuotient I G I' M) hsub Quotient.mk_surjective

/-! ### Smooth descent of invariant and equivariant maps -/

/-- **Pointwise smooth descent on a free proper quotient.** For `m ≤ ∞`, the descent of a
`G`-invariant map `f : M → N` is `C^m` at `[x]` exactly when `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff {m : ℕ∞ω} (hm : m ≤ ∞)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N]
    {f : M → N} (hf : ∀ (g : G) (x : M), f (g • x) = f x) {x : M} :
    letI := freeProperQuotientChartedSpace I G I' M
    ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J m
      (MulAction.orbitRelQuotientLift f hf) (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I' J m f x := by
  let := freeProperQuotientChartedSpace I G I' M
  rw [← ((isSubmersion_quotientMk_freeProperQuotient I G I' M).isSubmersionAt x)
    |>.contMDiffAt_comp_iff hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- **Smooth descent on a free proper quotient.** For `m ≤ ∞`, the descent of a `G`-invariant
map `f : M → N` is `C^m` on `M ⧸ G` exactly when `f` is `C^m` on `M`. -/
theorem contMDiff_orbitRelQuotientLift_freeProperQuotient_iff {m : ℕ∞ω} (hm : m ≤ ∞)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N]
    {f : M → N} (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace I G I' M
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J m
      (MulAction.orbitRelQuotientLift f hf) ↔ ContMDiff I' J m f := by
  let := freeProperQuotientChartedSpace I G I' M
  rw [← (isSubmersion_quotientMk_freeProperQuotient I G I' M).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- **Equivariant smooth maps descend to smooth maps of free proper quotients.** For `m ≤ ∞`, a
`C^m` map `φ : M →ₑ[σ] N` intertwining two free proper smooth Lie group actions induces a `C^m`
map `M ⧸ G → N ⧸ K`. -/
theorem contMDiff_orbitRelQuotientMap_freeProperQuotient {m : ℕ∞ω} (hm : m ≤ ∞)
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [FiniteDimensional ℝ EK]
    {HK : Type*} [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK}
    {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup IK ∞ K]
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
    [MulAction K N] [ProperSMul K N] [IsCancelSMul K N] [ContMDiffSMul IK IN ∞ K N]
    {σ : G → K} {φ : M →ₑ[σ] N} (hφ : ContMDiff I' IN m φ) :
    letI := freeProperQuotientChartedSpace I G I' M
    letI := freeProperQuotientChartedSpace IK K IN N
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ EN - finrank ℝ EK) → ℝ) m
      (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace I G I' M
  let := freeProperQuotientChartedSpace IK K IN N
  rw [← (isSubmersion_quotientMk_freeProperQuotient I G I' M).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((isSubmersion_quotientMk_freeProperQuotient IK K IN N).contMDiff.of_le hm).comp hφ

/-- **Equivariant smooth submersions descend to smooth submersions of free proper quotients.** -/
theorem isSubmersion_orbitRelQuotientMap_freeProperQuotient
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [FiniteDimensional ℝ EK]
    {HK : Type*} [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK}
    {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup IK ∞ K]
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
    [MulAction K N] [ProperSMul K N] [IsCancelSMul K N] [ContMDiffSMul IK IN ∞ K N]
    {σ : G → K} {φ : M →ₑ[σ] N} (hφ : Manifold.IsSubmersion I' IN ∞ φ) :
    letI := freeProperQuotientChartedSpace I G I' M
    letI := freeProperQuotientChartedSpace IK K IN N
    Manifold.IsSubmersion 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ EN - finrank ℝ EK) → ℝ) ∞
      (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace I G I' M
  let := freeProperQuotientChartedSpace IK K IN N
  have := isManifold_freeProperQuotient I G I' M
  have := isManifold_freeProperQuotient IK K IN N
  have hsmooth := contMDiff_orbitRelQuotientMap_freeProperQuotient
    (I := I) (G := G) (I' := I') (IK := IK) (K := K) (IN := IN) le_rfl hφ.contMDiff
  refine (hsmooth.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun q ↦ ?_)
    |>.isSubmersion
  induction q using Quotient.inductionOn with
  | h x =>
    have hπM := isSubmersion_quotientMk_freeProperQuotient I G I' M
    have hπN := isSubmersion_quotientMk_freeProperQuotient IK K IN N
    have hcomp : mfderiv I' 𝓘(ℝ, Fin (finrank ℝ EN - finrank ℝ EK) → ℝ)
        (MulActionHom.orbitRelQuotientMap φ ∘ Quotient.mk (MulAction.orbitRel G M)) x =
        (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
          𝓘(ℝ, Fin (finrank ℝ EN - finrank ℝ EK) → ℝ)
          (MulActionHom.orbitRelQuotientMap φ) (Quotient.mk (MulAction.orbitRel G M) x)).comp
          (mfderiv I' 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
            (Quotient.mk (MulAction.orbitRel G M)) x) :=
      mfderiv_comp x ((hsmooth _).mdifferentiableAt (by simp))
        ((hπM.contMDiff x).mdifferentiableAt (by simp))
    have hsurj_comp :
        Surjective (mfderiv I' 𝓘(ℝ, Fin (finrank ℝ EN - finrank ℝ EK) → ℝ)
          (MulActionHom.orbitRelQuotientMap φ ∘ Quotient.mk (MulAction.orbitRel G M)) x) := by
      rw [MulActionHom.orbitRelQuotientMap_comp_mk,
        mfderiv_comp x ((hπN.contMDiff (φ x)).mdifferentiableAt (by simp))
          ((hφ.contMDiff x).mdifferentiableAt (by simp))]
      exact (hπN.surjective_mfderiv (by simp) (φ x)).comp (hφ.surjective_mfderiv (by simp) x)
    rw [hcomp, ContinuousLinearMap.coe_comp] at hsurj_comp
    exact hsurj_comp.of_comp

variable (I G I' M) in
/-- **The quotient manifold theorem.** The orbit space of a free proper smooth action of a
finite-dimensional real Lie group `G` on a finite-dimensional boundaryless smooth real manifold `M`
admits a smooth atlas of dimension `dim M - dim G`, with its quotient topology, for which the orbit
projection is a smooth submersion whose differential has kernel equal to the orbit tangent space
`𝔤 · x` at every `x ∈ M`. Neither manifold needs separate Hausdorff or second-countability
assumptions, and `M` may be empty. -/
theorem exists_freeProperQuotient_isSubmersion :
    ∃ cs : ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
        (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      Manifold.IsSubmersion I'
        𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
        (Quotient.mk (MulAction.orbitRel G M)) ∧
      ∀ x : M,
        (mfderiv I' 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
          (Quotient.mk (MulAction.orbitRel G M)) x).ker =
          (InfinitesimalAction.fundamental I G I' M).orbitTangent x :=
  ⟨freeProperQuotientChartedSpace I G I' M, isManifold_freeProperQuotient I G I' M,
    isSubmersion_quotientMk_freeProperQuotient I G I' M,
    ker_mfderiv_quotientMk_freeProperQuotient (I := I) (G := G) (I' := I')⟩

end QuotientManifold

end TauCeti
