/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Quotient
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Manifold.GroupAction.Orbit
public import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.Instances.Quotient
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.Submersion.Descent
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# Quotient manifolds of free proper smooth Lie group actions

Let a finite-dimensional real Lie group `G` act freely, properly, and smoothly on the left on a
finite-dimensional boundaryless smooth real manifold `M`. This file proves the **quotient manifold
theorem**: the orbit space `MulAction.orbitRel.Quotient G M`, retaining its quotient topology,
carries a smooth manifold structure of dimension `dim M - dim G` for which the orbit projection
`Quotient.mk'' : M → MulAction.orbitRel.Quotient G M` is a surjective smooth submersion whose
differential has kernel the orbit tangent space `𝔤 · x` at every point `x : M`.

No global `ChartedSpace` instance is installed on `MulAction.orbitRel.Quotient G M`, so this
structure coexists without conflict with Mathlib's `MulAction.instChartedSpaceQuotient` for
properly discontinuous actions. No separation or second-countability assumptions on `M` or `G` are
needed: `G` is Hausdorff as a Lie group and `M` is Hausdorff from properness, so the orbit space is
Hausdorff (`instT2SpaceQuotientOrbitRel`) and inherits second countability from `M` when `M` is
second countable. Empty `M` is allowed.

## Construction

At each point `x : M`, triviality of the stabilizer makes the orbit map an immersion
(`TauCeti.isImmersion_smul_const_of_stabilizer_eq_bot`), so the isotropy algebra `𝔤_x` vanishes
and any complement `W` of the orbit tangent space `𝔤 · x` in `T_x M` has dimension `dim M - dim G`.
Parametrizing `W` by `Fin (dim M - dim G) → ℝ`, the chart slice `σ : v ↦ φ.symm (φ x + eW v)` gives
a slice map `(g, v) ↦ g • σ v` that is a local diffeomorphism at `(1, 0)`
(`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`), hence along `G × U` for a small open
neighbourhood `U` of `0` (`IsLocalDiffeomorphAt.eventually_forall_smul_slice`), and injective on
`G × U` after shrinking by properness (`ProperSMul.exists_mem_nhds_injOn_smul_slice`). The
resulting quotient charts `U → M ⧸ G` are open embeddings
(`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`) with smooth overlap transitions
(`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`), which glue via
`TauCeti.chartedSpaceOfIsOpenEmbedding`.

In each slice chart, the orbit projection composed with the slice map is the second projection
`G × U → U` followed by the open-embedding chart of `M ⧸ G`. Since both the slice map and the
quotient chart are local diffeomorphisms, the orbit projection is smooth with surjective
differential at every point, hence a submersion with complement the model space of `G`.

## Main declarations

* `TauCeti.freeProperQuotientChartedSpace`: the glued smooth atlas on
  `MulAction.orbitRel.Quotient G M`, modelled on `Fin (finrank ℝ E - finrank ℝ EG) → ℝ`.
* `TauCeti.isManifold_freeProperQuotient`: `MulAction.orbitRel.Quotient G M` with this atlas is a
  `C^∞` manifold.
* `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
  `TauCeti.isSubmersion_quotientMk_freeProperQuotient`: the orbit projection is a `C^∞` submersion
  with complement `EG`.
* `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`: the kernel of the differential of the orbit
  projection at `x` is the orbit tangent space `𝔤 · x`.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: existential form of the quotient manifold
  theorem.
* `TauCeti.freeProperQuotientDiffeomorph`, `TauCeti.maximalAtlas_freeProperQuotient_eq`: uniqueness
  of the smooth quotient structure among all smooth structures making `Quotient.mk''` a submersion,
  together with `TauCeti.ker_mfderiv_quotientMk_of_isSubmersion`.
* `TauCeti.freeProperQuotientDiffeomorphDiscrete`: when the action is also properly discontinuous,
  the identity is a `C^∞` diffeomorphism with `MulAction.instChartedSpaceQuotient`.
* `TauCeti.freeProperQuotientDiffeomorphOfSubsingleton`: for a trivial acting group, `Quotient.mk''`
  is a `C^∞` diffeomorphism `M ≃ₘ^∞ M ⧸ G`.
* `TauCeti.contMDiffAt_orbitRelQuotientLift_iff_freeProperQuotient`,
  `TauCeti.contMDiff_orbitRelQuotientLift_iff_freeProperQuotient`,
  `TauCeti.existsUnique_contMDiff_orbitRelQuotientLift_freeProperQuotient`,
  `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`,
  `TauCeti.freeProperQuotientCongr`, and
  `TauCeti.isImmersion_orbitRelQuotientLift_iff_freeProperQuotient`: smooth descent, equivariant
  maps, equivariant diffeomorphisms, and the immersion criterion on the quotient manifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013, Theorem 21.10
  (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21.
-/

public section

open Function Module Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

section Construction

variable {E EG H HG M G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  {I : ModelWithCorners ℝ E H} {IG : ModelWithCorners ℝ EG HG}
  [I.Boundaryless] [IG.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M]

/-- At any point of a free proper smooth action, the stabilizer and isotropy algebra are trivial. -/
private theorem isotropy_eq_bot_of_freeProper
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (x : M) :
    (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hstab : MulAction.stabilizer G x = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ hfree g x hg
  exact (isImmersion_smul_const_iff (I := IG) (I' := I)).1
    (isImmersion_smul_const_of_stabilizer_eq_bot hstab)

variable (I IG) in
include I IG in
/-- On a nonempty manifold with a free proper smooth action of a finite-dimensional Lie group `G`,
the dimension of `G` does not exceed the dimension of `M`. -/
theorem finrank_le_of_freeProper [Nonempty M]
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    finrank ℝ EG ≤ finrank ℝ E := by
  obtain ⟨x⟩ := ‹Nonempty M›
  have hO := (InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot
    x (isotropy_eq_bot_of_freeProper (I := I) (IG := IG) hfree x)
  have hle : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) ≤ finrank ℝ E :=
    Submodule.finrank_le _
  exact hO ▸ hle

variable (G I IG) in
/-- A transverse slice through `x` parametrized by `Fin (dim M - dim G) → ℝ`, on an open
neighbourhood `U` of `0` over which the slice map `(g, v) ↦ g • σ v` is both injective and a
smooth local diffeomorphism on `G × U`. -/
private structure FreeProperSlice (x : M) where
  slice : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M
  domain : TopologicalSpace.Opens (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  zero_mem : (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ domain
  slice_zero : slice 0 = x
  contMDiffOn_slice :
    ContMDiffOn 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞ slice domain
  injOn_smul :
    InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • slice p.2)
      (univ ×ˢ (domain : Set _))
  isLocalDiffeomorphOn_smul :
    IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
      (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • slice p.2)
      (univ ×ˢ (domain : Set _))

/-- A chart slice through `x` transverse to the `G`-orbit, giving a local diffeomorphism
`(g, v) ↦ g • σ v` at `(1, 0)`. -/
private theorem exists_transverseSlice_localDiffeomorph
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (x : M) :
    ∃ (σ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M)
      (U : Set (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)),
      IsOpen U ∧ (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ U ∧ σ 0 = x ∧
      ContMDiffOn 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞ σ U ∧
      IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
        (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2) (1, 0) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  set F := Fin (finrank ℝ E - finrank ℝ EG) → ℝ
  have hisot := isotropy_eq_bot_of_freeProper (I := I) (IG := IG) hfree x
  let O : Submodule ℝ E := (InfinitesimalAction.fundamental IG G I M).orbitTangent x
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl O
  have hO : finrank ℝ O = finrank ℝ EG :=
    (InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x hisot
  have hsum : finrank ℝ O + finrank ℝ W = finrank ℝ E := Submodule.finrank_add_eq_of_isCompl hW
  have hWdim : finrank ℝ F = finrank ℝ W := by
    rw [Module.finrank_fin_fun]
    omega
  let eW : F ≃L[ℝ] W := (LinearEquiv.ofFinrankEq F W hWdim).toContinuousLinearEquiv
  let τ : F → E := fun v ↦ extChartAt I x x + (eW v : E)
  let σ : F → M := fun v ↦ (extChartAt I x).symm (τ v)
  have hτ0 : τ 0 = extChartAt I x x := by simp [τ]
  have hσ0 : σ 0 = x := by simp [σ, hτ0]
  have hτsmooth : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ τ :=
    (contDiff_const.add (W.subtypeL.comp eW.toContinuousLinearMap).contDiff).contMDiff
  have hlocW := isLocalDiffeomorphAt_smul_extChartAt_symm (I := IG) (I' := I) hisot hW
  let T : (G × F) ≃ₘ^∞⟮IG.prod 𝓘(ℝ, F), IG.prod 𝓘(ℝ, W)⟯ (G × W) :=
    { toEquiv := (Equiv.refl G).prodCongr eW.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (eW.contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (eW.symm.contDiff.contMDiff.comp contMDiff_snd) }
  have hT0 : T (1, 0) = ((1 : G), (0 : W)) := Prod.ext rfl (map_zero eW)
  refine ⟨σ, τ ⁻¹' (extChartAt I x).target,
    (isOpen_extChartAt_target x).preimage hτsmooth.continuous,
    by rw [mem_preimage, hτ0]; exact mem_extChartAt_target x, hσ0,
    (contMDiffOn_extChartAt_symm x).comp hτsmooth.contMDiffOn fun _ hv ↦ hv,
    IsLocalDiffeomorphAt.comp (hf := T.isLocalDiffeomorph (1, 0)) (hg := hT0.symm ▸ hlocW)⟩

/-- Existence of a transverse slice through `x` for a free proper smooth action. -/
private theorem exists_freeProperSlice
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (x : M) :
    Nonempty (FreeProperSlice G I IG x) := by
  set F := Fin (finrank ℝ E - finrank ℝ EG) → ℝ
  obtain ⟨σ, U₁, hU₁, h0₁, hσ0, hσU₁, hloc0⟩ :=
    exists_transverseSlice_localDiffeomorph (I := I) (IG := IG) hfree x
  obtain ⟨U₂, hU₂_sub, hU₂_open, h0₂⟩ := mem_nhds_iff.1 hloc0.eventually_forall_smul_slice
  have hinj_loc : InjOn (fun p : G × F ↦ p.1 • σ p.2) hloc0.localInverse.target := by
    intro p hp q hq hpq
    dsimp only at hpq
    rw [← hloc0.localInverse_left_inv hp, ← hloc0.localInverse_left_inv hq, hpq]
  have hstab0 : MulAction.stabilizer G (σ 0) = ⊥ := by
    rw [hσ0]
    exact (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ hfree g x hg
  obtain ⟨U₃', hU₃'_nhds, hinj₃'⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice
    (hσU₁.contMDiffAt (hU₁.mem_nhds h0₁)).continuousAt hstab0
    (hloc0.localInverse.open_target.mem_nhds hloc0.localInverse_mem_target) hinj_loc
  obtain ⟨U₃, hU₃_sub, hU₃_open, h0₃⟩ := mem_nhds_iff.1 hU₃'_nhds
  let U : TopologicalSpace.Opens F := ⟨(U₁ ∩ U₂) ∩ U₃, (hU₁.inter hU₂_open).inter hU₃_open⟩
  refine ⟨⟨σ, U, ⟨⟨h0₁, h0₂⟩, h0₃⟩, hσ0,
    hσU₁.mono (inter_subset_left.trans inter_subset_left),
    hinj₃'.mono (prod_mono_right (inter_subset_right.trans hU₃_sub)), ?_⟩⟩
  rintro ⟨⟨g, v⟩, -, hv⟩
  exact hU₂_sub hv.1.2 g

variable (I IG) in
/-- A chosen transverse slice at each point of `M`. -/
private noncomputable def chosenSlice
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (x : M) : FreeProperSlice G I IG x :=
  Classical.choice (exists_freeProperSlice (I := I) (IG := IG) hfree x)

variable (I IG) in
/-- The quotient chart `v ↦ [σ_x v]` associated to the chosen transverse slice at `x`. -/
private noncomputable def sliceQuotientChart
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (x : M) :
    (chosenSlice I IG hfree x).domain → MulAction.orbitRel.Quotient G M :=
  fun v ↦ Quotient.mk (MulAction.orbitRel G M) ((chosenSlice I IG hfree x).slice v.1)

private theorem isOpenEmbedding_sliceQuotientChart
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (x : M) :
    IsOpenEmbedding (sliceQuotientChart I IG hfree x) :=
  TauCeti.MulAction.isOpenEmbedding_quotientMk_slice (chosenSlice I IG hfree x).domain.isOpen
    (chosenSlice I IG hfree x).injOn_smul
    (chosenSlice I IG hfree x).isLocalDiffeomorphOn_smul.isLocalHomeomorphOn

private theorem exists_sliceQuotientChart_eq
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (q : MulAction.orbitRel.Quotient G M) :
    ∃ (x : M) (v : (chosenSlice I IG hfree x).domain), sliceQuotientChart I IG hfree x v = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    refine ⟨x, ⟨0, (chosenSlice I IG hfree x).zero_mem⟩, ?_⟩
    simp only [sliceQuotientChart, (chosenSlice I IG hfree x).slice_zero]

private theorem exists_contMDiffAt_sliceQuotientChart_transition
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (x y : M)
    (u : (chosenSlice I IG hfree x).domain) (v : (chosenSlice I IG hfree y).domain)
    (huv : sliceQuotientChart I IG hfree x u = sliceQuotientChart I IG hfree y v) :
    ∃ T : (chosenSlice I IG hfree x).domain → (chosenSlice I IG hfree y).domain,
      ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ T u ∧
      sliceQuotientChart I IG hfree y ∘ T =ᶠ[𝓝 u] sliceQuotientChart I IG hfree x := by
  classical
  let sx := chosenSlice I IG hfree x
  let sy := chosenSlice I IG hfree y
  have hf : ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞
      (fun u' : sx.domain ↦ sx.slice u'.1) u :=
    (sx.contMDiffOn_slice.contMDiffAt (sx.domain.isOpen.mem_nhds u.2)).comp u
      contMDiff_subtype_val.contMDiffAt
  obtain ⟨t, ht, -, hev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff sy.domain.isOpen
    sy.injOn_smul sy.isLocalDiffeomorphOn_smul hf v.2 huv.symm
  let T : sx.domain → sy.domain := fun u' ↦ if h : t u' ∈ (sy.domain : Set _) then ⟨t u', h⟩ else v
  refine ⟨T, ?_, ?_⟩
  · rw [← TauCeti.ContMDiffAt.subtypeVal_comp_iff sy.domain T u]
    refine ht.congr_of_eventuallyEq ?_
    filter_upwards [hev] with u' hu'
    simp only [comp_apply, T, hu'.1, ↓reduceDIte]
  · filter_upwards [hev] with u' hu'
    simp only [comp_apply, T, hu'.1, ↓reduceDIte, sliceQuotientChart]
    exact (hu'.2 (t u') hu'.1).2 rfl

private theorem isLocalDiffeomorphAt_chosenSliceMap
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (x : M) :
    IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
      (fun p : G × (chosenSlice I IG hfree x).domain ↦
        p.1 • (chosenSlice I IG hfree x).slice p.2.1)
      (1, ⟨0, (chosenSlice I IG hfree x).zero_mem⟩) := by
  let K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  let sx := chosenSlice I IG hfree x
  have hmap : IsLocalDiffeomorphAt (IG.prod K) (IG.prod K) ∞
      (Prod.map (id : G → G) (Subtype.val : sx.domain → _)) (1, ⟨0, sx.zero_mem⟩) :=
    ((Diffeomorph.refl IG G ∞).isLocalDiffeomorph (1 : G)).prodMap
      (isLocalDiffeomorph_subtype_val (I := K) (n := ∞) (U := sx.domain) ⟨0, sx.zero_mem⟩)
  exact IsLocalDiffeomorphAt.comp (hf := hmap)
    (hg := sx.isLocalDiffeomorphOn_smul ⟨(1, 0), mem_univ _, sx.zero_mem⟩)

variable (I IG) in
include I IG in
/-- **The quotient manifold atlas of a free proper smooth action.** Glues the open-embedding
quotient charts of transverse slices into a `ChartedSpace` structure on
`MulAction.orbitRel.Quotient G M` modelled on `Fin (finrank ℝ E - finrank ℝ EG) → ℝ`, retaining the
quotient topology. Not registered as a global instance so it coexists with
`MulAction.instChartedSpaceQuotient` for properly discontinuous actions. -/
@[instance_reducible]
noncomputable def freeProperQuotientChartedSpace
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding
    (isOpenEmbedding_sliceQuotientChart (I := I) (IG := IG) hfree)
    (exists_sliceQuotientChart_eq (I := I) (IG := IG) hfree)

variable (I IG) in
/-- The orbit space of a free proper smooth action, equipped with `freeProperQuotientChartedSpace`,
is a smooth manifold of dimension `dim M - dim G`. -/
theorem isManifold_freeProperQuotient
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    letI := freeProperQuotientChartedSpace I IG hfree
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding
    (isOpenEmbedding_sliceQuotientChart (I := I) (IG := IG) hfree)
    (exists_sliceQuotientChart_eq (I := I) (IG := IG) hfree)
    (exists_contMDiffAt_sliceQuotientChart_transition (I := I) (IG := IG) hfree)

variable (I IG) in
/-- The orbit projection of a free proper smooth action is smooth. -/
theorem contMDiff_quotientMk_freeProperQuotient
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    letI := freeProperQuotientChartedSpace I IG hfree
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) := by
  let := freeProperQuotientChartedSpace I IG hfree
  have := isManifold_freeProperQuotient I IG hfree
  let K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  intro x
  let sx := chosenSlice I IG hfree x
  let p₀ : G × sx.domain := (1, ⟨0, sx.zero_mem⟩)
  let Ψ : G × sx.domain → M := fun p ↦ p.1 • sx.slice p.2.1
  have hΨ := isLocalDiffeomorphAt_chosenSliceMap (I := I) (IG := IG) hfree x
  have hφloc : IsLocalDiffeomorph K K ∞ (sliceQuotientChart I IG hfree x) :=
    isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
      (isOpenEmbedding_sliceQuotientChart (I := I) (IG := IG) hfree)
      (exists_sliceQuotientChart_eq (I := I) (IG := IG) hfree)
      (exists_contMDiffAt_sliceQuotientChart_transition (I := I) (IG := IG) hfree) x
  have heq : (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) ∘ Ψ =
      sliceQuotientChart I IG hfree x ∘ Prod.snd :=
    funext fun ⟨g, v⟩ ↦ Quotient.sound ⟨g, rfl⟩
  have hcomp : ContMDiffAt (IG.prod K) K ∞
      ((Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) ∘ Ψ) p₀ := by
    rw [heq]
    exact ((hφloc p₀.2).contMDiffAt).comp p₀ contMDiffAt_snd
  have h := (hΨ.contMDiffAt_comp_iff le_rfl).1 hcomp
  simpa only [one_smul, (chosenSlice I IG hfree x).slice_zero] using h

variable (I IG) in
/-- **The orbit projection of a free proper smooth action is a submersion with complement `EG`.** -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    letI := freeProperQuotientChartedSpace I IG hfree
    Manifold.IsSubmersionOfComplement EG I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) := by
  let := freeProperQuotientChartedSpace I IG hfree
  have := isManifold_freeProperQuotient I IG hfree
  let K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  have hcont := contMDiff_quotientMk_freeProperQuotient I IG hfree
  refine Manifold.isSubmersionOfComplement_iff.2 fun x ↦ ?_
  let sx := chosenSlice I IG hfree x
  let p₀ : G × sx.domain := (1, ⟨0, sx.zero_mem⟩)
  let Ψ : G × sx.domain → M := fun p ↦ p.1 • sx.slice p.2.1
  have hΨp₀ : Ψ p₀ = x := by simp [Ψ, p₀, sx.slice_zero]
  have hΨ := isLocalDiffeomorphAt_chosenSliceMap (I := I) (IG := IG) hfree x
  have hφloc : IsLocalDiffeomorph K K ∞ (sliceQuotientChart I IG hfree x) :=
    isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
      (isOpenEmbedding_sliceQuotientChart (I := I) (IG := IG) hfree)
      (exists_sliceQuotientChart_eq (I := I) (IG := IG) hfree)
      (exists_contMDiffAt_sliceQuotientChart_transition (I := I) (IG := IG) hfree) x
  have heq : (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) ∘ Ψ =
      sliceQuotientChart I IG hfree x ∘ Prod.snd :=
    funext fun ⟨g, v⟩ ↦ Quotient.sound ⟨g, rfl⟩
  have hsurj : Surjective
      (mfderiv I K (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) x) := by
    intro v
    obtain ⟨w, hw⟩ := ((hφloc p₀.2).isInvertible_mfderiv (by simp)).surjective v
    refine ⟨mfderiv (IG.prod K) I Ψ p₀ ((0 : TangentSpace IG (1 : G)), w), ?_⟩
    have h1 := mfderiv_comp_apply_of_eq p₀ (hcont.mdifferentiable (by simp) x)
      (hΨ.mdifferentiableAt (by simp)) hΨp₀ ((0 : TangentSpace IG (1 : G)), w)
    have h2 := mfderiv_comp_apply p₀ ((hφloc p₀.2).mdifferentiableAt (by simp))
      (mdifferentiableAt_snd (I := IG) (I' := K)) ((0 : TangentSpace IG (1 : G)), w)
    rw [heq] at h1
    rw [mfderiv_snd] at h2
    exact h1.symm.trans (h2.trans hw)
  have hsubF := hcont.contMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv
    isOpen_univ (mem_univ x) (by simp) hsurj
  have hle : finrank ℝ EG ≤ finrank ℝ E :=
    have : Nonempty M := ⟨x⟩
    finrank_le_of_freeProper I IG hfree
  have hdim : finrank ℝ (Fin (finrank ℝ E - finrank ℝ (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) → ℝ) =
      finrank ℝ EG := by
    simp only [Module.finrank_fin_fun]
    omega
  exact hsubF.trans_F (LinearEquiv.ofFinrankEq _ _ hdim).toContinuousLinearEquiv

variable (I IG) in
/-- **The orbit projection of a free proper smooth action is a smooth submersion.** -/
theorem isSubmersion_quotientMk_freeProperQuotient
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    letI := freeProperQuotientChartedSpace I IG hfree
    Manifold.IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) := by
  let := freeProperQuotientChartedSpace I IG hfree
  exact (isSubmersionOfComplement_quotientMk_freeProperQuotient I IG hfree).isSubmersion

variable (I IG) in
/-- **The vertical tangent space of a free proper quotient is the orbit tangent space.** At every
point `x : M`, the kernel of the differential of `Quotient.mk''` equals the orbit tangent space
`𝔤 · x`. -/
theorem ker_mfderiv_quotientMk_freeProperQuotient
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (x : M) :
    letI := freeProperQuotientChartedSpace I IG hfree
    (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG hfree
  have := isManifold_freeProperQuotient I IG hfree
  let K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  have hsub := isSubmersion_quotientMk_freeProperQuotient I IG hfree
  -- Every fundamental vector field is tangent to the fibres of `Quotient.mk''`.
  have hle : (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤
      (mfderiv I K (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) x).ker := by
    intro v hv
    obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ x).1 hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, InfinitesimalAction.fundamental_apply,
      fundamentalVectorField_apply]
    have hq_diff : MDifferentiableAt I K
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) x :=
      hsub.contMDiff.mdifferentiable (by simp) x
    have horb_diff : MDifferentiableAt IG I (fun g : G ↦ g • x) 1 :=
      (ContMDiffSMul.contMDiff_smul_const (I := IG) (I' := I) (n := ∞) x).mdifferentiable
        (by simp) 1
    have hconst : (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) ∘ (fun g : G ↦ g • x) =
        fun _ : G ↦ Quotient.mk'' x :=
      funext fun g ↦ Quotient.sound ⟨g, rfl⟩
    have hcomp := mfderiv_comp_apply_of_eq (1 : G) hq_diff horb_diff (one_smul G x) ξ
    rw [hconst, mfderiv_const, zero_apply] at hcomp
    exact hcomp.symm
  -- Equality follows from rank-nullity since `mfderiv Quotient.mk''` is surjective.
  have hO : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) =
      finrank ℝ EG :=
    (InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x
      (isotropy_eq_bot_of_freeProper (I := I) (IG := IG) hfree x)
  have hleEG : finrank ℝ EG ≤ finrank ℝ E :=
    have : Nonempty M := ⟨x⟩
    finrank_le_of_freeProper I IG hfree
  have hsurj := hsub.surjective_mfderiv (by simp) x
  have hrk := LinearMap.finrank_range_add_finrank_ker
    (mfderiv I K (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) x).toLinearMap
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  have hdim : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) =
      finrank ℝ (mfderiv I K (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) x).ker := by
    have hF : finrank ℝ (TangentSpace K (Quotient.mk'' x : MulAction.orbitRel.Quotient G M)) =
        finrank ℝ E - finrank ℝ EG := Module.finrank_fin_fun ℝ
    have hE : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
    rw [hF, hE] at hrk
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hdim).symm

variable (I IG) in
include I IG in
/-- **The quotient manifold theorem.** The orbit space of a free proper smooth action of a
finite-dimensional real Lie group on a finite-dimensional boundaryless smooth real manifold admits
a smooth manifold structure of dimension `dim M - dim G`, retaining its quotient topology, for
which the orbit projection `Quotient.mk''` is a smooth submersion. No separation or
second-countability hypotheses are needed, and `M` may be empty. -/
theorem exists_freeProperQuotient_isSubmersion
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    ∃ cs : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      Manifold.IsSubmersion I
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) :=
  ⟨freeProperQuotientChartedSpace I IG hfree,
    isManifold_freeProperQuotient I IG hfree,
    isSubmersion_quotientMk_freeProperQuotient I IG hfree⟩

end Construction

section UniquenessAndComparisons

variable {E EG H HG M G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  {I : ModelWithCorners ℝ E H} {IG : ModelWithCorners ℝ EG HG}
  [I.Boundaryless] [IG.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M]

variable (I IG) in
/-- **Uniqueness of the smooth structure on a free proper quotient.** The identity is a `C^∞`
diffeomorphism between `freeProperQuotientChartedSpace` and any other charted-space structure on
`MulAction.orbitRel.Quotient G M` for which `Quotient.mk''` is a `C^∞` submersion. -/
noncomputable def freeProperQuotientDiffeomorph
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1)
    (c : ChartedSpace H' (MulAction.orbitRel.Quotient G M))
    (hsub : letI := c; Manifold.IsSubmersion I J ∞
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)) :
    @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) J
      (MulAction.orbitRel.Quotient G M) _ (freeProperQuotientChartedSpace I IG hfree)
      (MulAction.orbitRel.Quotient G M) _ c ∞ :=
  ChartedSpace.diffeomorphOfSubmersions
    (freeProperQuotientChartedSpace I IG hfree) c Quotient.mk''_surjective
    (isSubmersion_quotientMk_freeProperQuotient I IG hfree) hsub

/-- `freeProperQuotientDiffeomorph` is the identity on points. -/
@[simp]
theorem freeProperQuotientDiffeomorph_apply
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1)
    (c : ChartedSpace H' (MulAction.orbitRel.Quotient G M))
    (hsub : letI := c; Manifold.IsSubmersion I J ∞
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M))
    (q : MulAction.orbitRel.Quotient G M) :
    freeProperQuotientDiffeomorph I IG hfree c hsub q = q :=
  ChartedSpace.diffeomorphOfSubmersions_apply _ c Quotient.mk''_surjective _ hsub q

/-- The inverse of `freeProperQuotientDiffeomorph` is the identity on points. -/
@[simp]
theorem freeProperQuotientDiffeomorph_symm_apply
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1)
    (c : ChartedSpace H' (MulAction.orbitRel.Quotient G M))
    (hsub : letI := c; Manifold.IsSubmersion I J ∞
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M))
    (q : MulAction.orbitRel.Quotient G M) :
    (@Diffeomorph.symm ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) J
      (MulAction.orbitRel.Quotient G M) _ (freeProperQuotientChartedSpace I IG hfree)
      (MulAction.orbitRel.Quotient G M) _ c ∞
      (freeProperQuotientDiffeomorph I IG hfree c hsub)) q = q :=
  ChartedSpace.diffeomorphOfSubmersions_symm_apply _ c Quotient.mk''_surjective _ hsub q

/-- Any `C^∞` manifold structure on `MulAction.orbitRel.Quotient G M` modelled on
`Fin (dim M - dim G) → ℝ` making `Quotient.mk''` a `C^∞` submersion has the same maximal atlas as
`freeProperQuotientChartedSpace`. -/
theorem maximalAtlas_freeProperQuotient_eq
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1)
    (c : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M))
    (hc : letI := c; IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M))
    (hsub : letI := c; Manifold.IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)) :
    (letI := freeProperQuotientChartedSpace I IG hfree;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) =
      (letI := c; IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) :=
  ChartedSpace.maximalAtlas_eq_of_isSubmersion
    (freeProperQuotientChartedSpace I IG hfree) c Quotient.mk''_surjective
    (isManifold_freeProperQuotient I IG hfree) hc
    (isSubmersion_quotientMk_freeProperQuotient I IG hfree) hsub

/-- **Kernel of the differential for any smooth quotient structure.** For any charted-space
structure on `MulAction.orbitRel.Quotient G M` making `Quotient.mk''` a `C^∞` submersion, the
kernel of `mfderiv Quotient.mk''` at `x` is the orbit tangent space `𝔤 · x`. -/
theorem ker_mfderiv_quotientMk_of_isSubmersion
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1)
    [c : ChartedSpace H' (MulAction.orbitRel.Quotient G M)]
    (hsub : Manifold.IsSubmersion I J ∞ (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M))
    (x : M) :
    (mfderiv I J (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x :=
  (ChartedSpace.ker_mfderiv_eq_of_isSubmersion
    (freeProperQuotientChartedSpace I IG hfree) c Quotient.mk''_surjective (by simp)
    (isSubmersion_quotientMk_freeProperQuotient I IG hfree) hsub x).symm.trans
    (ker_mfderiv_quotientMk_freeProperQuotient I IG hfree x)

variable (I IG) in
/-- **Comparison with discrete properly discontinuous quotients.** When a free proper smooth action
is also properly discontinuous, the identity is a `C^∞` diffeomorphism between
`freeProperQuotientChartedSpace` and Mathlib's `MulAction.instChartedSpaceQuotient` (made smooth by
`TauCeti.instIsManifoldQuotient`). -/
noncomputable def freeProperQuotientDiffeomorphDiscrete
    [ProperlyDiscontinuousSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M] :
    @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I
      (MulAction.orbitRel.Quotient G M) _
      (freeProperQuotientChartedSpace I IG fun _ _ ↦ IsCancelSMul.eq_one_of_smul)
      (MulAction.orbitRel.Quotient G M) _ MulAction.instChartedSpaceQuotient ∞ := by
  have : ContMDiffConstSMul I ∞ G M :=
    ⟨fun g ↦ (ContMDiffSMul.contMDiff_smul (I := IG) (I' := I) (n := ∞)).comp
      (contMDiff_const.prodMk contMDiff_id)⟩
  have hloc : IsLocalDiffeomorph I I ∞ (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) :=
    isLocalDiffeomorph_quotientMk (I := I) (n := ∞) (G := G) (M := M)
  have hsub : Manifold.IsSubmersion I I ∞
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) :=
    (hloc.contMDiff.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun x ↦
      (hloc.isInvertible_mfderiv (by simp) x).surjective).isSubmersion
  exact freeProperQuotientDiffeomorph I IG (fun _ _ ↦ IsCancelSMul.eq_one_of_smul)
    MulAction.instChartedSpaceQuotient hsub

/-- `freeProperQuotientDiffeomorphDiscrete` is the identity on points. -/
@[simp]
theorem freeProperQuotientDiffeomorphDiscrete_apply
    [ProperlyDiscontinuousSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
    (q : MulAction.orbitRel.Quotient G M) :
    freeProperQuotientDiffeomorphDiscrete I IG q = q :=
  freeProperQuotientDiffeomorph_apply _ _ _ q

/-- The inverse of `freeProperQuotientDiffeomorphDiscrete` is the identity on points. -/
@[simp]
theorem freeProperQuotientDiffeomorphDiscrete_symm_apply
    [ProperlyDiscontinuousSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
    (q : MulAction.orbitRel.Quotient G M) :
    (@Diffeomorph.symm ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I
      (MulAction.orbitRel.Quotient G M) _
      (freeProperQuotientChartedSpace I IG fun _ _ ↦ IsCancelSMul.eq_one_of_smul)
      (MulAction.orbitRel.Quotient G M) _ MulAction.instChartedSpaceQuotient ∞
      (freeProperQuotientDiffeomorphDiscrete I IG)) q = q :=
  freeProperQuotientDiffeomorph_symm_apply _ _ _ q

variable (G I IG) in
/-- **Quotient by a trivial group.** When the acting group is a subsingleton, the orbit projection
`Quotient.mk''` is a `C^∞` diffeomorphism from `M` onto `MulAction.orbitRel.Quotient G M` equipped
with `freeProperQuotientChartedSpace`. -/
noncomputable def freeProperQuotientDiffeomorphOfSubsingleton [Subsingleton G] :
    letI := freeProperQuotientChartedSpace I IG fun (g : G) (_ : M) _ ↦ Subsingleton.elim g 1
    M ≃ₘ^∞⟮I, 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)⟯ MulAction.orbitRel.Quotient G M := by
  let := freeProperQuotientChartedSpace I IG fun (g : G) (_ : M) _ ↦ Subsingleton.elim g 1
  have hbij : Bijective (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) :=
    ⟨fun x y h ↦ by
        obtain ⟨g, hg⟩ := Quotient.exact h
        simpa only [Subsingleton.elim g 1, one_smul] using hg.symm,
      Quotient.mk''_surjective⟩
  have hid_sub : Manifold.IsSubmersion I I ∞ (id : M → M) :=
    (contMDiff_id.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun x ↦ by
      rw [mfderiv_id]
      exact surjective_id).isSubmersion
  exact (Equiv.ofBijective Quotient.mk'' hbij).diffeomorphOfSubmersions
    hid_sub surjective_id
    (isSubmersion_quotientMk_freeProperQuotient I IG fun (g : G) (_ : M) _ ↦ Subsingleton.elim g 1)
    Quotient.mk''_surjective rfl

/-- For a trivial acting group, `freeProperQuotientDiffeomorphOfSubsingleton` sends each point to
its orbit. -/
@[simp]
theorem freeProperQuotientDiffeomorphOfSubsingleton_apply [Subsingleton G] (x : M) :
    letI := freeProperQuotientChartedSpace I IG fun (g : G) (_ : M) _ ↦ Subsingleton.elim g 1
    freeProperQuotientDiffeomorphOfSubsingleton G I IG x = Quotient.mk'' x := by
  let := freeProperQuotientChartedSpace I IG fun (g : G) (_ : M) _ ↦ Subsingleton.elim g 1
  exact Equiv.diffeomorphOfSubmersions_apply _ _ _ _ _ _ x

/-- For a trivial acting group, the inverse of `freeProperQuotientDiffeomorphOfSubsingleton` sends
the orbit of `x` back to `x`. -/
@[simp]
theorem freeProperQuotientDiffeomorphOfSubsingleton_symm_mk [Subsingleton G] (x : M) :
    letI := freeProperQuotientChartedSpace I IG fun (g : G) (_ : M) _ ↦ Subsingleton.elim g 1
    (freeProperQuotientDiffeomorphOfSubsingleton G I IG).symm (Quotient.mk'' x) = x := by
  let := freeProperQuotientChartedSpace I IG fun (g : G) (_ : M) _ ↦ Subsingleton.elim g 1
  simpa only [← freeProperQuotientDiffeomorphOfSubsingleton_apply (G := G) (I := I) (IG := IG) x]
    using (freeProperQuotientDiffeomorphOfSubsingleton G I IG).symm_apply_apply x

end UniquenessAndComparisons

section Descent

variable {E EG H HG M G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  {I : ModelWithCorners ℝ E H} {IG : ModelWithCorners ℝ EG HG}
  [I.Boundaryless] [IG.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M]

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]
  {m : ℕ∞ω} {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x}

/-- **Pointwise smooth descent to a free proper quotient.** For `m ≤ ∞`, the descent of a
`G`-invariant map `f : M → N` is `C^m` at `[x]` exactly when `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_iff_freeProperQuotient
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (hm : m ≤ ∞) (x : M) :
    letI := freeProperQuotientChartedSpace I IG hfree
    ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I' m
        (MulAction.orbitRelQuotientLift f hf) (Quotient.mk'' x) ↔
      ContMDiffAt I I' m f x := by
  let := freeProperQuotientChartedSpace I IG hfree
  rw [← ((isSubmersion_quotientMk_freeProperQuotient I IG hfree).isSubmersionAt x)
    |>.contMDiffAt_comp_iff hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- **Smooth descent to a free proper quotient.** For `m ≤ ∞`, the descent of a `G`-invariant map
`f : M → N` is `C^m` exactly when `f` is `C^m`. -/
theorem contMDiff_orbitRelQuotientLift_iff_freeProperQuotient
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (hm : m ≤ ∞) :
    letI := freeProperQuotientChartedSpace I IG hfree
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I' m
        (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I I' m f := by
  let := freeProperQuotientChartedSpace I IG hfree
  rw [← (isSubmersion_quotientMk_freeProperQuotient I IG hfree).contMDiff_comp_iff
    Quotient.mk''_surjective hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- **Universal property of a free proper quotient.** For `m ≤ ∞`, a `C^m` map constant on the
orbits of a free proper smooth action factors uniquely through a `C^m` map on the quotient
manifold. -/
theorem existsUnique_contMDiff_orbitRelQuotientLift_freeProperQuotient
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) (hm : m ≤ ∞)
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) (hf_smooth : ContMDiff I I' m f) :
    letI := freeProperQuotientChartedSpace I IG hfree
    ∃! g : MulAction.orbitRel.Quotient G M → N,
      ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I' m g ∧
        g ∘ (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) = f := by
  let := freeProperQuotientChartedSpace I IG hfree
  refine ⟨MulAction.orbitRelQuotientLift f hf,
    ⟨(contMDiff_orbitRelQuotientLift_iff_freeProperQuotient (I := I) (IG := IG) hfree hm).2
      hf_smooth, MulAction.orbitRelQuotientLift_comp_mk⟩,
    fun g ⟨_, hg⟩ ↦ (MulAction.eq_orbitRelQuotientLift_iff (hf := hf)).2 hg⟩

/-- **Immersion criterion on a free proper quotient.** For a finite-dimensional boundaryless target
`N`, the descent of a `G`-invariant map `f : M → N` is a `C^∞` immersion if and only if `f` is
`C^∞` and the kernel of `mfderiv f x` equals the orbit tangent space `𝔤 · x` at every `x : M`. -/
theorem isImmersion_orbitRelQuotientLift_iff_freeProperQuotient
    [FiniteDimensional ℝ E'] [I'.Boundaryless] [IsManifold I' ∞ N]
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    letI := freeProperQuotientChartedSpace I IG hfree
    Manifold.IsImmersion 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I' ∞
        (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I I' ∞ f ∧
        ∀ x : M, (mfderiv I I' f x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG hfree
  have := isManifold_freeProperQuotient I IG hfree
  rw [(isSubmersion_quotientMk_freeProperQuotient I IG hfree).isImmersion_iff_ker_mfderiv_comp
    Quotient.mk''_surjective (by simp), MulAction.orbitRelQuotientLift_comp_mk]
  simp only [ker_mfderiv_quotientMk_freeProperQuotient I IG hfree]

section Equivariant

variable {EK HK K : Type*}
  [NormedAddCommGroup EK] [NormedSpace ℝ EK] [FiniteDimensional ℝ EK]
  [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK} [IK.Boundaryless]
  [FiniteDimensional ℝ E'] [I'.Boundaryless] [IsManifold I' ∞ N]
  [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup IK ∞ K]
  [MulAction K N] [ContMDiffSMul IK I' ∞ K N] [ProperSMul K N]

/-- **Equivariant maps descend smoothly between free proper quotients.** For `m ≤ ∞`, an
equivariant `C^m` map `φ : M →ₑ[σ] N` induces a `C^m` map `MulActionHom.orbitRelQuotientMap φ`
between the quotient manifolds. -/
theorem contMDiff_orbitRelQuotientMap_freeProperQuotient
    (hfreeM : ∀ (g : G) (x : M), g • x = x → g = 1)
    (hfreeN : ∀ (k : K) (y : N), k • y = y → k = 1)
    (hm : m ≤ ∞) {σ : G → K} {φ : M →ₑ[σ] N} (hφ : ContMDiff I I' m φ) :
    letI := freeProperQuotientChartedSpace I IG hfreeM
    letI := freeProperQuotientChartedSpace I' IK hfreeN
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ EK) → ℝ) m
      (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace I IG hfreeM
  let := freeProperQuotientChartedSpace I' IK hfreeN
  rw [← (isSubmersion_quotientMk_freeProperQuotient I IG hfreeM).contMDiff_comp_iff
    Quotient.mk''_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_quotientMk_freeProperQuotient I' IK hfreeN).of_le hm).comp hφ

variable (IG IK) in
/-- **Equivariant diffeomorphisms induce diffeomorphisms of free proper quotients.** A `C^∞`
diffeomorphism `e : M ≃ₘ^∞ N` carrying the `G`-action to the `K`-action along a group isomorphism
`σ : G ≃* K` descends to a `C^∞` diffeomorphism between the quotient manifolds. -/
noncomputable def freeProperQuotientCongr
    (hfreeM : ∀ (g : G) (x : M), g • x = x → g = 1)
    (hfreeN : ∀ (k : K) (y : N), k • y = y → k = 1)
    (σ : G ≃* K) (e : M ≃ₘ^∞⟮I, I'⟯ N)
    (he : ∀ (g : G) (x : M), e (g • x) = σ g • e x) :
    letI := freeProperQuotientChartedSpace I IG hfreeM
    letI := freeProperQuotientChartedSpace I' IK hfreeN
    MulAction.orbitRel.Quotient G M ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ EK) → ℝ)⟯ MulAction.orbitRel.Quotient K N := by
  let := freeProperQuotientChartedSpace I IG hfreeM
  let := freeProperQuotientChartedSpace I' IK hfreeN
  refine
    { toEquiv := MulAction.orbitRelQuotientCongr σ e.toEquiv he
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · rw [← (isSubmersion_quotientMk_freeProperQuotient I IG hfreeM).contMDiff_comp_iff
      Quotient.mk''_surjective le_rfl]
    have hcomp : (MulAction.orbitRelQuotientCongr σ e.toEquiv he : _) ∘ Quotient.mk'' =
        Quotient.mk'' ∘ e :=
      funext fun x ↦ MulAction.orbitRelQuotientCongr_mk σ e.toEquiv he x
    rw [hcomp]
    exact (contMDiff_quotientMk_freeProperQuotient I' IK hfreeN).comp e.contMDiff
  · rw [← (isSubmersion_quotientMk_freeProperQuotient I' IK hfreeN).contMDiff_comp_iff
      Quotient.mk''_surjective le_rfl]
    have hcomp : ((MulAction.orbitRelQuotientCongr σ e.toEquiv he).symm : _) ∘ Quotient.mk'' =
        Quotient.mk'' ∘ e.symm :=
      funext fun y ↦ MulAction.orbitRelQuotientCongr_symm_mk σ e.toEquiv he y
    rw [hcomp]
    exact (contMDiff_quotientMk_freeProperQuotient I IG hfreeM).comp e.symm.contMDiff

/-- `freeProperQuotientCongr` sends `[x]` to `[e x]`. -/
@[simp]
theorem freeProperQuotientCongr_mk
    (hfreeM : ∀ (g : G) (x : M), g • x = x → g = 1)
    (hfreeN : ∀ (k : K) (y : N), k • y = y → k = 1)
    (σ : G ≃* K) (e : M ≃ₘ^∞⟮I, I'⟯ N)
    (he : ∀ (g : G) (x : M), e (g • x) = σ g • e x) (x : M) :
    letI := freeProperQuotientChartedSpace I IG hfreeM
    letI := freeProperQuotientChartedSpace I' IK hfreeN
    freeProperQuotientCongr IG IK hfreeM hfreeN σ e he (Quotient.mk'' x) =
      Quotient.mk'' (e x) :=
  MulAction.orbitRelQuotientCongr_mk σ e.toEquiv he x

/-- The inverse of `freeProperQuotientCongr` sends `[y]` to `[e.symm y]`. -/
@[simp]
theorem freeProperQuotientCongr_symm_mk
    (hfreeM : ∀ (g : G) (x : M), g • x = x → g = 1)
    (hfreeN : ∀ (k : K) (y : N), k • y = y → k = 1)
    (σ : G ≃* K) (e : M ≃ₘ^∞⟮I, I'⟯ N)
    (he : ∀ (g : G) (x : M), e (g • x) = σ g • e x) (y : N) :
    letI := freeProperQuotientChartedSpace I IG hfreeM
    letI := freeProperQuotientChartedSpace I' IK hfreeN
    (freeProperQuotientCongr IG IK hfreeM hfreeN σ e he).symm (Quotient.mk'' y) =
      Quotient.mk'' (e.symm y) :=
  MulAction.orbitRelQuotientCongr_symm_mk σ e.toEquiv he y

end Equivariant

end Descent

end TauCeti
