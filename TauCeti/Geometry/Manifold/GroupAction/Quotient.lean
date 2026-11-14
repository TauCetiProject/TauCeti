/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap
public import TauCeti.Geometry.Manifold.Algebra.TypeTags
public import TauCeti.Geometry.Manifold.GroupAction.Orbit
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
public import TauCeti.Topology.Algebra.GroupAction.Quotient
public import TauCeti.Topology.Algebra.ProperAction.Basic
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# The quotient manifold theorem for free proper Lie group actions

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on a
finite-dimensional boundaryless smooth real manifold `M`. This file equips the orbit space
`MulAction.orbitRel.Quotient G M` (with its quotient topology) with a smooth manifold structure of
dimension `dim M - dim G` (`TauCeti.freeProperQuotientChartedSpace`,
`TauCeti.isManifold_freeProperQuotient`) for which the orbit projection
`Quotient.mk (MulAction.orbitRel G M)` is a smooth submersion with fibre complement `EG`
(`TauCeti.isSubmersionOfComplement_freeProperQuotientMk`,
`TauCeti.isSubmersion_freeProperQuotientMk`) whose vertical tangent space at every `x : M` is the
orbit tangent space `𝔤 · x` (`TauCeti.ker_mfderiv_freeProperQuotientMk`).

The charts are built from the transverse chart slices of
`TauCeti.Geometry.Manifold.GroupAction.TransverseSlice` and glued via
`TauCeti.Geometry.Manifold.Gluing.Basic`:
* freeness gives trivial stabilizers and properness makes `M` Hausdorff, so the isotropy Lie
  algebra vanishes at every `x : M`
  (`TauCeti.isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot`);
* choosing a linear complement `W` of `𝔤 · x` in `T_x M` gives a transverse chart slice whose slice
  map `(g, u) ↦ g • τ u` is a smooth local diffeomorphism at `(1, 0)`
  (`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`), hence along `G × U` for a small open
  neighbourhood `U` of `0` in `Fin (dim M - dim G) → ℝ`
  (`IsLocalDiffeomorphAt.eventually_forall_smul_slice`);
* properness and triviality of stabilizers shrink `U` further so that the slice map is injective on
  `G × U` (`ProperSMul.exists_mem_nhds_injOn_smul_slice`), making `u ↦ [τ u]` an open embedding of
  `U` into `M ⧸ G` (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`);
* the smoothness of overlap transitions and of the orbit projection is read off from the smooth
  local inverses of slice maps (`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`), gluing the
  open slice pieces via `TauCeti.chartedSpaceOfIsOpenEmbedding` and
  `TauCeti.isManifold_chartedSpaceOfIsOpenEmbedding`.

Neither Hausdorffness nor second-countability needs to be assumed: `T2Space G` follows from the Lie
group structure (`ModelWithCorners.t2Space_of_lieGroup`), `T2Space M` and
`T2Space (MulAction.orbitRel.Quotient G M)` follow from properness
(`t2Space_of_properSMul_of_t1Group`, `t2Space_quotient_mulAction_of_properSMul`), and when `M` is
second countable `ContinuousConstSMul.secondCountableTopology` (and
`ContinuousConstVAdd.secondCountableTopology`; see also
`Topology.IsOpenQuotientMap.secondCountableTopology`) supplies `SecondCountableTopology` on the
orbit space. The manifold `M` may be empty; when `M` is nonempty, `dim G ≤ dim M`
(`TauCeti.finrank_le_of_properSMul_of_isCancelSMul`,
`TauCeti.finrank_le_of_properVAdd_of_isCancelVAdd`).

`TauCeti.freeProperQuotientChartedSpace` is an `@[instance_reducible]` definition rather than a
global `ChartedSpace` instance: its model space `Fin (dim E - dim EG) → ℝ` depends on `E` and `EG`,
which cannot be inferred from `MulAction.orbitRel.Quotient G M`, and when `G` is discrete
(`dim EG = 0`) a global instance would create a diamond with `MulAction.instChartedSpaceQuotient`.

For a free proper smooth action of `G` on `M`, by `Equiv.diffeomorphOfSubmersions` any surjective
smooth submersion `p : M → Q` whose fibres are the `G`-orbits induces a canonical diffeomorphism
`(M ⧸ G) ≃ₘ Q` (`TauCeti.diffeomorphOfOrbitSubmersion`), and any `C^m` (`m ≠ 0`) submersion at `x`
whose fibres are the `G`-orbits has vertical kernel `𝔤 · x`
(`TauCeti.ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt`). Smoothness of `G`-invariant
`C^m` maps (`m ≤ ∞`) descends to the orbit space
(`TauCeti.contMDiff_orbitRelQuotientLift_iff_of_properSMul_of_isCancelSMul`,
`TauCeti.existsUnique_contMDiff_comp_freeProperQuotientMk_eq`), equivariant maps and `C^m`
diffeomorphisms descend functorially
(`TauCeti.contMDiff_orbitRelQuotientMap_of_properSMul_of_isCancelSMul`,
`TauCeti.freeProperQuotientDiffeomorph`), and the additive Lie group counterpart on
`AddAction.orbitRel.Quotient G M` is obtained by pulling back the multiplicative atlas of
`Multiplicative G` (`TauCeti.freeProperAddQuotientDiffeomorphMultiplicative`).

## Main definitions

* `TauCeti.freeProperQuotientChartedSpace`: the slice-chart atlas on
  `MulAction.orbitRel.Quotient G M` for a free proper smooth Lie group action.
* `TauCeti.diffeomorphOfOrbitSubmersion`: for a free proper smooth Lie group action, the canonical
  diffeomorphism `(M ⧸ G) ≃ₘ Q` induced by any surjective smooth submersion `p : M → Q` whose
  fibres are the `G`-orbits.
* `TauCeti.freeProperQuotientDiffeomorph`, `TauCeti.freeProperAddQuotientDiffeomorph`: the `C^m`
  diffeomorphism of free-proper orbit manifolds induced by an equivariant `C^m` diffeomorphism
  (`m ≤ ∞`).
* `TauCeti.freeProperAddQuotientChartedSpace`,
  `TauCeti.freeProperAddQuotientDiffeomorphMultiplicative`,
  `TauCeti.diffeomorphOfAddOrbitSubmersion`: the additive free proper Lie group action counterparts
  on `AddAction.orbitRel.Quotient G M`.

## Main results

* `TauCeti.isManifold_freeProperQuotient`,
  `TauCeti.isSubmersionOfComplement_freeProperQuotientMk`,
  `TauCeti.isSubmersion_freeProperQuotientMk`, `TauCeti.ker_mfderiv_freeProperQuotientMk`,
  `TauCeti.exists_freeProperQuotient_isSubmersion`: the quotient manifold theorem for free proper
  Lie group actions.
* `TauCeti.ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt`,
  `TauCeti.ker_mfderiv_eq_orbitTangent_fundamental_multiplicative_of_isSubmersionAt`: for a free
  proper smooth (multiplicative or additive) Lie group action, identification of `ker dp_x` with
  `𝔤 · x` for any `C^m` (`m ≠ 0`) submersion at `x` whose fibres are the orbits.
* `TauCeti.contMDiffAt_orbitRelQuotientLift_iff_of_properSMul_of_isCancelSMul`,
  `TauCeti.contMDiff_orbitRelQuotientLift_iff_of_properSMul_of_isCancelSMul`,
  `TauCeti.existsUnique_contMDiff_comp_freeProperQuotientMk_eq`,
  `TauCeti.contMDiff_orbitRelQuotientMap_of_properSMul_of_isCancelSMul`: smooth descent and
  equivariant maps.
* `TauCeti.isManifold_freeProperAddQuotient`,
  `TauCeti.isSubmersionOfComplement_freeProperAddQuotientMk`,
  `TauCeti.isSubmersion_freeProperAddQuotientMk`, `TauCeti.ker_mfderiv_freeProperAddQuotientMk`,
  `TauCeti.exists_contMDiffOn_section_freeProperAddQuotientMk`,
  `TauCeti.contMDiff_addOrbitRelQuotientLift_iff_of_properVAdd_of_isCancelVAdd`,
  `TauCeti.contMDiff_addOrbitRelQuotientMap_of_properVAdd_of_isCancelVAdd`,
  `TauCeti.exists_freeProperAddQuotient_isSubmersion`: the additive quotient manifold theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 4.31
  (uniqueness of quotient manifold structures) and Theorem 21.10 (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto (2003),
  Theorem 1.21.
-/

public section

noncomputable section

open Function Set Filter Manifold Topology
open scoped ContDiff Manifold

namespace TauCeti

/-! ### Transverse slice charts of a free proper Lie group action -/

namespace FreeProperQuotient

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E EG H HG M G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- The quotient model space `ℝ^(dim M - dim G)` of `M ⧸ G`. -/
private abbrev ModelSpace (E EG : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] : Type :=
  Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ

/-- Bundled transverse slice data through a point `x : M`: a smooth slice
`τ : (Fin (dim E - dim EG) → ℝ) → M` sending `0` to `x`, together with an open neighbourhood `U` of
`0` on which `τ` is smooth and the slice map `(g, u) ↦ g • τ u` is injective and a smooth local
diffeomorphism on `G × U`. -/
private structure SliceData (x : M) where
  τ : ModelSpace E EG → M
  U : Set (ModelSpace E EG)
  isOpen_U : IsOpen U
  zero_mem_U : (0 : ModelSpace E EG) ∈ U
  τ_zero : τ 0 = x
  contMDiffOn_τ : ContMDiffOn 𝓘(ℝ, ModelSpace E EG) I ∞ τ U
  injOn_smul : InjOn (fun p : G × ModelSpace E EG ↦ p.1 • τ p.2) (univ ×ˢ U)
  isLocalDiffeomorphOn_smul :
    IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, ModelSpace E EG)) I ∞
      (fun p : G × ModelSpace E EG ↦ p.1 • τ p.2) (univ ×ˢ U)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ EG] [I.Boundaryless] [IsManifold I ∞ M] in
/-- Shrink a smooth slice `τ : S → M` whose slice map `(g, s) ↦ g • τ s` is a smooth local
diffeomorphism at `(1, s₀)` to an open neighbourhood `U ⊆ D` of `s₀` on which `τ` is smooth and the
slice map is injective and a smooth local diffeomorphism on `G × U`. -/
private theorem exists_isOpen_slice_of_isLocalDiffeomorphAt {ES HS S : Type*}
    [NormedAddCommGroup ES] [NormedSpace ℝ ES] [TopologicalSpace HS]
    {JS : ModelWithCorners ℝ ES HS} [TopologicalSpace S] [ChartedSpace HS S]
    {τ : S → M} {D : Set S} {s₀ : S} (hD_open : IsOpen D) (hs₀D : s₀ ∈ D)
    (hτ_smooth : ContMDiffOn JS I ∞ τ D)
    (hloc : IsLocalDiffeomorphAt (IG.prod JS) I ∞ (fun p : G × S ↦ p.1 • τ p.2) (1, s₀)) :
    ∃ U : Set S, IsOpen U ∧ s₀ ∈ U ∧ ContMDiffOn JS I ∞ τ U ∧
      InjOn (fun p : G × S ↦ p.1 • τ p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (IG.prod JS) I ∞ (fun p : G × S ↦ p.1 • τ p.2) (univ ×ˢ U) := by
  obtain ⟨N, hN, hinjN⟩ := hloc.exists_mem_nhds_injOn
  have hτ_cont : ContinuousAt τ s₀ := (hτ_smooth.contMDiffAt (hD_open.mem_nhds hs₀D)).continuousAt
  obtain ⟨V, hV, hinjV⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice hτ_cont
    (IsCancelSMul.stabilizer_eq_bot (τ s₀)) hN hinjN
  obtain ⟨U, hU_sub, hU_open, hs₀U⟩ := mem_nhds_iff.1
    (inter_mem (hD_open.mem_nhds hs₀D) (inter_mem hloc.eventually_forall_smul_slice hV))
  exact ⟨U, hU_open, hs₀U, hτ_smooth.mono fun _ hu ↦ (hU_sub hu).1,
    hinjV.mono (prod_mono_right fun _ hu ↦ (hU_sub hu).2.2),
    fun ⟨⟨g, _⟩, _, hu⟩ ↦ (hU_sub hu).2.1 g⟩

/-- Existence of a transverse slice chart through any `x : M`. -/
private theorem nonempty_sliceData (x : M) : Nonempty (SliceData I IG (G := G) x) := by
  have := FiniteDimensional.completeSpace ℝ E
  have := FiniteDimensional.completeSpace ℝ EG
  have hx := isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot (I := IG) (I' := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)
  -- `TangentSpace I x` is `E` by definition, so `orbitTangent x` is a submodule of `E`.
  let O : Submodule ℝ E := (InfinitesimalAction.fundamental IG G I M).orbitTangent x
  obtain ⟨W, hW⟩ := O.exists_isCompl
  have hdimW : Module.finrank ℝ (ModelSpace E EG) = Module.finrank ℝ W := by
    have hO : Module.finrank ℝ O = Module.finrank ℝ EG :=
      ((InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot
        x hx).trans (finrank_tangentSpace (1 : G))
    have hsum := Submodule.finrank_add_eq_of_isCompl hW
    rw [hO] at hsum
    rw [Module.finrank_fin_fun ℝ]
    omega
  let L : ModelSpace E EG ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq hdimW
  let φ := extChartAt I x
  let α : ModelSpace E EG → E := fun u ↦ φ x + (L u : E)
  have hα_smooth : ContMDiff 𝓘(ℝ, ModelSpace E EG) 𝓘(ℝ, E) ∞ α :=
    (contDiff_const.add (W.subtypeL.comp (L : ModelSpace E EG →L[ℝ] W)).contDiff).contMDiff
  have hα0 : α 0 = φ x := by simp [α]
  let τ : ModelSpace E EG → M := φ.symm ∘ α
  have hτ0 : τ 0 = x := by simp only [τ, φ, comp_apply, hα0, extChartAt_to_inv]
  -- Transport `isLocalDiffeomorphAt_smul_extChartAt_symm` along `id × L` (conjugating by `prodComm`
  -- because `Diffeomorph.prodCongr` allows distinct normed spaces only in the first factor).
  let T : (G × ModelSpace E EG) ≃ₘ⟮IG.prod 𝓘(ℝ, ModelSpace E EG), IG.prod 𝓘(ℝ, W)⟯ G × W :=
    (Diffeomorph.prodComm _ _ _ _ ∞).trans
      ((L.toDiffeomorph.prodCongr (Diffeomorph.refl IG G ∞)).trans
        (Diffeomorph.prodComm _ _ _ _ ∞))
  have hT0 : T (1, 0) = (1, 0) := by simp [T]
  have hcomp_eq : (fun p : G × ModelSpace E EG ↦ p.1 • τ p.2) =
      (fun p : G × W ↦ p.1 • φ.symm (φ x + p.2)) ∘ T := by
    ext ⟨g, u⟩
    simp [T, τ, α]
  have hloc0 : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, ModelSpace E EG)) I ∞
      (fun p : G × ModelSpace E EG ↦ p.1 • τ p.2) (1, 0) := by
    rw [hcomp_eq]
    exact IsLocalDiffeomorphAt.comp (hf := T.isLocalDiffeomorph (1, 0))
      (hg := hT0.symm ▸ isLocalDiffeomorphAt_smul_extChartAt_symm (I := IG) (I' := I) (G := G)
        hx hW)
  obtain ⟨U, hU_open, h0U, hτ_on, hinj, hloc⟩ :=
    exists_isOpen_slice_of_isLocalDiffeomorphAt I IG
      ((isOpen_extChartAt_target x).preimage hα_smooth.continuous)
      (by rw [mem_preimage, hα0]; exact mem_extChartAt_target x)
      ((contMDiffOn_extChartAt_symm x).comp hα_smooth.contMDiffOn fun _ hu ↦ hu) hloc0
  exact ⟨⟨τ, U, hU_open, h0U, hτ0, hτ_on, hinj, hloc⟩⟩

/-- Chosen transverse slice data through `x : M`. -/
private def sliceData (x : M) : SliceData I IG (G := G) x :=
  (nonempty_sliceData I IG x).some

/-- The open slice domain `U ⊆ ℝ^(dim M - dim G)` of `sliceData x`, bundled as `Opens`. -/
private def sliceOpens (x : M) : TopologicalSpace.Opens (ModelSpace E EG) :=
  ⟨(sliceData I IG (G := G) x).U, (sliceData I IG (G := G) x).isOpen_U⟩

/-- The slice chart embedding `u ↦ [τ u]` from `sliceOpens x` into `M ⧸ G`. -/
private def sliceMap (x : M) (u : sliceOpens I IG (G := G) x) :
    MulAction.orbitRel.Quotient G M :=
  Quotient.mk (MulAction.orbitRel G M) ((sliceData I IG (G := G) x).τ u)

private theorem sliceMap_eq_comp (x : M) :
    sliceMap I IG (G := G) x =
      Quotient.mk (MulAction.orbitRel G M) ∘ (sliceData I IG (G := G) x).τ ∘ Subtype.val :=
  rfl

/-- Every `sliceMap x` is an open embedding into `M ⧸ G`. -/
private theorem isOpenEmbedding_sliceMap (x : M) :
    IsOpenEmbedding (sliceMap I IG (G := G) x) :=
  let s := sliceData I IG (G := G) x
  MulAction.isOpenEmbedding_quotientMk_slice s.isOpen_U s.injOn_smul
    s.isLocalDiffeomorphOn_smul.isLocalHomeomorphOn

/-- The images of the open embeddings `sliceMap x` cover `M ⧸ G`. -/
private theorem exists_sliceMap_eq (q : MulAction.orbitRel.Quotient G M) :
    ∃ (x : M) (u : sliceOpens I IG (G := G) x), sliceMap I IG (G := G) x u = q :=
  ⟨q.out, ⟨0, (sliceData I IG (G := G) q.out).zero_mem_U⟩,
    (congrArg (Quotient.mk (MulAction.orbitRel G M))
      (sliceData I IG (G := G) q.out).τ_zero).trans (Quotient.out_eq q)⟩

/-- Lift `exists_contMDiffAt_quotientMk_slice_eq_iff` to a smooth map into `sliceOpens y`: if
`f : P → M` is smooth at `z` and `sliceMap y v = [f z]`, then near `z` the orbit `[f z']` equals
`sliceMap y (T z')` for a map `T : P → sliceOpens y` smooth at `z`. -/
private theorem exists_contMDiffAt_sliceMap_comp_eventuallyEq
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {LP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
    {f : P → M} {z : P} (hf : ContMDiffAt LP I ∞ f z)
    (y : M) (v : sliceOpens I IG (G := G) y)
    (hfv : sliceMap I IG (G := G) y v = Quotient.mk (MulAction.orbitRel G M) (f z)) :
    ∃ T : P → sliceOpens I IG (G := G) y,
      ContMDiffAt LP 𝓘(ℝ, ModelSpace E EG) ∞ T z ∧
      sliceMap I IG (G := G) y ∘ T =ᶠ[𝓝 z] Quotient.mk (MulAction.orbitRel G M) ∘ f := by
  let sy := sliceData I IG (G := G) y
  obtain ⟨t, ht_diff, -, ht_ev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff sy.isOpen_U
    sy.injOn_smul sy.isLocalDiffeomorphOn_smul hf v.2 hfv
  classical
  let T : P → sliceOpens I IG (G := G) y := fun z' ↦
    if h : t z' ∈ sy.U then ⟨t z', h⟩ else v
  have hT_val : Subtype.val ∘ T =ᶠ[𝓝 z] t := by
    filter_upwards [ht_ev] with z' ⟨htz', _⟩
    simp only [comp_apply, T, dite_eq_left htz']
  refine ⟨T, (_root_.ContMDiffAt.subtypeVal_comp_iff (sliceOpens I IG (G := G) y) T z).1
    (ht_diff.congr_of_eventuallyEq hT_val), ?_⟩
  filter_upwards [ht_ev] with z' ⟨htz', hiff⟩
  simp only [comp_apply, sliceMap, T, dite_eq_left htz']
  exact (hiff (t z') htz').2 rfl

/-- Overlap transitions between `sliceMap` embeddings are smooth. -/
private theorem exists_contMDiffAt_sliceMap_transition
    (x y : M) (u : sliceOpens I IG (G := G) x) (v : sliceOpens I IG (G := G) y)
    (huv : sliceMap I IG (G := G) x u = sliceMap I IG (G := G) y v) :
    ∃ T : sliceOpens I IG (G := G) x → sliceOpens I IG (G := G) y,
      ContMDiffAt 𝓘(ℝ, ModelSpace E EG) 𝓘(ℝ, ModelSpace E EG) ∞ T u ∧
      sliceMap I IG (G := G) y ∘ T =ᶠ[𝓝 u] sliceMap I IG (G := G) x := by
  let sx := sliceData I IG (G := G) x
  have hτx : ContMDiffAt 𝓘(ℝ, ModelSpace E EG) I ∞ (sx.τ ∘ Subtype.val) u :=
    (sx.contMDiffOn_τ.contMDiffAt (sx.isOpen_U.mem_nhds u.2)).comp u
      (contMDiff_subtype_val (U := sliceOpens I IG (G := G) x)).contMDiffAt
  exact exists_contMDiffAt_sliceMap_comp_eventuallyEq I IG hτx y v huv.symm

end FreeProperQuotient

/-! ### The quotient manifold theorem -/

section QuotientManifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless]
  {G M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

include I IG G in
omit [I.Boundaryless] in
/-- When a Lie group `G` acts smoothly, freely and properly on a nonempty boundaryless manifold `M`,
we have `dim G ≤ dim M`. -/
theorem finrank_le_of_properSMul_of_isCancelSMul [BoundarylessManifold I M] [Nonempty M] :
    Module.finrank ℝ EG ≤ Module.finrank ℝ E := by
  obtain ⟨x⟩ := ‹Nonempty M›
  have hle := (InfinitesimalAction.fundamental IG G I M).finrank_le_of_isotropy_eq_bot
    (isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot (I := IG) (I' := I)
      (IsCancelSMul.stabilizer_eq_bot x))
  rwa [finrank_tangentSpace] at hle

variable (G M) in
/-- **The transverse-slice atlas on `M ⧸ G`.** For a free proper smooth action of a
finite-dimensional real Lie group `G` on a finite-dimensional boundaryless smooth real manifold `M`,
this equips `MulAction.orbitRel.Quotient G M` (carrying its quotient topology) with charts valued in
`Fin (dim E - dim EG) → ℝ`. It is marked `@[instance_reducible]` rather than registered as a global
instance because the model space depends on `E` and `EG`. -/
@[instance_reducible]
def freeProperQuotientChartedSpace :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding (FreeProperQuotient.isOpenEmbedding_sliceMap I IG (G := G))
    (FreeProperQuotient.exists_sliceMap_eq I IG (G := G))

/-- **Smoothness of the quotient manifold.** Equipped with `freeProperQuotientChartedSpace`, the
orbit space `MulAction.orbitRel.Quotient G M` is a smooth (`C^∞`) manifold. -/
theorem isManifold_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding
    (FreeProperQuotient.isOpenEmbedding_sliceMap I IG (G := G))
    (FreeProperQuotient.exists_sliceMap_eq I IG (G := G))
    (FreeProperQuotient.exists_contMDiffAt_sliceMap_transition I IG (G := G))

/-- The orbit projection `M → M ⧸ G` is smooth for `freeProperQuotientChartedSpace`. -/
theorem contMDiff_freeProperQuotientMk :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiff I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace I IG G M
  intro x
  let s := FreeProperQuotient.sliceData I IG (G := G) x
  obtain ⟨T, hT, hT_eq⟩ := FreeProperQuotient.exists_contMDiffAt_sliceMap_comp_eventuallyEq I IG
    (contMDiffAt_id (I := I) (x := x)) x ⟨0, s.zero_mem_U⟩
    (congrArg (Quotient.mk (MulAction.orbitRel G M)) s.τ_zero)
  have hφ := contMDiff_chartedSpaceOfIsOpenEmbedding
    (I := 𝓘(ℝ, FreeProperQuotient.ModelSpace E EG)) (n := ∞)
    (FreeProperQuotient.isOpenEmbedding_sliceMap I IG (G := G))
    (FreeProperQuotient.exists_sliceMap_eq I IG (G := G))
    (FreeProperQuotient.exists_contMDiffAt_sliceMap_transition I IG (G := G)) x
  exact ((hφ (T x)).comp x hT).congr_of_eventuallyEq hT_eq.symm

/-- At every `x : M`, the differential of the orbit projection `M → M ⧸ G` is surjective. -/
theorem surjective_mfderiv_freeProperQuotientMk (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    Surjective (mfderiv I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x) := by
  let := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG (G := G) (M := M)
  let s := FreeProperQuotient.sliceData I IG (G := G) x
  let u₀ : FreeProperQuotient.sliceOpens I IG (G := G) x := ⟨0, s.zero_mem_U⟩
  let JQ := 𝓘(ℝ, FreeProperQuotient.ModelSpace E EG)
  have hloc := isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding (I := JQ) (n := ∞)
    (FreeProperQuotient.isOpenEmbedding_sliceMap I IG (G := G))
    (FreeProperQuotient.exists_sliceMap_eq I IG (G := G))
    (FreeProperQuotient.exists_contMDiffAt_sliceMap_transition I IG (G := G)) x u₀
  have hsurj_comp := (hloc.isInvertible_mfderiv (by simp)).surjective
  rw [FreeProperQuotient.sliceMap_eq_comp] at hsurj_comp
  have hτ_diff : MDifferentiableAt JQ I (s.τ ∘ Subtype.val) u₀ :=
    ((s.contMDiffOn_τ.contMDiffAt (s.isOpen_U.mem_nhds u₀.2)).comp u₀
      (contMDiff_subtype_val (U := FreeProperQuotient.sliceOpens I IG (G := G) x)).contMDiffAt)
      |>.mdifferentiableAt (by simp)
  have hq_diff : MDifferentiableAt I JQ (Quotient.mk (MulAction.orbitRel G M)) (s.τ u₀) :=
    ((contMDiff_freeProperQuotientMk I IG (G := G) (M := M)) (s.τ u₀)).mdifferentiableAt (by simp)
  rw [mfderiv_comp u₀ hq_diff hτ_diff, ContinuousLinearMap.coe_comp] at hsurj_comp
  have hsurj_τ0 := hsurj_comp.of_comp
  rwa [comp_apply, s.τ_zero] at hsurj_τ0

/-- **The orbit projection is a smooth submersion with fibre complement `EG`.** Even when `M` is
empty, the orbit projection has the submersion normal form with complement `EG`. -/
theorem isSubmersionOfComplement_freeProperQuotientMk :
    letI := freeProperQuotientChartedSpace I IG G M
    IsSubmersionOfComplement EG I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG (G := G) (M := M)
  by_cases hM : Nonempty M
  · have hle : Module.finrank ℝ EG ≤ Module.finrank ℝ E :=
      finrank_le_of_properSMul_of_isCancelSMul I IG (G := G) (M := M)
    have hsub := (contMDiff_freeProperQuotientMk I IG (G := G) (M := M))
      |>.isSubmersionOfComplement_of_surjective_mfderiv (by simp)
        (surjective_mfderiv_freeProperQuotientMk I IG (G := G) (M := M))
    have hdim : Module.finrank ℝ
        (Fin (Module.finrank ℝ E -
          Module.finrank ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)) → ℝ) =
        Module.finrank ℝ EG := by
      simp only [Module.finrank_fin_fun]
      omega
    let K := ContinuousLinearEquiv.ofFinrankEq hdim
    exact (IsSubmersionOfComplement.congr_F K).1 hsub
  · rw [not_nonempty_iff] at hM
    exact isSubmersionOfComplement_iff.2 fun x ↦ isEmptyElim x

/-- **The orbit projection of a free proper smooth Lie group action is a smooth submersion.** -/
theorem isSubmersion_freeProperQuotientMk :
    letI := freeProperQuotientChartedSpace I IG G M
    IsSubmersion I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) :=
  letI := freeProperQuotientChartedSpace I IG G M
  (isSubmersionOfComplement_freeProperQuotientMk I IG (G := G) (M := M)).isSubmersion

/-- **The vertical tangent space of `M → M ⧸ G` is the orbit tangent space.** At every `x : M`, the
kernel of the differential of `Quotient.mk (MulAction.orbitRel G M)` equals `𝔤 · x`. -/
theorem ker_mfderiv_freeProperQuotientMk (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    (mfderiv I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG (G := G) (M := M)
  have : Nonempty M := ⟨x⟩
  have hle : Module.finrank ℝ EG ≤ Module.finrank ℝ E :=
    finrank_le_of_properSMul_of_isCancelSMul I IG (G := G) (M := M)
  refine ker_mfderiv_eq_orbitTangent_fundamental
    (isotropy_fundamental_eq_bot_of_properSMul_of_stabilizer_eq_bot (I := IG) (I' := I)
      (IsCancelSMul.stabilizer_eq_bot x))
    (((contMDiff_freeProperQuotientMk I IG (G := G) (M := M)) x).mdifferentiableAt (by simp))
    (Eventually.of_forall fun g ↦ MulAction.orbitRel.Quotient.quotient_smul_eq)
    (surjective_mfderiv_freeProperQuotientMk I IG x) ?_
  rw [Module.finrank_fin_fun]
  omega

/-- Over an open neighbourhood of `[x]` in `M ⧸ G`, the orbit projection admits a smooth local
section sending `[x]` to `x`. -/
theorem exists_contMDiffOn_section_freeProperQuotientMk (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    ∃ U : Set (MulAction.orbitRel.Quotient G M),
      IsOpen U ∧ Quotient.mk (MulAction.orbitRel G M) x ∈ U ∧
      ∃ s : MulAction.orbitRel.Quotient G M → M,
        s (Quotient.mk (MulAction.orbitRel G M) x) = x ∧
        ContMDiffOn 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) I ∞ s U ∧
        ∀ q ∈ U, Quotient.mk (MulAction.orbitRel G M) (s q) = q :=
  letI := freeProperQuotientChartedSpace I IG G M
  ((isSubmersion_freeProperQuotientMk I IG (G := G) (M := M)).isSubmersionAt
    x).exists_contMDiffOn_section

/-- **The quotient manifold theorem for free proper Lie group actions.** Let a finite-dimensional
real Lie group `G` act smoothly, freely and properly on a finite-dimensional boundaryless smooth
real manifold `M`. Then the orbit space `MulAction.orbitRel.Quotient G M`, with its quotient
topology, admits a smooth (`C^∞`) manifold structure of dimension `dim E - dim EG` for which the
orbit projection is a smooth submersion. No explicit separation or countability hypotheses are
needed, and `M` may be empty. -/
theorem exists_freeProperQuotient_isSubmersion
    {E EG H HG M G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace H] [TopologicalSpace HG]
    (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
    [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
    [MulAction G M] [ProperSMul G M]
    (hsm : ContMDiff (IG.prod I) I ∞ (fun gx : G × M ↦ gx.1 • gx.2))
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    ∃ cs : ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
        (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      IsSubmersion I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) := by
  let : ContMDiffSMul IG I ∞ G M := ⟨hsm⟩
  let : IsCancelSMul G M := isCancelSMul_iff_eq_one_of_smul_eq.2 hfree
  exact ⟨freeProperQuotientChartedSpace I IG G M,
    isManifold_freeProperQuotient I IG,
    isSubmersion_freeProperQuotientMk I IG⟩

end QuotientManifold

/-! ### Smooth descent, universal property and equivariant maps -/

section Descent

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless]
  {G M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  {m : ℕ∞ω}

/-- For a free proper smooth Lie group action and `m ≤ ∞`, the descent
`MulAction.orbitRelQuotientLift f hf` of a `G`-invariant map `f : M → N` is `C^m` at `[x]`
exactly when `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_iff_of_properSMul_of_isCancelSMul (hm : m ≤ ∞) {f : M → N}
    {hf : ∀ (g : G) (x : M), f (g • x) = f x} {x : M} :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) IN m
      (MulAction.orbitRelQuotientLift f hf)
      (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I IN m f x := by
  let := freeProperQuotientChartedSpace I IG G M
  rw [← (((isSubmersion_freeProperQuotientMk I IG (G := G) (M := M)).isSubmersionAt
    x).contMDiffAt_comp_iff hm), MulAction.orbitRelQuotientLift_comp_mk]

/-- **Smooth descent to the orbit space.** For a free proper smooth Lie group action and `m ≤ ∞`,
the descent `MulAction.orbitRelQuotientLift f hf` of a `G`-invariant map `f : M → N` is `C^m` on
`M ⧸ G` exactly when `f` is `C^m` on `M`. -/
theorem contMDiff_orbitRelQuotientLift_iff_of_properSMul_of_isCancelSMul (hm : m ≤ ∞) {f : M → N}
    {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) IN m
      (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I IN m f := by
  let := freeProperQuotientChartedSpace I IG G M
  rw [← ((isSubmersion_freeProperQuotientMk I IG (G := G) (M := M)).contMDiff_comp_iff
    Quotient.mk_surjective hm), MulAction.orbitRelQuotientLift_comp_mk]

/-- **Universal property of the free-proper quotient manifold.** Every `G`-invariant `C^m` map
(`m ≤ ∞`) `f : M → N` factors uniquely through `Quotient.mk (MulAction.orbitRel G M)` as a `C^m` map
on `M ⧸ G`. -/
theorem existsUnique_contMDiff_comp_freeProperQuotientMk_eq (hm : m ≤ ∞) {f : M → N}
    (hf_diff : ContMDiff I IN m f) (hf_inv : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace I IG G M
    ∃! f' : MulAction.orbitRel.Quotient G M → N,
      ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) IN m f' ∧
        f' ∘ Quotient.mk (MulAction.orbitRel G M) = f := by
  let := freeProperQuotientChartedSpace I IG G M
  refine (isSubmersion_freeProperQuotientMk I IG (G := G) (M := M)).existsUnique_contMDiff_comp_eq
    Quotient.mk_surjective hm hf_diff ?_
  rintro x y hxy
  obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.1 (Quotient.exact hxy)
  exact hf_inv g y

/-- **Canonical diffeomorphism with any orbit submersion.** For a free proper smooth Lie group
action of `G` on `M`, if `p : M → Q` is a surjective smooth submersion whose fibres are the
`G`-orbits (`p x = p y ↔ ∃ g : G, g • y = x`), then `p` descends to a diffeomorphism `(M ⧸ G) ≃ₘ Q`
sending `[x]` to `p x`. -/
def diffeomorphOfOrbitSubmersion
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • y = x) :
    letI := freeProperQuotientChartedSpace I IG G M
    MulAction.orbitRel.Quotient G M ≃ₘ⟮𝓘(ℝ,
      Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ), JQ⟯ Q :=
  letI := freeProperQuotientChartedSpace I IG G M
  let e : MulAction.orbitRel.Quotient G M ≃ Q :=
    (Quotient.congrRight fun x y ↦
      (MulAction.orbitRel_apply.trans MulAction.mem_orbit_iff).trans (hfib x y).symm).trans
      (Setoid.quotientKerEquivOfSurjective p hp_surj)
  e.diffeomorphOfSubmersions (isSubmersion_freeProperQuotientMk I IG) Quotient.mk_surjective hp
    (funext fun _ ↦ rfl)

/-- `diffeomorphOfOrbitSubmersion` sends the orbit `[x]` to `p x`. -/
@[simp]
theorem diffeomorphOfOrbitSubmersion_mk
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • y = x) (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    diffeomorphOfOrbitSubmersion I IG p hp hp_surj hfib
      (Quotient.mk (MulAction.orbitRel G M) x) = p x := by
  let := freeProperQuotientChartedSpace I IG G M
  rw [diffeomorphOfOrbitSubmersion, Equiv.diffeomorphOfSubmersions_apply]
  -- Both `Quotient.congrRight` and `Setoid.quotientKerEquivOfSurjective` compute on `Quotient.mk`
  -- by `Quot.lift_beta`, so `(e ∘ Quotient.mk _) x` is definitionally `p x`.
  rfl

/-- Composing `diffeomorphOfOrbitSubmersion` with the orbit projection recovers `p`. -/
@[simp]
theorem diffeomorphOfOrbitSubmersion_comp_mk
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • y = x) :
    letI := freeProperQuotientChartedSpace I IG G M
    ⇑(diffeomorphOfOrbitSubmersion I IG p hp hp_surj hfib) ∘
      Quotient.mk (MulAction.orbitRel G M) = p := by
  let := freeProperQuotientChartedSpace I IG G M
  ext x
  exact diffeomorphOfOrbitSubmersion_mk I IG p hp hp_surj hfib x

/-- The inverse of `diffeomorphOfOrbitSubmersion` sends `p x` back to `[x]`. -/
@[simp]
theorem diffeomorphOfOrbitSubmersion_symm_apply
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • y = x) (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    (diffeomorphOfOrbitSubmersion I IG p hp hp_surj hfib).symm (p x) =
      Quotient.mk (MulAction.orbitRel G M) x := by
  let := freeProperQuotientChartedSpace I IG G M
  exact (diffeomorphOfOrbitSubmersion I IG p hp hp_surj hfib).symm_apply_eq.2
    (diffeomorphOfOrbitSubmersion_mk I IG p hp hp_surj hfib x).symm

/-- For a free proper smooth Lie group action of `G` on `M`, if `p : M → Q` is a `C^m` (`m ≠ 0`)
submersion at `x` whose fibres are the `G`-orbits, then its vertical tangent space at `x` is the
orbit tangent space `ker dp_x = 𝔤 · x`. -/
theorem ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    {p : M → Q} {x : M} (hp : IsSubmersionAt I JQ m p x) (hm₀ : m ≠ 0)
    (hfib : ∀ y z : M, p y = p z ↔ ∃ g : G, g • z = y) :
    (mfderiv I JQ p x).ker = (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG G M
  let J0 := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  let π := Quotient.mk (MulAction.orbitRel G M)
  have hp_diff : MDifferentiableAt I JQ p x := hp.contMDiffAt.mdifferentiableAt hm₀
  refine le_antisymm ?_
    (orbitTangent_fundamental_le_ker_mfderiv hp_diff
      (Eventually.of_forall fun g ↦ (hfib (g • x) x).2 ⟨g, rfl⟩))
  obtain ⟨U, hU, hxU, s, -, hs, hps⟩ := hp.exists_contMDiffOn_section
  have hs_diff : MDifferentiableAt JQ I s (p x) :=
    (hs.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt hm₀
  have hπ_diff : MDifferentiableAt I J0 π (s (p x)) :=
    ((contMDiff_freeProperQuotientMk I IG (G := G) (M := M)) (s (p x))).mdifferentiableAt (by simp)
  have heq : ((π ∘ s) ∘ p) =ᶠ[𝓝 x] π := by
    filter_upwards [hp.contMDiffAt.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with y hy
    obtain ⟨g, hg⟩ := (hfib (s (p y)) y).1 (hps (p y) hy)
    exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g, hg⟩))
  have hπ_congr := ((hπ_diff.hasMFDerivAt.comp (p x) hs_diff.hasMFDerivAt).comp x
    hp_diff.hasMFDerivAt).congr_of_eventuallyEq heq.symm
  rw [← ker_mfderiv_freeProperQuotientMk I IG (G := G) x, hπ_congr.mfderiv]
  exact (LinearMap.ker_le_ker_comp _ _).trans (LinearMap.ker_le_ker_comp _ _)

section Equivariant

variable {E' EG' H' HG' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
  [TopologicalSpace H'] [TopologicalSpace HG']
  (I' : ModelWithCorners ℝ E' H') (IG' : ModelWithCorners ℝ EG' HG')
  [I'.Boundaryless]
  {G' M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [TopologicalSpace G'] [ChartedSpace HG' G'] [Group G'] [LieGroup IG' ∞ G']
  [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [ProperSMul G' M'] [IsCancelSMul G' M']

/-- **Smoothness of equivariant maps on orbit spaces.** For `m ≤ ∞`, a `C^m` map `φ : M →ₑ[σ] M'`
between two free proper smooth Lie group actions descends to a `C^m` map `M ⧸ G → M' ⧸ G'`. -/
theorem contMDiff_orbitRelQuotientMap_of_properSMul_of_isCancelSMul (hm : m ≤ ∞) {σ : G → G'}
    {φ : M →ₑ[σ] M'} (hφ : ContMDiff I I' m φ) :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ EG') → ℝ) m
      (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace I IG G M
  let := freeProperQuotientChartedSpace I' IG' G' M'
  rw [← (isSubmersion_freeProperQuotientMk I IG (G := G) (M := M)).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_freeProperQuotientMk I' IG' (G := G') (M := M')).of_le hm).comp hφ

/-- **An equivariant `C^m` diffeomorphism induces a `C^m` diffeomorphism of free-proper orbit
manifolds.** For `m ≤ ∞`, if `e : M ≃ₘ^m⟮I, I'⟯ M'` intertwines the actions of `G` and `G'` along a
group isomorphism `φ : G ≃* G'`, then `MulAction.orbitRelQuotientCongr φ e.toEquiv he` is a `C^m`
diffeomorphism `(M ⧸ G) ≃ₘ^m (M' ⧸ G')`. No smoothness assumption on `φ` is needed. -/
def freeProperQuotientDiffeomorph (hm : m ≤ ∞) (φ : G ≃* G') (e : M ≃ₘ^m⟮I, I'⟯ M')
    (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    MulAction.orbitRel.Quotient G M ≃ₘ^m⟮𝓘(ℝ,
      Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ),
      𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ EG') → ℝ)⟯
      MulAction.orbitRel.Quotient G' M' :=
  letI := freeProperQuotientChartedSpace I IG G M
  letI := freeProperQuotientChartedSpace I' IG' G' M'
  { toEquiv := MulAction.orbitRelQuotientCongr φ e.toEquiv he
    contMDiff_toFun :=
      ((isSubmersion_freeProperQuotientMk I IG).contMDiff_comp_iff Quotient.mk_surjective hm).1 <|
        (((contMDiff_freeProperQuotientMk I' IG').of_le hm).comp e.contMDiff).congr fun x ↦
          MulAction.orbitRelQuotientCongr_mk φ e.toEquiv he x
    contMDiff_invFun :=
      ((isSubmersion_freeProperQuotientMk I' IG').contMDiff_comp_iff Quotient.mk_surjective hm).1 <|
        (((contMDiff_freeProperQuotientMk I IG).of_le hm).comp e.symm.contMDiff).congr fun y ↦
          MulAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y }

/-- The underlying equivalence of `freeProperQuotientDiffeomorph` is
`MulAction.orbitRelQuotientCongr`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_toEquiv (hm : m ≤ ∞) (φ : G ≃* G')
    (e : M ≃ₘ^m⟮I, I'⟯ M') (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    (freeProperQuotientDiffeomorph I IG I' IG' hm φ e he).toEquiv =
      MulAction.orbitRelQuotientCongr φ e.toEquiv he :=
  (rfl)

/-- `freeProperQuotientDiffeomorph` sends `[x]` to `[e x]`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_mk (hm : m ≤ ∞) (φ : G ≃* G')
    (e : M ≃ₘ^m⟮I, I'⟯ M') (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    freeProperQuotientDiffeomorph I IG I' IG' hm φ e he
      (Quotient.mk (MulAction.orbitRel G M) x) =
      Quotient.mk (MulAction.orbitRel G' M') (e x) := by
  let := freeProperQuotientChartedSpace I IG G M
  let := freeProperQuotientChartedSpace I' IG' G' M'
  exact MulAction.orbitRelQuotientCongr_mk φ e.toEquiv he x

/-- The inverse of `freeProperQuotientDiffeomorph` sends `[y]` to `[e.symm y]`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_symm_mk (hm : m ≤ ∞) (φ : G ≃* G')
    (e : M ≃ₘ^m⟮I, I'⟯ M') (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) (y : M') :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    (freeProperQuotientDiffeomorph I IG I' IG' hm φ e he).symm
      (Quotient.mk (MulAction.orbitRel G' M') y) =
      Quotient.mk (MulAction.orbitRel G M) (e.symm y) := by
  let := freeProperQuotientChartedSpace I IG G M
  let := freeProperQuotientChartedSpace I' IG' G' M'
  exact MulAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y

end Equivariant

end Descent

/-! ### Additive Lie group actions -/

section Additive

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless]
  {G M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [AddGroup G] [LieAddGroup IG ∞ G]
  [AddAction G M] [ContMDiffVAdd IG I ∞ G M] [ProperVAdd G M] [IsCancelVAdd G M]

include I IG G in
omit [I.Boundaryless] in
/-- When an additive Lie group `G` acts smoothly, freely and properly on a nonempty boundaryless
manifold `M`, we have `dim G ≤ dim M`. -/
theorem finrank_le_of_properVAdd_of_isCancelVAdd [BoundarylessManifold I M] [Nonempty M] :
    Module.finrank ℝ EG ≤ Module.finrank ℝ E :=
  finrank_le_of_properSMul_of_isCancelSMul I IG (G := Multiplicative G) (M := M)

variable (G M) in
/-- **The transverse-slice atlas on `AddAction.orbitRel.Quotient G M`.** Pulled back from
`freeProperQuotientChartedSpace I IG (Multiplicative G) M` along
`TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative`, for a free proper smooth action of an
additive Lie group `G` (such as a torus `(ℝ / 2πℤ)^k` or a closed Lie subgroup thereof). -/
@[instance_reducible]
def freeProperAddQuotientChartedSpace :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (_root_.AddAction.orbitRel.Quotient G M) :=
  letI := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  (AddAction.orbitRelQuotientHomeomorphMultiplicative (G := G) (X := M)).pullbackChartedSpace

/-- Equipped with `freeProperAddQuotientChartedSpace`, `AddAction.orbitRel.Quotient G M` is a smooth
manifold. -/
theorem isManifold_freeProperAddQuotient :
    letI := freeProperAddQuotientChartedSpace I IG G M
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (_root_.AddAction.orbitRel.Quotient G M) := by
  let := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  have := isManifold_freeProperQuotient I IG (G := Multiplicative G) (M := M)
  exact (AddAction.orbitRelQuotientHomeomorphMultiplicative
    (G := G) (X := M)).pullback_isManifold _ ∞

variable (G M) in
/-- **Canonical diffeomorphism between the additive orbit manifold and its `Multiplicative`
counterpart.** -/
def freeProperAddQuotientDiffeomorphMultiplicative :
    letI := freeProperAddQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I IG (Multiplicative G) M
    _root_.AddAction.orbitRel.Quotient G M ≃ₘ⟮𝓘(ℝ,
      Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ),
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)⟯
      MulAction.orbitRel.Quotient (Multiplicative G) M :=
  letI := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  (AddAction.orbitRelQuotientHomeomorphMultiplicative (G := G) (X := M)).pullbackDiffeomorph
    𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞

/-- The underlying homeomorphism of `freeProperAddQuotientDiffeomorphMultiplicative` is
`AddAction.orbitRelQuotientHomeomorphMultiplicative`. -/
@[simp]
theorem freeProperAddQuotientDiffeomorphMultiplicative_toHomeomorph :
    letI := freeProperAddQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I IG (Multiplicative G) M
    (freeProperAddQuotientDiffeomorphMultiplicative I IG G M).toHomeomorph =
      AddAction.orbitRelQuotientHomeomorphMultiplicative (G := G) (X := M) := by
  let := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  exact (AddAction.orbitRelQuotientHomeomorphMultiplicative
    (G := G) (X := M)).pullbackDiffeomorph_toHomeomorph _ ∞

/-- `freeProperAddQuotientDiffeomorphMultiplicative` sends the additive orbit `[x]` to the
`Multiplicative G`-orbit `[x]`. -/
@[simp]
theorem freeProperAddQuotientDiffeomorphMultiplicative_mk (x : M) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I IG (Multiplicative G) M
    freeProperAddQuotientDiffeomorphMultiplicative I IG G M
      (Quotient.mk (_root_.AddAction.orbitRel G M) x) =
      Quotient.mk (MulAction.orbitRel (Multiplicative G) M) x := by
  let := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  rw [freeProperAddQuotientDiffeomorphMultiplicative, Homeomorph.coe_pullbackDiffeomorph,
    AddAction.orbitRelQuotientHomeomorphMultiplicative_mk]

/-- The inverse of `freeProperAddQuotientDiffeomorphMultiplicative` sends the
`Multiplicative G`-orbit `[x]` to the additive orbit `[x]`. -/
@[simp]
theorem freeProperAddQuotientDiffeomorphMultiplicative_symm_mk (x : M) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I IG (Multiplicative G) M
    (freeProperAddQuotientDiffeomorphMultiplicative I IG G M).symm
      (Quotient.mk (MulAction.orbitRel (Multiplicative G) M) x) =
      Quotient.mk (_root_.AddAction.orbitRel G M) x := by
  let := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  rw [freeProperAddQuotientDiffeomorphMultiplicative, Homeomorph.coe_pullbackDiffeomorph_symm,
    AddAction.orbitRelQuotientHomeomorphMultiplicative_symm_mk]

/-- The additive orbit projection `M → AddAction.orbitRel.Quotient G M` is a smooth submersion with
fibre complement `EG`. -/
theorem isSubmersionOfComplement_freeProperAddQuotientMk :
    letI := freeProperAddQuotientChartedSpace I IG G M
    IsSubmersionOfComplement EG I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (_root_.AddAction.orbitRel G M)) := by
  let := freeProperAddQuotientChartedSpace I IG G M
  let := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  have := isManifold_freeProperAddQuotient I IG (G := G) (M := M)
  have := isManifold_freeProperQuotient I IG (G := Multiplicative G) (M := M)
  let Φ := (freeProperAddQuotientDiffeomorphMultiplicative I IG G M).symm
  have hcomp : ⇑Φ ∘ Quotient.mk (MulAction.orbitRel (Multiplicative G) M) =
      Quotient.mk (_root_.AddAction.orbitRel G M) := by
    ext y
    simp [Φ]
  rw [← hcomp]
  exact isSubmersionOfComplement_iff.2 fun x ↦
    (Φ.isLocalDiffeomorph _).comp_isSubmersionAtOfComplement
      ((isSubmersionOfComplement_freeProperQuotientMk I IG
        (G := Multiplicative G) (M := M)).isSubmersionAt x)

/-- The additive orbit projection `M → AddAction.orbitRel.Quotient G M` is a smooth submersion. -/
theorem isSubmersion_freeProperAddQuotientMk :
    letI := freeProperAddQuotientChartedSpace I IG G M
    IsSubmersion I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (_root_.AddAction.orbitRel G M)) :=
  letI := freeProperAddQuotientChartedSpace I IG G M
  (isSubmersionOfComplement_freeProperAddQuotientMk I IG (G := G) (M := M)).isSubmersion

/-- The additive orbit projection `M → AddAction.orbitRel.Quotient G M` is smooth. -/
theorem contMDiff_freeProperAddQuotientMk :
    letI := freeProperAddQuotientChartedSpace I IG G M
    ContMDiff I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (_root_.AddAction.orbitRel G M)) :=
  letI := freeProperAddQuotientChartedSpace I IG G M
  (isSubmersion_freeProperAddQuotientMk I IG (G := G) (M := M)).contMDiff

/-- Over an open neighbourhood of `[x]` in `AddAction.orbitRel.Quotient G M`, the additive orbit
projection admits a smooth local section sending `[x]` to `x`. -/
theorem exists_contMDiffOn_section_freeProperAddQuotientMk (x : M) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    ∃ U : Set (_root_.AddAction.orbitRel.Quotient G M),
      IsOpen U ∧ Quotient.mk (_root_.AddAction.orbitRel G M) x ∈ U ∧
      ∃ s : _root_.AddAction.orbitRel.Quotient G M → M,
        s (Quotient.mk (_root_.AddAction.orbitRel G M) x) = x ∧
        ContMDiffOn 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) I ∞ s U ∧
        ∀ q ∈ U, Quotient.mk (_root_.AddAction.orbitRel G M) (s q) = q :=
  letI := freeProperAddQuotientChartedSpace I IG G M
  ((isSubmersion_freeProperAddQuotientMk I IG (G := G) (M := M)).isSubmersionAt
    x).exists_contMDiffOn_section

/-- For a free proper smooth action of an additive Lie group `G` on `M`, if `p : M → Q` is a `C^m`
(`m ≠ 0`) submersion at `x` whose fibres are the additive `G`-orbits, then `ker dp_x` is the orbit
tangent space of `Multiplicative G` at `x`. -/
theorem ker_mfderiv_eq_orbitTangent_fundamental_multiplicative_of_isSubmersionAt
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    {m : ℕ∞ω} {p : M → Q} {x : M} (hp : IsSubmersionAt I JQ m p x) (hm₀ : m ≠ 0)
    (hfib : ∀ y z : M, p y = p z ↔ ∃ g : G, g +ᵥ z = y) :
    (mfderiv I JQ p x).ker =
      (InfinitesimalAction.fundamental IG (Multiplicative G) I M).orbitTangent x :=
  ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt I IG (G := Multiplicative G) hp hm₀
    fun y z ↦ (hfib y z).trans Multiplicative.ofAdd.exists_congr_left

/-- At every `x : M`, the kernel of the differential of the additive orbit projection is the orbit
tangent space of `Multiplicative G` at `x`. -/
theorem ker_mfderiv_freeProperAddQuotientMk (x : M) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    (mfderiv I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (Quotient.mk (_root_.AddAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG (Multiplicative G) I M).orbitTangent x := by
  let := freeProperAddQuotientChartedSpace I IG G M
  exact ker_mfderiv_eq_orbitTangent_fundamental_multiplicative_of_isSubmersionAt I IG
    ((isSubmersion_freeProperAddQuotientMk I IG (G := G) (M := M)).isSubmersionAt x) (by simp)
    fun y z ↦ Quotient.eq.trans
      (_root_.AddAction.orbitRel_apply.trans _root_.AddAction.mem_orbit_iff)

/-- Pointwise smooth descent (`m ≤ ∞`) for a `G`-invariant map out of a free proper smooth additive
Lie group action. -/
theorem contMDiffAt_addOrbitRelQuotientLift_iff_of_properVAdd_of_isCancelVAdd
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {m : ℕ∞ω} (hm : m ≤ ∞) {f : M → N} {hf : ∀ (g : G) (x : M), f (g +ᵥ x) = f x} {x : M} :
    letI := freeProperAddQuotientChartedSpace I IG G M
    ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) IN m
      (AddAction.orbitRelQuotientLift f hf)
      (Quotient.mk (_root_.AddAction.orbitRel G M) x) ↔
      ContMDiffAt I IN m f x := by
  let := freeProperAddQuotientChartedSpace I IG G M
  rw [← (((isSubmersion_freeProperAddQuotientMk I IG (G := G) (M := M)).isSubmersionAt
    x).contMDiffAt_comp_iff hm), AddAction.orbitRelQuotientLift_comp_mk]

/-- Smooth descent (`m ≤ ∞`) for a `G`-invariant map out of a free proper smooth additive Lie group
action. -/
theorem contMDiff_addOrbitRelQuotientLift_iff_of_properVAdd_of_isCancelVAdd
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {m : ℕ∞ω} (hm : m ≤ ∞) {f : M → N} {hf : ∀ (g : G) (x : M), f (g +ᵥ x) = f x} :
    letI := freeProperAddQuotientChartedSpace I IG G M
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) IN m
      (AddAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I IN m f := by
  let := freeProperAddQuotientChartedSpace I IG G M
  rw [← ((isSubmersion_freeProperAddQuotientMk I IG (G := G) (M := M)).contMDiff_comp_iff
    Quotient.mk_surjective hm), AddAction.orbitRelQuotientLift_comp_mk]

/-- Universal property of the additive free-proper quotient manifold (`m ≤ ∞`). -/
theorem existsUnique_contMDiff_comp_freeProperAddQuotientMk_eq
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {m : ℕ∞ω} (hm : m ≤ ∞) {f : M → N}
    (hf_diff : ContMDiff I IN m f) (hf_inv : ∀ (g : G) (x : M), f (g +ᵥ x) = f x) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    ∃! f' : _root_.AddAction.orbitRel.Quotient G M → N,
      ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) IN m f' ∧
        f' ∘ Quotient.mk (_root_.AddAction.orbitRel G M) = f := by
  let := freeProperAddQuotientChartedSpace I IG G M
  have hsub := isSubmersion_freeProperAddQuotientMk I IG (G := G) (M := M)
  refine hsub.existsUnique_contMDiff_comp_eq Quotient.mk_surjective hm hf_diff ?_
  rintro x y hxy
  obtain ⟨g, rfl⟩ := _root_.AddAction.orbitRel_apply.1 (Quotient.exact hxy)
  exact hf_inv g y

/-- For a free proper smooth action of an additive Lie group `G` on `M`, the canonical
diffeomorphism between `AddAction.orbitRel.Quotient G M` and the target of any surjective smooth
submersion `p : M → Q` whose fibres are the additive `G`-orbits. -/
def diffeomorphOfAddOrbitSubmersion
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g +ᵥ y = x) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    _root_.AddAction.orbitRel.Quotient G M ≃ₘ⟮𝓘(ℝ,
      Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ), JQ⟯ Q :=
  letI := freeProperAddQuotientChartedSpace I IG G M
  letI := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  (freeProperAddQuotientDiffeomorphMultiplicative I IG G M).trans
    (diffeomorphOfOrbitSubmersion I IG (G := Multiplicative G) p hp hp_surj
      fun x y ↦ (hfib x y).trans Multiplicative.ofAdd.exists_congr_left)

/-- `diffeomorphOfAddOrbitSubmersion` sends the additive orbit `[x]` to `p x`. -/
@[simp]
theorem diffeomorphOfAddOrbitSubmersion_mk
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g +ᵥ y = x) (x : M) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    diffeomorphOfAddOrbitSubmersion I IG p hp hp_surj hfib
      (Quotient.mk (_root_.AddAction.orbitRel G M) x) = p x := by
  let := freeProperAddQuotientChartedSpace I IG G M
  simp [diffeomorphOfAddOrbitSubmersion]

/-- Composing `diffeomorphOfAddOrbitSubmersion` with the additive orbit projection recovers `p`. -/
@[simp]
theorem diffeomorphOfAddOrbitSubmersion_comp_mk
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g +ᵥ y = x) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    ⇑(diffeomorphOfAddOrbitSubmersion I IG p hp hp_surj hfib) ∘
      Quotient.mk (_root_.AddAction.orbitRel G M) = p := by
  let := freeProperAddQuotientChartedSpace I IG G M
  ext x
  exact diffeomorphOfAddOrbitSubmersion_mk I IG p hp hp_surj hfib x

/-- The inverse of `diffeomorphOfAddOrbitSubmersion` sends `p x` back to `[x]`. -/
@[simp]
theorem diffeomorphOfAddOrbitSubmersion_symm_apply
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g +ᵥ y = x) (x : M) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    (diffeomorphOfAddOrbitSubmersion I IG p hp hp_surj hfib).symm (p x) =
      Quotient.mk (_root_.AddAction.orbitRel G M) x := by
  let := freeProperAddQuotientChartedSpace I IG G M
  exact (diffeomorphOfAddOrbitSubmersion I IG p hp hp_surj hfib).symm_apply_eq.2
    (diffeomorphOfAddOrbitSubmersion_mk I IG p hp hp_surj hfib x).symm

section Equivariant

variable {E' EG' H' HG' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
  [TopologicalSpace H'] [TopologicalSpace HG']
  (I' : ModelWithCorners ℝ E' H') (IG' : ModelWithCorners ℝ EG' HG')
  [I'.Boundaryless]
  {G' M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [TopologicalSpace G'] [ChartedSpace HG' G'] [AddGroup G'] [LieAddGroup IG' ∞ G']
  [AddAction G' M'] [ContMDiffVAdd IG' I' ∞ G' M'] [ProperVAdd G' M'] [IsCancelVAdd G' M']
  {m : ℕ∞ω}

/-- **Smoothness of equivariant maps on additive orbit spaces.** For `m ≤ ∞`, a `C^m` equivariant
map `φ : AddActionHom σ M M'` between two free proper smooth additive Lie group actions descends to
a `C^m` map of additive orbit spaces. -/
theorem contMDiff_addOrbitRelQuotientMap_of_properVAdd_of_isCancelVAdd (hm : m ≤ ∞) {σ : G → G'}
    {φ : AddActionHom σ M M'} (hφ : ContMDiff I I' m φ) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    letI := freeProperAddQuotientChartedSpace I' IG' G' M'
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ EG') → ℝ) m
      (AddActionHom.orbitRelQuotientMap φ) := by
  let := freeProperAddQuotientChartedSpace I IG G M
  let := freeProperAddQuotientChartedSpace I' IG' G' M'
  rw [← (isSubmersion_freeProperAddQuotientMk I IG (G := G) (M := M)).contMDiff_comp_iff
    Quotient.mk_surjective hm, AddActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_freeProperAddQuotientMk I' IG' (G := G') (M := M')).of_le hm).comp hφ

/-- **An equivariant `C^m` diffeomorphism induces a `C^m` diffeomorphism of additive free-proper
orbit manifolds.** For `m ≤ ∞`, if `e : M ≃ₘ^m⟮I, I'⟯ M'` intertwines the additive actions of `G`
and `G'` along an additive group isomorphism `φ : G ≃+ G'`, then
`AddAction.orbitRelQuotientCongr φ e.toEquiv he` is a `C^m` diffeomorphism of additive orbit
spaces. No smoothness assumption on `φ` is needed. -/
def freeProperAddQuotientDiffeomorph (hm : m ≤ ∞) (φ : G ≃+ G') (e : M ≃ₘ^m⟮I, I'⟯ M')
    (he : ∀ (g : G) (x : M), e (g +ᵥ x) = φ g +ᵥ e x) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    letI := freeProperAddQuotientChartedSpace I' IG' G' M'
    _root_.AddAction.orbitRel.Quotient G M ≃ₘ^m⟮𝓘(ℝ,
      Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ),
      𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ EG') → ℝ)⟯
      _root_.AddAction.orbitRel.Quotient G' M' :=
  letI := freeProperAddQuotientChartedSpace I IG G M
  letI := freeProperAddQuotientChartedSpace I' IG' G' M'
  { toEquiv := AddAction.orbitRelQuotientCongr φ e.toEquiv he
    contMDiff_toFun :=
      ((isSubmersion_freeProperAddQuotientMk I IG).contMDiff_comp_iff Quotient.mk_surjective
        hm).1 <|
        (((contMDiff_freeProperAddQuotientMk I' IG').of_le hm).comp e.contMDiff).congr fun x ↦
          AddAction.orbitRelQuotientCongr_mk φ e.toEquiv he x
    contMDiff_invFun :=
      ((isSubmersion_freeProperAddQuotientMk I' IG').contMDiff_comp_iff Quotient.mk_surjective
        hm).1 <|
        (((contMDiff_freeProperAddQuotientMk I IG).of_le hm).comp e.symm.contMDiff).congr fun y ↦
          AddAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y }

/-- The underlying equivalence of `freeProperAddQuotientDiffeomorph` is
`AddAction.orbitRelQuotientCongr`. -/
@[simp]
theorem freeProperAddQuotientDiffeomorph_toEquiv (hm : m ≤ ∞) (φ : G ≃+ G')
    (e : M ≃ₘ^m⟮I, I'⟯ M') (he : ∀ (g : G) (x : M), e (g +ᵥ x) = φ g +ᵥ e x) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    letI := freeProperAddQuotientChartedSpace I' IG' G' M'
    (freeProperAddQuotientDiffeomorph I IG I' IG' hm φ e he).toEquiv =
      AddAction.orbitRelQuotientCongr φ e.toEquiv he :=
  (rfl)

/-- `freeProperAddQuotientDiffeomorph` sends `[x]` to `[e x]`. -/
@[simp]
theorem freeProperAddQuotientDiffeomorph_mk (hm : m ≤ ∞) (φ : G ≃+ G')
    (e : M ≃ₘ^m⟮I, I'⟯ M') (he : ∀ (g : G) (x : M), e (g +ᵥ x) = φ g +ᵥ e x) (x : M) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    letI := freeProperAddQuotientChartedSpace I' IG' G' M'
    freeProperAddQuotientDiffeomorph I IG I' IG' hm φ e he
      (Quotient.mk (_root_.AddAction.orbitRel G M) x) =
      Quotient.mk (_root_.AddAction.orbitRel G' M') (e x) := by
  let := freeProperAddQuotientChartedSpace I IG G M
  let := freeProperAddQuotientChartedSpace I' IG' G' M'
  exact AddAction.orbitRelQuotientCongr_mk φ e.toEquiv he x

/-- The inverse of `freeProperAddQuotientDiffeomorph` sends `[y]` to `[e.symm y]`. -/
@[simp]
theorem freeProperAddQuotientDiffeomorph_symm_mk (hm : m ≤ ∞) (φ : G ≃+ G')
    (e : M ≃ₘ^m⟮I, I'⟯ M') (he : ∀ (g : G) (x : M), e (g +ᵥ x) = φ g +ᵥ e x) (y : M') :
    letI := freeProperAddQuotientChartedSpace I IG G M
    letI := freeProperAddQuotientChartedSpace I' IG' G' M'
    (freeProperAddQuotientDiffeomorph I IG I' IG' hm φ e he).symm
      (Quotient.mk (_root_.AddAction.orbitRel G' M') y) =
      Quotient.mk (_root_.AddAction.orbitRel G M) (e.symm y) := by
  let := freeProperAddQuotientChartedSpace I IG G M
  let := freeProperAddQuotientChartedSpace I' IG' G' M'
  exact AddAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y

end Equivariant

/-- **The additive quotient manifold theorem.** Let a finite-dimensional additive real Lie group `G`
act smoothly, freely and properly on a finite-dimensional boundaryless smooth real manifold `M`.
Then `AddAction.orbitRel.Quotient G M`, with its quotient topology, admits a smooth (`C^∞`) manifold
structure of dimension `dim E - dim EG` for which the orbit projection is a smooth submersion. -/
theorem exists_freeProperAddQuotient_isSubmersion
    {E EG H HG M G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace H] [TopologicalSpace HG]
    (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
    [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace G] [ChartedSpace HG G] [AddGroup G] [LieAddGroup IG ∞ G]
    [AddAction G M] [ProperVAdd G M]
    (hvadd : ContMDiff (IG.prod I) I ∞ (fun gx : G × M ↦ gx.1 +ᵥ gx.2))
    (hfree : ∀ (g : G) (x : M), g +ᵥ x = x → g = 0) :
    ∃ cs : ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
        (_root_.AddAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (_root_.AddAction.orbitRel.Quotient G M) ∧
      IsSubmersion I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (Quotient.mk'' : M → _root_.AddAction.orbitRel.Quotient G M) := by
  let : ContMDiffVAdd IG I ∞ G M := ⟨hvadd⟩
  let : IsCancelVAdd G M := isCancelVAdd_iff_eq_zero_of_vadd_eq.2 hfree
  exact ⟨freeProperAddQuotientChartedSpace I IG G M,
    isManifold_freeProperAddQuotient I IG,
    isSubmersion_freeProperAddQuotientMk I IG⟩

end Additive

end TauCeti
