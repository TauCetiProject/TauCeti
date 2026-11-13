/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Algebra.TypeTags
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.GroupAction.Orbit
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Algebra.GroupAction.Quotient
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
`TauCeti.Geometry.Manifold.GroupAction.TransverseSlice`:
* freeness and properness make the orbit map at every `x : M` an immersion
  (`TauCeti.isImmersion_smul_const_of_stabilizer_eq_bot`), so `𝔤_x = 0`;
* choosing a linear complement `W` of `𝔤 · x` in `T_x M` gives a transverse chart slice whose slice
  map `(g, u) ↦ g • τ u` is a smooth local diffeomorphism at `(1, 0)`
  (`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`), hence along `G × U` for a small open
  neighbourhood `U` of `0` in `Fin (dim M - dim G) → ℝ`
  (`IsLocalDiffeomorphAt.eventually_forall_smul_slice`);
* properness and triviality of stabilizers shrink `U` further so that the slice map is injective on
  `G × U` (`ProperSMul.exists_mem_nhds_injOn_smul_slice`), making `u ↦ [τ u]` an open embedding of
  `U` into `M ⧸ G` (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`);
* the smoothness of chart transitions and of the orbit projection is read off from the smooth local
  inverses of slice maps (`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`).

Neither Hausdorffness nor second-countability needs to be assumed: `T2Space G` follows from the Lie
group structure (`ModelWithCorners.t2Space_of_lieGroup`), `T2Space M` and
`T2Space (MulAction.orbitRel.Quotient G M)` follow from properness
(`t2Space_of_properSMul_of_t1Group`, `t2Space_quotient_mulAction_of_properSMul`), and when `M` is
second countable the orbit space inherits `SecondCountableTopology` automatically along the open
quotient projection (`MulAction.isOpenQuotientMap_quotientMk`). The manifold `M` may be empty.

`TauCeti.freeProperQuotientChartedSpace` is an `@[instance_reducible]` definition rather than a
global `ChartedSpace` instance: its model space `Fin (dim E - dim EG) → ℝ` depends on `E` and `EG`,
which cannot be inferred from `MulAction.orbitRel.Quotient G M`, and when `G` is discrete
(`dim EG = 0`) a global instance would create a diamond with `MulAction.instChartedSpaceQuotient`.

By `Equiv.diffeomorphOfSubmersions`, any surjective smooth submersion `p : M → Q` whose fibres are
the `G`-orbits induces a canonical diffeomorphism `(M ⧸ G) ≃ₘ Q`
(`TauCeti.diffeomorphOfOrbitSubmersion`) and has vertical kernel `𝔤 · x`
(`TauCeti.ker_mfderiv_of_isSubmersion_orbit`). Smoothness of `G`-invariant `C^m` maps (`m ≤ ∞`)
descends to the orbit space (`TauCeti.contMDiff_orbitRelQuotientLift_of_freeProper_iff`,
`TauCeti.existsUnique_contMDiff_freeProperQuotientMk_comp_eq`), equivariant maps and diffeomorphisms
descend functorially (`TauCeti.contMDiff_orbitRelQuotientMap_of_freeProper`,
`TauCeti.orbitRelQuotientDiffeomorphOfFreeProper`), and the additive Lie group counterpart on
`AddAction.orbitRel.Quotient G M` is obtained by pulling back the multiplicative atlas of
`Multiplicative G`.

## Main definitions

* `TauCeti.freeProperQuotientChartedSpace`: the slice-chart atlas on
  `MulAction.orbitRel.Quotient G M` for a free proper smooth Lie group action.
* `TauCeti.diffeomorphOfOrbitSubmersion`: the canonical diffeomorphism `(M ⧸ G) ≃ₘ Q` induced by any
  surjective smooth submersion `p : M → Q` whose fibres are the `G`-orbits.
* `TauCeti.orbitRelQuotientDiffeomorphOfFreeProper`: the diffeomorphism of free-proper orbit
  manifolds induced by an equivariant diffeomorphism.
* `TauCeti.freeProperAddQuotientChartedSpace`, `TauCeti.diffeomorphOfAddOrbitSubmersion`: the
  additive Lie group action counterparts on `AddAction.orbitRel.Quotient G M`.

## Main results

* `TauCeti.mfderiv_fundamentalVectorField_eq_zero`,
  `TauCeti.orbitTangent_fundamental_le_ker_mfderiv`,
  `TauCeti.ker_mfderiv_eq_orbitTangent_fundamental`, `TauCeti.ker_mfderiv_of_isSubmersion_orbit`:
  verticality of fundamental vector fields and identification of the vertical kernel with `𝔤 · x`.
* `TauCeti.isManifold_freeProperQuotient`,
  `TauCeti.isSubmersionOfComplement_freeProperQuotientMk`,
  `TauCeti.isSubmersion_freeProperQuotientMk`, `TauCeti.ker_mfderiv_freeProperQuotientMk`,
  `TauCeti.exists_freeProperQuotient_isSubmersion`: the quotient manifold theorem for free proper
  Lie group actions.
* `TauCeti.contMDiffAt_orbitRelQuotientLift_of_freeProper_iff`,
  `TauCeti.contMDiff_orbitRelQuotientLift_of_freeProper_iff`,
  `TauCeti.existsUnique_contMDiff_freeProperQuotientMk_comp_eq`,
  `TauCeti.contMDiff_orbitRelQuotientMap_of_freeProper`: smooth descent and equivariant maps.
* `TauCeti.isManifold_freeProperAddQuotient`,
  `TauCeti.isSubmersionOfComplement_freeProperAddQuotientMk`,
  `TauCeti.isSubmersion_freeProperAddQuotientMk`, `TauCeti.ker_mfderiv_freeProperAddQuotientMk`,
  `TauCeti.exists_freeProperAddQuotient_isSubmersion`: the additive quotient manifold theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 4.31
  (uniqueness of quotient manifold structures) and Theorem 21.10 (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto (2003),
  Theorem 1.21.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience (1963),
  Chapter I, Proposition 5.2.
-/

public section

noncomputable section

open Function Set Filter Manifold Topology
open scoped ContDiff Manifold

namespace TauCeti

/-! ### Verticality of fundamental vector fields and the orbit kernel -/

section VerticalKernel

section GeneralField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction G M] [ContMDiffSMul IG I 1 G M]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
  {HQ : Type*} [TopologicalSpace HQ] {JQ : ModelWithCorners 𝕜 EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]

/-- **Fundamental vector fields are vertical along orbit-invariant maps.** If `p : M → Q` is
differentiable at `x` and constant on the local orbit `{g • x | g near 1}`, then `dp_x` annihilates
every fundamental vector `ξ_M(x)`. -/
theorem mfderiv_fundamentalVectorField_eq_zero {p : M → Q} {x : M}
    (hp : MDifferentiableAt I JQ p x) (hinv : ∀ᶠ g in 𝓝 (1 : G), p (g • x) = p x)
    (ξ : GroupLieAlgebra IG G) :
    mfderiv I JQ p x (fundamentalVectorField I ξ x) = 0 := by
  rw [fundamentalVectorField_apply]
  have horb : MDifferentiableAt IG I (fun g : G ↦ g • x) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (I := IG) (I' := I) (n := 1) x).mdifferentiableAt
      one_ne_zero
  have hcomp := mfderiv_comp_apply_of_eq (I := IG) (I' := I) (I'' := JQ) (1 : G) hp horb
    (one_smul G x) ξ
  -- Since `g ↦ p (g • x)` agrees near `1` with the constant map `p x`, its differential vanishes.
  have heq : (p ∘ fun g : G ↦ g • x) =ᶠ[𝓝 (1 : G)] fun _ ↦ p x := hinv
  have hconst : mfderiv IG JQ (p ∘ fun g : G ↦ g • x) 1 ξ = 0 := by
    have h0 : HasMFDerivAt IG JQ (fun _ : G ↦ p x) (1 : G) 0 := hasMFDerivAt_const (p x) (1 : G)
    have h1 : HasMFDerivAt IG JQ (p ∘ fun g : G ↦ g • x) (1 : G) 0 :=
      h0.congr_of_eventuallyEq (heq.trans (Eventually.of_forall fun _ ↦ rfl))
    simp [h1.mfderiv]
  exact hcomp.symm.trans hconst

end GeneralField

section Real

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  {HQ : Type*} [TopologicalSpace HQ] {JQ : ModelWithCorners ℝ EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]

private local instance : ContMDiffSMul IG I 1 G M :=
  ContMDiffSMul.of_le (M := M) ENat.LEInfty.out

/-- The orbit tangent space `𝔤 · x` is contained in the kernel of `dp_x` whenever `p` is
differentiable at `x` and locally invariant along the orbit of `x`. -/
theorem orbitTangent_fundamental_le_ker_mfderiv {p : M → Q} {x : M}
    (hp : MDifferentiableAt I JQ p x) (hinv : ∀ᶠ g in 𝓝 (1 : G), p (g • x) = p x) :
    (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤ (mfderiv I JQ p x).ker := by
  intro v hv
  obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ x).1 hv
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, InfinitesimalAction.fundamental_apply]
  exact mfderiv_fundamentalVectorField_eq_zero hp hinv ξ

/-- At a locally free point `x` (`𝔤_x = 0`), the dimension of `G` is at most the dimension of `M`,
since the orbit map injects `𝔤` into `T_x M`. -/
theorem finrank_le_of_isotropy_eq_bot [FiniteDimensional ℝ E] {x : M}
    (hx : (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥) :
    Module.finrank ℝ EG ≤ Module.finrank ℝ E := by
  have hle : Module.finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) ≤
      Module.finrank ℝ (TangentSpace I x) := Submodule.finrank_le _
  rwa [(InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x hx]
    at hle

/-- **Vertical kernel by dimension counting.** If `p : M → Q` is differentiable at a locally free
point `x`, locally invariant along the orbit of `x`, and has surjective differential `dp_x` onto a
target model of complementary dimension `dim EQ + dim EG = dim E`, then `ker dp_x = 𝔤 · x`. -/
theorem ker_mfderiv_eq_orbitTangent_fundamental [FiniteDimensional ℝ E] {p : M → Q} {x : M}
    (hx : (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥)
    (hp : MDifferentiableAt I JQ p x) (hinv : ∀ᶠ g in 𝓝 (1 : G), p (g • x) = p x)
    (hsurj : Surjective (mfderiv I JQ p x))
    (hdim : Module.finrank ℝ EQ + Module.finrank ℝ EG = Module.finrank ℝ E) :
    (mfderiv I JQ p x).ker = (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  refine (Submodule.eq_of_le_of_finrank_eq
    (orbitTangent_fundamental_le_ker_mfderiv hp hinv) ?_).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker (mfderiv I JQ p x).toLinearMap
  have hrange : Module.finrank ℝ (LinearMap.range (mfderiv I JQ p x).toLinearMap) =
      Module.finrank ℝ EQ := by
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top]
    rfl
  rw [(InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x hx]
  change Module.finrank ℝ EG = Module.finrank ℝ (LinearMap.ker (mfderiv I JQ p x).toLinearMap)
  change Module.finrank ℝ (LinearMap.range (mfderiv I JQ p x).toLinearMap) +
      Module.finrank ℝ (LinearMap.ker (mfderiv I JQ p x).toLinearMap) = Module.finrank ℝ E at hrn
  omega

end Real

end VerticalKernel

/-! ### Transverse slice charts of a free proper Lie group action -/

namespace FreeProperQuotient

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E EG H HG M G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless] [IG.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- The quotient model space `ℝ^(dim M - dim G)` of `M ⧸ G`. -/
private abbrev ModelSpace (E EG : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] : Type :=
  Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ

/-- At every point of a free proper smooth Lie group action, the isotropy Lie algebra vanishes. -/
theorem isotropy_eq_bot (x : M) :
    (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ := by
  have := FiniteDimensional.completeSpace ℝ E
  have := FiniteDimensional.completeSpace ℝ EG
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  exact (isImmersion_smul_const_iff (I := IG) (I' := I)).1
    (isImmersion_smul_const_of_stabilizer_eq_bot (IsCancelSMul.stabilizer_eq_bot x))

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

/-- Existence of a transverse slice chart through any `x : M`. -/
private theorem nonempty_sliceData (x : M) : Nonempty (SliceData I IG (G := G) x) := by
  have := FiniteDimensional.completeSpace ℝ E
  have := FiniteDimensional.completeSpace ℝ EG
  have hx := isotropy_eq_bot I IG (G := G) x
  let O : Submodule ℝ E := (InfinitesimalAction.fundamental IG G I M).orbitTangent x
  obtain ⟨W, hW⟩ := O.exists_isCompl
  have hdimO : Module.finrank ℝ O = Module.finrank ℝ EG :=
    (InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x hx
  have hdimW : Module.finrank ℝ (ModelSpace E EG) = Module.finrank ℝ W := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hW
    rw [hdimO] at hsum
    rw [Module.finrank_fin_fun]
    omega
  let L : ModelSpace E EG ≃L[ℝ] W := (LinearEquiv.ofFinrankEq _ _ hdimW).toContinuousLinearEquiv
  let φ := extChartAt I x
  let α : ModelSpace E EG → E := fun u ↦ φ x + (L u : E)
  have hα_smooth : ContMDiff 𝓘(ℝ, ModelSpace E EG) 𝓘(ℝ, E) ∞ α :=
    (contDiff_const.add (W.subtypeL.comp (L : ModelSpace E EG →L[ℝ] W)).contDiff).contMDiff
  have hα0 : α 0 = φ x := by simp [α]
  let τ : ModelSpace E EG → M := φ.symm ∘ α
  have hτ0 : τ 0 = x := by
    change φ.symm (α 0) = x
    rw [hα0]
    exact extChartAt_to_inv x
  have hopen_dom : IsOpen (α ⁻¹' φ.target) :=
    (isOpen_extChartAt_target x).preimage hα_smooth.continuous
  have h0_dom : (0 : ModelSpace E EG) ∈ α ⁻¹' φ.target := by
    rw [mem_preimage, hα0]
    exact mem_extChartAt_target x
  have hτ_smooth : ContMDiffOn 𝓘(ℝ, ModelSpace E EG) I ∞ τ (α ⁻¹' φ.target) :=
    (contMDiffOn_extChartAt_symm x).comp hα_smooth.contMDiffOn fun _ hu ↦ hu
  -- Transport `isLocalDiffeomorphAt_smul_extChartAt_symm` from `G × W` to `G × ModelSpace E EG`.
  have hlocW := isLocalDiffeomorphAt_smul_extChartAt_symm (I := IG) (I' := I) (G := G) hx hW
  let T : (G × ModelSpace E EG) ≃ₘ⟮IG.prod 𝓘(ℝ, ModelSpace E EG), IG.prod 𝓘(ℝ, W)⟯ (G × W) :=
    { toEquiv := (Equiv.refl G).prodCongr L.toLinearEquiv.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (L.contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (L.symm.contDiff.contMDiff.comp contMDiff_snd) }
  have hT0 : T (1, 0) = (1, 0) := Prod.ext rfl (map_zero L)
  have hcomp_eq : (fun p : G × ModelSpace E EG ↦ p.1 • τ p.2) =
      (fun p : G × W ↦ p.1 • (extChartAt I x).symm (extChartAt I x x + p.2)) ∘ T := rfl
  have hloc0 : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, ModelSpace E EG)) I ∞
      (fun p : G × ModelSpace E EG ↦ p.1 • τ p.2) (1, 0) := by
    rw [hcomp_eq]
    exact IsLocalDiffeomorphAt.comp (hf := T.isLocalDiffeomorph (1, 0)) (hg := hT0.symm ▸ hlocW)
  -- Combine orbitwise local diffeomorphism with tube injectivity from properness.
  have hev_loc := hloc0.eventually_forall_smul_slice
  obtain ⟨N, hN, hinjN⟩ := hloc0.exists_mem_nhds_injOn
  have hτ_cont : ContinuousAt τ 0 :=
    (hτ_smooth.contMDiffAt (hopen_dom.mem_nhds h0_dom)).continuousAt
  obtain ⟨V, hV, hinjV⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice hτ_cont
    (hτ0.symm ▸ IsCancelSMul.stabilizer_eq_bot x) hN hinjN
  obtain ⟨U, hU_sub, hU_open, h0U⟩ := mem_nhds_iff.1
    (inter_mem (hopen_dom.mem_nhds h0_dom) (inter_mem hev_loc hV))
  refine ⟨⟨τ, U, hU_open, h0U, hτ0, hτ_smooth.mono fun u hu ↦ (hU_sub hu).1,
    hinjV.mono (prod_mono_right fun u hu ↦ (hU_sub hu).2.2), ?_⟩⟩
  rintro ⟨⟨g, u⟩, -, hu⟩
  exact (hU_sub hu).2.1 g

/-- Chosen transverse slice data through `x : M`. -/
private def sliceData (x : M) : SliceData I IG (G := G) x :=
  (nonempty_sliceData I IG x).some

/-- The open embedding `U → M ⧸ G` associated with `sliceData x`. -/
private theorem isOpenEmbedding_sliceChart (x : M) :
    let s := sliceData I IG (G := G) x
    IsOpenEmbedding fun u : s.U ↦ Quotient.mk (MulAction.orbitRel G M) (s.τ u) :=
  let s := sliceData I IG (G := G) x
  MulAction.isOpenEmbedding_quotientMk_slice s.isOpen_U s.injOn_smul
    s.isLocalDiffeomorphOn_smul.isLocalHomeomorphOn

/-- The slice chart of `M ⧸ G` centred at `[x]`, sending `[τ u]` (`u ∈ U`) to `u`. -/
private def chartAtPoint (x : M) :
    OpenPartialHomeomorph (MulAction.orbitRel.Quotient G M) (ModelSpace E EG) :=
  let s := sliceData I IG (G := G) x
  let Uo : TopologicalSpace.Opens (ModelSpace E EG) := ⟨s.U, s.isOpen_U⟩
  (Uo.openPartialHomeomorphSubtypeCoe ⟨⟨0, s.zero_mem_U⟩⟩).lift_openEmbedding
    (isOpenEmbedding_sliceChart I IG x)

private theorem chartAtPoint_source (x : M) :
    (chartAtPoint I IG (G := G) x).source =
      (fun u : (sliceData I IG (G := G) x).U ↦
        Quotient.mk (MulAction.orbitRel G M) ((sliceData I IG (G := G) x).τ u)) '' univ := by
  let s := sliceData I IG (G := G) x
  let Uo : TopologicalSpace.Opens (ModelSpace E EG) := ⟨s.U, s.isOpen_U⟩
  rw [chartAtPoint, OpenPartialHomeomorph.lift_openEmbedding_source,
    Uo.openPartialHomeomorphSubtypeCoe_source ⟨⟨0, s.zero_mem_U⟩⟩]

private theorem chartAtPoint_target (x : M) :
    (chartAtPoint I IG (G := G) x).target = (sliceData I IG (G := G) x).U := by
  let s := sliceData I IG (G := G) x
  let Uo : TopologicalSpace.Opens (ModelSpace E EG) := ⟨s.U, s.isOpen_U⟩
  rw [chartAtPoint, OpenPartialHomeomorph.lift_openEmbedding_target,
    Uo.openPartialHomeomorphSubtypeCoe_target ⟨⟨0, s.zero_mem_U⟩⟩]
  rfl

private theorem mem_chartAtPoint_source (x : M) :
    Quotient.mk (MulAction.orbitRel G M) x ∈ (chartAtPoint I IG (G := G) x).source := by
  rw [chartAtPoint_source]
  exact ⟨⟨0, (sliceData I IG (G := G) x).zero_mem_U⟩, mem_univ _,
    by dsimp only; rw [(sliceData I IG (G := G) x).τ_zero]⟩

private theorem chartAtPoint_symm_apply (x : M) {u : ModelSpace E EG}
    (hu : u ∈ (sliceData I IG (G := G) x).U) :
    (chartAtPoint I IG (G := G) x).symm u =
      Quotient.mk (MulAction.orbitRel G M) ((sliceData I IG (G := G) x).τ u) := by
  let s := sliceData I IG (G := G) x
  let Uo : TopologicalSpace.Opens (ModelSpace E EG) := ⟨s.U, s.isOpen_U⟩
  let e0 := Uo.openPartialHomeomorphSubtypeCoe ⟨⟨0, s.zero_mem_U⟩⟩
  have hu' : u ∈ e0.target := by rwa [Uo.openPartialHomeomorphSubtypeCoe_target]
  have hcoe : ((e0.symm u : Uo) : ModelSpace E EG) = u := by
    rw [← Uo.openPartialHomeomorphSubtypeCoe_coe ⟨⟨0, s.zero_mem_U⟩⟩]
    exact e0.right_inv hu'
  rw [chartAtPoint, OpenPartialHomeomorph.lift_openEmbedding_symm, comp_apply]
  exact congrArg (fun v ↦ Quotient.mk (MulAction.orbitRel G M) (s.τ v)) hcoe

private theorem chartAtPoint_apply_quotientMk_τ (x : M) {u : ModelSpace E EG}
    (hu : u ∈ (sliceData I IG (G := G) x).U) :
    chartAtPoint I IG (G := G) x
        (Quotient.mk (MulAction.orbitRel G M) ((sliceData I IG (G := G) x).τ u)) = u := by
  have htarget : u ∈ (chartAtPoint I IG (G := G) x).target := by
    rwa [chartAtPoint_target]
  rw [← chartAtPoint_symm_apply I IG x hu]
  exact (chartAtPoint I IG (G := G) x).right_inv htarget

end FreeProperQuotient

/-! ### The quotient manifold theorem -/

section QuotientManifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless] [IG.Boundaryless]
  {G M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

include I IG G in
/-- When a Lie group `G` acts smoothly, freely and properly on a nonempty manifold `M`, we have
`dim G ≤ dim M`. -/
theorem finrank_le_of_freeProper [Nonempty M] :
    Module.finrank ℝ EG ≤ Module.finrank ℝ E :=
  let ⟨x⟩ := ‹Nonempty M›
  finrank_le_of_isotropy_eq_bot (FreeProperQuotient.isotropy_eq_bot I IG (G := G) x)

variable (G M) in
/-- **The transverse-slice atlas on `M ⧸ G`.** For a free proper smooth action of a
finite-dimensional real Lie group `G` on a finite-dimensional boundaryless smooth real manifold `M`,
this equips `MulAction.orbitRel.Quotient G M` (carrying its quotient topology) with charts valued in
`Fin (dim E - dim EG) → ℝ`. It is marked `@[instance_reducible]` rather than registered as a global
instance because the model space depends on `E` and `EG`. -/
@[instance_reducible]
def freeProperQuotientChartedSpace :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (MulAction.orbitRel.Quotient G M) where
  atlas := range (FreeProperQuotient.chartAtPoint I IG (G := G))
  chartAt q := FreeProperQuotient.chartAtPoint I IG (G := G) q.out
  mem_chart_source q := by
    have hq : Quotient.mk (MulAction.orbitRel G M) q.out = q := Quotient.out_eq q
    simpa only [hq] using FreeProperQuotient.mem_chartAtPoint_source I IG (G := G) q.out
  chart_mem_atlas q := ⟨q.out, rfl⟩

/-- **Smoothness of the quotient manifold.** Equipped with `freeProperQuotientChartedSpace`, the
orbit space `MulAction.orbitRel.Quotient G M` is a smooth (`C^∞`) manifold. -/
theorem isManifold_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M) := by
  let := freeProperQuotientChartedSpace I IG G M
  refine isManifold_of_contDiffOn _ ∞ _ ?_
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩ u hu
  let sx := FreeProperQuotient.sliceData I IG (G := G) x
  let sy := FreeProperQuotient.sliceData I IG (G := G) y
  have hu_mem : u ∈ sx.U ∧
      Quotient.mk (MulAction.orbitRel G M) (sx.τ u) ∈
        (FreeProperQuotient.chartAtPoint I IG (G := G) y).source := by
    obtain ⟨hu1, hu2⟩ : u ∈ (FreeProperQuotient.chartAtPoint I IG (G := G) x).target ∧
        (FreeProperQuotient.chartAtPoint I IG (G := G) x).symm u ∈
          (FreeProperQuotient.chartAtPoint I IG (G := G) y).source := by
      simpa only [mfld_simps] using hu
    rw [FreeProperQuotient.chartAtPoint_target] at hu1
    rw [FreeProperQuotient.chartAtPoint_symm_apply I IG x hu1] at hu2
    exact ⟨hu1, hu2⟩
  obtain ⟨huU, hq_mem⟩ := hu_mem
  rw [FreeProperQuotient.chartAtPoint_source] at hq_mem
  obtain ⟨⟨v, hvU⟩, -, hvu⟩ := hq_mem
  have hτx_at : ContMDiffAt 𝓘(ℝ, FreeProperQuotient.ModelSpace E EG) I ∞ sx.τ u :=
    sx.contMDiffOn_τ.contMDiffAt (sx.isOpen_U.mem_nhds huU)
  obtain ⟨t, ht_diff, -, ht_ev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff sy.isOpen_U
    sy.injOn_smul sy.isLocalDiffeomorphOn_smul hτx_at hvU hvu
  have hcont : ContDiffAt ℝ ∞ t u := contMDiffAt_iff_contDiffAt.1 ht_diff
  refine (hcont.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [sx.isOpen_U.mem_nhds huU, ht_ev] with u' hu'U ⟨htu', hiff⟩
  have hq_eq : Quotient.mk (MulAction.orbitRel G M) (sy.τ (t u')) =
      Quotient.mk (MulAction.orbitRel G M) (sx.τ u') := (hiff (t u') htu').2 rfl
  change FreeProperQuotient.chartAtPoint I IG (G := G) y
      ((FreeProperQuotient.chartAtPoint I IG (G := G) x).symm u') = t u'
  rw [FreeProperQuotient.chartAtPoint_symm_apply I IG x hu'U, ← hq_eq,
    FreeProperQuotient.chartAtPoint_apply_quotientMk_τ I IG y htu']

/-- The orbit projection `M → M ⧸ G` is smooth for `freeProperQuotientChartedSpace`. -/
theorem contMDiff_freeProperQuotientMk :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiff I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG (G := G) (M := M)
  intro x
  set s := FreeProperQuotient.sliceData I IG (G := G) x
  obtain ⟨t, ht_diff, ht0, ht_ev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff s.isOpen_U
    s.injOn_smul s.isLocalDiffeomorphOn_smul (contMDiffAt_id (I := I) (x := x)) s.zero_mem_U
    (congrArg (Quotient.mk (MulAction.orbitRel G M)) s.τ_zero)
  have hchart_mem : FreeProperQuotient.chartAtPoint I IG (G := G) x ∈
      IsManifold.maximalAtlas 𝓘(ℝ, FreeProperQuotient.ModelSpace E EG) ∞
        (MulAction.orbitRel.Quotient G M) :=
    IsManifold.subset_maximalAtlas ⟨x, rfl⟩
  have h0_target : t x ∈ (FreeProperQuotient.chartAtPoint I IG (G := G) x).target := by
    rw [FreeProperQuotient.chartAtPoint_target, ht0]
    exact s.zero_mem_U
  have hsymm := (contMDiffAt_symm_of_mem_maximalAtlas hchart_mem h0_target).comp x ht_diff
  refine hsymm.congr_of_eventuallyEq ?_
  filter_upwards [ht_ev] with x' ⟨htx', hiff⟩
  have hq_eq : Quotient.mk (MulAction.orbitRel G M) (s.τ (t x')) =
      Quotient.mk (MulAction.orbitRel G M) x' := (hiff (t x') htx').2 rfl
  rw [comp_apply, FreeProperQuotient.chartAtPoint_symm_apply I IG x htx', hq_eq]

/-- At every `x : M`, the differential of the orbit projection `M → M ⧸ G` is surjective: its
composite with the transverse slice `τ` at `0` agrees with the inverse of the slice chart at `[x]`,
which is a smooth local diffeomorphism. -/
theorem surjective_mfderiv_freeProperQuotientMk (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    Surjective (mfderiv I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x) := by
  let := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG (G := G) (M := M)
  set s := FreeProperQuotient.sliceData I IG (G := G) x
  let JQ := 𝓘(ℝ, FreeProperQuotient.ModelSpace E EG)
  have hchart_mem : FreeProperQuotient.chartAtPoint I IG (G := G) x ∈
      IsManifold.maximalAtlas JQ ∞ (MulAction.orbitRel.Quotient G M) :=
    IsManifold.subset_maximalAtlas ⟨x, rfl⟩
  have h0_target : (0 : FreeProperQuotient.ModelSpace E EG) ∈
      (FreeProperQuotient.chartAtPoint I IG (G := G) x).target := by
    rw [FreeProperQuotient.chartAtPoint_target]
    exact s.zero_mem_U
  have hloc_symm := (FreeProperQuotient.chartAtPoint I IG (G := G) x)
    |>.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas hchart_mem h0_target
  have hinv_symm := hloc_symm.isInvertible_mfderiv (by simp)
  have heq : (Quotient.mk (MulAction.orbitRel G M) ∘ s.τ) =ᶠ[𝓝 0]
      (FreeProperQuotient.chartAtPoint I IG (G := G) x).symm := by
    filter_upwards [s.isOpen_U.mem_nhds s.zero_mem_U] with u hu
    exact (FreeProperQuotient.chartAtPoint_symm_apply I IG x hu).symm
  have hτ_diff : MDifferentiableAt JQ I s.τ 0 :=
    (s.contMDiffOn_τ.contMDiffAt (s.isOpen_U.mem_nhds s.zero_mem_U)).mdifferentiableAt (by simp)
  have hq_diff : MDifferentiableAt I JQ (Quotient.mk (MulAction.orbitRel G M)) (s.τ 0) :=
    ((contMDiff_freeProperQuotientMk I IG (G := G) (M := M)) (s.τ 0)).mdifferentiableAt (by simp)
  have hsurj_comp : Surjective
      (mfderiv JQ JQ (Quotient.mk (MulAction.orbitRel G M) ∘ s.τ) 0) := by
    rw [heq.mfderiv_eq]
    exact hinv_symm.surjective
  rw [mfderiv_comp 0 hq_diff hτ_diff, ContinuousLinearMap.coe_comp] at hsurj_comp
  have hsurj_τ0 := hsurj_comp.of_comp
  rwa [s.τ_zero] at hsurj_τ0

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
      finrank_le_of_freeProper I IG (G := G) (M := M)
    have hsub := (contMDiff_freeProperQuotientMk I IG (G := G) (M := M))
      |>.isSubmersionOfComplement_of_surjective_mfderiv (by simp)
        (surjective_mfderiv_freeProperQuotientMk I IG (G := G) (M := M))
    have hdim : Module.finrank ℝ
        (Fin (Module.finrank ℝ E -
          Module.finrank ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)) → ℝ) =
        Module.finrank ℝ EG := by
      simp only [Module.finrank_fin_fun]
      omega
    let K := (LinearEquiv.ofFinrankEq _ _ hdim).toContinuousLinearEquiv
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
    finrank_le_of_freeProper I IG (G := G) (M := M)
  refine ker_mfderiv_eq_orbitTangent_fundamental
    (FreeProperQuotient.isotropy_eq_bot I IG (G := G) x)
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
    [I.Boundaryless] [IG.Boundaryless]
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
  [I.Boundaryless] [IG.Boundaryless]
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
theorem contMDiffAt_orbitRelQuotientLift_of_freeProper_iff (hm : m ≤ ∞) {f : M → N}
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
theorem contMDiff_orbitRelQuotientLift_of_freeProper_iff (hm : m ≤ ∞) {f : M → N}
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
theorem existsUnique_contMDiff_freeProperQuotientMk_comp_eq (hm : m ≤ ∞) {f : M → N}
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

/-- **Canonical diffeomorphism with any orbit submersion.** If `p : M → Q` is a surjective smooth
submersion whose fibres are the `G`-orbits (`p x = p y ↔ ∃ g : G, g • y = x`), then `p` descends to
a diffeomorphism `(M ⧸ G) ≃ₘ Q` sending `[x]` to `p x`. -/
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
    Equiv.ofBijective
      (MulAction.orbitRelQuotientLift p fun g x ↦ (hfib (g • x) x).2 ⟨g, rfl⟩)
      ⟨by
        rintro ⟨x⟩ ⟨y⟩ hxy
        change MulAction.orbitRelQuotientLift p _ (Quotient.mk (MulAction.orbitRel G M) x) =
          MulAction.orbitRelQuotientLift p _ (Quotient.mk (MulAction.orbitRel G M) y) at hxy
        rw [MulAction.orbitRelQuotientLift_mk, MulAction.orbitRelQuotientLift_mk] at hxy
        exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2
          ((hfib x y).1 hxy))),
       fun q ↦ by
        obtain ⟨x, rfl⟩ := hp_surj q
        exact ⟨Quotient.mk _ x, MulAction.orbitRelQuotientLift_mk x⟩⟩
  e.diffeomorphOfSubmersions (isSubmersion_freeProperQuotientMk I IG) Quotient.mk_surjective
    hp hp_surj (by ext x; exact MulAction.orbitRelQuotientLift_mk x)

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
  exact MulAction.orbitRelQuotientLift_mk x

/-- Any surjective smooth submersion `p : M → Q` whose fibres are the `G`-orbits has vertical
tangent space `ker dp_x = 𝔤 · x` at every `x : M`. -/
theorem ker_mfderiv_of_isSubmersion_orbit
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • y = x) (x : M) :
    (mfderiv I JQ p x).ker = (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG G M
  let J0 := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  let Φ := diffeomorphOfOrbitSubmersion I IG p hp hp_surj hfib
  have hΦ : (mfderiv J0 JQ Φ (Quotient.mk (MulAction.orbitRel G M) x)).IsInvertible :=
    Φ.isInvertible_mfderiv (by simp)
  have hcomp : ⇑Φ ∘ Quotient.mk (MulAction.orbitRel G M) = p := by
    ext y
    exact diffeomorphOfOrbitSubmersion_mk I IG p hp hp_surj hfib y
  rw [← hcomp, mfderiv_comp x (Φ.contMDiffAt.mdifferentiableAt (by simp))
    (((contMDiff_freeProperQuotientMk I IG (G := G) (M := M)) x).mdifferentiableAt (by simp))]
  ext v
  rw [← SetLike.ext_iff.1 (ker_mfderiv_freeProperQuotientMk I IG (G := G) x) v]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  exact map_eq_zero_iff (mfderiv J0 JQ Φ (Quotient.mk (MulAction.orbitRel G M) x)) hΦ.injective

section Equivariant

variable {E' EG' H' HG' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
  [TopologicalSpace H'] [TopologicalSpace HG']
  (I' : ModelWithCorners ℝ E' H') (IG' : ModelWithCorners ℝ EG' HG')
  [I'.Boundaryless] [IG'.Boundaryless]
  {G' M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [TopologicalSpace G'] [ChartedSpace HG' G'] [Group G'] [LieGroup IG' ∞ G']
  [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [ProperSMul G' M'] [IsCancelSMul G' M']

/-- **Smoothness of equivariant maps on orbit spaces.** For `m ≤ ∞`, a `C^m` map `φ : M →ₑ[σ] M'`
between two free proper smooth Lie group actions descends to a `C^m` map `M ⧸ G → M' ⧸ G'`. -/
theorem contMDiff_orbitRelQuotientMap_of_freeProper (hm : m ≤ ∞) {σ : G → G'} {φ : M →ₑ[σ] M'}
    (hφ : ContMDiff I I' m φ) :
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

/-- **An equivariant diffeomorphism induces a diffeomorphism of free-proper orbit manifolds.** If
`e : M ≃ₘ⟮I, I'⟯ M'` intertwines the actions of `G` and `G'` along a group isomorphism
`φ : G ≃* G'`, then `MulAction.orbitRelQuotientCongr φ e.toEquiv he` is a smooth diffeomorphism
`(M ⧸ G) ≃ₘ (M' ⧸ G')`. No smoothness assumption on `φ` is needed. -/
def orbitRelQuotientDiffeomorphOfFreeProper (φ : G ≃* G') (e : M ≃ₘ⟮I, I'⟯ M')
    (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    MulAction.orbitRel.Quotient G M ≃ₘ⟮𝓘(ℝ,
      Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ),
      𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ EG') → ℝ)⟯
      MulAction.orbitRel.Quotient G' M' :=
  letI := freeProperQuotientChartedSpace I IG G M
  letI := freeProperQuotientChartedSpace I' IG' G' M'
  { toEquiv := MulAction.orbitRelQuotientCongr φ e.toEquiv he
    contMDiff_toFun := by
      let f : M →ₑ[φ] M' := ⟨e, he⟩
      have hfun : ⇑(MulAction.orbitRelQuotientCongr φ e.toEquiv he) = f.orbitRelQuotientMap :=
        funext fun q ↦ Quotient.inductionOn' q fun x ↦
          (MulAction.orbitRelQuotientCongr_mk φ e.toEquiv he x).trans
            (MulActionHom.orbitRelQuotientMap_mk f x).symm
      rw [hfun]
      exact contMDiff_orbitRelQuotientMap_of_freeProper I IG I' IG' le_rfl (φ := f) e.contMDiff
    contMDiff_invFun := by
      have he_symm : ∀ (g' : G') (y : M'), e.symm (g' • y) = φ.symm g' • e.symm y := fun g' y ↦
        e.toEquiv.injective (by
          change e (e.symm (g' • y)) = e (φ.symm g' • e.symm y)
          rw [e.apply_symm_apply, he, φ.apply_symm_apply, e.apply_symm_apply])
      let f_inv : M' →ₑ[φ.symm] M := ⟨e.symm, he_symm⟩
      have hfun : ⇑(MulAction.orbitRelQuotientCongr φ e.toEquiv he).symm =
          f_inv.orbitRelQuotientMap :=
        funext fun q ↦ Quotient.inductionOn' q fun y ↦
          (MulAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y).trans
            (MulActionHom.orbitRelQuotientMap_mk f_inv y).symm
      rw [hfun]
      exact contMDiff_orbitRelQuotientMap_of_freeProper I' IG' I IG le_rfl (φ := f_inv)
        e.symm.contMDiff }

/-- `orbitRelQuotientDiffeomorphOfFreeProper` sends `[x]` to `[e x]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphOfFreeProper_mk (φ : G ≃* G') (e : M ≃ₘ⟮I, I'⟯ M')
    (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    orbitRelQuotientDiffeomorphOfFreeProper I IG I' IG' φ e he
      (Quotient.mk (MulAction.orbitRel G M) x) =
      Quotient.mk (MulAction.orbitRel G' M') (e x) := by
  let := freeProperQuotientChartedSpace I IG G M
  let := freeProperQuotientChartedSpace I' IG' G' M'
  exact MulAction.orbitRelQuotientCongr_mk φ e.toEquiv he x

/-- The inverse of `orbitRelQuotientDiffeomorphOfFreeProper` sends `[y]` to `[e.symm y]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphOfFreeProper_symm_mk (φ : G ≃* G') (e : M ≃ₘ⟮I, I'⟯ M')
    (he : ∀ (g : G) (x : M), e (g • x) = φ g • e x) (y : M') :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    (orbitRelQuotientDiffeomorphOfFreeProper I IG I' IG' φ e he).symm
      (Quotient.mk (MulAction.orbitRel G' M') y) =
      Quotient.mk (MulAction.orbitRel G M) (e.symm y) := by
  let := freeProperQuotientChartedSpace I IG G M
  let := freeProperQuotientChartedSpace I' IG' G' M'
  exact MulAction.orbitRelQuotientCongr_symm_mk φ e.toEquiv he y

end Equivariant

end Descent

/-! ### Additive Lie group actions -/

section Additive

section MultiplicativeTransfer

private def orbitRelQuotientEquivMul {G X : Type*} [AddGroup G] [AddAction G X] :
    _root_.AddAction.orbitRel.Quotient G X ≃ MulAction.orbitRel.Quotient (Multiplicative G) X :=
  Quotient.congrRight fun _ _ ↦ by
    rw [_root_.AddAction.orbitRel_apply, _root_.AddAction.mem_orbit_iff,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact Multiplicative.ofAdd.exists_congr_left

private def orbitRelQuotientHomeomorphMul {G X : Type*} [AddGroup G] [AddAction G X]
    [TopologicalSpace X] :
    _root_.AddAction.orbitRel.Quotient G X ≃ₜ MulAction.orbitRel.Quotient (Multiplicative G) X where
  toEquiv := orbitRelQuotientEquivMul
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.2 continuous_quot_mk
  continuous_invFun := isQuotientMap_quot_mk.continuous_iff.2 continuous_quot_mk

private theorem orbitRelQuotientHomeomorphMul_symm_mk {G X : Type*} [AddGroup G] [AddAction G X]
    [TopologicalSpace X] (x : X) :
    (orbitRelQuotientHomeomorphMul (G := G) (X := X)).symm
      (Quotient.mk (MulAction.orbitRel (Multiplicative G) X) x) =
      Quotient.mk (_root_.AddAction.orbitRel G X) x :=
  (rfl)

private theorem isCancelSMul_multiplicative {G M : Type*} [AddGroup G] [AddAction G M]
    [IsCancelVAdd G M] : IsCancelSMul (Multiplicative G) M where
  left_cancel' a := IsCancelVAdd.left_cancel a.toAdd
  right_cancel' a b c h :=
    Multiplicative.toAdd.injective (IsCancelVAdd.right_cancel a.toAdd b.toAdd c h)

private theorem properSMul_multiplicative {G M : Type*} [TopologicalSpace G] [TopologicalSpace M]
    [AddGroup G] [AddAction G M] [ProperVAdd G M] : ProperSMul (Multiplicative G) M where
  isProperMap_smul_pair := ProperVAdd.isProperMap_vadd_pair (G := G) (X := M)

end MultiplicativeTransfer

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless] [IG.Boundaryless]
  {G M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [AddGroup G] [LieAddGroup IG ∞ G]
  [AddAction G M] [ContMDiffVAdd IG I ∞ G M] [ProperVAdd G M] [IsCancelVAdd G M]

variable (G M) in
/-- **The transverse-slice atlas on `AddAction.orbitRel.Quotient G M`.** Pulled back from
`freeProperQuotientChartedSpace I IG (Multiplicative G) M` along the canonical homeomorphism with
`MulAction.orbitRel.Quotient (Multiplicative G) M`, for a free proper smooth action of an additive
Lie group `G` (such as a torus `(ℝ / 2πℤ)^k` or a closed Lie subgroup thereof). -/
@[instance_reducible]
def freeProperAddQuotientChartedSpace :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (_root_.AddAction.orbitRel.Quotient G M) :=
  letI := isCancelSMul_multiplicative (G := G) (M := M)
  letI := properSMul_multiplicative (G := G) (M := M)
  letI := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  (orbitRelQuotientHomeomorphMul (G := G) (X := M)).pullbackChartedSpace

/-- Equipped with `freeProperAddQuotientChartedSpace`, `AddAction.orbitRel.Quotient G M` is a smooth
manifold. -/
theorem isManifold_freeProperAddQuotient :
    letI := freeProperAddQuotientChartedSpace I IG G M
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (_root_.AddAction.orbitRel.Quotient G M) := by
  let := isCancelSMul_multiplicative (G := G) (M := M)
  let := properSMul_multiplicative (G := G) (M := M)
  let := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  have := isManifold_freeProperQuotient I IG (G := Multiplicative G) (M := M)
  exact (orbitRelQuotientHomeomorphMul (G := G) (X := M)).pullback_isManifold _ ∞

/-- The additive orbit projection `M → AddAction.orbitRel.Quotient G M` is a smooth submersion with
fibre complement `EG`. -/
theorem isSubmersionOfComplement_freeProperAddQuotientMk :
    letI := freeProperAddQuotientChartedSpace I IG G M
    IsSubmersionOfComplement EG I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (_root_.AddAction.orbitRel G M)) := by
  let := isCancelSMul_multiplicative (G := G) (M := M)
  let := properSMul_multiplicative (G := G) (M := M)
  let := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  have := isManifold_freeProperQuotient I IG (G := Multiplicative G) (M := M)
  let JQ := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  let e := orbitRelQuotientHomeomorphMul (G := G) (X := M)
  let := e.pullbackChartedSpace (H := Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  have := e.pullback_isManifold JQ ∞
  let Φ := (e.pullbackDiffeomorph JQ ∞).symm
  have hsub := isSubmersionOfComplement_freeProperQuotientMk I IG (G := Multiplicative G) (M := M)
  have hcomp : ⇑Φ ∘ Quotient.mk (MulAction.orbitRel (Multiplicative G) M) =
      Quotient.mk (_root_.AddAction.orbitRel G M) := by
    ext y
    simp only [comp_apply, Φ, Homeomorph.coe_pullbackDiffeomorph_symm, e,
      orbitRelQuotientHomeomorphMul_symm_mk]
  rw [← hcomp]
  refine isSubmersionOfComplement_iff.2 fun x ↦ ?_
  exact (Φ.isLocalDiffeomorph (Quotient.mk (MulAction.orbitRel (Multiplicative G) M)
    x)).comp_isSubmersionAtOfComplement (hsub.isSubmersionAt x)

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

/-- At every `x : M`, the kernel of the differential of the additive orbit projection is the orbit
tangent space of `Multiplicative G` at `x`. -/
theorem ker_mfderiv_freeProperAddQuotientMk (x : M) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    (mfderiv I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (Quotient.mk (_root_.AddAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG (Multiplicative G) I M).orbitTangent x := by
  let := isCancelSMul_multiplicative (G := G) (M := M)
  let := properSMul_multiplicative (G := G) (M := M)
  let := freeProperQuotientChartedSpace I IG (Multiplicative G) M
  have := isManifold_freeProperQuotient I IG (G := Multiplicative G) (M := M)
  let JQ := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  let e := orbitRelQuotientHomeomorphMul (G := G) (X := M)
  let := e.pullbackChartedSpace (H := Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  have := e.pullback_isManifold JQ ∞
  let Φ := (e.pullbackDiffeomorph JQ ∞).symm
  have hΦ : (mfderiv JQ JQ Φ
      (Quotient.mk (MulAction.orbitRel (Multiplicative G) M) x)).IsInvertible :=
    Φ.isInvertible_mfderiv (by simp)
  have hcomp : ⇑Φ ∘ Quotient.mk (MulAction.orbitRel (Multiplicative G) M) =
      Quotient.mk (_root_.AddAction.orbitRel G M) := by
    ext y
    simp only [comp_apply, Φ, Homeomorph.coe_pullbackDiffeomorph_symm, e,
      orbitRelQuotientHomeomorphMul_symm_mk]
  rw [← hcomp, mfderiv_comp x (Φ.contMDiffAt.mdifferentiableAt (by simp))
    (((contMDiff_freeProperQuotientMk I IG (G := Multiplicative G) (M := M)) x).mdifferentiableAt
      (by simp))]
  ext v
  rw [← SetLike.ext_iff.1 (ker_mfderiv_freeProperQuotientMk I IG (G := Multiplicative G) x) v]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  exact map_eq_zero_iff
    (mfderiv JQ JQ Φ (Quotient.mk (MulAction.orbitRel (Multiplicative G) M) x)) hΦ.injective

/-- Pointwise smooth descent (`m ≤ ∞`) for a `G`-invariant map out of a free proper smooth additive
Lie group action. -/
theorem contMDiffAt_addOrbitRelQuotientLift_of_freeProper_iff
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
theorem contMDiff_addOrbitRelQuotientLift_of_freeProper_iff
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
theorem existsUnique_contMDiff_freeProperAddQuotientMk_comp_eq
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

/-- Canonical diffeomorphism between `AddAction.orbitRel.Quotient G M` and the target of any
surjective smooth submersion `p : M → Q` whose fibres are the additive `G`-orbits. -/
def diffeomorphOfAddOrbitSubmersion
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (p : M → Q) (hp : IsSubmersion I JQ ∞ p) (hp_surj : Surjective p)
    (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g +ᵥ y = x) :
    letI := freeProperAddQuotientChartedSpace I IG G M
    _root_.AddAction.orbitRel.Quotient G M ≃ₘ⟮𝓘(ℝ,
      Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ), JQ⟯ Q :=
  letI := freeProperAddQuotientChartedSpace I IG G M
  let e : _root_.AddAction.orbitRel.Quotient G M ≃ Q :=
    Equiv.ofBijective
      (AddAction.orbitRelQuotientLift p fun g x ↦ (hfib (g +ᵥ x) x).2 ⟨g, rfl⟩)
      ⟨by
        rintro ⟨x⟩ ⟨y⟩ hxy
        change AddAction.orbitRelQuotientLift p _ (Quotient.mk (_root_.AddAction.orbitRel G M) x) =
          AddAction.orbitRelQuotientLift p _ (Quotient.mk (_root_.AddAction.orbitRel G M) y) at hxy
        rw [AddAction.orbitRelQuotientLift_mk, AddAction.orbitRelQuotientLift_mk] at hxy
        exact Quotient.sound (_root_.AddAction.orbitRel_apply.2 (_root_.AddAction.mem_orbit_iff.2
          ((hfib x y).1 hxy))),
       fun q ↦ by
        obtain ⟨x, rfl⟩ := hp_surj q
        exact ⟨Quotient.mk _ x, AddAction.orbitRelQuotientLift_mk x⟩⟩
  e.diffeomorphOfSubmersions (isSubmersion_freeProperAddQuotientMk I IG) Quotient.mk_surjective
    hp hp_surj (by ext x; exact AddAction.orbitRelQuotientLift_mk x)

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
  rw [diffeomorphOfAddOrbitSubmersion, Equiv.diffeomorphOfSubmersions_apply]
  exact AddAction.orbitRelQuotientLift_mk x

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
    [I.Boundaryless] [IG.Boundaryless]
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
