/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.Orbit
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.Submersion.Descent
public import TauCeti.Topology.Algebra.GroupAction.Quotient
import TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# Quotients of manifolds by free proper Lie group actions

Let a finite-dimensional real Lie group `G`, modelled on a boundaryless model `(EG, IG)`, act
smoothly, freely, and properly on a boundaryless smooth manifold `M`, modelled on a
finite-dimensional real space `(E, I)`. The **quotient manifold theorem** equips the orbit space
`MulAction.orbitRel.Quotient G M`, retaining its native quotient topology, with a smooth manifold
structure of dimension `dim E - dim EG` for which the orbit projection
`Quotient.mk (MulAction.orbitRel G M)` is a surjective smooth submersion with vertical tangent
spaces equal to the orbit tangent spaces `𝔤 · x`.

## Mathematical overview

The construction combines four local ingredients around each point `x ∈ M`:

1. **Local freeness and complement dimension.** Because the action is free and proper and `G` is a
   Hausdorff Lie group, `M` is Hausdorff (`t2Space_of_properSMul_of_t1Group`) and the orbit map
   `g ↦ g • x` is a smooth embedding (`TauCeti.isSmoothEmbedding_smul_const`). Its differential at
   `1` is injective, so the isotropy Lie algebra `𝔤_x` vanishes
   (`TauCeti.isotropy_fundamental_eq_bot_of_properSMul`) and the orbit tangent space `𝔤 · x` has
   dimension `dim EG`. Every linear complement `W` of `𝔤 · x` in `E` therefore has dimension
   `n = dim E - dim EG`.
2. **Transverse chart slices.** Reading a linear equivalence `(Fin n → ℝ) ≃L[ℝ] W` through the
   extended chart `φ` at `x` defines a smooth slice `σ_x : (Fin n → ℝ) → M`,
   `u ↦ φ⁻¹ (φ x + e u)`, passing through `x` at `0`, whose slice map `(g, u) ↦ g • σ_x u` is a
   local diffeomorphism at `(1, 0)` (`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`), hence
   along `G × U₀` for a neighbourhood `U₀` of `0`
   (`IsLocalDiffeomorphAt.eventually_forall_smul_slice`).
3. **Properness and open slice charts.** Properness shrinks `U₀` to an open neighbourhood `U_x` of
   `0` in `Fin n → ℝ` on which `(g, u) ↦ g • σ_x u` is globally injective on `G × U_x`
   (`ProperSMul.exists_mem_nhds_injOn_smul_slice`). On `U_x`, the composite `u ↦ [σ_x u]` into the
   orbit space is an open topological embedding
   (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`), while `(g, u) ↦ g • σ_x u` is an open
   smooth embedding and local diffeomorphism of `G × U_x` onto an open `G`-invariant tube around
   the orbit of `x`.
4. **Gluing and submersion normal form.** Transporting the Euclidean charts of the open sets
   `U_x ⊆ Fin n → ℝ` along these open embeddings via `TauCeti.chartedSpaceOfIsOpenEmbedding` equips
   `MulAction.orbitRel.Quotient G M` with an atlas whose overlap transitions are smooth by
   `TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`. Near `x`, the orbit projection factors
   smoothly through the slice coordinate `M → U_x` followed by the chart embedding `U_x → M ⧸ G`,
   and precomposing it with the smooth slice `U_x → M` gives that local diffeomorphism `U_x → M ⧸ G`
   with invertible differential at `0`; hence the orbit projection is smooth with surjective
   differentials, and `ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv` supplies its
   submersion normal form with complement `EG`.

## Design notes

* **Explicit charted-space constructor.** Because the carrier `MulAction.orbitRel.Quotient G M`
  does not mention the models `I`, `IG` or the target dimension `n` (and Mathlib already registers
  a global `ChartedSpace` instance for discrete `ProperlyDiscontinuousSMul` actions), the smooth
  atlas is provided as an `@[instance_reducible]` definition
  `TauCeti.freeProperQuotientChartedSpace` rather than a global instance.
* **Flexible model dimension.** As in `TauCeti.regularLevelChartedSpace` and
  `TauCeti.SmoothTwoForm.IsMomentMap.levelChartedSpace`, the model space is `Fin n → ℝ` for a
  parameter `n : ℕ` accompanied by `(hn : Module.finrank ℝ E - Module.finrank ℝ EG = n)`, allowing
  downstream callers (such as symplectic reduction or toric quotients) to supply simplified
  dimension expressions directly; passing `rfl` specializes to
  `Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ`, as in the existential statement
  `TauCeti.exists_freeProperQuotient_isSubmersion`.
* **Separation, second countability, and empty source.** Neither explicit Hausdorff hypotheses on
  `M` and `G` nor second countability are needed to construct the atlas or prove the submersion
  property, and `M` may be empty. Because the atlas retains the native quotient topology, the
  quotient automatically inherits `T2Space` from `t2Space_quotient_mulAction_of_properSMul`, and
  when `M` is second countable, `SecondCountableTopology` on the quotient is obtained from the
  theorem `ContinuousConstSMul.secondCountableTopology` together with
  `ContMDiffSMul.continuousSMul`.

## Main declarations

* `TauCeti.isotropy_fundamental_eq_bot_of_properSMul`,
  `TauCeti.finrank_orbitTangent_fundamental_of_isotropy_eq_bot`,
  `TauCeti.finrank_le_of_properSMul`, and `TauCeti.finrank_freeProperQuotient_add_finrank`:
  vanishing of the isotropy Lie algebra, dimension of the orbit tangent space, and exactness of
  `dim E - dim EG` when `M` is nonempty.
* `TauCeti.exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice`: existence of smooth transverse
  slice charts and equivariant open-tube local diffeomorphisms around every point of `M`.
* `TauCeti.freeProperQuotientChartedSpace` and `TauCeti.isManifold_freeProperQuotient`: the smooth
  manifold atlas on `MulAction.orbitRel.Quotient G M`.
* `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
  `TauCeti.isSubmersion_quotientMk_freeProperQuotient`,
  `TauCeti.contMDiff_quotientMk_freeProperQuotient`,
  `TauCeti.surjective_mfderiv_quotientMk_freeProperQuotient`, and
  `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`: the orbit projection is a smooth submersion
  with complement `EG` whose vertical tangent kernel is the orbit tangent space `𝔤 · x`.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: existential form of the quotient manifold
  theorem on `Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ`.
* `TauCeti.contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.existsUnique_contMDiff_comp_quotientMk_freeProperQuotient`,
  `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`,
  `TauCeti.isImmersion_orbitRelQuotientLift_freeProperQuotient_iff`, and
  `TauCeti.isSmoothEmbedding_orbitRelQuotientLift_freeProperQuotient_iff`: smooth descent of
  invariant and equivariant maps, immersions, and embeddings.
* `TauCeti.diffeomorphOfIsSubmersionOrbitEq` and `TauCeti.maximalAtlas_freeProperQuotient_eq`:
  uniqueness of the quotient manifold structure up to canonical diffeomorphism and equality of
  maximal atlases.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer, 2013, Theorem 21.10 (the quotient manifold theorem) and Theorem 4.31 (uniqueness
  of quotient manifold structures).
* Eckhard Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21, pp. 10–11.
-/

public section

noncomputable section

open Function Set Filter Manifold Module TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-! ### Infinitesimal freeness and dimension of orbit tangent spaces -/

section Dimension

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  {I : ModelWithCorners ℝ E H} {IG : ModelWithCorners ℝ EG HG}
  {M G : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M]

/-- At a locally free point `x` (`𝔤_x = 0`), the orbit tangent space `𝔤 · x` has the dimension of
the model space `EG` of `G`. -/
theorem finrank_orbitTangent_fundamental_of_isotropy_eq_bot {x : M}
    (hx : (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥) :
    finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) = finrank ℝ EG := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have hsum := InfinitesimalAction.finrank_orbitTangent_add_finrank_isotropy
    (InfinitesimalAction.fundamental IG G I M) x
  have hbot : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).isotropy x) = 0 := by
    have h0 := hx
    rw [LieSubalgebra.eq_bot_iff] at h0
    have : Subsingleton ↥((InfinitesimalAction.fundamental IG G I M).isotropy x) :=
      ⟨fun a b ↦ Subtype.ext ((h0 a.1 a.2).trans (h0 b.1 b.2).symm)⟩
    exact finrank_zero_of_subsingleton
  rw [hbot, add_zero] at hsum
  exact hsum

/-- Where an action has a locally free point `x`, the dimension of `G` is at most the dimension of
`M`. -/
theorem finrank_le_of_isotropy_eq_bot {x : M}
    (hx : (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥) :
    finrank ℝ EG ≤ finrank ℝ E := by
  rw [← finrank_orbitTangent_fundamental_of_isotropy_eq_bot hx]
  exact Submodule.finrank_le ((InfinitesimalAction.fundamental IG G I M).orbitTangent x)

variable [I.Boundaryless] [IG.Boundaryless]

/-- **Free proper smooth actions are locally free.** For a free proper smooth action of a
finite-dimensional boundaryless real Lie group, the isotropy Lie algebra `𝔤_x` vanishes at every
point `x : M`. -/
theorem isotropy_fundamental_eq_bot_of_properSMul [ProperSMul G M] [IsCancelSMul G M] (x : M) :
    (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have hx : MulAction.stabilizer G x = ⊥ :=
    isCancelSMul_iff_stabilizer_eq_bot.mp inferInstance x
  exact isImmersion_smul_const_iff.mp
    (isSmoothEmbedding_smul_const (I := IG) (I' := I) hx).isImmersion

/-- For a free proper smooth action on `M`, every orbit tangent space `𝔤 · x` has dimension
`dim EG`. -/
theorem finrank_orbitTangent_fundamental_of_properSMul [ProperSMul G M] [IsCancelSMul G M]
    (x : M) :
    finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) = finrank ℝ EG :=
  finrank_orbitTangent_fundamental_of_isotropy_eq_bot
    (isotropy_fundamental_eq_bot_of_properSMul x)

include I IG in
/-- For a free proper smooth action on a nonempty manifold `M`, `dim G ≤ dim M`. -/
theorem finrank_le_of_properSMul [ProperSMul G M] [IsCancelSMul G M] [Nonempty M] :
    finrank ℝ EG ≤ finrank ℝ E :=
  let ⟨x⟩ := ‹Nonempty M›
  finrank_le_of_isotropy_eq_bot
    (isotropy_fundamental_eq_bot_of_properSMul (I := I) (IG := IG) (G := G) x)

include I IG in
/-- When `M` is nonempty and `dim E - dim EG = n`, the quotient dimension satisfies
`n + dim EG = dim E`. -/
theorem finrank_freeProperQuotient_add_finrank [ProperSMul G M] [IsCancelSMul G M] [Nonempty M]
    {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) :
    n + finrank ℝ EG = finrank ℝ E := by
  have hle := finrank_le_of_properSMul (I := I) (IG := IG) (M := M) (G := G)
  omega

end Dimension

/-! ### Transverse slice charts of free proper actions -/

section SliceData

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  {I : ModelWithCorners ℝ E H} {IG : ModelWithCorners ℝ EG HG}
  [I.Boundaryless] [IG.Boundaryless]
  {M G : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ProperSMul G M] [ContMDiffSMul IG I ∞ G M] [IsCancelSMul G M]

variable (IG G) in
/-- **Transverse slice tubes around orbits of a free proper action.** For `dim E - dim EG = n` and
any point `x : M`, there exist an open neighbourhood `U` of `0` in `Fin n → ℝ` and a map
`σ : (Fin n → ℝ) → M` sending `0` to `x` such that `σ` is smooth on `U` and the slice map
`(g, u) ↦ g • σ u` is injective and a smooth local diffeomorphism on `univ ×ˢ U`. Consequently
`(g, u) ↦ g • σ u.1 : G × U → M` and `u ↦ [σ u.1] : U → M ⧸ G` are open embeddings. -/
theorem exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice {n : ℕ}
    (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    ∃ (U : Opens (Fin n → ℝ)) (σ : (Fin n → ℝ) → M),
      (0 : Fin n → ℝ) ∈ U ∧ σ 0 = x ∧
      ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ σ U ∧
      InjOn (fun p : G × (Fin n → ℝ) ↦ p.1 • σ p.2) (univ ×ˢ (U : Set (Fin n → ℝ))) ∧
      IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin n → ℝ)) I ∞
        (fun p : G × (Fin n → ℝ) ↦ p.1 • σ p.2) (univ ×ˢ (U : Set (Fin n → ℝ))) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : BoundarylessManifold IG G := inferInstance
  have hx_iso : (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ :=
    isotropy_fundamental_eq_bot_of_properSMul x
  -- Choose a linear complement `W` of `𝔤 · x` in `E` and identify `Fin n → ℝ` with `W`.
  obtain ⟨W, hW⟩ :
      ∃ W : Submodule ℝ E, IsCompl ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) W :=
    Submodule.exists_isCompl _
  have hW_dim : finrank ℝ (Fin n → ℝ) = finrank ℝ W := by
    have hadd :
        finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) + finrank ℝ W =
          finrank ℝ E :=
      Submodule.finrank_add_eq_of_isCompl hW
    have horb : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) =
        finrank ℝ EG :=
      finrank_orbitTangent_fundamental_of_isotropy_eq_bot hx_iso
    rw [finrank_fin_fun]
    omega
  let eW : (Fin n → ℝ) ≃L[ℝ] W :=
    (LinearEquiv.ofFinrankEq (Fin n → ℝ) W hW_dim).toContinuousLinearEquiv
  let σ : (Fin n → ℝ) → M := fun u ↦ (extChartAt I x).symm (extChartAt I x x + (eW u : E))
  have hσ0 : σ 0 = x := by
    simp only [σ, map_zero, ZeroMemClass.coe_zero, add_zero, extChartAt_to_inv]
  -- Smoothness of `σ` near `0`, on the preimage of the extended chart target.
  let τ : (Fin n → ℝ) → E := fun u ↦ extChartAt I x x + (eW u : E)
  have hτ_smooth : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, E) ∞ τ :=
    (contDiff_const.add (W.subtypeL.comp eW.toContinuousLinearMap).contDiff).contMDiff
  have hVσ_open : IsOpen (τ ⁻¹' (extChartAt I x).target) :=
    (isOpen_extChartAt_target x).preimage hτ_smooth.continuous
  have h0_Vσ : (0 : Fin n → ℝ) ∈ τ ⁻¹' (extChartAt I x).target := by
    simp only [mem_preimage, τ, map_zero, ZeroMemClass.coe_zero, add_zero]
    exact mem_extChartAt_target x
  have hσ_smooth : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ σ (τ ⁻¹' (extChartAt I x).target) :=
    (contMDiffOn_extChartAt_symm x).comp hτ_smooth.contMDiffOn fun _ hu ↦ hu
  -- Precompose the `G × W` slice map with `id × eW` to obtain a local diffeomorphism at `(1, 0)`.
  have hlocW : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, W)) I ∞
      (fun p : G × W ↦ p.1 • (extChartAt I x).symm (extChartAt I x x + p.2)) (1, 0) :=
    isLocalDiffeomorphAt_smul_extChartAt_symm hx_iso hW
  let Φ : (G × (Fin n → ℝ)) ≃ₘ⟮IG.prod 𝓘(ℝ, Fin n → ℝ), IG.prod 𝓘(ℝ, W)⟯ (G × W) :=
    { toEquiv := (Equiv.refl G).prodCongr eW.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (eW.contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (eW.symm.contDiff.contMDiff.comp contMDiff_snd) }
  have hloc10 : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin n → ℝ)) I ∞
      (fun p : G × (Fin n → ℝ) ↦ p.1 • σ p.2) (1, 0) := by
    have hΦ0 : Φ (1, 0) = (1, 0) := Prod.ext rfl (map_zero eW)
    exact IsLocalDiffeomorphAt.comp (x := (1, 0)) (hg := hΦ0 ▸ hlocW)
      (hf := Φ.isLocalDiffeomorph (1, 0))
  -- Propagate `IsLocalDiffeomorphAt` along `G` and use properness to shrink to a global tube.
  have hev_loc : ∀ᶠ u in 𝓝 (0 : Fin n → ℝ), ∀ g : G,
      IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin n → ℝ)) I ∞
        (fun p : G × (Fin n → ℝ) ↦ p.1 • σ p.2) (g, u) :=
    hloc10.eventually_forall_smul_slice
  obtain ⟨N, hN, hinjN⟩ := hloc10.exists_mem_nhds_injOn
  have hfree0 : MulAction.stabilizer G (σ 0) = ⊥ := by
    rw [hσ0]
    exact isCancelSMul_iff_stabilizer_eq_bot.mp inferInstance x
  have hσ_cont : ContinuousAt σ 0 :=
    (hσ_smooth.contMDiffAt (hVσ_open.mem_nhds h0_Vσ)).continuousAt
  obtain ⟨U₁, hU₁, hinjU₁⟩ :=
    ProperSMul.exists_mem_nhds_injOn_smul_slice hσ_cont hfree0 hN hinjN
  -- Take the open interior of the intersection of all three neighbourhoods of `0`.
  let S : Set (Fin n → ℝ) :=
    U₁ ∩ (τ ⁻¹' (extChartAt I x).target) ∩
      {u | ∀ g : G, IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin n → ℝ)) I ∞
        (fun p : G × (Fin n → ℝ) ↦ p.1 • σ p.2) (g, u)}
  have hS_nhds : S ∈ 𝓝 (0 : Fin n → ℝ) :=
    inter_mem (inter_mem hU₁ (hVσ_open.mem_nhds h0_Vσ)) hev_loc
  refine ⟨⟨interior S, isOpen_interior⟩, σ, mem_interior_iff_mem_nhds.mpr hS_nhds, hσ0,
    hσ_smooth.mono (interior_subset.trans (inter_subset_left.trans inter_subset_right)),
    hinjU₁.mono (prod_mono_right
      (interior_subset.trans (inter_subset_left.trans inter_subset_left))),
    fun p ↦ (interior_subset.trans inter_subset_right p.2.2) p.1.1⟩

namespace FreeProperQuotient

/-- Chosen open slice domain `U_x ⊆ Fin n → ℝ` at `x : M`. -/
private def sliceDomain {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    Opens (Fin n → ℝ) :=
  (exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice (I := I) IG G hn x).choose

/-- Chosen smooth transverse slice `σ_x : (Fin n → ℝ) → M` through `x`. -/
private def sliceMap {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    (Fin n → ℝ) → M :=
  (exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice (I := I) IG G hn x).choose_spec.choose

private theorem zero_mem_sliceDomain {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    (0 : Fin n → ℝ) ∈ sliceDomain (I := I) (IG := IG) (G := G) hn x :=
  (exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice
    (I := I) IG G hn x).choose_spec.choose_spec.1

private theorem sliceMap_zero {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    sliceMap (I := I) (IG := IG) (G := G) hn x 0 = x :=
  (exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice
    (I := I) IG G hn x).choose_spec.choose_spec.2.1

private theorem contMDiffOn_sliceMap {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ (sliceMap (I := I) (IG := IG) (G := G) hn x)
      (sliceDomain (I := I) (IG := IG) (G := G) hn x) :=
  (exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice
    (I := I) IG G hn x).choose_spec.choose_spec.2.2.1

private theorem injOn_smul_sliceMap {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    InjOn (fun p : G × (Fin n → ℝ) ↦ p.1 • sliceMap (I := I) (IG := IG) (G := G) hn x p.2)
      (univ ×ˢ (sliceDomain (I := I) (IG := IG) (G := G) hn x : Set (Fin n → ℝ))) :=
  (exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice
    (I := I) IG G hn x).choose_spec.choose_spec.2.2.2.1

private theorem isLocalDiffeomorphOn_smul_sliceMap {n : ℕ}
    (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin n → ℝ)) I ∞
      (fun p : G × (Fin n → ℝ) ↦ p.1 • sliceMap (I := I) (IG := IG) (G := G) hn x p.2)
      (univ ×ˢ (sliceDomain (I := I) (IG := IG) (G := G) hn x : Set (Fin n → ℝ))) :=
  (exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice
    (I := I) IG G hn x).choose_spec.choose_spec.2.2.2.2

/-- The open embedding `u ↦ [σ_x u]` from the slice domain `U_x` into `M ⧸ G`. -/
private def pieceEmbedding {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) (x : M)
    (u : sliceDomain (I := I) (IG := IG) (G := G) hn x) :
    MulAction.orbitRel.Quotient G M :=
  Quotient.mk (MulAction.orbitRel G M) (sliceMap (I := I) (IG := IG) (G := G) hn x u.1)

private theorem isOpenEmbedding_pieceEmbedding {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) :
    ∀ x : M, IsOpenEmbedding (pieceEmbedding (I := I) (IG := IG) (G := G) hn x) := fun x ↦
  MulAction.isOpenEmbedding_quotientMk_slice
    (sliceDomain (I := I) (IG := IG) (G := G) hn x).isOpen
    (injOn_smul_sliceMap hn x)
    (isLocalDiffeomorphOn_smul_sliceMap hn x).isLocalHomeomorphOn

private theorem cover_pieceEmbedding {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) :
    ∀ q : MulAction.orbitRel.Quotient G M,
      ∃ (x : M) (u : sliceDomain (I := I) (IG := IG) (G := G) hn x),
        pieceEmbedding (I := I) (IG := IG) (G := G) hn x u = q := by
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  refine ⟨x, ⟨0, zero_mem_sliceDomain hn x⟩, ?_⟩
  simp [pieceEmbedding, sliceMap_zero]

private theorem deck_pieceEmbedding {n : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) :
    ∀ (x y : M) (u : sliceDomain (I := I) (IG := IG) (G := G) hn x)
      (v : sliceDomain (I := I) (IG := IG) (G := G) hn y),
      pieceEmbedding (I := I) (IG := IG) (G := G) hn x u =
        pieceEmbedding (I := I) (IG := IG) (G := G) hn y v →
      ∃ T : sliceDomain (I := I) (IG := IG) (G := G) hn x →
          sliceDomain (I := I) (IG := IG) (G := G) hn y,
        ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ T u ∧
        pieceEmbedding (I := I) (IG := IG) (G := G) hn y ∘ T =ᶠ[𝓝 u]
          pieceEmbedding (I := I) (IG := IG) (G := G) hn x := by
  intro x y u v huv
  have hfu : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞
      (fun u' : sliceDomain (I := I) (IG := IG) (G := G) hn x ↦
        sliceMap (I := I) (IG := IG) (G := G) hn x u'.1) u := by
    have h1 := (contMDiffOn_sliceMap (I := I) (IG := IG) (G := G) hn x).contMDiffAt
      ((sliceDomain (I := I) (IG := IG) (G := G) hn x).isOpen.mem_nhds u.2)
    exact h1.comp u (isLocalDiffeomorph_subtype_val u).contMDiffAt
  obtain ⟨t, ht, -, hev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff
    (sliceDomain (I := I) (IG := IG) (G := G) hn y).isOpen
    (injOn_smul_sliceMap hn y)
    (isLocalDiffeomorphOn_smul_sliceMap hn y)
    hfu v.2 huv.symm
  classical
  let T : sliceDomain (I := I) (IG := IG) (G := G) hn x →
      sliceDomain (I := I) (IG := IG) (G := G) hn y :=
    fun u' ↦
      if h : t u' ∈ (sliceDomain (I := I) (IG := IG) (G := G) hn y : Set (Fin n → ℝ)) then
        ⟨t u', h⟩
      else v
  have hT_val : Subtype.val ∘ T =ᶠ[𝓝 u] t := by
    filter_upwards [hev] with u' hu'
    simp only [comp_apply, T]
    split_ifs with h
    · rfl
    · exact (h hu'.1).elim
  refine ⟨T, ?_, ?_⟩
  · rw [← ContMDiffAt.subtypeVal_comp_iff (sliceDomain (I := I) (IG := IG) (G := G) hn y)]
    exact ht.congr_of_eventuallyEq hT_val
  · filter_upwards [hev] with u' hu'
    simp only [comp_apply, pieceEmbedding, T]
    split_ifs with h
    · exact (hu'.2 (t u') hu'.1).mpr rfl
    · exact (h hu'.1).elim

end FreeProperQuotient

end SliceData

/-! ### The quotient manifold structure and submersion projection -/

section QuotientManifold

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  {I : ModelWithCorners ℝ E H} {IG : ModelWithCorners ℝ EG HG}
  [I.Boundaryless] [IG.Boundaryless]
  {M G : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ProperSMul G M] [ContMDiffSMul IG I ∞ G M] [IsCancelSMul G M]
  {n : ℕ}

variable (I IG M G) in
/-- **Smooth atlas on the orbit space of a free proper Lie group action.** For a smooth, free,
proper action of a finite-dimensional boundaryless real Lie group `G` on a finite-dimensional
boundaryless smooth manifold `M`, with `dim E - dim EG = n`, this equips
`MulAction.orbitRel.Quotient G M` (with its quotient topology) with charts in `Fin n → ℝ`
transported from transverse slice open subsets. This is not a global instance because the carrier
does not mention `I`, `IG` or `n`. -/
@[instance_reducible]
def freeProperQuotientChartedSpace (hn : finrank ℝ E - finrank ℝ EG = n) :
    ChartedSpace (Fin n → ℝ) (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding
    (FreeProperQuotient.isOpenEmbedding_pieceEmbedding (I := I) (IG := IG) (G := G) (M := M) hn)
    (FreeProperQuotient.cover_pieceEmbedding (I := I) (IG := IG) (G := G) (M := M) hn)

variable (I IG M G) in
/-- **The orbit space of a free proper Lie group action is a smooth manifold** of dimension
`n = dim E - dim EG` for `TauCeti.freeProperQuotientChartedSpace`. -/
theorem isManifold_freeProperQuotient (hn : finrank ℝ E - finrank ℝ EG = n) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding
    (FreeProperQuotient.isOpenEmbedding_pieceEmbedding (I := I) (IG := IG) (G := G) (M := M) hn)
    (FreeProperQuotient.cover_pieceEmbedding (I := I) (IG := IG) (G := G) (M := M) hn)
    (FreeProperQuotient.deck_pieceEmbedding (I := I) (IG := IG) (G := G) (M := M) hn)

variable (I IG M G) in
/-- The orbit projection `Quotient.mk (MulAction.orbitRel G M)` of a free proper Lie group action
is smooth with respect to `freeProperQuotientChartedSpace`. -/
theorem contMDiff_quotientMk_freeProperQuotient (hn : finrank ℝ E - finrank ℝ EG = n) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    ContMDiff I 𝓘(ℝ, Fin n → ℝ) ∞ (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace I IG M G hn
  have := isManifold_freeProperQuotient I IG M G hn
  intro x
  set U := FreeProperQuotient.sliceDomain (I := I) (IG := IG) (G := G) hn x
  have h0 : (0 : Fin n → ℝ) ∈ U := FreeProperQuotient.zero_mem_sliceDomain hn x
  have hfx : Quotient.mk (MulAction.orbitRel G M)
      (FreeProperQuotient.sliceMap (I := I) (IG := IG) (G := G) hn x 0) =
      Quotient.mk (MulAction.orbitRel G M) x := by
    rw [FreeProperQuotient.sliceMap_zero]
  obtain ⟨t, ht, -, hev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff U.isOpen
    (FreeProperQuotient.injOn_smul_sliceMap hn x)
    (FreeProperQuotient.isLocalDiffeomorphOn_smul_sliceMap hn x)
    (f := id) contMDiffAt_id h0 hfx
  classical
  let T : M → U := fun y ↦ if h : t y ∈ (U : Set (Fin n → ℝ)) then ⟨t y, h⟩ else ⟨0, h0⟩
  have hT_val : Subtype.val ∘ T =ᶠ[𝓝 x] t := by
    filter_upwards [hev] with y hy
    simp only [comp_apply, T]
    split_ifs with h
    · rfl
    · exact (h hy.1).elim
  have hT : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ T x := by
    rw [← ContMDiffAt.subtypeVal_comp_iff U]
    exact ht.congr_of_eventuallyEq hT_val
  have hφ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
      (FreeProperQuotient.pieceEmbedding (I := I) (IG := IG) (G := G) hn x) :=
    contMDiff_chartedSpaceOfIsOpenEmbedding
      (FreeProperQuotient.isOpenEmbedding_pieceEmbedding (I := I) (IG := IG) (G := G) hn)
      (FreeProperQuotient.cover_pieceEmbedding (I := I) (IG := IG) (G := G) hn)
      (FreeProperQuotient.deck_pieceEmbedding (I := I) (IG := IG) (G := G) hn) x
  refine ((hφ (T x)).comp x hT).congr_of_eventuallyEq ?_
  filter_upwards [hev] with y hy
  simp only [comp_apply, FreeProperQuotient.pieceEmbedding, T]
  split_ifs with h
  · exact ((hy.2 (t y) hy.1).mpr rfl).symm
  · exact (h hy.1).elim

variable (I IG G) in
/-- At every point `x : M`, the differential
`mfderiv I 𝓘(ℝ, Fin n → ℝ) (Quotient.mk (MulAction.orbitRel G M)) x` of the orbit projection is
surjective. -/
theorem surjective_mfderiv_quotientMk_freeProperQuotient
    (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    Surjective (mfderiv I 𝓘(ℝ, Fin n → ℝ) (Quotient.mk (MulAction.orbitRel G M)) x) := by
  let := freeProperQuotientChartedSpace I IG M G hn
  have := isManifold_freeProperQuotient I IG M G hn
  set U := FreeProperQuotient.sliceDomain (I := I) (IG := IG) (G := G) hn x
  let u₀ : U := ⟨0, FreeProperQuotient.zero_mem_sliceDomain hn x⟩
  let s : U → M := fun u ↦ FreeProperQuotient.sliceMap (I := I) (IG := IG) (G := G) hn x u.1
  have hs₀ : s u₀ = x := FreeProperQuotient.sliceMap_zero hn x
  have hs : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ s u₀ :=
    ((FreeProperQuotient.contMDiffOn_sliceMap (I := I) (IG := IG) (G := G) hn x).contMDiffAt
      (U.isOpen.mem_nhds u₀.2)).comp u₀ (isLocalDiffeomorph_subtype_val u₀).contMDiffAt
  have hφ : IsLocalDiffeomorph 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
      (FreeProperQuotient.pieceEmbedding (I := I) (IG := IG) (G := G) hn x) :=
    isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
      (FreeProperQuotient.isOpenEmbedding_pieceEmbedding (I := I) (IG := IG) (G := G) hn)
      (FreeProperQuotient.cover_pieceEmbedding (I := I) (IG := IG) (G := G) hn)
      (FreeProperQuotient.deck_pieceEmbedding (I := I) (IG := IG) (G := G) hn) x
  have hsurj : Surjective
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
        (Quotient.mk (MulAction.orbitRel G M) ∘ s) u₀) :=
    ((hφ u₀).isInvertible_mfderiv (by simp)).surjective
  have hq_diff : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) (s u₀) :=
    (contMDiff_quotientMk_freeProperQuotient I IG M G hn (s u₀)).mdifferentiableAt (by simp)
  rw [mfderiv_comp u₀ hq_diff (hs.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
    at hsurj
  have h := hsurj.of_comp
  rwa [hs₀] at h

variable (I IG M G) in
/-- **The orbit projection of a free proper Lie group action is a smooth submersion with complement
`EG`.** -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient
    (hn : finrank ℝ E - finrank ℝ EG = n) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    IsSubmersionOfComplement EG I 𝓘(ℝ, Fin n → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace I IG M G hn
  have := isManifold_freeProperQuotient I IG M G hn
  have hsub :=
    (contMDiff_quotientMk_freeProperQuotient I IG M G hn
      ).isSubmersionOfComplement_of_surjective_mfderiv
      (by simp) (surjective_mfderiv_quotientMk_freeProperQuotient I IG G hn)
  refine isSubmersionOfComplement_iff.mpr fun x ↦ ?_
  have : Nonempty M := ⟨x⟩
  have hdim := finrank_freeProperQuotient_add_finrank (I := I) (IG := IG) (M := M) (G := G) hn
  have hK : finrank ℝ (Fin (finrank ℝ E - finrank ℝ (Fin n → ℝ)) → ℝ) = finrank ℝ EG := by
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
    omega
  let K : (Fin (finrank ℝ E - finrank ℝ (Fin n → ℝ)) → ℝ) ≃L[ℝ] EG :=
    (LinearEquiv.ofFinrankEq _ _ hK).toContinuousLinearEquiv
  exact (IsSubmersionAtOfComplement.congr_F K).mp (hsub.isSubmersionAt x)

variable (I IG M G) in
/-- **The orbit projection of a free proper Lie group action is a smooth submersion.** -/
theorem isSubmersion_quotientMk_freeProperQuotient (hn : finrank ℝ E - finrank ℝ EG = n) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    IsSubmersion I 𝓘(ℝ, Fin n → ℝ) ∞ (Quotient.mk (MulAction.orbitRel G M)) :=
  letI := freeProperQuotientChartedSpace I IG M G hn
  (isSubmersionOfComplement_quotientMk_freeProperQuotient I IG M G hn).isSubmersion

variable (I IG G) in
/-- **Smooth local sections of the orbit projection.** Around the orbit of any point `x : M`, the
orbit projection `M → M ⧸ G` admits a smooth local section defined on an open neighbourhood of
`[x]` and sending `[x]` to `x`. -/
theorem exists_contMDiffOn_section_quotientMk_freeProperQuotient
    (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    ∃ U : Set (MulAction.orbitRel.Quotient G M),
      IsOpen U ∧ Quotient.mk (MulAction.orbitRel G M) x ∈ U ∧
      ∃ s : MulAction.orbitRel.Quotient G M → M,
        s (Quotient.mk (MulAction.orbitRel G M) x) = x ∧
        ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ s U ∧
        ∀ q ∈ U, Quotient.mk (MulAction.orbitRel G M) (s q) = q :=
  letI := freeProperQuotientChartedSpace I IG M G hn
  ((isSubmersion_quotientMk_freeProperQuotient I IG M G hn
    ).isSubmersionAt x).exists_contMDiffOn_section

variable (I IG G) in
/-- **Vertical tangent spaces of the orbit projection.** At every point `x : M`, the kernel of the
differential of `Quotient.mk : M → M ⧸ G` is the orbit tangent space `𝔤 · x` spanned by the
fundamental vector fields of the action. -/
theorem ker_mfderiv_quotientMk_freeProperQuotient
    (hn : finrank ℝ E - finrank ℝ EG = n) (x : M) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    (mfderiv I 𝓘(ℝ, Fin n → ℝ) (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG M G hn
  have := isManifold_freeProperQuotient I IG M G hn
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : Nonempty M := ⟨x⟩
  -- Every orbit tangent vector comes from differentiating `g ↦ g • x` at `1`, which `Quotient.mk`
  -- sends to the constant `[x]`.
  have hle : (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤
      (mfderiv I 𝓘(ℝ, Fin n → ℝ) (Quotient.mk (MulAction.orbitRel G M)) x).ker := by
    have hrange := range_mfderiv_smul_const (I := IG) (I' := I) (G := G) x 1
    rw [one_smul] at hrange
    rw [← hrange]
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    have hq_diff : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) (Quotient.mk (MulAction.orbitRel G M))
        ((1 : G) • x) := by
      rw [one_smul]
      exact (contMDiff_quotientMk_freeProperQuotient I IG M G hn x).mdifferentiableAt (by simp)
    have horb_diff : MDifferentiableAt IG I (fun g : G ↦ g • x) 1 :=
      ((ContMDiffSMul.contMDiff_smul_const (I := IG) (I' := I) (n := ∞) x) 1).mdifferentiableAt
        (by simp)
    have hconst : (Quotient.mk (MulAction.orbitRel G M) ∘ fun g : G ↦ g • x) =
        fun _ : G ↦ Quotient.mk (MulAction.orbitRel G M) ((1 : G) • x) :=
      funext fun g ↦ Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, by simp⟩)
    have hchain :
        mfderiv I 𝓘(ℝ, Fin n → ℝ) (Quotient.mk (MulAction.orbitRel G M)) ((1 : G) • x)
          (mfderiv IG I (fun g : G ↦ g • x) 1 v) =
        mfderiv IG 𝓘(ℝ, Fin n → ℝ)
          (Quotient.mk (MulAction.orbitRel G M) ∘ fun g : G ↦ g • x) 1 v := by
      rw [mfderiv_comp (1 : G) hq_diff horb_diff, ContinuousLinearMap.comp_apply]
    rw [hconst, mfderiv_const, zero_apply] at hchain
    rwa [one_smul] at hchain
  -- Both subspaces of `E` have dimension `dim EG`, so inclusion implies equality.
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hsurj : LinearMap.range
      (mfderiv I 𝓘(ℝ, Fin n → ℝ) (Quotient.mk (MulAction.orbitRel G M)) x).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (surjective_mfderiv_quotientMk_freeProperQuotient I IG G hn x)
  have hrn :
      finrank ℝ (Fin n → ℝ) +
        finrank ℝ (mfderiv I 𝓘(ℝ, Fin n → ℝ) (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      finrank ℝ E := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (mfderiv I 𝓘(ℝ, Fin n → ℝ) (Quotient.mk (MulAction.orbitRel G M)) x).toLinearMap
    rwa [hsurj, finrank_top] at h
  rw [Module.finrank_fin_fun] at hrn
  have hdim := finrank_freeProperQuotient_add_finrank (I := I) (IG := IG) (M := M) (G := G) hn
  rw [finrank_orbitTangent_fundamental_of_properSMul x]
  omega

end QuotientManifold

/-! ### Existential quotient manifold theorem -/

/-- **The quotient manifold theorem for free proper Lie group actions.** The orbit space
`MulAction.orbitRel.Quotient G M` of a free proper smooth action of a finite-dimensional
boundaryless real Lie group `G` on a finite-dimensional boundaryless smooth real manifold `M`
admits a smooth manifold structure of dimension `dim E - dim EG`, retaining its quotient topology,
for which the orbit projection `Quotient.mk''` is a smooth submersion. Neither countability nor
explicit separation assumptions are needed (`T2Space` of the quotient holds automatically from
`ProperSMul G M`, and when `M` is second countable `SecondCountableTopology` is obtained from
`ContinuousConstSMul.secondCountableTopology` together with `ContMDiffSMul.continuousSMul`), and
`M` may be empty. -/
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
    ∃ cs : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      IsSubmersion I
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) := by
  have : ContMDiffSMul IG I ∞ G M := ⟨hsm⟩
  have : IsCancelSMul G M := isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  exact ⟨freeProperQuotientChartedSpace I IG M G rfl,
    isManifold_freeProperQuotient I IG M G rfl,
    isSubmersion_quotientMk_freeProperQuotient I IG M G rfl⟩

/-! ### Smooth descent, equivariant maps, immersions, and uniqueness -/

section DescentAndUniqueness

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  {I : ModelWithCorners ℝ E H} {IG : ModelWithCorners ℝ EG HG}
  [I.Boundaryless] [IG.Boundaryless]
  {M G : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ProperSMul G M] [ContMDiffSMul IG I ∞ G M] [IsCancelSMul G M]
  {n : ℕ}

variable (I IG) in
/-- For `m ≤ ∞`, the descent `MulAction.orbitRelQuotientLift f hf` of a `G`-invariant map to the
free proper quotient manifold is `C^m` at `[x]` if and only if `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {J : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
    (hn : finrank ℝ E - finrank ℝ EG = n) {m : ℕ∞ω} (hm : m ≤ ∞) {f : M → P}
    {hf : ∀ (g : G) (x : M), f (g • x) = f x} {x : M} :
    letI := freeProperQuotientChartedSpace I IG M G hn
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) J m (MulAction.orbitRelQuotientLift f hf)
        (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I J m f x := by
  let := freeProperQuotientChartedSpace I IG M G hn
  rw [← ((isSubmersion_quotientMk_freeProperQuotient I IG M G hn
    ).isSubmersionAt x).contMDiffAt_comp_iff hm, MulAction.orbitRelQuotientLift_comp_mk]

variable (I IG) in
/-- For `m ≤ ∞`, the descent `MulAction.orbitRelQuotientLift f hf` of a `G`-invariant map to the
free proper quotient manifold is `C^m` if and only if `f` is `C^m`. -/
theorem contMDiff_orbitRelQuotientLift_freeProperQuotient_iff
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {J : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
    (hn : finrank ℝ E - finrank ℝ EG = n) {m : ℕ∞ω} (hm : m ≤ ∞) {f : M → P}
    {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := freeProperQuotientChartedSpace I IG M G hn
    ContMDiff 𝓘(ℝ, Fin n → ℝ) J m (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I J m f := by
  let := freeProperQuotientChartedSpace I IG M G hn
  rw [← (isSubmersion_quotientMk_freeProperQuotient I IG M G hn).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulAction.orbitRelQuotientLift_comp_mk]

variable (IG) in
/-- **Universal property of the free proper quotient manifold.** Every `G`-invariant `C^m` map
`f : M → P` (`m ≤ ∞`) factors uniquely through `Quotient.mk` via a `C^m` map out of the quotient
manifold. -/
theorem existsUnique_contMDiff_comp_quotientMk_freeProperQuotient
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {J : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
    (hn : finrank ℝ E - finrank ℝ EG = n) {m : ℕ∞ω} (hm : m ≤ ∞) {f : M → P}
    (hf_smooth : ContMDiff I J m f) (hf_inv : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    ∃! f' : MulAction.orbitRel.Quotient G M → P,
      ContMDiff 𝓘(ℝ, Fin n → ℝ) J m f' ∧
        f' ∘ Quotient.mk (MulAction.orbitRel G M) = f := by
  let := freeProperQuotientChartedSpace I IG M G hn
  refine (isSubmersion_quotientMk_freeProperQuotient I IG M G hn).existsUnique_contMDiff_comp_eq
    Quotient.mk_surjective hm hf_smooth fun x y hxy ↦ ?_
  obtain ⟨g, rfl⟩ := Quotient.exact hxy
  exact hf_inv g y

variable (IG) in
/-- **Smoothness of maps induced on orbit spaces by equivariant maps.** An equivariant `C^m` map
(`m ≤ ∞`) between two manifolds with free proper smooth Lie group actions descends to a `C^m` map
between their smooth quotient manifolds. -/
theorem contMDiff_orbitRelQuotientMap_freeProperQuotient
    {E' EG' H' HG' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
    [TopologicalSpace H'] [TopologicalSpace HG']
    {I' : ModelWithCorners ℝ E' H'} (IG' : ModelWithCorners ℝ EG' HG')
    [I'.Boundaryless] [IG'.Boundaryless]
    {M' G' : Type*}
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [TopologicalSpace G'] [ChartedSpace HG' G'] [Group G'] [LieGroup IG' ∞ G']
    [MulAction G' M'] [ProperSMul G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [IsCancelSMul G' M']
    {n' : ℕ} (hn : finrank ℝ E - finrank ℝ EG = n) (hn' : finrank ℝ E' - finrank ℝ EG' = n')
    {m : ℕ∞ω} (hm : m ≤ ∞) {ρ : G → G'} {φ : M →ₑ[ρ] M'} (hφ : ContMDiff I I' m φ) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    letI := freeProperQuotientChartedSpace I' IG' M' G' hn'
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n' → ℝ) m (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace I IG M G hn
  let := freeProperQuotientChartedSpace I' IG' M' G' hn'
  rw [← (isSubmersion_quotientMk_freeProperQuotient I IG M G hn).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_quotientMk_freeProperQuotient I' IG' M' G' hn').of_le hm).comp hφ

variable (I IG) in
/-- **Immersion criterion for invariant maps out of a free proper quotient.** Into a
finite-dimensional boundaryless real manifold `P`, the descended map
`MulAction.orbitRelQuotientLift f hf` is a smooth immersion if and only if `f` is smooth and the
kernel of `df_x` at every `x : M` is precisely the orbit tangent space `𝔤 · x`. -/
theorem isImmersion_orbitRelQuotientLift_freeProperQuotient_iff
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP] {J : ModelWithCorners ℝ EP HP} [J.Boundaryless]
    [TopologicalSpace P] [ChartedSpace HP P] [IsManifold J ∞ P]
    (hn : finrank ℝ E - finrank ℝ EG = n) {f : M → P}
    {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := freeProperQuotientChartedSpace I IG M G hn
    IsImmersion 𝓘(ℝ, Fin n → ℝ) J ∞ (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I J ∞ f ∧
        ∀ x : M, (mfderiv I J f x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG M G hn
  have := isManifold_freeProperQuotient I IG M G hn
  rw [(isSubmersion_quotientMk_freeProperQuotient I IG M G hn).isImmersion_iff_ker_mfderiv_comp
    Quotient.mk_surjective (by simp), MulAction.orbitRelQuotientLift_comp_mk]
  simp only [ker_mfderiv_quotientMk_freeProperQuotient I IG G hn]

variable (I IG) in
/-- **Smooth-embedding criterion for invariant maps out of a free proper quotient.** Into a
finite-dimensional boundaryless real manifold `P`, the descended map
`MulAction.orbitRelQuotientLift f hf` is a smooth embedding if and only if it is a topological
embedding, `f` is smooth, and the kernel of `df_x` at every `x : M` is the orbit tangent space
`𝔤 · x`. -/
theorem isSmoothEmbedding_orbitRelQuotientLift_freeProperQuotient_iff
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP] {J : ModelWithCorners ℝ EP HP} [J.Boundaryless]
    [TopologicalSpace P] [ChartedSpace HP P] [IsManifold J ∞ P]
    (hn : finrank ℝ E - finrank ℝ EG = n) {f : M → P}
    {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := freeProperQuotientChartedSpace I IG M G hn
    IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) J ∞ (MulAction.orbitRelQuotientLift f hf) ↔
      IsEmbedding (MulAction.orbitRelQuotientLift f hf) ∧ ContMDiff I J ∞ f ∧
        ∀ x : M, (mfderiv I J f x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG M G hn
  rw [isSmoothEmbedding_iff, isImmersion_orbitRelQuotientLift_freeProperQuotient_iff I IG hn]
  tauto

omit [TopologicalSpace M] [TopologicalSpace G] [ProperSMul G M] [IsCancelSMul G M] in
private theorem bijective_orbitRelQuotientLift_of_fib {Q : Type*} {p : M → Q}
    (hsurj : Surjective p) (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • x = y) :
    Bijective (MulAction.orbitRelQuotientLift p
      (fun g x ↦ (hfib (g • x) x).mpr ⟨g⁻¹, by simp⟩)) := by
  refine ⟨?_, ?_⟩
  · intro q₁ q₂ hxy
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q₁
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective q₂
    rw [MulAction.orbitRelQuotientLift_mk, MulAction.orbitRelQuotientLift_mk] at hxy
    obtain ⟨g, hg⟩ := (hfib x y).mp hxy
    exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g⁻¹, by simp [← hg]⟩)
  · intro q
    obtain ⟨x, rfl⟩ := hsurj q
    exact ⟨Quotient.mk _ x, MulAction.orbitRelQuotientLift_mk x⟩

variable (IG G) in
/-- **Identification of the orbit manifold with the target of a surjective submersion.** If
`p : M → Q` is a surjective smooth submersion whose fibres are the `G`-orbits
(`p x = p y ↔ ∃ g : G, g • x = y`), then `MulAction.orbitRelQuotientLift p` is a diffeomorphism
from `MulAction.orbitRel.Quotient G M` onto `Q`. -/
def diffeomorphOfIsSubmersionOrbitEq
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hn : finrank ℝ E - finrank ℝ EG = n) {p : M → Q} (hp : IsSubmersion I JQ ∞ p)
    (hsurj : Surjective p) (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • x = y) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    MulAction.orbitRel.Quotient G M ≃ₘ⟮𝓘(ℝ, Fin n → ℝ), JQ⟯ Q :=
  letI := freeProperQuotientChartedSpace I IG M G hn
  (isSubmersion_quotientMk_freeProperQuotient I IG M G hn).diffeomorphOfCompEq hp
    Quotient.mk_surjective
    (Equiv.ofBijective _ (bijective_orbitRelQuotientLift_of_fib hsurj hfib))
    fun x ↦ MulAction.orbitRelQuotientLift_mk x

/-- The underlying map of `diffeomorphOfIsSubmersionOrbitEq` is `MulAction.orbitRelQuotientLift`. -/
@[simp]
theorem coe_diffeomorphOfIsSubmersionOrbitEq
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hn : finrank ℝ E - finrank ℝ EG = n) {p : M → Q} (hp : IsSubmersion I JQ ∞ p)
    (hsurj : Surjective p) (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • x = y) :
    ⇑(diffeomorphOfIsSubmersionOrbitEq IG G hn hp hsurj hfib) =
      MulAction.orbitRelQuotientLift p (fun g x ↦ (hfib (g • x) x).mpr ⟨g⁻¹, by simp⟩) :=
  letI := freeProperQuotientChartedSpace I IG M G hn
  (IsSubmersion.coe_diffeomorphOfCompEq _ _ _ _ _).trans (Equiv.coe_ofBijective _ _)

/-- `diffeomorphOfIsSubmersionOrbitEq` evaluates on `[x]` as `p x`. -/
theorem diffeomorphOfIsSubmersionOrbitEq_mk
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hn : finrank ℝ E - finrank ℝ EG = n) {p : M → Q} (hp : IsSubmersion I JQ ∞ p)
    (hsurj : Surjective p) (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • x = y) (x : M) :
    diffeomorphOfIsSubmersionOrbitEq IG G hn hp hsurj hfib
      (Quotient.mk (MulAction.orbitRel G M) x) = p x := by
  simp

/-- The inverse of `diffeomorphOfIsSubmersionOrbitEq` sends `p x` to `[x]`. -/
@[simp]
theorem diffeomorphOfIsSubmersionOrbitEq_symm_apply
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (hn : finrank ℝ E - finrank ℝ EG = n) {p : M → Q} (hp : IsSubmersion I JQ ∞ p)
    (hsurj : Surjective p) (hfib : ∀ x y : M, p x = p y ↔ ∃ g : G, g • x = y) (x : M) :
    letI := freeProperQuotientChartedSpace I IG M G hn
    (diffeomorphOfIsSubmersionOrbitEq IG G hn hp hsurj hfib).symm (p x) =
      Quotient.mk (MulAction.orbitRel G M) x := by
  let := freeProperQuotientChartedSpace I IG M G hn
  apply (diffeomorphOfIsSubmersionOrbitEq IG G hn hp hsurj hfib).injective
  simp

variable (IG) in
/-- **Uniqueness of the smooth quotient structure.** Any smooth manifold structure on
`MulAction.orbitRel.Quotient G M` modelled on `Fin n → ℝ` for which `Quotient.mk` is a smooth
submersion has the same maximal atlas as `freeProperQuotientChartedSpace`. -/
theorem maximalAtlas_freeProperQuotient_eq (hn : finrank ℝ E - finrank ℝ EG = n)
    {c : ChartedSpace (Fin n → ℝ) (MulAction.orbitRel.Quotient G M)}
    (hc : letI := c; IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ (MulAction.orbitRel.Quotient G M))
    (hq : letI := c; IsSubmersion I 𝓘(ℝ, Fin n → ℝ) ∞ (Quotient.mk (MulAction.orbitRel G M))) :
    (letI := freeProperQuotientChartedSpace I IG M G hn;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ (MulAction.orbitRel.Quotient G M)) =
    (letI := c;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ (MulAction.orbitRel.Quotient G M)) :=
  IsSubmersion.maximalAtlas_eq_of_surjective (isManifold_freeProperQuotient I IG M G hn) hc
    (isSubmersion_quotientMk_freeProperQuotient I IG M G hn) hq Quotient.mk_surjective

end DescentAndUniqueness

end TauCeti
