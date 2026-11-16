/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Topology.Algebra.ProperAction.Slice

import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.Instances.Quotient
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.Submersion.Descent
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# The quotient manifold theorem for free proper Lie group actions

Let a finite-dimensional real Lie group `G` act freely, properly, and smoothly on a
finite-dimensional boundaryless smooth real manifold `M`. This file proves the **quotient manifold
theorem**: the orbit space `MulAction.orbitRel.Quotient G M`, retaining its quotient topology,
carries a unique smooth manifold structure of dimension `dim M - dim G` for which the orbit
projection `Quotient.mk : M → M ⧸ G` is a smooth submersion. No Hausdorff or second-countability
hypotheses are required on `M` or `G` (Hausdorffness of `G` follows from the Lie group structure,
and Hausdorffness of `M` follows from properness of the action), and `M` may be empty.

The construction assembles the local transverse-slice pieces:

1. **Transverse slice charts** (`TauCeti.exists_freeProperSliceChart`): at each `x : M`, triviality
   of the stabilizer makes the isotropy algebra trivial
   (`TauCeti.Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot`), so the orbit tangent space
   `𝔤 · x` has dimension `dim G` and any linear complement `W` has dimension `dim M - dim G`.
   Identifying `Fin (dim M - dim G) → ℝ` with `W`, the chart slice `v ↦ φ⁻¹(φ x + eW v)` gives a
   slice map `(g, v) ↦ g • σ v` which is a smooth local diffeomorphism at `(1, 0)`
   (`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`), hence along all of `G × U` for a small
   open neighbourhood `U` of `0` (`IsLocalDiffeomorphAt.eventually_forall_smul_slice`), and
   injective on `G × U` after further shrinking by properness
   (`ProperSMul.exists_mem_nhds_injOn_smul_slice`).
2. **Gluing the quotient atlas** (`TauCeti.freeProperQuotientChartedSpace`,
   `TauCeti.isManifold_freeProperQuotient`): each slice defines an open embedding
   `U → M ⧸ G` (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`), the family indexed by
   `x : M` covers `M ⧸ G`, and overlap transitions are smooth by
   `TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`, so
   `TauCeti.chartedSpaceOfIsOpenEmbedding` and `TauCeti.isManifold_chartedSpaceOfIsOpenEmbedding`
   yield a smooth atlas on `M ⧸ G`. It is defined as a named `@[instance_reducible]` definition
   rather than a global instance so it does not clash with Mathlib's discrete-action quotient
   charts `MulAction.instChartedSpaceQuotient`.
3. **Submersion and vertical tangent space**
   (`TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
   `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`, `TauCeti.freeProperQuotientTangentEquiv`):
   near `x : M`, the orbit projection factors through the local inverse of the slice map
   `(g, v) ↦ g • σ v` followed by projection onto `U` and the slice chart `U → M ⧸ G`, hence is
   smooth; its differential is surjective by the chain rule along the slice local diffeomorphism,
   so `ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv` yields the submersion normal form
   with complement `EG`. Its derivative at `x` has kernel equal to the orbit tangent space `𝔤 · x`,
   inducing a canonical linear isomorphism `T_x M ⧸ (𝔤 · x) ≃ₗ[ℝ] T_[x] (M ⧸ G)`.
4. **Smooth descent, uniqueness, arbitrary slice charts, and specializations**:
   smoothness of invariant maps (`TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`),
   equivariant maps (`TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`), and immersions
   (`TauCeti.isImmersion_orbitRelQuotientLift_freeProperQuotient_iff`) descends through the
   surjective submersion; any bijection `e : M ⧸ G ≃ N` into a manifold making `e ∘ Quotient.mk` a
   submersion is a smooth diffeomorphism (`TauCeti.freeProperQuotientDiffeomorphOfIsSubmersion`)
   and any smooth atlas on `M ⧸ G` over the same model making `Quotient.mk` a submersion has the
   same maximal atlas (`TauCeti.maximalAtlas_freeProperQuotient_eq_of_isSubmersion`); arbitrary
   transverse slices give smooth local diffeomorphisms onto open sets of `M ⧸ G`
   (`TauCeti.isLocalDiffeomorph_quotientMk_slice_freeProperQuotient`) and smooth equivariant local
   group coordinates (`TauCeti.exists_contMDiffOn_equivariant_coord`); when `G` is discrete, the
   identity is a smooth diffeomorphism onto Mathlib's discrete-action quotient manifold
   `MulAction.instChartedSpaceQuotient` (`TauCeti.freeProperQuotientDiscreteDiffeomorph`); and when
   `G` is trivial, `M ⧸ G` is canonically diffeomorphic to `M`
   (`TauCeti.freeProperQuotientSubsingletonDiffeomorph`).

## Main definitions

* `TauCeti.freeProperQuotientChartedSpace`: the named smooth atlas on
  `MulAction.orbitRel.Quotient G M` modelled on `Fin (finrank ℝ E - finrank ℝ EG) → ℝ`.
* `TauCeti.freeProperQuotientTangentEquiv`: the canonical linear isomorphism
  `TangentSpace I x ⧸ orbitTangent x ≃ₗ[ℝ] TangentSpace _ (Quotient.mk _ x)`.
* `TauCeti.freeProperQuotientDiffeomorphOfIsSubmersion`: uniqueness of the quotient manifold
  structure up to canonical diffeomorphism.
* `TauCeti.freeProperQuotientDiscreteDiffeomorph`: canonical smooth diffeomorphism between the
  free-proper quotient atlas and Mathlib's discrete-action quotient atlas when `G` is discrete.
* `TauCeti.freeProperQuotientSubsingletonDiffeomorph`: canonical smooth diffeomorphism `M ⧸ G ≃ₘ M`
  when `G` is trivial.

## Main results

* `TauCeti.exists_freeProperSliceChart`: existence of transverse slice charts at every point.
* `TauCeti.isManifold_freeProperQuotient`: `MulAction.orbitRel.Quotient G M` with
  `freeProperQuotientChartedSpace` is a `C^∞` manifold.
* `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
  `TauCeti.isSubmersion_quotientMk_freeProperQuotient`: the orbit projection is a `C^∞` submersion
  with complement `EG`.
* `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`: the kernel of the differential of the orbit
  projection at `x` is the orbit tangent space `𝔤 · x`.
* `TauCeti.contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`,
  `TauCeti.isImmersion_orbitRelQuotientLift_freeProperQuotient_iff`: smooth descent of invariant
  maps, equivariant maps, and immersions.
* `TauCeti.maximalAtlas_freeProperQuotient_eq_of_isSubmersion`: uniqueness of the maximal atlas.
* `TauCeti.isLocalDiffeomorph_quotientMk_slice_freeProperQuotient`: any transverse slice gives a
  smooth local diffeomorphism into the quotient manifold.
* `TauCeti.exists_contMDiffOn_equivariant_coord`: local smooth `G`-equivariant maps `π⁻¹ W → G`
  near every orbit.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: the existential form of the quotient manifold
  theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013, Theorem 21.10
  (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21.
-/

public section

noncomputable section

open Function Module Set Filter Topology Manifold TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

section SliceChart

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

private theorem isotropy_eq_bot (x : M) :
    (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have : Subsingleton (MulAction.stabilizer G x) := by
    rw [IsCancelSMul.stabilizer_eq_bot x]
    infer_instance
  exact (Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := IG) (I' := I)).1 inferInstance

/-- **Transverse slice charts for free proper smooth actions.** At every point `x : M`, letting
`d = dim M - dim G`, there is an open neighbourhood `U` of `0` in `Fin d → ℝ` and a map
`σ : (Fin d → ℝ) → M` with `σ 0 = x` such that the slice map `(g, v) ↦ g • σ v` is injective on
`G × U` and a `C^∞` local diffeomorphism at every point of `G × U`. -/
theorem exists_freeProperSliceChart (x : M) :
    ∃ (U : Opens (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)),
      (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ U ∧
      ∃ σ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M,
        σ 0 = x ∧
        InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2)
          (univ ×ˢ (U : Set _)) ∧
        IsLocalDiffeomorphOn
          (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
          (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2)
          (univ ×ˢ (U : Set _)) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  set d := finrank ℝ E - finrank ℝ EG
  have hiso := isotropy_eq_bot I IG (G := G) x
  let V : Submodule ℝ E := (InfinitesimalAction.fundamental IG G I M).orbitTangent x
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  -- Identify `Fin d → ℝ` with a transverse complement `W` of the orbit tangent space.
  have hdimW : finrank ℝ (Fin d → ℝ) = finrank ℝ W := by
    have hadd := Submodule.finrank_add_eq_of_isCompl hW
    have hV : finrank ℝ V = finrank ℝ EG :=
      (InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x hiso
    rw [hV] at hadd; rw [finrank_fin_fun]; omega
  let eW : (Fin d → ℝ) ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq hdimW
  let σ₀ : W → M := fun w ↦ (extChartAt I x).symm (extChartAt I x x + (w : E))
  let σ : (Fin d → ℝ) → M := σ₀ ∘ eW
  have hσ0 : σ 0 = x := by simp [σ, σ₀, eW]
  -- Precomposing the chart slice on `W` with `id × eW` yields a local diffeomorphism at `(1, 0)`.
  let dW : (Fin d → ℝ) ≃ₘ^∞⟮𝓘(ℝ, Fin d → ℝ), 𝓘(ℝ, W)⟯ W :=
    { toEquiv := eW.toEquiv
      contMDiff_toFun := eW.contDiff.contMDiff
      contMDiff_invFun := eW.symm.contDiff.contMDiff }
  have hT0 : Prod.map (id : G → G) (dW : (Fin d → ℝ) → W) (1, 0) = (1, 0) :=
    Prod.ext rfl (map_zero eW)
  have hloc₁ : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin d → ℝ)) I ∞
      (fun p : G × (Fin d → ℝ) ↦ p.1 • σ p.2) (1, 0) :=
    IsLocalDiffeomorphAt.comp
      (hf := ((Diffeomorph.refl IG G ∞).isLocalDiffeomorph 1).prodMap (dW.isLocalDiffeomorph 0))
      (hg := hT0.symm ▸ isLocalDiffeomorphAt_smul_extChartAt_symm hiso hW)
  -- Equivariance propagates the local diffeomorphism property to entire orbits near `0`,
  -- and properness upgrades local injectivity at `(1, 0)` to injectivity on a tube `G × U`.
  obtain ⟨N, hN, hNinj⟩ := hloc₁.exists_mem_nhds_injOn
  have hσcont : ContinuousAt σ 0 := by
    simpa only [Function.comp_def, one_smul] using
      hloc₁.contMDiffAt.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
  obtain ⟨U₁, hU₁, hU₁inj⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice hσcont
    (by rw [hσ0]; exact IsCancelSMul.stabilizer_eq_bot x) hN hNinj
  let U : Opens (Fin d → ℝ) :=
    ⟨interior ({v | ∀ g : G, IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin d → ℝ)) I ∞
      (fun p : G × (Fin d → ℝ) ↦ p.1 • σ p.2) (g, v)} ∩ U₁), isOpen_interior⟩
  refine ⟨U, mem_interior_iff_mem_nhds.2 (inter_mem hloc₁.eventually_forall_smul_slice hU₁),
    σ, hσ0, hU₁inj.mono (prod_mono_right (interior_subset.trans inter_subset_right)), ?_⟩
  rintro ⟨⟨g, v⟩, -, hv⟩
  exact (interior_subset hv).1 g

end SliceChart

section Gluing

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless]
  (G : Type*) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- The open slice domain chosen at `x : M`. -/
private def chosenSliceOpen (x : M) : Opens (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) :=
  (exists_freeProperSliceChart I IG (G := G) x).choose

private theorem zero_mem_chosenSliceOpen (x : M) :
    (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ chosenSliceOpen I IG G x :=
  (exists_freeProperSliceChart I IG (G := G) x).choose_spec.1

/-- The transverse slice map chosen at `x : M`. -/
private def chosenSlice (x : M) : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M :=
  (exists_freeProperSliceChart I IG (G := G) x).choose_spec.2.choose

private theorem chosenSlice_zero (x : M) : chosenSlice I IG G x 0 = x :=
  (exists_freeProperSliceChart I IG (G := G) x).choose_spec.2.choose_spec.1

private theorem injOn_smul_chosenSlice (x : M) :
    InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • chosenSlice I IG G x p.2)
      (univ ×ˢ (chosenSliceOpen I IG G x : Set _)) :=
  (exists_freeProperSliceChart I IG (G := G) x).choose_spec.2.choose_spec.2.1

private theorem isLocalDiffeomorphOn_smul_chosenSlice (x : M) :
    IsLocalDiffeomorphOn
      (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
      (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • chosenSlice I IG G x p.2)
      (univ ×ˢ (chosenSliceOpen I IG G x : Set _)) :=
  (exists_freeProperSliceChart I IG (G := G) x).choose_spec.2.choose_spec.2.2

/-- The orbit-space parametrization attached to the chosen slice at `x : M`. -/
private def chosenSliceQuotientMap (x : M) :
    chosenSliceOpen I IG G x → MulAction.orbitRel.Quotient G M :=
  fun v ↦ Quotient.mk (MulAction.orbitRel G M) (chosenSlice I IG G x v)

private theorem isOpenEmbedding_chosenSliceQuotientMap (x : M) :
    IsOpenEmbedding (chosenSliceQuotientMap I IG G x) :=
  MulAction.isOpenEmbedding_quotientMk_slice (chosenSliceOpen I IG G x).isOpen
    (injOn_smul_chosenSlice I IG G x)
    (isLocalDiffeomorphOn_smul_chosenSlice I IG G x).isLocalHomeomorphOn

private theorem chosenSliceQuotientMap_cover (q : MulAction.orbitRel.Quotient G M) :
    ∃ (x : M) (v : chosenSliceOpen I IG G x), chosenSliceQuotientMap I IG G x v = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    exact ⟨x, ⟨0, zero_mem_chosenSliceOpen I IG G x⟩, by
      simp [chosenSliceQuotientMap, chosenSlice_zero]⟩

private theorem contMDiffAt_chosenSlice_comp_val (x : M) (u : chosenSliceOpen I IG G x) :
    ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞
      (chosenSlice I IG G x ∘ Subtype.val) u := by
  have hloc := isLocalDiffeomorphOn_smul_chosenSlice I IG G x ⟨(1, u.1), mem_univ _, u.2⟩
  have h1 : ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞
      ((fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • chosenSlice I IG G x p.2) ∘
        fun w : chosenSliceOpen I IG G x ↦ ((1 : G), (w : Fin (finrank ℝ E - finrank ℝ EG) → ℝ)))
      u :=
    hloc.contMDiffAt.comp u (contMDiffAt_const.prodMk contMDiff_subtype_val.contMDiffAt)
  simpa only [Function.comp_def, one_smul] using h1

private theorem chosenSliceQuotientMap_deck (x y : M) (u : chosenSliceOpen I IG G x)
    (v : chosenSliceOpen I IG G y)
    (hxy : chosenSliceQuotientMap I IG G x u = chosenSliceQuotientMap I IG G y v) :
    ∃ T : chosenSliceOpen I IG G x → chosenSliceOpen I IG G y,
      ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ T u ∧
      chosenSliceQuotientMap I IG G y ∘ T =ᶠ[𝓝 u] chosenSliceQuotientMap I IG G x := by
  obtain ⟨t, ht, -, htev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff
    (chosenSliceOpen I IG G y).isOpen (injOn_smul_chosenSlice I IG G y)
    (isLocalDiffeomorphOn_smul_chosenSlice I IG G y)
    (contMDiffAt_chosenSlice_comp_val I IG G x u) v.2 hxy.symm
  classical
  let T : chosenSliceOpen I IG G x → chosenSliceOpen I IG G y :=
    fun w ↦ if hw : t w ∈ (chosenSliceOpen I IG G y : Set _) then ⟨t w, hw⟩ else v
  refine ⟨T, ?_, ?_⟩
  · refine (ContMDiffAt.subtypeVal_comp_iff (chosenSliceOpen I IG G y) T u).1 ?_
    refine ht.congr_of_eventuallyEq ?_
    filter_upwards [htev] with w hw
    simp only [comp_apply, T, hw.1, ↓reduceDIte]
  · filter_upwards [htev] with w hw
    simp only [comp_apply, chosenSliceQuotientMap, T, hw.1, ↓reduceDIte]
    exact (hw.2 (t w) hw.1).2 rfl

private theorem isLocalDiffeomorph_chosenSliceSmul (x : M) :
    IsLocalDiffeomorph (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
      (fun p : G × chosenSliceOpen I IG G x ↦ p.1 • chosenSlice I IG G x p.2) :=
  fun ⟨g, v⟩ ↦ IsLocalDiffeomorphAt.comp
    (hf := ((Diffeomorph.refl IG G ∞).isLocalDiffeomorph g).prodMap
      (isLocalDiffeomorph_subtype_val (I := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) (n := ∞) v))
    (hg := isLocalDiffeomorphOn_smul_chosenSlice I IG G x ⟨(g, v.1), mem_univ _, v.2⟩)

variable (M)

/-- **The quotient manifold atlas for a free proper smooth action.** Built by gluing the transverse
slice charts over `M` via `TauCeti.chartedSpaceOfIsOpenEmbedding`. It retains the quotient topology
on `MulAction.orbitRel.Quotient G M` and is marked `@[instance_reducible]` rather than `instance`
so that it does not conflict with Mathlib's discrete-action quotient charts
`MulAction.instChartedSpaceQuotient`. -/
@[instance_reducible]
noncomputable def freeProperQuotientChartedSpace :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding
    (isOpenEmbedding_chosenSliceQuotientMap I IG G (M := M))
    (chosenSliceQuotientMap_cover I IG G (M := M))

/-- The orbit space of a free proper smooth action, equipped with
`TauCeti.freeProperQuotientChartedSpace`, is a `C^∞` manifold of dimension `dim M - dim G`. -/
theorem isManifold_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding
    (isOpenEmbedding_chosenSliceQuotientMap I IG G (M := M))
    (chosenSliceQuotientMap_cover I IG G (M := M))
    (chosenSliceQuotientMap_deck I IG G (M := M))

private theorem contMDiff_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let _ := freeProperQuotientChartedSpace I IG G M
  set K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  intro x
  let U := chosenSliceOpen I IG G x
  let σ := chosenSlice I IG G x
  let u₀ : U := ⟨0, zero_mem_chosenSliceOpen I IG G x⟩
  let Φ : G × U → M := fun p ↦ p.1 • σ p.2
  have hΦ : IsLocalDiffeomorphAt (IG.prod K) I ∞ Φ (1, u₀) :=
    isLocalDiffeomorph_chosenSliceSmul I IG G x (1, u₀)
  have hΦ0 : Φ (1, u₀) = x := by simp [Φ, u₀, σ, chosenSlice_zero]
  have hφ : ContMDiffAt K K ∞ (chosenSliceQuotientMap I IG G x) u₀ :=
    (isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
      (isOpenEmbedding_chosenSliceQuotientMap I IG G (M := M))
      (chosenSliceQuotientMap_cover I IG G (M := M))
      (chosenSliceQuotientMap_deck I IG G (M := M)) x u₀).contMDiffAt
  have hinv : ContMDiffAt I (IG.prod K) ∞ hΦ.localInverse x := hΦ0 ▸ hΦ.contMDiffAt_localInverse
  have hinv0 : hΦ.localInverse x = (1, u₀) := by
    rw [← hΦ0]
    exact hΦ.localInverse_left_inv hΦ.localInverse_mem_target
  have hcomp : ContMDiffAt I K ∞
      (chosenSliceQuotientMap I IG G x ∘ Prod.snd ∘ hΦ.localInverse) x :=
    (hinv0 ▸ (hφ.comp (1, u₀) contMDiffAt_snd)).comp x hinv
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hΦ0 ▸ hΦ.localInverse_eventuallyEq_right] with y hy
  simp only [comp_apply, chosenSliceQuotientMap]
  exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨_, hy⟩))

/-- **The orbit projection is a smooth submersion with complement `EG`.** At each `x : M`, the
transverse slice map `U → M ⧸ G` is a smooth local diffeomorphism factoring through `Quotient.mk`,
so `dπ_x` is surjective and the constant-rank theorem supplies the submersion normal form. -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    IsSubmersionOfComplement EG I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let _ := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG G M
  set K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  by_cases hM : IsEmpty M
  · exact isSubmersionOfComplement_iff.2 fun x ↦ (IsEmpty.false x).elim
  obtain ⟨x₀⟩ := not_isEmpty_iff.1 hM
  have hcont : ContMDiff I K ∞ (Quotient.mk (MulAction.orbitRel G M)) :=
    contMDiff_quotientMk_freeProperQuotient I IG G M
  have hsurj : ∀ x : M, Surjective (mfderiv I K (Quotient.mk (MulAction.orbitRel G M)) x) := by
    intro x
    let U := chosenSliceOpen I IG G x
    let u₀ : U := ⟨0, zero_mem_chosenSliceOpen I IG G x⟩
    have hφ : IsLocalDiffeomorphAt K K ∞ (chosenSliceQuotientMap I IG G x) u₀ :=
      isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
        (isOpenEmbedding_chosenSliceQuotientMap I IG G (M := M))
        (chosenSliceQuotientMap_cover I IG G (M := M))
        (chosenSliceQuotientMap_deck I IG G (M := M)) x u₀
    have hσ : MDifferentiableAt K I (chosenSlice I IG G x ∘ Subtype.val) u₀ :=
      (contMDiffAt_chosenSlice_comp_val I IG G x u₀).mdifferentiableAt (by simp)
    have hπ : MDifferentiableAt I K (Quotient.mk (MulAction.orbitRel G M)) x :=
      (hcont x).mdifferentiableAt (by simp)
    intro w
    obtain ⟨v, hv⟩ := (hφ.isInvertible_mfderiv (by simp)).surjective w
    refine ⟨mfderiv K I (chosenSlice I IG G x ∘ Subtype.val) u₀ v, ?_⟩
    rw [← mfderiv_comp_apply_of_eq u₀ hπ hσ (by simp [u₀, chosenSlice_zero]) v]
    exact hv
  have hle : finrank ℝ EG ≤ finrank ℝ E := by
    have hV : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x₀) =
        finrank ℝ EG :=
      (InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x₀
        (isotropy_eq_bot I IG x₀)
    exact hV ▸ Submodule.finrank_le _
  let eF : (Fin (finrank ℝ E - finrank ℝ (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) → ℝ) ≃L[ℝ] EG :=
    ContinuousLinearEquiv.ofFinrankEq (by simp; omega)
  exact (hcont.isSubmersionOfComplement_of_surjective_mfderiv (by simp) hsurj).trans_F eF

/-- **The orbit projection is a smooth submersion.** -/
theorem isSubmersion_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let _ := freeProperQuotientChartedSpace I IG G M
  exact (isSubmersionOfComplement_quotientMk_freeProperQuotient I IG G M).isSubmersion

variable {M}

/-- **Any transverse slice gives a smooth local diffeomorphism into the quotient manifold.** If
`σ : S → M` is a slice over an open set `U ⊆ S` whose slice map `(g, s) ↦ g • σ s` is injective
and a `C^∞` local diffeomorphism on `G × U`, then `s ↦ ⟦σ s⟧` is a `C^∞` local diffeomorphism
from `U` into `MulAction.orbitRel.Quotient G M`. -/
theorem isLocalDiffeomorph_quotientMk_slice_freeProperQuotient
    {F KS S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace KS]
    {J : ModelWithCorners ℝ F KS} [TopologicalSpace S] [ChartedSpace KS S]
    {σ : S → M} {U : Opens S}
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ (U : Set S)))
    (hloc : IsLocalDiffeomorphOn (IG.prod J) I ∞
      (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ (U : Set S))) :
    letI := freeProperQuotientChartedSpace I IG G M
    IsLocalDiffeomorph J 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (fun s : U ↦ Quotient.mk (MulAction.orbitRel G M) (σ s)) := by
  let _ := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG G M
  set K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  set φ : U → MulAction.orbitRel.Quotient G M := fun s ↦ Quotient.mk (MulAction.orbitRel G M) (σ s)
  have hopen : IsOpenEmbedding φ :=
    MulAction.isOpenEmbedding_quotientMk_slice U.isOpen hinj hloc.isLocalHomeomorphOn
  have hφsmooth : ContMDiff J K ∞ φ := by
    intro s
    have hσs : ContMDiffAt J I ∞ (σ ∘ Subtype.val) s := by
      have h1 : ContMDiffAt J I ∞
          ((fun p : G × S ↦ p.1 • σ p.2) ∘ fun w : U ↦ ((1 : G), (w : S))) s :=
        (hloc ⟨(1, s.1), mem_univ _, s.2⟩).contMDiffAt.comp s
          (contMDiffAt_const.prodMk contMDiff_subtype_val.contMDiffAt)
      simpa only [Function.comp_def, one_smul] using h1
    exact ((isSubmersion_quotientMk_freeProperQuotient I IG G M).contMDiff (σ s)).comp s hσs
  intro s₀
  have : Nonempty U := ⟨s₀⟩
  let e := hopen.toOpenPartialHomeomorph φ
  have hsymm : ContMDiffOn K J ∞ e.symm e.target := by
    rintro _ ⟨s, -, rfl⟩
    refine ContMDiffAt.contMDiffWithinAt ?_
    -- Smoothness of `e.symm` at `⟦σ s⟧` descends from smoothness of `e.symm ∘ Quotient.mk`
    -- at `σ s`.
    refine (((isSubmersion_quotientMk_freeProperQuotient I IG G M).isSubmersionAt
      (σ s)).contMDiffAt_comp_iff le_rfl).1 ?_
    obtain ⟨t, ht, -, htev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff U.isOpen hinj hloc
      (contMDiffAt_id (I := I) (x := σ s)) s.2 rfl
    refine (ContMDiffAt.subtypeVal_comp_iff U (e.symm ∘ Quotient.mk (MulAction.orbitRel G M))
      (σ s)).1 ?_
    refine ht.congr_of_eventuallyEq ?_
    filter_upwards [htev] with y hy
    have hq : φ ⟨t y, hy.1⟩ = Quotient.mk (MulAction.orbitRel G M) y := (hy.2 (t y) hy.1).2 rfl
    rw [comp_apply, comp_apply, ← hq, hopen.toOpenPartialHomeomorph_left_inv φ (x := ⟨t y, hy.1⟩)]
  let Φ : PartialDiffeomorph J K U (MulAction.orbitRel.Quotient G M) ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := hφsmooth.contMDiffOn
      contMDiffOn_invFun := hsymm }
  exact Φ.isLocalDiffeomorphAt J K ∞ (mem_univ s₀)

/-- **Local smooth equivariant group coordinates.** Every orbit has an open neighbourhood `W` in
the orbit space over which there is a smooth map `u : M → G` defined on `π⁻¹ W` satisfying
`u (g • y) = g * u y`. Together with `TauCeti.orbitTrivialization`, this supplies smooth local
trivializations of the orbit projection. -/
theorem exists_contMDiffOn_equivariant_coord (x : M) :
    ∃ W : Set (MulAction.orbitRel.Quotient G M),
      IsOpen W ∧ Quotient.mk (MulAction.orbitRel G M) x ∈ W ∧
      ∃ u : M → G,
        ContMDiffOn I IG ∞ u (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W) ∧
        ∀ (g : G), ∀ y ∈ Quotient.mk (MulAction.orbitRel G M) ⁻¹' W, u (g • y) = g * u y := by
  let U := chosenSliceOpen I IG G x
  let σ := chosenSlice I IG G x
  let φ := chosenSliceQuotientMap I IG G x
  let Φ : G × U → M := fun p ↦ p.1 • σ p.2
  have hΦopen : IsOpenEmbedding Φ :=
    MulAction.isOpenEmbedding_smul_slice U.isOpen (injOn_smul_chosenSlice I IG G x)
      (isLocalDiffeomorphOn_smul_chosenSlice I IG G x).isLocalHomeomorphOn
  have : Nonempty (G × U) := ⟨(1, ⟨0, zero_mem_chosenSliceOpen I IG G x⟩)⟩
  let e := hΦopen.toOpenPartialHomeomorph Φ
  have hWopen : IsOpen (range φ) := (isOpenEmbedding_chosenSliceQuotientMap I IG G x).isOpen_range
  have hxW : Quotient.mk (MulAction.orbitRel G M) x ∈ range φ :=
    ⟨⟨0, zero_mem_chosenSliceOpen I IG G x⟩, by simp [φ, chosenSliceQuotientMap, chosenSlice_zero]⟩
  -- The preimage of `range φ` is precisely `range Φ = e.target`.
  have hpre : Quotient.mk (MulAction.orbitRel G M) ⁻¹' range φ = range Φ := by
    ext y
    simp only [mem_preimage, mem_range, φ, chosenSliceQuotientMap, Φ, Prod.exists]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hv))
      exact ⟨g⁻¹, v, inv_smul_eq_iff.2 hg.symm⟩
    · rintro ⟨g, v, rfl⟩
      exact ⟨v, (Quotient.sound (MulAction.orbitRel_apply.2
        (MulAction.mem_orbit_iff.2 ⟨g, rfl⟩))).symm⟩
  refine ⟨range φ, hWopen, hxW, fun y ↦ (e.symm y).1, ?_, ?_⟩
  · -- On `range Φ`, `e.symm` coincides locally with the smooth local inverse of `Φ`.
    rw [hpre]
    rintro _ ⟨p, rfl⟩
    refine ContMDiffAt.contMDiffWithinAt ?_
    have hloc := isLocalDiffeomorph_chosenSliceSmul I IG G x p
    have heq : e.symm =ᶠ[𝓝 (Φ p)] hloc.localInverse := by
      filter_upwards [hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source] with y hy
      calc e.symm y
        _ = e.symm (Φ (hloc.localInverse y)) := by
          dsimp only [Φ, σ]
          rw [hloc.localInverse_right_inv hy]
        _ = hloc.localInverse y := hΦopen.toOpenPartialHomeomorph_left_inv Φ
    exact contMDiffAt_fst.comp (Φ p) (hloc.contMDiffAt_localInverse.congr_of_eventuallyEq heq)
  · intro g y hy
    rw [hpre] at hy
    obtain ⟨⟨g₀, v⟩, rfl⟩ := hy
    have h1 : e.symm (g₀ • σ v) = (g₀, v) :=
      hΦopen.toOpenPartialHomeomorph_left_inv Φ (x := (g₀, v))
    have h2 : e.symm (g • (g₀ • σ v)) = (g * g₀, v) := by
      rw [← mul_smul]
      exact hΦopen.toOpenPartialHomeomorph_left_inv Φ (x := (g * g₀, v))
    dsimp only [Φ]
    rw [h1, h2]

end Gluing

section TangentKernel

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless]
  (G : Type*) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **Vertical tangent space of the quotient projection.** At every point `x : M`, the kernel of
the differential of the orbit projection `M → M ⧸ G` is the orbit tangent space `𝔤 · x`. -/
theorem ker_mfderiv_quotientMk_freeProperQuotient (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let _ := freeProperQuotientChartedSpace I IG G M
  set K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  have hsub := isSubmersion_quotientMk_freeProperQuotient I IG G M
  -- Every fundamental vector at `x` is killed by `dπ_x` because `π` is constant along orbits.
  have hle : (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤
      (mfderiv I K (Quotient.mk (MulAction.orbitRel G M)) x).ker := by
    rw [InfinitesimalAction.orbitTangent_eq_range]
    rintro _ ⟨ξ, rfl⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, InfinitesimalAction.eval_apply,
      InfinitesimalAction.fundamental_apply, fundamentalVectorField_apply]
    have hconst : (Quotient.mk (MulAction.orbitRel G M) ∘ fun g : G ↦ g • x) =
        fun _ : G ↦ Quotient.mk (MulAction.orbitRel G M) x :=
      funext fun g ↦ Quotient.sound
        (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g, rfl⟩))
    have hdiffπ : MDifferentiableAt I K (Quotient.mk (MulAction.orbitRel G M)) x :=
      (hsub.contMDiff x).mdifferentiableAt (by simp)
    have hdifforb : MDifferentiableAt IG I (fun g : G ↦ g • x) 1 :=
      (ContMDiffSMul.contMDiff_smul_const (I := IG) (I' := I) (n := ∞) x 1).mdifferentiableAt
        (by simp)
    rw [← mfderiv_comp_apply_of_eq (1 : G) hdiffπ hdifforb (one_smul G x) ξ, hconst, mfderiv_const]
    rfl
  -- Equality follows from rank-nullity since `dπ_x` is surjective.
  have hdim : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) =
      finrank ℝ (mfderiv I K (Quotient.mk (MulAction.orbitRel G M)) x).ker := by
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (mfderiv I K (Quotient.mk (MulAction.orbitRel G M)) x).toLinearMap
    have hrange : LinearMap.range
        (mfderiv I K (Quotient.mk (MulAction.orbitRel G M)) x).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.2 (hsub.surjective_mfderiv (by simp) x)
    rw [hrange, finrank_top] at hrn
    have hV : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) =
        finrank ℝ EG :=
      (InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x
        (isotropy_eq_bot I IG x)
    have hle_dim : finrank ℝ EG ≤ finrank ℝ E := hV ▸ Submodule.finrank_le _
    have hE : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
    have hQ : finrank ℝ (TangentSpace K (Quotient.mk (MulAction.orbitRel G M) x)) =
        finrank ℝ E - finrank ℝ EG := finrank_fin_fun ℝ
    rw [hE, hQ] at hrn
    rw [hV]
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hdim).symm

/-- **Quotient description of the tangent space of `M ⧸ G`.** The differential of the orbit
projection at `x : M` induces a canonical linear isomorphism
`T_x M ⧸ (𝔤 · x) ≃ₗ[ℝ] T_[x] (M ⧸ G)`. -/
def freeProperQuotientTangentEquiv (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    (TangentSpace I x ⧸ (InfinitesimalAction.fundamental IG G I M).orbitTangent x) ≃ₗ[ℝ]
      TangentSpace 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M) x) :=
  letI := freeProperQuotientChartedSpace I IG G M
  (Submodule.quotEquivOfEq _ _
    (ker_mfderiv_quotientMk_freeProperQuotient I IG G x).symm).trans
    (LinearMap.quotKerEquivOfSurjective
      (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M)) x).toLinearMap
      ((isSubmersion_quotientMk_freeProperQuotient I IG G M).surjective_mfderiv (by simp) x))

/-- The tangent-space isomorphism sends the class of `v ∈ T_x M` to `dπ_x v`. -/
@[simp]
theorem freeProperQuotientTangentEquiv_mk (x : M) (v : TangentSpace I x) :
    freeProperQuotientTangentEquiv I IG G x (Submodule.Quotient.mk v) =
      letI := freeProperQuotientChartedSpace I IG G M
      mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M)) x v :=
  (rfl)

end TangentKernel

section DescentAndUniqueness

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless]
  (G : Type*) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- **Pointwise smooth descent.** For `m ≤ ∞`, the descent of a `G`-invariant map `f : M → N` to
the orbit space is `C^m` at the orbit of `x` exactly when `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff {m : ℕ∞ω} (hm : m ≤ ∞)
    {f : M → N} (hf : ∀ (g : G) (x : M), f (g • x) = f x) (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I' m
      (MulAction.orbitRelQuotientLift f hf) (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I I' m f x := by
  let _ := freeProperQuotientChartedSpace I IG G M
  rw [← ((isSubmersion_quotientMk_freeProperQuotient I IG G M).isSubmersionAt
    x).contMDiffAt_comp_iff hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- **Global smooth descent.** For `m ≤ ∞`, the descent of a `G`-invariant map `f : M → N` to the
orbit space is `C^m` exactly when `f` is `C^m`. -/
theorem contMDiff_orbitRelQuotientLift_freeProperQuotient_iff {m : ℕ∞ω} (hm : m ≤ ∞)
    {f : M → N} (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I' m
      (MulAction.orbitRelQuotientLift f hf) ↔ ContMDiff I I' m f := by
  let _ := freeProperQuotientChartedSpace I IG G M
  rw [← (isSubmersion_quotientMk_freeProperQuotient I IG G M).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- **Immersion criterion for descended maps.** A `G`-invariant map `f : M → N` into a
finite-dimensional boundaryless smooth manifold descends to a `C^∞` immersion `M ⧸ G → N`
exactly when `f` is `C^∞` and the kernel of `df_x` equals the orbit tangent space `𝔤 · x` at
every `x : M`. -/
theorem isImmersion_orbitRelQuotientLift_freeProperQuotient_iff [FiniteDimensional ℝ E']
    [I'.Boundaryless] [IsManifold I' ∞ N]
    {f : M → N} (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace I IG G M
    IsImmersion 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I' ∞
      (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I I' ∞ f ∧
        ∀ x : M, (mfderiv I I' f x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let _ := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG G M
  rw [(isSubmersion_quotientMk_freeProperQuotient I IG G M).isImmersion_iff_ker_mfderiv_comp
    Quotient.mk_surjective (by simp), MulAction.orbitRelQuotientLift_comp_mk]
  simp_rw [ker_mfderiv_quotientMk_freeProperQuotient I IG G]

/-- **Equivariant smooth maps descend smoothly between free proper quotients.** For `m ≤ ∞`, an
equivariant `C^m` map between two free proper smooth Lie group actions induces a `C^m` map of
orbit spaces. -/
theorem contMDiff_orbitRelQuotientMap_freeProperQuotient
    {E' EG' H' HG' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
    [TopologicalSpace H'] [TopologicalSpace HG']
    (I' : ModelWithCorners ℝ E' H') (IG' : ModelWithCorners ℝ EG' HG')
    [I'.Boundaryless]
    (G' : Type*) {M' : Type*}
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [TopologicalSpace G'] [ChartedSpace HG' G'] [Group G'] [LieGroup IG' ∞ G']
    [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [ProperSMul G' M'] [IsCancelSMul G' M']
    {σ : G → G'} {m : ℕ∞ω} (hm : m ≤ ∞) {φ : M →ₑ[σ] M'} (hφ : ContMDiff I I' m φ) :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ EG') → ℝ) m
      (MulActionHom.orbitRelQuotientMap φ) := by
  let _ := freeProperQuotientChartedSpace I IG G M
  let _ := freeProperQuotientChartedSpace I' IG' G' M'
  rw [← (isSubmersion_quotientMk_freeProperQuotient I IG G M).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact (((isSubmersion_quotientMk_freeProperQuotient I' IG' G' M').contMDiff).of_le hm).comp hφ

/-- **Uniqueness of the quotient manifold structure up to canonical diffeomorphism.** If `e` is a
bijection from `MulAction.orbitRel.Quotient G M` onto a manifold `N` for which `e ∘ Quotient.mk`
is a `C^∞` submersion, then `e` is a `C^∞` diffeomorphism. -/
def freeProperQuotientDiffeomorphOfIsSubmersion (e : MulAction.orbitRel.Quotient G M ≃ N)
    (he : IsSubmersion I I' ∞ (e ∘ Quotient.mk (MulAction.orbitRel G M))) :
    letI := freeProperQuotientChartedSpace I IG G M
    MulAction.orbitRel.Quotient G M ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ), I'⟯ N :=
  letI := freeProperQuotientChartedSpace I IG G M
  (isSubmersion_quotientMk_freeProperQuotient I IG G M).diffeomorphOfEquiv he
    Quotient.mk_surjective e rfl

/-- The forward map of `freeProperQuotientDiffeomorphOfIsSubmersion` is the given bijection. -/
@[simp]
theorem coe_freeProperQuotientDiffeomorphOfIsSubmersion
    (e : MulAction.orbitRel.Quotient G M ≃ N)
    (he : IsSubmersion I I' ∞ (e ∘ Quotient.mk (MulAction.orbitRel G M))) :
    ⇑(freeProperQuotientDiffeomorphOfIsSubmersion I IG G e he) = e := by
  let _ := freeProperQuotientChartedSpace I IG G M
  exact (isSubmersion_quotientMk_freeProperQuotient I IG G M).coe_diffeomorphOfEquiv he
    Quotient.mk_surjective e rfl

/-- The inverse of `freeProperQuotientDiffeomorphOfIsSubmersion` is the inverse bijection. -/
@[simp]
theorem coe_freeProperQuotientDiffeomorphOfIsSubmersion_symm
    (e : MulAction.orbitRel.Quotient G M ≃ N)
    (he : IsSubmersion I I' ∞ (e ∘ Quotient.mk (MulAction.orbitRel G M))) :
    letI := freeProperQuotientChartedSpace I IG G M
    ⇑(freeProperQuotientDiffeomorphOfIsSubmersion I IG G e he).symm = e.symm := by
  let _ := freeProperQuotientChartedSpace I IG G M
  exact (isSubmersion_quotientMk_freeProperQuotient I IG G M).coe_diffeomorphOfEquiv_symm he
    Quotient.mk_surjective e rfl

/-- **Uniqueness of the maximal atlas.** Any `C^∞` manifold structure on
`MulAction.orbitRel.Quotient G M` over `Fin (dim M - dim G) → ℝ` for which the orbit projection is
a `C^∞` submersion has the same maximal atlas as `TauCeti.freeProperQuotientChartedSpace`. -/
theorem maximalAtlas_freeProperQuotient_eq_of_isSubmersion
    {c : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M)}
    (hc : letI := c; IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M))
    (hsub : letI := c; IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M))) :
    (letI := freeProperQuotientChartedSpace I IG G M;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) =
      (letI := c;
        IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
          (MulAction.orbitRel.Quotient G M)) :=
  IsSubmersion.maximalAtlas_eq (isSubmersion_quotientMk_freeProperQuotient I IG G M) hsub
    Quotient.mk_surjective (isManifold_freeProperQuotient I IG G M) hc

end DescentAndUniqueness

section Specializations

variable {E EG H HG : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace H] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
  [I.Boundaryless]
  (G M : Type*)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **Compatibility with discrete-action quotients.** When `G` is discrete, the action is properly
discontinuous (`ProperSMul.properlyDiscontinuousSMul`), so Mathlib equips
`MulAction.orbitRel.Quotient G M` with the pushed-forward charts
`MulAction.instChartedSpaceQuotient` modelled on `I`. The identity map is a `C^∞` diffeomorphism
from `TauCeti.freeProperQuotientChartedSpace` to `MulAction.instChartedSpaceQuotient`. -/
def freeProperQuotientDiscreteDiffeomorph [DiscreteTopology G] :
    letI := freeProperQuotientChartedSpace I IG G M
    haveI := ProperSMul.properlyDiscontinuousSMul G M
    haveI := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
    haveI := IG.t2Space_of_lieGroup (G := G) ∞
    haveI := t2Space_of_properSMul_of_t1Group (G := G) (X := M)
    haveI := I.locallyCompactSpace
    haveI := ChartedSpace.locallyCompactSpace H M
    MulAction.orbitRel.Quotient G M ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ), I⟯
      MulAction.orbitRel.Quotient G M :=
  letI := freeProperQuotientChartedSpace I IG G M
  haveI : ProperlyDiscontinuousSMul G M := ProperSMul.properlyDiscontinuousSMul G M
  haveI : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := IG) (I' := I) ∞
  haveI : T2Space G := IG.t2Space_of_lieGroup ∞
  haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI : ContMDiffConstSMul I ∞ G M :=
    ⟨fun _ ↦ (ContMDiffSMul.contMDiff_smul (I := IG) (I' := I) (n := ∞)).comp
      (contMDiff_const.prodMk contMDiff_id)⟩
  have hdisc : IsSubmersion I I ∞
      (⇑(Equiv.refl (MulAction.orbitRel.Quotient G M)) ∘ Quotient.mk (MulAction.orbitRel G M)) :=
    (isSubmersionOfComplement_iff (F := PUnit.{1}).2 fun x ↦
      (isLocalDiffeomorph_quotientMk (I := I) (n := ∞) (G := G) x).isSubmersionAtOfComplement_comp
        (IsSubmersionOfComplement.id.isSubmersionAt _)).isSubmersion
  freeProperQuotientDiffeomorphOfIsSubmersion I IG G (Equiv.refl _) hdisc

/-- The discrete-action comparison diffeomorphism is the identity on orbits. -/
@[simp]
theorem freeProperQuotientDiscreteDiffeomorph_apply [DiscreteTopology G]
    (q : MulAction.orbitRel.Quotient G M) :
    freeProperQuotientDiscreteDiffeomorph I IG G M q = q := by
  let _ := freeProperQuotientChartedSpace I IG G M
  have := ProperSMul.properlyDiscontinuousSMul G M
  have := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
  have := IG.t2Space_of_lieGroup (G := G) ∞
  have := t2Space_of_properSMul_of_t1Group (G := G) (X := M)
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  exact congrFun (coe_freeProperQuotientDiffeomorphOfIsSubmersion I IG G (Equiv.refl _) _) q

/-- The inverse of the discrete-action comparison diffeomorphism is the identity on orbits. -/
@[simp]
theorem freeProperQuotientDiscreteDiffeomorph_symm_apply [DiscreteTopology G]
    (q : MulAction.orbitRel.Quotient G M) :
    letI := freeProperQuotientChartedSpace I IG G M
    haveI := ProperSMul.properlyDiscontinuousSMul G M
    haveI := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
    haveI := IG.t2Space_of_lieGroup (G := G) ∞
    haveI := t2Space_of_properSMul_of_t1Group (G := G) (X := M)
    haveI := I.locallyCompactSpace
    haveI := ChartedSpace.locallyCompactSpace H M
    (freeProperQuotientDiscreteDiffeomorph I IG G M).symm q = q := by
  let _ := freeProperQuotientChartedSpace I IG G M
  have := ProperSMul.properlyDiscontinuousSMul G M
  have := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
  have := IG.t2Space_of_lieGroup (G := G) ∞
  have := t2Space_of_properSMul_of_t1Group (G := G) (X := M)
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  exact congrFun (coe_freeProperQuotientDiffeomorphOfIsSubmersion_symm I IG G (Equiv.refl _) _) q

/-- **Trivial group specialization.** When `G` is a subsingleton, the orbit projection is bijective
and identifies `MulAction.orbitRel.Quotient G M` smoothly with `M`. -/
def freeProperQuotientSubsingletonDiffeomorph [Subsingleton G] :
    letI := freeProperQuotientChartedSpace I IG G M
    MulAction.orbitRel.Quotient G M ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ), I⟯ M := by
  letI := freeProperQuotientChartedSpace I IG G M
  have hbij : Bijective (Quotient.mk (MulAction.orbitRel G M)) := by
    refine ⟨fun x y hxy ↦ ?_, Quotient.mk_surjective⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hxy))
    simpa only [Subsingleton.elim g 1, one_smul] using hg.symm
  let e : MulAction.orbitRel.Quotient G M ≃ M := (Equiv.ofBijective _ hbij).symm
  have he : e ∘ Quotient.mk (MulAction.orbitRel G M) = id :=
    funext fun x ↦ Equiv.symm_apply_apply (Equiv.ofBijective _ hbij) x
  exact freeProperQuotientDiffeomorphOfIsSubmersion I IG G e (he.symm ▸ IsSubmersion.id)

/-- On an orbit `⟦x⟧`, the trivial-group diffeomorphism returns `x`. -/
@[simp]
theorem freeProperQuotientSubsingletonDiffeomorph_mk [Subsingleton G] (x : M) :
    freeProperQuotientSubsingletonDiffeomorph I IG G M
      (Quotient.mk (MulAction.orbitRel G M) x) = x := by
  unfold freeProperQuotientSubsingletonDiffeomorph
  simp only [coe_freeProperQuotientDiffeomorphOfIsSubmersion]
  exact Equiv.symm_apply_apply _ x

/-- The inverse of the trivial-group diffeomorphism is the orbit projection. -/
@[simp]
theorem freeProperQuotientSubsingletonDiffeomorph_symm_apply [Subsingleton G] (x : M) :
    letI := freeProperQuotientChartedSpace I IG G M
    (freeProperQuotientSubsingletonDiffeomorph I IG G M).symm x =
      Quotient.mk (MulAction.orbitRel G M) x := by
  let _ := freeProperQuotientChartedSpace I IG G M
  unfold freeProperQuotientSubsingletonDiffeomorph
  rw [coe_freeProperQuotientDiffeomorphOfIsSubmersion_symm]
  rfl

end Specializations

/-- **The quotient manifold theorem.** The orbit space `MulAction.orbitRel.Quotient G M` of a free,
proper, smooth action of a finite-dimensional real Lie group `G` on a finite-dimensional
boundaryless smooth real manifold `M` admits a `C^∞` manifold structure of dimension
`dim M - dim G`, retaining its quotient topology, for which the orbit projection `Quotient.mk''` is
a `C^∞` submersion. No separation or countability hypotheses are needed, and `M` may be empty. -/
theorem exists_freeProperQuotient_isSubmersion
    {E EG H HG M G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace H] [TopologicalSpace HG]
    (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG)
    [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
    [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M] :
    ∃ cs : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) :=
  ⟨freeProperQuotientChartedSpace I IG G M,
    isManifold_freeProperQuotient I IG G M,
    isSubmersion_quotientMk_freeProperQuotient I IG G M⟩

end TauCeti
