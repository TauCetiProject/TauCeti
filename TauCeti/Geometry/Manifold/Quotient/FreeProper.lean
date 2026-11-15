/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
public import TauCeti.Geometry.Manifold.Submersion.Descent
public import TauCeti.Topology.Algebra.GroupAction.SliceChart

import TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.Orbit
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# The quotient manifold theorem for free proper Lie group actions

Let a finite-dimensional real Lie group `G` modelled on `(EG, IG)` act smoothly, freely and
properly on a finite-dimensional boundaryless smooth manifold `M` modelled on `(E, I)`. This file
equips the orbit space `MulAction.orbitRel.Quotient G M` (carrying its quotient topology) with a
smooth manifold structure of dimension `dim M - dim G` for which the orbit projection
`Quotient.mk (MulAction.orbitRel G M) : M → MulAction.orbitRel.Quotient G M` is a smooth
submersion with complement `EG` and vertical tangent kernel equal at each `x : M` to the orbit
tangent space `𝔤 · x`.

## Mathematical overview

1. **Transverse slice tubes at free points**
   (`TauCeti.exists_injOn_isLocalDiffeomorphOn_smul_slice`):
   at any point `x : M` with trivial stabilizer, the isotropy algebra `𝔤_x` vanishes
   (`TauCeti.isotropy_fundamental_eq_bot_of_stabilizer_eq_bot`) and the orbit tangent space `𝔤 · x`
   has dimension `dim G` (`TauCeti.finrank_orbitTangent_fundamental_of_stabilizer_eq_bot`). Choosing
   a linear complement `W` of `𝔤 · x` in `T_x M` and identifying `W` with
   `Fin (dim M - dim G) → ℝ` gives a chart slice `σ` through `x` whose slice map
   `(g, s) ↦ g • σ s` is a smooth local diffeomorphism at `(1, 0)`
   (`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`), hence along `G × U` for small `U` by
   equivariance (`IsLocalDiffeomorphAt.eventually_forall_smul_slice`), and injective on `G × U`
   after shrinking `U` by properness (`ProperSMul.exists_mem_nhds_injOn_smul_slice`).
2. **Gluing slice charts** (`TauCeti.freeProperQuotientChartedSpace`,
   `TauCeti.isManifold_freeProperQuotient`): for a free action, each point `x : M` supplies an open
   embedding `u ↦ ⟦σ_x u⟧` of an open subset of `Fin (dim M - dim G) → ℝ` into `M ⧸ G`
   (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`), with smooth overlap transitions
   (`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`), assembled into a smooth manifold via
   `TauCeti.chartedSpaceOfIsOpenEmbedding`. No global `ChartedSpace` instance is installed on
   `MulAction.orbitRel.Quotient G M`, avoiding an instance diamond with
   `MulAction.instChartedSpaceQuotient` for discrete actions.
3. **Submersion and vertical kernel**
   (`TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
   `TauCeti.isSubmersion_quotientMk_freeProperQuotient`,
   `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`,
   `TauCeti.exists_freeProperQuotient_isSubmersion`): reading the orbit projection against the local
   inverse of each slice tube shows it is smooth, and composing with the slice at `x` shows its
   differential is surjective; `ContMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv` then
   supplies the submersion normal form with complement `EG`, and dimension counting identifies
   `ker dπ_x` with `𝔤 · x`.
4. **Descent, uniqueness, and discrete actions**: `C^m` maps (`m ≤ ∞`), immersions, and submersions
   out of `M ⧸ G` are characterized by composition with the orbit projection; equivariant smooth
   maps and submersions descend to orbit spaces; any surjective smooth submersion out of `M` whose
   fibres are the `G`-orbits is canonically diffeomorphic to `M ⧸ G`
   (`TauCeti.freeProperQuotientDiffeomorph`), and the smooth structure on `M ⧸ G` making the orbit
   projection a submersion is unique up to maximal atlas
   (`TauCeti.maximalAtlas_freeProperQuotient_eq`). When `G` is discrete, the orbit projection is a
   smooth local diffeomorphism
   (`TauCeti.isLocalDiffeomorph_quotientMk_freeProperQuotient_of_discreteTopology`).

No explicit Hausdorff or second-countability hypotheses are needed: `G`, `M`, and `M ⧸ G` are
automatically Hausdorff (`ModelWithCorners.t2Space_of_lieGroup`,
`t2Space_of_properSMul_of_t1Group`, `t2Space_quotient_mulAction_of_properSMul`), and when `M` is
second countable so is `M ⧸ G` (`MulAction.isOpenQuotientMap_quotientMk.secondCountableTopology`).
An empty manifold `M` is allowed.

## Main declarations

* `TauCeti.exists_injOn_isLocalDiffeomorphOn_smul_slice`: existence of an injective local
  diffeomorphism slice tube `G × U → M` around any free point of a proper smooth action.
* `TauCeti.freeProperQuotientChartedSpace`: the glued atlas on `MulAction.orbitRel.Quotient G M`
  modelled on `Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ`.
* `TauCeti.isManifold_freeProperQuotient`: `MulAction.orbitRel.Quotient G M` is a smooth manifold.
* `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient` and
  `TauCeti.isSubmersion_quotientMk_freeProperQuotient`: the orbit projection is a smooth submersion
  with complement `EG`.
* `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`: the vertical kernel `(mfderiv π x).ker` is
  the orbit tangent space `(InfinitesimalAction.fundamental IG G I M).orbitTangent x`.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: existential form of the quotient manifold
  theorem packaging the atlas, manifold structure, submersion property, and vertical kernel.
* `TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.isImmersion_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.isSubmersion_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`,
  `TauCeti.isSubmersion_orbitRelQuotientMap_freeProperQuotient`,
  `TauCeti.smoothFreeProperQuotientMk`, and `ContMDiffMap.freeProperQuotientLift`: smooth descent
  and functoriality on orbit spaces.
* `TauCeti.freeProperQuotientDiffeomorph` and `TauCeti.maximalAtlas_freeProperQuotient_eq`:
  uniqueness of the quotient manifold up to canonical diffeomorphism and equality of maximal
  atlases.
* `TauCeti.isLocalDiffeomorph_quotientMk_freeProperQuotient_of_discreteTopology`: for a discrete
  Lie group `G`, the orbit projection is a smooth local diffeomorphism.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorems 4.29–4.31 and Theorem 21.10 (the quotient manifold theorem).
* Eckhard Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21.
-/

public section

noncomputable section

open Function Set Filter Manifold Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### Transverse slice tubes at free points -/

section PointwiseSlice

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M]

/-- **Transverse slice tubes at free points of proper smooth actions.** Let a finite-dimensional
real Lie group `G` act smoothly and properly on a finite-dimensional boundaryless smooth manifold
`M`, and let `x : M` have trivial stabilizer. Then there exist a slice
`σ : (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) → M` sending `0` to `x` and an open
neighbourhood `U` of `0` on which `σ` is smooth and such that the slice map `(g, s) ↦ g • σ s` is
injective on `G × U` and a smooth local diffeomorphism at every point of `G × U`. -/
theorem exists_injOn_isLocalDiffeomorphOn_smul_slice {x : M}
    (hx : MulAction.stabilizer G x = ⊥) :
    ∃ (σ : (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) → M)
      (U : Set (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)),
      σ 0 = x ∧ IsOpen U ∧ 0 ∈ U ∧
      ContMDiffOn 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) I ∞ σ U ∧
      InjOn (fun p : G × (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2)
        (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn
        (IG.prod 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)) I ∞
        (fun p : G × (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2)
        (univ ×ˢ U) := by
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hiso := isotropy_fundamental_eq_bot_of_stabilizer_eq_bot (I := IG) (I' := I) hx
  have hdimO := finrank_orbitTangent_fundamental_of_stabilizer_eq_bot (I := IG) (I' := I) hx
  -- Choose a complement `W` of the orbit tangent space in `E` and identify it with standard
  -- Euclidean space of dimension `dim M - dim G`.
  let O : Submodule ℝ E := (InfinitesimalAction.fundamental IG G I M).orbitTangent x
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl O
  have hWW := Submodule.finrank_add_eq_of_isCompl hW
  let S := Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ
  let K := 𝓘(ℝ, S)
  let e : W ≃L[ℝ] S := ContinuousLinearEquiv.ofFinrankEq (by
    have hdimO' : Module.finrank ℝ O = Module.finrank ℝ EG := hdimO
    dsimp only [S]
    rw [Module.finrank_fin_fun]
    omega)
  let σ : S → M := fun s ↦ (extChartAt I x).symm (extChartAt I x x + (e.symm s : E))
  have hσ0 : σ 0 = x := by simp [σ]
  -- Transport the chart-slice local diffeomorphism along `id × e.symm`; `Diffeomorph.prodCongr`
  -- restricts both second factors to share a model vector space, so we assemble `D` directly.
  let D : (G × S) ≃ₘ⟮IG.prod K, IG.prod 𝓘(ℝ, W)⟯ (G × W) :=
    { toEquiv := (Equiv.refl G).prodCongr e.symm.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (e.symm.toDiffeomorph.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (e.toDiffeomorph.contMDiff.comp contMDiff_snd) }
  have hlocW := isLocalDiffeomorphAt_smul_extChartAt_symm (I := IG) (I' := I) hiso hW
  have hD0 : D (1, 0) = (1, 0) := Prod.ext rfl (map_zero e.symm)
  have hloc0 : IsLocalDiffeomorphAt (IG.prod K) I ∞ (fun p : G × S ↦ p.1 • σ p.2) (1, 0) :=
    IsLocalDiffeomorphAt.comp I M (D.isLocalDiffeomorph (1, 0))
      (g := fun q : G × W ↦ q.1 • (extChartAt I x).symm (extChartAt I x x + q.2))
      (hD0.symm ▸ hlocW)
  -- Equivariance extends the local diffeomorphism along `G`, and properness shrinks the slice to
  -- make the tube map globally injective on `G × U`.
  have hloc_ev := hloc0.eventually_forall_smul_slice
  obtain ⟨N, hN, hinjN⟩ := hloc0.exists_mem_nhds_injOn
  have hσ_cont : ContinuousAt σ 0 := by
    have h1 : ContinuousAt (fun s : S ↦ (1 : G) • σ s) 0 :=
      hloc0.contMDiffAt.continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
    simpa only [one_smul] using h1
  obtain ⟨U₀, hU₀, hinjU₀⟩ :=
    ProperSMul.exists_mem_nhds_injOn_smul_slice hσ_cont (hσ0.symm ▸ hx) hN hinjN
  obtain ⟨U, hU_sub, hU_open, h0U⟩ := mem_nhds_iff.1 (inter_mem hU₀ hloc_ev)
  have hlocU : IsLocalDiffeomorphOn (IG.prod K) I ∞ (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) :=
    fun p ↦ (hU_sub p.2.2).2 p.1.1
  have hσU : ContMDiffOn K I ∞ σ U := by
    have h1 : ContMDiffOn K I ∞ (fun s : S ↦ (1 : G) • σ s) U :=
      hlocU.contMDiffOn.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        fun s hs ↦ ⟨mem_univ _, hs⟩
    simpa only [one_smul] using h1
  exact ⟨σ, U, hσ0, hU_open, h0U, hσU,
    hinjU₀.mono (prod_mono_right fun _ hu ↦ (hU_sub hu).1), hlocU⟩

end PointwiseSlice

/-! ### Gluing slice charts on the orbit space -/

namespace FreeProperQuotient

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners ℝ EG HG)
  (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- Chosen slice map `Fin (dim M - dim G) → ℝ → M` through `x`. -/
private def sliceFn (x : M) : (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) → M :=
  (exists_injOn_isLocalDiffeomorphOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot x)).choose

/-- Chosen open slice parameter domain around `0` for `x`. -/
private def sliceOpens (x : M) :
    TopologicalSpace.Opens (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) :=
  let h := (exists_injOn_isLocalDiffeomorphOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot x)).choose_spec
  ⟨h.choose, h.choose_spec.2.1⟩

private theorem sliceFn_zero (x : M) : sliceFn IG G I M x 0 = x :=
  (exists_injOn_isLocalDiffeomorphOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.choose_spec.1

private theorem zero_mem_sliceOpens (x : M) : (0 : Fin _ → ℝ) ∈ sliceOpens IG G I M x :=
  (exists_injOn_isLocalDiffeomorphOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.choose_spec.2.2.1

private theorem contMDiffOn_sliceFn (x : M) :
    ContMDiffOn 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) I ∞
      (sliceFn IG G I M x) (sliceOpens IG G I M x) :=
  (exists_injOn_isLocalDiffeomorphOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.choose_spec.2.2.2.1

private theorem injOn_smul_sliceFn (x : M) :
    InjOn (fun p : G × (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ↦
      p.1 • sliceFn IG G I M x p.2) (univ ×ˢ (sliceOpens IG G I M x : Set _)) :=
  (exists_injOn_isLocalDiffeomorphOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.choose_spec.2.2.2.2.1

private theorem isLocalDiffeomorphOn_smul_sliceFn (x : M) :
    IsLocalDiffeomorphOn
      (IG.prod 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)) I ∞
      (fun p : G × (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ↦
        p.1 • sliceFn IG G I M x p.2)
      (univ ×ˢ (sliceOpens IG G I M x : Set _)) :=
  (exists_injOn_isLocalDiffeomorphOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot x)).choose_spec.choose_spec.2.2.2.2.2

/-- The open slice-chart parametrization `u ↦ ⟦σ_x u⟧` of the orbit space near `⟦x⟧`. -/
private def sliceChart (x : M) (u : sliceOpens IG G I M x) : MulAction.orbitRel.Quotient G M :=
  Quotient.mk (MulAction.orbitRel G M) (sliceFn IG G I M x u)

private theorem contMDiff_sliceFn_coe (x : M) :
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) I ∞
      (fun u : sliceOpens IG G I M x ↦ sliceFn IG G I M x u) :=
  (contMDiffOn_sliceFn IG G I M x).comp_contMDiff contMDiff_subtype_val fun u ↦ u.2

private theorem isOpenEmbedding_sliceChart (x : M) :
    IsOpenEmbedding (sliceChart IG G I M x) :=
  MulAction.isOpenEmbedding_quotientMk_slice (sliceOpens IG G I M x).isOpen
    (injOn_smul_sliceFn IG G I M x)
    (isLocalDiffeomorphOn_smul_sliceFn IG G I M x).isLocalHomeomorphOn

private theorem exists_sliceChart_eq (q : MulAction.orbitRel.Quotient G M) :
    ∃ (x : M) (u : sliceOpens IG G I M x), sliceChart IG G I M x u = q :=
  Quotient.inductionOn q fun x ↦
    ⟨x, ⟨0, zero_mem_sliceOpens IG G I M x⟩, congrArg (Quotient.mk _) (sliceFn_zero IG G I M x)⟩

/-- Any smooth map `f : P → M` whose value at `z` meets the orbit of `σ_y v` factors modulo `G`
near `z` through a smooth map into `sliceOpens y`. Applied to another slice this gives smooth
overlap transitions; applied to `id : M → M` it gives smoothness of the orbit projection. -/
private theorem exists_contMDiffAt_sliceChart_comp_eq
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] {L : ModelWithCorners ℝ EP HP}
    [TopologicalSpace P] [ChartedSpace HP P]
    {f : P → M} {z : P} (hf : ContMDiffAt L I ∞ f z)
    (y : M) (v : sliceOpens IG G I M y)
    (hv : sliceChart IG G I M y v = Quotient.mk (MulAction.orbitRel G M) (f z)) :
    ∃ T : P → sliceOpens IG G I M y,
      ContMDiffAt L 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞ T z ∧
        sliceChart IG G I M y ∘ T =ᶠ[𝓝 z] Quotient.mk (MulAction.orbitRel G M) ∘ f := by
  classical
  obtain ⟨t, ht_smooth, -, ht_ev⟩ :=
    exists_contMDiffAt_quotientMk_slice_eq_iff (sliceOpens IG G I M y).isOpen
      (injOn_smul_sliceFn IG G I M y) (isLocalDiffeomorphOn_smul_sliceFn IG G I M y)
      hf v.2 hv
  let T : P → sliceOpens IG G I M y := fun z' ↦
    if h : t z' ∈ sliceOpens IG G I M y then ⟨t z', h⟩ else v
  have hval : Subtype.val ∘ T =ᶠ[𝓝 z] t := by
    filter_upwards [ht_ev] with z' hz'
    dsimp only [Function.comp_apply, T]
    split_ifs with h
    · rfl
    · exact (h hz'.1).elim
  have hT_smooth : ContMDiffAt L 𝓘(ℝ, Fin _ → ℝ) ∞ T z :=
    (ContMDiffAt.subtypeVal_comp_iff (sliceOpens IG G I M y) T z).1
      (ht_smooth.congr_of_eventuallyEq hval)
  refine ⟨T, hT_smooth, ?_⟩
  filter_upwards [ht_ev] with z' hz'
  dsimp only [Function.comp_apply, sliceChart, T]
  split_ifs with h
  · exact (hz'.2 (t z') hz'.1).2 rfl
  · exact (h hz'.1).elim

private theorem exists_contMDiffAt_sliceTransition (x y : M)
    (u : sliceOpens IG G I M x) (v : sliceOpens IG G I M y)
    (huv : sliceChart IG G I M x u = sliceChart IG G I M y v) :
    ∃ T : sliceOpens IG G I M x → sliceOpens IG G I M y,
      ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
        𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞ T u ∧
        sliceChart IG G I M y ∘ T =ᶠ[𝓝 u] sliceChart IG G I M x :=
  exists_contMDiffAt_sliceChart_comp_eq IG G I M
    (contMDiff_sliceFn_coe IG G I M x u) y v huv.symm

end FreeProperQuotient

/-! ### The quotient manifold structure and submersion property -/

section QuotientManifold

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

variable (IG G I M) in
/-- The charted-space structure on the orbit space `MulAction.orbitRel.Quotient G M` of a free
proper smooth action of a finite-dimensional real Lie group `G` on a finite-dimensional
boundaryless smooth manifold `M`, glued from transverse slice charts modelled on
`Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ`.

It uses the quotient topology on `MulAction.orbitRel.Quotient G M` and is deliberately not a global
instance so that it cannot collide with `MulAction.instChartedSpaceQuotient` when `G` is discrete.
-/
@[instance_reducible]
noncomputable def freeProperQuotientChartedSpace :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding
    (FreeProperQuotient.isOpenEmbedding_sliceChart IG G I M)
    (FreeProperQuotient.exists_sliceChart_eq IG G I M)

/-- The orbit space of a free proper smooth Lie group action equipped with
`TauCeti.freeProperQuotientChartedSpace` is a smooth manifold of dimension `dim M - dim G`. -/
theorem isManifold_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding
    (FreeProperQuotient.isOpenEmbedding_sliceChart IG G I M)
    (FreeProperQuotient.exists_sliceChart_eq IG G I M)
    (FreeProperQuotient.exists_contMDiffAt_sliceTransition IG G I M)

private theorem isLocalDiffeomorph_sliceChart (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    IsLocalDiffeomorph 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (FreeProperQuotient.sliceChart IG G I M x) :=
  isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
    (FreeProperQuotient.isOpenEmbedding_sliceChart IG G I M)
    (FreeProperQuotient.exists_sliceChart_eq IG G I M)
    (FreeProperQuotient.exists_contMDiffAt_sliceTransition IG G I M) x

/-- The orbit projection `M → M ⧸ G` of a free proper smooth Lie group action is smooth for
`TauCeti.freeProperQuotientChartedSpace`. -/
theorem contMDiff_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiff I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG G I M
  intro x
  obtain ⟨T, hT_smooth, hT_eq⟩ :=
    FreeProperQuotient.exists_contMDiffAt_sliceChart_comp_eq IG G I M
      (f := id) contMDiffAt_id x ⟨0, FreeProperQuotient.zero_mem_sliceOpens IG G I M x⟩
      (congrArg (Quotient.mk _) (FreeProperQuotient.sliceFn_zero IG G I M x))
  exact ((isLocalDiffeomorph_sliceChart (IG := IG) x (T x)).contMDiffAt.comp x
    hT_smooth).congr_of_eventuallyEq hT_eq.symm

/-- At every point `x : M`, the differential of the orbit projection `M → M ⧸ G` is surjective. -/
theorem surjective_mfderiv_quotientMk_freeProperQuotient (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    Surjective (mfderiv I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x) := by
  let := freeProperQuotientChartedSpace IG G I M
  let K := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  let u₀ : FreeProperQuotient.sliceOpens IG G I M x :=
    ⟨0, FreeProperQuotient.zero_mem_sliceOpens IG G I M x⟩
  let g : FreeProperQuotient.sliceOpens IG G I M x → M :=
    fun u ↦ FreeProperQuotient.sliceFn IG G I M x u
  have hgu₀ : g u₀ = x := FreeProperQuotient.sliceFn_zero IG G I M x
  have hq : MDifferentiableAt I K (Quotient.mk (MulAction.orbitRel G M)) x :=
    (contMDiff_quotientMk_freeProperQuotient (IG := IG) x).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt K I g u₀ :=
    (FreeProperQuotient.contMDiff_sliceFn_coe IG G I M x u₀).mdifferentiableAt (by simp)
  have hsurj :=
    ((isLocalDiffeomorph_sliceChart (IG := IG) x u₀).isInvertible_mfderiv (by simp)).surjective
  intro w
  obtain ⟨v, hv⟩ := hsurj w
  refine ⟨mfderiv K I g u₀ v, ?_⟩
  rw [← mfderiv_comp_apply_of_eq u₀ hq hg hgu₀ v]
  exact hv

/-- **The orbit projection of a free proper smooth Lie group action is a smooth submersion with
complement `EG`.** -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    Manifold.IsSubmersionOfComplement EG I
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient (IG := IG) (G := G) (I := I) (M := M)
  refine Manifold.isSubmersionOfComplement_iff.2 fun x ↦ ?_
  have hsub :=
    (contMDiff_quotientMk_freeProperQuotient (IG := IG) (G := G) (I := I) (M := M)).contMDiffOn
      |>.isSubmersionAtOfComplement_of_surjective_mfderiv isOpen_univ (mem_univ x) (by simp)
        (surjective_mfderiv_quotientMk_freeProperQuotient (IG := IG) (G := G) (I := I) (M := M) x)
  -- At `x : M`, the orbit tangent space embeds into `E` with dimension `dim EG`, so
  -- `dim EG ≤ dim E` and the standard complement has dimension `dim EG`.
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hdimO := finrank_orbitTangent_fundamental_of_stabilizer_eq_bot (I := IG) (I' := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)
  have hle : Module.finrank ℝ EG ≤ Module.finrank ℝ E := by
    rw [← hdimO]
    exact Submodule.finrank_le _
  let L : (Fin (Module.finrank ℝ E -
      Module.finrank ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)) → ℝ) ≃L[ℝ] EG :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
      omega)
  exact (Manifold.IsSubmersionAtOfComplement.congr_F L).mp hsub

/-- **The orbit projection of a free proper smooth Lie group action is a smooth submersion.** -/
theorem isSubmersion_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    Manifold.IsSubmersion I
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) :=
  letI := freeProperQuotientChartedSpace IG G I M
  (isSubmersionOfComplement_quotientMk_freeProperQuotient
    (IG := IG) (G := G) (I := I) (M := M)).isSubmersion

/-- **Vertical tangent spaces of the free proper quotient.** At every `x : M`, the kernel of the
differential of the orbit projection `M → M ⧸ G` is the orbit tangent space `𝔤 · x`. -/
theorem ker_mfderiv_quotientMk_freeProperQuotient (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    (mfderiv I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace IG G I M
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have : FiniteDimensional ℝ (TangentSpace I x) :=
    (tangentSpaceCastModel I x).toLinearEquiv.finiteDimensional
  let K := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  let q := Quotient.mk (MulAction.orbitRel G M)
  let D := mfderiv I K q x
  -- Every orbit tangent vector comes from the orbit map `h ↦ h • x`, on which `q` is constant.
  have hle : (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤ D.ker := by
    intro v hv
    obtain ⟨ξ, rfl⟩ :=
      ((InfinitesimalAction.fundamental IG G I M).mem_orbitTangent_iff x).1 hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      InfinitesimalAction.fundamental_apply, fundamentalVectorField_apply]
    have hq_diff : MDifferentiableAt I K q x :=
      (contMDiff_quotientMk_freeProperQuotient (IG := IG) (G := G) (I := I)
        x).mdifferentiableAt (by simp)
    have horb_diff : MDifferentiableAt IG I (fun g : G ↦ g • x) 1 :=
      (ContMDiffSMul.contMDiff_smul_const (I := IG) (I' := I) (n := ∞) (G := G)
        x).mdifferentiableAt (by simp)
    have hconst : q ∘ (fun g : G ↦ g • x) = fun _ : G ↦ q x :=
      funext fun g ↦ Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, rfl⟩)
    have hcomp := mfderiv_comp_apply_of_eq (1 : G) hq_diff horb_diff (one_smul G x) ξ
    rw [hconst, mfderiv_const, zero_apply] at hcomp
    exact hcomp.symm
  -- Both subspaces have dimension `dim EG`, hence coincide.
  have hdimO := finrank_orbitTangent_fundamental_of_stabilizer_eq_bot (I := IG) (I' := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)
  have hle_dim : Module.finrank ℝ EG ≤ Module.finrank ℝ E :=
    hdimO ▸ Submodule.finrank_le _
  have hdimK : Module.finrank ℝ D.ker = Module.finrank ℝ EG := by
    have hk := D.toLinearMap.finrank_ker_eq_sub_of_surjective
      (surjective_mfderiv_quotientMk_freeProperQuotient (IG := IG) (G := G) x)
    simp only [finrank_tangentSpace, Module.finrank_fin_fun] at hk
    exact hk.trans (by omega)
  exact (Submodule.eq_of_le_of_finrank_eq hle (hdimO.trans hdimK.symm)).symm

variable (IG G I M) in
/-- **The quotient manifold theorem for free proper Lie group actions.** If a finite-dimensional
real Lie group `G` acts smoothly, freely and properly on a finite-dimensional boundaryless smooth
manifold `M`, then the orbit space `MulAction.orbitRel.Quotient G M` (with its quotient topology)
admits a smooth manifold structure of dimension `dim M - dim G` for which the orbit projection is a
smooth submersion whose differential at each `x : M` has kernel equal to the orbit tangent space
`𝔤 · x`. -/
theorem exists_freeProperQuotient_isSubmersion :
    ∃ cs : ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
        (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      Manifold.IsSubmersion I
        𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (Quotient.mk (MulAction.orbitRel G M)) ∧
      ∀ x : M,
        (mfderiv I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
          (Quotient.mk (MulAction.orbitRel G M)) x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x :=
  ⟨freeProperQuotientChartedSpace IG G I M,
    isManifold_freeProperQuotient (IG := IG),
    isSubmersion_quotientMk_freeProperQuotient (IG := IG),
    ker_mfderiv_quotientMk_freeProperQuotient (IG := IG)⟩

end QuotientManifold

/-! ### Smooth descent, immersions, and equivariant maps -/

section Descent

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {m : ℕ∞ω}

/-- For `m ≤ ∞`, a map out of the free proper quotient `M ⧸ G` is `C^m` at the orbit of `x`
exactly when its composite with the orbit projection is `C^m` at `x`. -/
theorem contMDiffAt_comp_quotientMk_freeProperQuotient_iff (hm : m ≤ ∞)
    {g : MulAction.orbitRel.Quotient G M → N} {x : M} :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiffAt I J m (g ∘ Quotient.mk (MulAction.orbitRel G M)) x ↔
      ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) J m g
        (Quotient.mk (MulAction.orbitRel G M) x) :=
  letI := freeProperQuotientChartedSpace IG G I M
  ((isSubmersion_quotientMk_freeProperQuotient (IG := IG)).isSubmersionAt x).contMDiffAt_comp_iff hm

/-- For `m ≤ ∞`, a map out of the free proper quotient `M ⧸ G` is `C^m` globally exactly when its
composite with the orbit projection is `C^m`. -/
theorem contMDiff_comp_quotientMk_freeProperQuotient_iff (hm : m ≤ ∞)
    {g : MulAction.orbitRel.Quotient G M → N} :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiff I J m (g ∘ Quotient.mk (MulAction.orbitRel G M)) ↔
      ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) J m g :=
  letI := freeProperQuotientChartedSpace IG G I M
  (isSubmersion_quotientMk_freeProperQuotient (IG := IG)).contMDiff_comp_iff
    Quotient.mk_surjective hm

/-- For `m ≤ ∞`, the descent of a `G`-invariant map `f : M → N` to the free proper quotient `M ⧸ G`
is `C^m` at the orbit of `x` exactly when `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff (hm : m ≤ ∞)
    {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} {x : M} :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) J m
      (MulAction.orbitRelQuotientLift f hf) (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I J m f x := by
  let := freeProperQuotientChartedSpace IG G I M
  rw [← contMDiffAt_comp_quotientMk_freeProperQuotient_iff (IG := IG) hm,
    MulAction.orbitRelQuotientLift_comp_mk]

/-- For `m ≤ ∞`, the descent of a `G`-invariant map `f : M → N` to the free proper quotient `M ⧸ G`
is `C^m` globally exactly when `f` is `C^m`. -/
theorem contMDiff_orbitRelQuotientLift_freeProperQuotient_iff (hm : m ≤ ∞)
    {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) J m
      (MulAction.orbitRelQuotientLift f hf) ↔ ContMDiff I J m f := by
  let := freeProperQuotientChartedSpace IG G I M
  rw [← contMDiff_comp_quotientMk_freeProperQuotient_iff (IG := IG) hm,
    MulAction.orbitRelQuotientLift_comp_mk]

/-- **Immersion criterion for maps descended to a free proper quotient.** Into a finite-dimensional
boundaryless smooth manifold `N`, the descent of a `G`-invariant map `f : M → N` is a smooth
immersion exactly when `f` is smooth and at every `x : M` its differential kills precisely the
orbit tangent space `𝔤 · x`. -/
theorem isImmersion_orbitRelQuotientLift_freeProperQuotient_iff
    [FiniteDimensional ℝ EN] [J.Boundaryless] [IsManifold J ∞ N]
    {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := freeProperQuotientChartedSpace IG G I M
    Manifold.IsImmersion 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) J ∞
      (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I J ∞ f ∧
        ∀ x : M, (mfderiv I J f x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient (IG := IG) (G := G) (I := I) (M := M)
  rw [(isSubmersion_quotientMk_freeProperQuotient (IG := IG)).isImmersion_iff_ker_mfderiv_comp
    Quotient.mk_surjective (by simp), MulAction.orbitRelQuotientLift_comp_mk]
  exact and_congr_right' (forall_congr' fun x ↦ by
    rw [ker_mfderiv_quotientMk_freeProperQuotient (IG := IG) x])

/-- **Submersion criterion for maps descended to a free proper quotient.** Into a finite-dimensional
smooth manifold `N`, the descent of a `G`-invariant map `f : M → N` is a smooth submersion exactly
when `f` is smooth and has surjective differential at every `x : M`. -/
theorem isSubmersion_orbitRelQuotientLift_freeProperQuotient_iff
    [FiniteDimensional ℝ EN] [IsManifold J ∞ N]
    {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := freeProperQuotientChartedSpace IG G I M
    Manifold.IsSubmersion 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) J ∞
      (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I J ∞ f ∧ ∀ x : M, Surjective (mfderiv I J f x) := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient (IG := IG) (G := G) (I := I) (M := M)
  rw [(isSubmersion_quotientMk_freeProperQuotient
      (IG := IG)).isSubmersion_iff_surjective_mfderiv_comp Quotient.mk_surjective (by simp),
    MulAction.orbitRelQuotientLift_comp_mk]

end Descent

section Equivariant

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **Functoriality of free proper orbit spaces.** For `m ≤ ∞`, an equivariant `C^m` map between
two manifolds carrying free proper smooth Lie group actions induces a `C^m` map between their orbit
spaces. -/
theorem contMDiff_orbitRelQuotientMap_freeProperQuotient
    {EG' : Type*} [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
    {HG' : Type*} [TopologicalSpace HG'] {IG' : ModelWithCorners ℝ EG' HG'}
    {G' : Type*} [Group G'] [TopologicalSpace G'] [ChartedSpace HG' G'] [LieGroup IG' ∞ G']
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [ProperSMul G' M'] [IsCancelSMul G' M']
    {m : ℕ∞ω} {σ : G → G'} (hm : m ≤ ∞) {φ : M →ₑ[σ] M'} (hφ : ContMDiff I I' m φ) :
    letI := freeProperQuotientChartedSpace IG G I M
    letI := freeProperQuotientChartedSpace IG' G' I' M'
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ EG') → ℝ) m
      (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace IG G I M
  let := freeProperQuotientChartedSpace IG' G' I' M'
  rw [← contMDiff_comp_quotientMk_freeProperQuotient_iff (IG := IG) hm,
    MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_quotientMk_freeProperQuotient (IG := IG')).of_le hm).comp hφ

/-- **Equivariant submersions descend to submersions of free proper orbit spaces.** An equivariant
smooth submersion between two manifolds carrying free proper smooth Lie group actions induces a
smooth submersion between their orbit spaces. -/
theorem isSubmersion_orbitRelQuotientMap_freeProperQuotient
    {EG' : Type*} [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
    {HG' : Type*} [TopologicalSpace HG'] {IG' : ModelWithCorners ℝ EG' HG'}
    {G' : Type*} [Group G'] [TopologicalSpace G'] [ChartedSpace HG' G'] [LieGroup IG' ∞ G']
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [ProperSMul G' M'] [IsCancelSMul G' M']
    {σ : G → G'} {φ : M →ₑ[σ] M'} (hφ : Manifold.IsSubmersion I I' ∞ φ) :
    letI := freeProperQuotientChartedSpace IG G I M
    letI := freeProperQuotientChartedSpace IG' G' I' M'
    Manifold.IsSubmersion 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ EG') → ℝ) ∞
      (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace IG G I M
  let := freeProperQuotientChartedSpace IG' G' I' M'
  have := isManifold_freeProperQuotient (IG := IG) (G := G) (I := I) (M := M)
  have := isManifold_freeProperQuotient (IG := IG') (G := G') (I := I') (M := M')
  rw [(isSubmersion_quotientMk_freeProperQuotient
      (IG := IG)).isSubmersion_iff_surjective_mfderiv_comp Quotient.mk_surjective (by simp),
    MulActionHom.orbitRelQuotientMap_comp_mk]
  refine ⟨(contMDiff_quotientMk_freeProperQuotient (IG := IG')).comp hφ.contMDiff, fun x ↦ ?_⟩
  rw [mfderiv_comp x
    ((contMDiff_quotientMk_freeProperQuotient (IG := IG') (φ x)).mdifferentiableAt (by simp))
    (hφ.contMDiff.mdifferentiableAt (by simp))]
  exact (surjective_mfderiv_quotientMk_freeProperQuotient (IG := IG') (φ x)).comp
    (hφ.surjective_mfderiv (by simp) x)

variable (IG G I M) in
/-- The orbit projection `M → M ⧸ G` of a free proper smooth Lie group action, as a bundled smooth
map for `TauCeti.freeProperQuotientChartedSpace`. -/
def smoothFreeProperQuotientMk :
    letI := freeProperQuotientChartedSpace IG G I M
    C^∞⟮I, M; 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ),
      MulAction.orbitRel.Quotient G M⟯ :=
  letI := freeProperQuotientChartedSpace IG G I M
  ⟨Quotient.mk _, contMDiff_quotientMk_freeProperQuotient (IG := IG)⟩

/-- The underlying function of `TauCeti.smoothFreeProperQuotientMk` is the orbit projection. -/
theorem coe_smoothFreeProperQuotientMk :
    letI := freeProperQuotientChartedSpace IG G I M
    ⇑(smoothFreeProperQuotientMk IG G I M) = Quotient.mk (MulAction.orbitRel G M) :=
  (rfl)

/-- `TauCeti.smoothFreeProperQuotientMk` sends each `x : M` to its `G`-orbit. -/
@[simp]
theorem smoothFreeProperQuotientMk_apply (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    smoothFreeProperQuotientMk IG G I M x = Quotient.mk (MulAction.orbitRel G M) x :=
  (rfl)

end Equivariant

/-! ### Uniqueness and discrete specialization -/

section Uniqueness

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **Uniqueness of the free proper quotient up to diffeomorphism.** Any surjective smooth
submersion `q : M → N` whose fibres are the `G`-orbits induces a canonical smooth diffeomorphism
`M ⧸ G ≃ₘ N` intertwining the orbit projection with `q`. -/
noncomputable def freeProperQuotientDiffeomorph
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) :
    letI := freeProperQuotientChartedSpace IG G I M
    MulAction.orbitRel.Quotient G M ≃ₘ⟮
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ), J⟯ N :=
  letI := freeProperQuotientChartedSpace IG G I M
  (isSubmersion_quotientMk_freeProperQuotient (IG := IG)).diffeomorphOfSurjective
    Quotient.mk_surjective hq hq_surj fun x y ↦ Quotient.eq.trans (hfib x y).symm

/-- `TauCeti.freeProperQuotientDiffeomorph` sends the orbit of `x` to `q x`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_apply_mk
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib
      (Quotient.mk (MulAction.orbitRel G M) x) = q x :=
  letI := freeProperQuotientChartedSpace IG G I M
  (isSubmersion_quotientMk_freeProperQuotient (IG := IG)).diffeomorphOfSurjective_apply
    Quotient.mk_surjective hq hq_surj _ x

/-- Composing `TauCeti.freeProperQuotientDiffeomorph` with the orbit projection recovers `q`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_comp_quotientMk
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) :
    letI := freeProperQuotientChartedSpace IG G I M
    ⇑(freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib) ∘
      Quotient.mk (MulAction.orbitRel G M) = q :=
  letI := freeProperQuotientChartedSpace IG G I M
  (isSubmersion_quotientMk_freeProperQuotient (IG := IG)).diffeomorphOfSurjective_comp
    Quotient.mk_surjective hq hq_surj _

/-- The inverse of `TauCeti.freeProperQuotientDiffeomorph` sends `q x` to the orbit of `x`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_symm_apply
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    (freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib).symm (q x) =
      Quotient.mk (MulAction.orbitRel G M) x := by
  let := freeProperQuotientChartedSpace IG G I M
  rw [← freeProperQuotientDiffeomorph_apply_mk (IG := IG) hq hq_surj hfib x,
    Diffeomorph.symm_apply_apply]

/-- Composing the inverse of `TauCeti.freeProperQuotientDiffeomorph` with `q` recovers the orbit
projection. -/
@[simp]
theorem freeProperQuotientDiffeomorph_symm_comp
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y) :
    letI := freeProperQuotientChartedSpace IG G I M
    ⇑(freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib).symm ∘ q =
      Quotient.mk (MulAction.orbitRel G M) :=
  funext (freeProperQuotientDiffeomorph_symm_apply (IG := IG) hq hq_surj hfib)

/-- `TauCeti.freeProperQuotientDiffeomorph` is the unique map `M ⧸ G → N` intertwining the orbit
projection with `q`. -/
theorem eq_freeProperQuotientDiffeomorph_iff
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {q : M → N} (hq : Manifold.IsSubmersion I J ∞ q) (hq_surj : Surjective q)
    (hfib : ∀ x y : M, q x = q y ↔ MulAction.orbitRel G M x y)
    {e : MulAction.orbitRel.Quotient G M → N} :
    letI := freeProperQuotientChartedSpace IG G I M
    e = ⇑(freeProperQuotientDiffeomorph (IG := IG) hq hq_surj hfib) ↔
      e ∘ Quotient.mk (MulAction.orbitRel G M) = q :=
  letI := freeProperQuotientChartedSpace IG G I M
  (isSubmersion_quotientMk_freeProperQuotient (IG := IG)).eq_diffeomorphOfSurjective_iff
    Quotient.mk_surjective hq hq_surj _

/-- **Uniqueness of the smooth atlas on `M ⧸ G`.** Any charted-space structure on
`MulAction.orbitRel.Quotient G M` modelled on `Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ`
that makes `M ⧸ G` a smooth manifold and the orbit projection a smooth submersion has the same
maximal atlas as `TauCeti.freeProperQuotientChartedSpace`. -/
theorem maximalAtlas_freeProperQuotient_eq
    {c : ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
      (MulAction.orbitRel.Quotient G M)}
    (hc : letI := c;
      IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M))
    (hq : letI := c;
      Manifold.IsSubmersion I 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (Quotient.mk (MulAction.orbitRel G M))) :
    (letI := freeProperQuotientChartedSpace IG G I M;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) =
    (letI := c;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) := by
  let K := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  refine maximalAtlas_chartedSpaceOfIsOpenEmbedding_eq
    (FreeProperQuotient.isOpenEmbedding_sliceChart IG G I M)
    (FreeProperQuotient.exists_sliceChart_eq IG G I M) hc fun x u ↦ ?_
  let := c
  have : Nonempty (FreeProperQuotient.sliceOpens IG G I M x) := ⟨u⟩
  let φ := FreeProperQuotient.sliceChart IG G I M x
  let hφ := FreeProperQuotient.isOpenEmbedding_sliceChart IG G I M x
  let e := hφ.toOpenPartialHomeomorph φ
  -- For `c`, `φ` is smooth as `Quotient.mk ∘ σ_x`, and `e.symm` is smooth on `range φ` because
  -- its composite with the submersion `Quotient.mk` is locally the slice projection `T`.
  have hto : ContMDiffOn K K ∞ e e.source := by
    rw [hφ.toOpenPartialHomeomorph_apply]
    exact (hq.contMDiff.comp (FreeProperQuotient.contMDiff_sliceFn_coe IG G I M x)).contMDiffOn
  have hinv : ContMDiffOn K K ∞ e.symm e.target := by
    rw [hφ.toOpenPartialHomeomorph_target]
    rintro _ ⟨w, rfl⟩
    refine ContMDiffAt.contMDiffWithinAt ?_
    refine ((hq.isSubmersionAt (FreeProperQuotient.sliceFn IG G I M x w)).contMDiffAt_comp_iff
      le_rfl).1 ?_
    obtain ⟨T, hT_smooth, hT_eq⟩ :=
      FreeProperQuotient.exists_contMDiffAt_sliceChart_comp_eq IG G I M
        (f := id) contMDiffAt_id x w rfl
    refine hT_smooth.congr_of_eventuallyEq ?_
    filter_upwards [hT_eq] with z hz
    simp only [Function.comp_apply, id_eq] at hz
    rw [Function.comp_apply, ← hz, hφ.toOpenPartialHomeomorph_left_inv]
  let Φ : PartialDiffeomorph K K (FreeProperQuotient.sliceOpens IG G I M x)
      (MulAction.orbitRel.Quotient G M) ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := hto
      contMDiffOn_invFun := hinv }
  have hu : u ∈ Φ.source := by simp [Φ, e]
  exact isLocalDiffeomorphAt_of_eqOn (Φ := Φ) hu fun _ _ ↦ by simp [Φ, e, φ]

/-- **Discrete Lie groups act by smooth local diffeomorphisms onto the free proper quotient.** When
`G` carries the discrete topology, the orbit projection `M → M ⧸ G` is a smooth local
diffeomorphism for `TauCeti.freeProperQuotientChartedSpace`. -/
theorem isLocalDiffeomorph_quotientMk_freeProperQuotient_of_discreteTopology
    [DiscreteTopology G] :
    letI := freeProperQuotientChartedSpace IG G I M
    IsLocalDiffeomorph I
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient (IG := IG) (G := G) (I := I) (M := M)
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let K := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ)
  intro x
  -- Since `G` is discrete, the orbit map is locally constant at `1`, so `𝔤 · x = 0`.
  have hconst : (fun h : G ↦ h • x) =ᶠ[𝓝 (1 : G)] fun _ : G ↦ (1 : G) • x := by
    filter_upwards [(isOpen_discrete {(1 : G)}).mem_nhds rfl] with h hh
    rw [mem_singleton_iff.1 hh]
  have horb : (InfinitesimalAction.fundamental IG G I M).orbitTangent x = ⊥ := by
    have hr := range_mfderiv_smul_const (I := IG) (I' := I) x (1 : G)
    rw [← one_smul G x, ← hr, hconst.mfderiv_eq, mfderiv_const]
    exact LinearMap.range_zero
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hdimG : Module.finrank ℝ EG = 0 := by
    have hdimO := finrank_orbitTangent_fundamental_of_stabilizer_eq_bot (I := IG) (I' := I)
      (IsCancelSMul.stabilizer_eq_bot (G := G) x)
    rw [horb, finrank_bot] at hdimO
    exact hdimO.symm
  have hinj : Injective (mfderiv I K (Quotient.mk (MulAction.orbitRel G M)) x) :=
    LinearMap.ker_eq_bot.1
      ((ker_mfderiv_quotientMk_freeProperQuotient (IG := IG) (G := G) x).trans horb)
  exact isLocalDiffeomorphAt_of_injective_mfderiv
    (contMDiff_quotientMk_freeProperQuotient (IG := IG) (G := G)).contMDiffOn
    isOpen_univ (mem_univ x) BoundarylessManifold.isInteriorPoint (by simp) hinj
    (by rw [Module.finrank_fin_fun, hdimG, Nat.sub_zero])

end Uniqueness

end TauCeti

/-! ### Bundled smooth descent -/

namespace ContMDiffMap

open TauCeti

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ProperSMul G M] [IsCancelSMul G M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- A smooth map `f : C^∞⟮I, M; J, N⟯` invariant under a free proper smooth Lie group action
descends to a bundled smooth map on the orbit space `M ⧸ G`. -/
def freeProperQuotientLift (f : C^∞⟮I, M; J, N⟯) (IG : ModelWithCorners ℝ EG HG)
    [LieGroup IG ∞ G] [ContMDiffSMul IG I ∞ G M]
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace IG G I M
    C^∞⟮𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ),
      MulAction.orbitRel.Quotient G M; J, N⟯ :=
  letI := freeProperQuotientChartedSpace IG G I M
  ⟨MulAction.orbitRelQuotientLift f hf,
    (contMDiff_orbitRelQuotientLift_freeProperQuotient_iff (IG := IG) le_rfl).2 f.contMDiff⟩

/-- The underlying function of `ContMDiffMap.freeProperQuotientLift` is
`TauCeti.MulAction.orbitRelQuotientLift`. -/
theorem coe_freeProperQuotientLift (f : C^∞⟮I, M; J, N⟯) (IG : ModelWithCorners ℝ EG HG)
    [LieGroup IG ∞ G] [ContMDiffSMul IG I ∞ G M]
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace IG G I M
    ⇑(f.freeProperQuotientLift IG hf) = MulAction.orbitRelQuotientLift f hf :=
  (rfl)

/-- `ContMDiffMap.freeProperQuotientLift` evaluates on the orbit of `x` as `f x`. -/
@[simp]
theorem freeProperQuotientLift_apply_mk (f : C^∞⟮I, M; J, N⟯) (IG : ModelWithCorners ℝ EG HG)
    [LieGroup IG ∞ G] [ContMDiffSMul IG I ∞ G M]
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    f.freeProperQuotientLift IG hf (Quotient.mk (MulAction.orbitRel G M) x) = f x :=
  MulAction.orbitRelQuotientLift_mk x

/-- Pulling `ContMDiffMap.freeProperQuotientLift` back along
`TauCeti.smoothFreeProperQuotientMk` recovers `f`. -/
@[simp]
theorem freeProperQuotientLift_comp_smoothFreeProperQuotientMk (f : C^∞⟮I, M; J, N⟯)
    (IG : ModelWithCorners ℝ EG HG) [LieGroup IG ∞ G]
    [ContMDiffSMul IG I ∞ G M] (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace IG G I M
    (f.freeProperQuotientLift IG hf).comp (smoothFreeProperQuotientMk IG G I M) = f := by
  let := freeProperQuotientChartedSpace IG G I M
  exact ContMDiffMap.ext fun x ↦ by simp

/-- `ContMDiffMap.freeProperQuotientLift` is the unique bundled smooth map on `M ⧸ G` whose
pullback along the orbit projection is `f`. -/
theorem eq_freeProperQuotientLift_iff (f : C^∞⟮I, M; J, N⟯) (IG : ModelWithCorners ℝ EG HG)
    [LieGroup IG ∞ G] [ContMDiffSMul IG I ∞ G M]
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace IG G I M
    ∀ {u : C^∞⟮𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ EG) → ℝ),
        MulAction.orbitRel.Quotient G M; J, N⟯},
      u = f.freeProperQuotientLift IG hf ↔
        u.comp (smoothFreeProperQuotientMk IG G I M) = f := by
  let := freeProperQuotientChartedSpace IG G I M
  intro u
  refine ⟨fun h ↦ h ▸ freeProperQuotientLift_comp_smoothFreeProperQuotientMk f IG hf,
    fun h ↦ DFunLike.ext' ?_⟩
  rw [coe_freeProperQuotientLift, MulAction.eq_orbitRelQuotientLift_iff]
  exact funext fun x ↦ by simpa using DFunLike.congr_fun h x

end ContMDiffMap
