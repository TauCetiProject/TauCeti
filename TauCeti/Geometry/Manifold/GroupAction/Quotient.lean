/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Quotient.Descent
import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.Orbit
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# The quotient manifold theorem for free proper Lie group actions

Let a real Lie group `G` act smoothly, freely, and properly on a finite-dimensional boundaryless
smooth manifold `M`. This file equips the orbit space `MulAction.orbitRel.Quotient G M`, retaining
its quotient topology, with a smooth manifold structure of dimension `dim M - dim G` for which the
orbit projection `Quotient.mk (MulAction.orbitRel G M)` is a surjective smooth submersion with
vertical kernel equal to the orbit tangent space `𝔤 · x` at every point `x : M`.

Neither Hausdorff separation, second countability, boundarylessness of the group model, nor
finite-dimensionality of `G` needs to be assumed separately: a Lie group modelled on a normed space
is `T₂` (`ModelWithCorners.t2Space_of_lieGroup`) and boundaryless
(`ContMDiffMul.boundarylessManifold`), a space admitting a proper action of a `T₁` group is `T₂`
(`t2Space_of_properSMul_of_t1Group`), and whenever `M` is nonempty each free proper orbit embeds
`G` as a closed subspace of the locally compact manifold `M`, forcing `G` to be finite-dimensional
by Riesz's theorem (`FiniteDimensional.of_locallyCompact_manifold`); when `M` is empty the orbit
space is empty and the atlas and submersion conditions hold vacuously. Mathlib already supplies the
quotient's Hausdorff (`t2Space_quotient_mulAction_of_properSMul`) and second-countable instances.

At each `x : M`, choosing a linear complement `W` of the orbit tangent space `𝔤 · x` inside `T_x M`
produces a chart slice whose slice map `G × W → M` is a smooth local diffeomorphism at `(1, 0)`
(`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`), hence along `G × U` for a small open
neighbourhood `U` of `0` (`IsLocalDiffeomorphAt.eventually_forall_smul_slice`), and properness of
the action shrinks `U` further so that the slice map is injective on `G × U`
(`ProperSMul.exists_mem_nhds_injOn_smul_slice`). The induced open embeddings `U → M ⧸ G`
(`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`) have smooth overlap transitions
(`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`) and assemble via
`TauCeti.chartedSpaceOfIsOpenEmbedding` into the smooth manifold structure on `M ⧸ G`.

## Main declarations

* `TauCeti.freeProperQuotientChartedSpace`: the slice-chart atlas on
  `MulAction.orbitRel.Quotient G M`, modelled on `Fin (finrank ℝ E - finrank ℝ EG) → ℝ`.
* `TauCeti.isManifold_freeProperQuotient`: this atlas makes `MulAction.orbitRel.Quotient G M` a
  smooth manifold.
* `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
  `TauCeti.isSubmersion_quotientMk_freeProperQuotient`: the orbit projection is a smooth submersion
  (with fibre model `EG`).
* `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`,
  `TauCeti.mem_ker_mfderiv_quotientMk_freeProperQuotient_iff`: the vertical kernel of the orbit
  projection at `x` is the orbit tangent space `𝔤 · x` (spanned by the fundamental vector fields).
* `TauCeti.exists_freeProperQuotient_isSubmersion`: existential packaging of the quotient manifold
  theorem.
* `TauCeti.contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`: smooth universal property and
  functoriality for equivariant maps.
* `TauCeti.freeProperQuotientDiffeomorphOfIsSubmersion`,
  `TauCeti.exists_diffeomorph_freeProperQuotient_apply_eq_self`,
  `TauCeti.exists_diffeomorph_freeProperQuotient_instChartedSpaceQuotient_apply_eq_self`:
  uniqueness of the quotient smooth structure up to canonical diffeomorphism, and compatibility
  with Mathlib's discrete-quotient atlas `MulAction.instChartedSpaceQuotient`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 21.10 (the quotient manifold theorem) and Theorem 21.13.
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto (2003),
  Theorem 1.21.
-/

public section

noncomputable section

open Function Filter Manifold Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace FreeProperQuotient

variable {EG HG E H : Type*}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  (IG : ModelWithCorners ℝ EG HG) (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (G : Type*) [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [IsCancelSMul G M] [ProperSMul G M]

omit [FiniteDimensional ℝ E] in
/-- For a free proper smooth action, the isotropy Lie algebra at every point `x : M` is trivial and
the orbit tangent space `𝔤 · x` has dimension `finrank ℝ EG`. -/
private theorem isotropy_eq_bot_and_finrank_orbitTangent [FiniteDimensional ℝ EG]
    [CompleteSpace EG] [CompleteSpace E] (x : M) :
    (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ ∧
      finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) = finrank ℝ EG := by
  have hstab : MulAction.stabilizer G x = ⊥ := IsCancelSMul.stabilizer_eq_bot x
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have : Subsingleton (MulAction.stabilizer G x) := hstab ▸ inferInstance
  have hiso : (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ :=
    (Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := IG) (I' := I)).1 inferInstance
  exact ⟨hiso,
    (InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x hiso⟩

include IG I G in
/-- At any point `x : M`, the free proper orbit embedding into the locally compact manifold `M`
forces `EG` to be finite-dimensional of dimension at most `finrank ℝ E`. -/
private theorem finiteDimensional_and_finrank_le (x : M) :
    FiniteDimensional ℝ EG ∧ finrank ℝ EG ≤ finrank ℝ E := by
  have : Nonempty M := ⟨x⟩
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : LocallyCompactSpace G :=
    (ProperSMul.isClosedEmbedding_smul_const (IsCancelSMul.stabilizer_eq_bot x)).locallyCompactSpace
  have : Nonempty G := ⟨1⟩
  have : FiniteDimensional ℝ EG := FiniteDimensional.of_locallyCompact_manifold G IG
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have horb := (isotropy_eq_bot_and_finrank_orbitTangent IG I G x).2
  exact ⟨‹_›, horb ▸ Submodule.finrank_le _⟩

/-- At any point `x : M`, a free proper smooth action forces `G` to be finite-dimensional and
admits a chart slice `τ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M` through `x` at `0` whose
slice map `(g, u) ↦ g • τ u` is a smooth local diffeomorphism at `(1, 0)`. -/
private theorem exists_rawSlice (x : M) :
    ∃ τ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M,
      τ 0 = x ∧ ContinuousAt τ 0 ∧
      IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
        (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • τ p.2) (1, 0) := by
  obtain ⟨_, _⟩ := finiteDimensional_and_finrank_le IG I G x
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨hiso, horb'⟩ := isotropy_eq_bot_and_finrank_orbitTangent IG I G x
  let O : Submodule ℝ E := (InfinitesimalAction.fundamental IG G I M).orbitTangent x
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl O
  have horb : finrank ℝ O = finrank ℝ EG := horb'
  have hdimW : finrank ℝ (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) = finrank ℝ W := by
    have hcompl := Submodule.finrank_add_eq_of_isCompl hW
    rw [finrank_fin_fun]
    omega
  let eW : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ≃L[ℝ] W :=
    ContinuousLinearEquiv.ofFinrankEq hdimW
  let τ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M :=
    fun u ↦ (extChartAt I x).symm (extChartAt I x x + (eW u : E))
  have hτ0 : τ 0 = x := by simp [τ]
  have hτcont : ContinuousAt τ 0 := by
    refine ((continuousOn_extChartAt_symm x).continuousAt
      ((isOpen_extChartAt_target x).mem_nhds (by simp))).comp ?_
    exact continuousAt_const.add (continuous_subtype_val.comp eW.continuous).continuousAt
  let D : (G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) ≃ₘ^∞⟮IG.prod
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ), IG.prod 𝓘(ℝ, W)⟯ (G × W) :=
    { toEquiv := (Equiv.refl G).prodCongr eW.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (eW.contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (eW.symm.contDiff.contMDiff.comp contMDiff_snd) }
  have hD (p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) : D p = (p.1, eW p.2) := by
    rw [← Diffeomorph.coe_toEquiv]
    rfl
  have hD0 : D (1, 0) = (1, 0) := by
    rw [hD]
    exact Prod.ext rfl (map_zero eW)
  have hlocD : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, W)) I ∞
      (fun p : G × W ↦ p.1 • (extChartAt I x).symm (extChartAt I x x + p.2)) (D (1, 0)) := by
    rw [hD0]
    exact isLocalDiffeomorphAt_smul_extChartAt_symm (I := IG) (I' := I) hiso hW
  have hcomp : ((fun p : G × W ↦ p.1 • (extChartAt I x).symm (extChartAt I x x + p.2)) ∘ D) =
      fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • τ p.2 :=
    funext fun p ↦ by simp [hD, τ]
  refine ⟨τ, hτ0, hτcont, ?_⟩
  rw [← hcomp]
  exact (D.isLocalDiffeomorph (1, 0)).comp I M hlocD

/-- Shrinking the domain of `exists_rawSlice` by equivariance and properness produces an open
neighbourhood `U` of `0` on which the slice map `(g, u) ↦ g • τ u` is injective and a smooth local
diffeomorphism along `G × U`. -/
private theorem exists_sliceOpen (x : M) :
    ∃ (τ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M)
      (U : TopologicalSpace.Opens (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)),
      (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ U ∧ τ 0 = x ∧
      InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • τ p.2)
        (univ ×ˢ (U : Set _)) ∧
      IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
        (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • τ p.2)
        (univ ×ˢ (U : Set _)) := by
  obtain ⟨τ, hτ0, hτcont, hloc0⟩ := exists_rawSlice IG I G x
  obtain ⟨N, hN, hinjN⟩ := hloc0.exists_mem_nhds_injOn
  have hstab : MulAction.stabilizer G (τ 0) = ⊥ := by
    rw [hτ0]
    exact IsCancelSMul.stabilizer_eq_bot x
  obtain ⟨U₁, hU₁, hinj₁⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice hτcont hstab hN hinjN
  have hev := inter_mem hU₁ hloc0.eventually_forall_smul_slice
  obtain ⟨U, hUsub, hUopen, h0U⟩ := mem_nhds_iff.1 hev
  exact ⟨τ, ⟨U, hUopen⟩, h0U, hτ0, hinj₁.mono (prod_mono_right fun _ hu ↦ (hUsub hu).1),
    fun ⟨⟨g, u⟩, _, hu⟩ ↦ (hUsub hu).2 g⟩

private def rawSlice (x : M) : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M :=
  (exists_sliceOpen IG I G x).choose

private def sliceOpen (x : M) : TopologicalSpace.Opens (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) :=
  (exists_sliceOpen IG I G x).choose_spec.choose

private theorem zero_mem_sliceOpen (x : M) :
    (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ sliceOpen IG I G x :=
  (exists_sliceOpen IG I G x).choose_spec.choose_spec.1

private theorem rawSlice_zero (x : M) : rawSlice IG I G x 0 = x :=
  (exists_sliceOpen IG I G x).choose_spec.choose_spec.2.1

private theorem injOn_smul_rawSlice (x : M) :
    InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • rawSlice IG I G x p.2)
      (univ ×ˢ (sliceOpen IG I G x : Set _)) :=
  (exists_sliceOpen IG I G x).choose_spec.choose_spec.2.2.1

private theorem isLocalDiffeomorphOn_smul_rawSlice (x : M) :
    IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
      (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • rawSlice IG I G x p.2)
      (univ ×ˢ (sliceOpen IG I G x : Set _)) :=
  (exists_sliceOpen IG I G x).choose_spec.choose_spec.2.2.2

/-- The orbit-space slice chart centred at `x`, sending `u ∈ sliceOpen x` to the orbit of
`rawSlice x u`. -/
private def sliceChart (x : M) (u : sliceOpen IG I G x) : MulAction.orbitRel.Quotient G M :=
  Quotient.mk (MulAction.orbitRel G M) (rawSlice IG I G x u)

private theorem sliceChart_zero (x : M) :
    sliceChart IG I G x ⟨0, zero_mem_sliceOpen IG I G x⟩ =
      Quotient.mk (MulAction.orbitRel G M) x := by
  simp [sliceChart, rawSlice_zero]

private theorem contMDiff_rawSlice_subtype (x : M) :
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞
      (fun u : sliceOpen IG I G x ↦ rawSlice IG I G x u) := by
  intro u
  have hl : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
      (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • rawSlice IG I G x p.2)
      (1, u.1) :=
    isLocalDiffeomorphOn_smul_rawSlice IG I G x ⟨(1, u.1), mem_univ _, u.2⟩
  have hpair : ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) ∞
      (fun v : sliceOpen IG I G x ↦ ((1 : G), (v : Fin (finrank ℝ E - finrank ℝ EG) → ℝ))) u :=
    contMDiffAt_const.prodMk (contMDiff_subtype_val u)
  have hcomp := hl.contMDiffAt.comp u hpair
  refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun v ↦ ?_)
  exact (one_smul G (rawSlice IG I G x v)).symm

private theorem isOpenEmbedding_sliceChart (x : M) : IsOpenEmbedding (sliceChart IG I G x) :=
  MulAction.isOpenEmbedding_quotientMk_slice (sliceOpen IG I G x).isOpen
    (injOn_smul_rawSlice IG I G x)
    (isLocalDiffeomorphOn_smul_rawSlice IG I G x).isLocalHomeomorphOn

private theorem exists_sliceChart_eq (q : MulAction.orbitRel.Quotient G M) :
    ∃ (x : M) (u : sliceOpen IG I G x), sliceChart IG I G x u = q := by
  induction q using Quotient.inductionOn with
  | h x => exact ⟨x, ⟨0, zero_mem_sliceOpen IG I G x⟩, sliceChart_zero IG I G x⟩

/-- Smooth maps into `M` factor locally in orbit space through any slice chart meeting the target
orbit. -/
private theorem exists_contMDiffAt_sliceChart_comp_eventuallyEq
    {FP KP P : Type*} [NormedAddCommGroup FP] [NormedSpace ℝ FP] [TopologicalSpace KP]
    {L : ModelWithCorners ℝ FP KP} [TopologicalSpace P] [ChartedSpace KP P]
    {f : P → M} {z : P} (hf : ContMDiffAt L I ∞ f z) (x : M) (u : sliceOpen IG I G x)
    (hfu : sliceChart IG I G x u = Quotient.mk (MulAction.orbitRel G M) (f z)) :
    ∃ T : P → sliceOpen IG I G x,
      ContMDiffAt L 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ T z ∧
      sliceChart IG I G x ∘ T =ᶠ[𝓝 z] Quotient.mk (MulAction.orbitRel G M) ∘ f := by
  obtain ⟨t, ht, -, hmem⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff
    (sliceOpen IG I G x).isOpen (injOn_smul_rawSlice IG I G x)
    (isLocalDiffeomorphOn_smul_rawSlice IG I G x) hf u.2 hfu
  classical
  let T : P → sliceOpen IG I G x := fun z' ↦
    if hz' : t z' ∈ sliceOpen IG I G x then ⟨t z', hz'⟩ else u
  have hTz {z' : P} (hz'U : t z' ∈ sliceOpen IG I G x) :
      (T z' : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) = t z' := by
    dsimp only [T]
    split_ifs
    rfl
  have hTeq : Subtype.val ∘ T =ᶠ[𝓝 z] t :=
    hmem.mono fun z' hz' ↦ hTz hz'.1
  refine ⟨T, (ContMDiffAt.subtypeVal_comp_iff (sliceOpen IG I G x) T z).1
    (ht.congr_of_eventuallyEq hTeq), hmem.mono fun z' ⟨hz'U, hz'iff⟩ ↦ ?_⟩
  rw [comp_apply, sliceChart, hTz hz'U]
  exact (hz'iff (t z') hz'U).2 rfl

private theorem exists_contMDiffAt_sliceChart_transition (x₁ x₂ : M) (u₁ : sliceOpen IG I G x₁)
    (u₂ : sliceOpen IG I G x₂) (hu : sliceChart IG I G x₁ u₁ = sliceChart IG I G x₂ u₂) :
    ∃ T : sliceOpen IG I G x₁ → sliceOpen IG I G x₂,
      ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ T u₁ ∧
      sliceChart IG I G x₂ ∘ T =ᶠ[𝓝 u₁] sliceChart IG I G x₁ :=
  exists_contMDiffAt_sliceChart_comp_eventuallyEq IG I G
    (contMDiff_rawSlice_subtype IG I G x₁ u₁) x₂ u₂ hu.symm

end FreeProperQuotient

section QuotientManifold

variable {EG HG E H : Type*}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {IG : ModelWithCorners ℝ EG HG} {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G M : Type*}
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [IsCancelSMul G M] [ProperSMul G M]

variable (IG I G M) in
/-- The smooth slice-chart atlas on the orbit space `MulAction.orbitRel.Quotient G M` of a free
proper smooth Lie group action, retaining its quotient topology and modelled on
`Fin (finrank ℝ E - finrank ℝ EG) → ℝ`. Deliberately a definition rather than a global instance. -/
@[instance_reducible]
def freeProperQuotientChartedSpace :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding (FreeProperQuotient.isOpenEmbedding_sliceChart IG I G)
    (FreeProperQuotient.exists_sliceChart_eq IG I G)

variable (IG I G M) in
/-- **Smoothness of the quotient atlas.** The orbit space `MulAction.orbitRel.Quotient G M` of a
free proper smooth Lie group action is a smooth manifold of dimension `dim M - dim G` for
`TauCeti.freeProperQuotientChartedSpace`. -/
theorem isManifold_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG I G M
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding (FreeProperQuotient.isOpenEmbedding_sliceChart IG I G)
    (FreeProperQuotient.exists_sliceChart_eq IG I G)
    (FreeProperQuotient.exists_contMDiffAt_sliceChart_transition IG I G)

variable (IG I G M) in
/-- The orbit projection `M → MulAction.orbitRel.Quotient G M` of a free proper smooth Lie group
action is smooth. -/
theorem contMDiff_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG I G M
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG I G M
  intro x
  obtain ⟨T, hT, hEq⟩ := FreeProperQuotient.exists_contMDiffAt_sliceChart_comp_eventuallyEq IG I G
    contMDiffAt_id x ⟨0, FreeProperQuotient.zero_mem_sliceOpen IG I G x⟩
    (FreeProperQuotient.sliceChart_zero IG I G x)
  have hchart := contMDiff_chartedSpaceOfIsOpenEmbedding
    (FreeProperQuotient.isOpenEmbedding_sliceChart IG I G)
    (FreeProperQuotient.exists_sliceChart_eq IG I G)
    (FreeProperQuotient.exists_contMDiffAt_sliceChart_transition IG I G) x
  exact ((hchart (T x)).comp x hT).congr_of_eventuallyEq hEq.symm

variable (IG I G) in
/-- At every point `x : M`, the differential of the orbit projection is surjective: the slice
through `x` is a smooth right inverse in orbit space near the orbit of `x`. -/
theorem surjective_mfderiv_quotientMk_freeProperQuotient (x : M) :
    letI := freeProperQuotientChartedSpace IG I G M
    Surjective (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x) := by
  let := freeProperQuotientChartedSpace IG I G M
  have := isManifold_freeProperQuotient IG I G M
  let u₀ : FreeProperQuotient.sliceOpen IG I G x :=
    ⟨0, FreeProperQuotient.zero_mem_sliceOpen IG I G x⟩
  let σ : FreeProperQuotient.sliceOpen IG I G x → M :=
    fun u ↦ FreeProperQuotient.rawSlice IG I G x u
  have hσx : σ u₀ = x := FreeProperQuotient.rawSlice_zero IG I G x
  have hchart : IsLocalDiffeomorphAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M) ∘ σ) u₀ :=
    isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
      (FreeProperQuotient.isOpenEmbedding_sliceChart IG I G)
      (FreeProperQuotient.exists_sliceChart_eq IG I G)
      (FreeProperQuotient.exists_contMDiffAt_sliceChart_transition IG I G) x u₀
  have hsurj := (hchart.isInvertible_mfderiv (by simp)).surjective
  have hq : MDifferentiableAt I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x :=
    (contMDiff_quotientMk_freeProperQuotient IG I G M x).mdifferentiableAt (by simp)
  have hσd : MDifferentiableAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I σ u₀ :=
    (FreeProperQuotient.contMDiff_rawSlice_subtype IG I G x u₀).mdifferentiableAt (by simp)
  rw [mfderiv_comp_of_eq hq hσd hσx, ContinuousLinearMap.coe_comp] at hsurj
  have hsurj' := hsurj.of_comp
  rwa [hσx] at hsurj'

variable (IG I G M) in
/-- The orbit projection of a free proper smooth Lie group action is a smooth submersion with fibre
model `EG`. -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG I G M
    Manifold.IsSubmersionOfComplement EG I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG I G M
  have := isManifold_freeProperQuotient IG I G M
  have hstd := (contMDiff_quotientMk_freeProperQuotient IG I G M
    |>.isSubmersionOfComplement_of_surjective_mfderiv ENat.LEInfty.out
      (surjective_mfderiv_quotientMk_freeProperQuotient IG I G))
  rw [Manifold.isSubmersionOfComplement_iff] at hstd ⊢
  intro x
  obtain ⟨_, hdim⟩ := FreeProperQuotient.finiteDimensional_and_finrank_le IG I G x
  let K : (Fin (finrank ℝ E -
      finrank ℝ (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) → ℝ) ≃L[ℝ] EG :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_fin_fun, finrank_fin_fun]; omega)
  exact (Manifold.IsSubmersionAtOfComplement.congr_F K).mp (hstd x)

variable (IG I G M) in
/-- **The orbit projection is a submersion.** For a free proper smooth Lie group action, the orbit
projection `M → MulAction.orbitRel.Quotient G M` is a smooth submersion. -/
theorem isSubmersion_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG I G M
    Manifold.IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG I G M
  exact (isSubmersionOfComplement_quotientMk_freeProperQuotient IG I G M).isSubmersion

variable (IG I G) in
/-- **Vertical tangent space as the orbit tangent space.** At every `x : M`, the kernel of the
differential of the orbit projection is the orbit tangent space `𝔤 · x` of the fundamental
infinitesimal action. -/
theorem ker_mfderiv_quotientMk_freeProperQuotient [CompleteSpace EG] (x : M) :
    letI := freeProperQuotientChartedSpace IG I G M
    (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace IG I G M
  have := isManifold_freeProperQuotient IG I G M
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨_, hdim⟩ := FreeProperQuotient.finiteDimensional_and_finrank_le IG I G x
  have hq : MDifferentiableAt I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x :=
    (contMDiff_quotientMk_freeProperQuotient IG I G M x).mdifferentiableAt (by simp)
  have horb : MDifferentiableAt IG I (fun g : G ↦ g • x) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (I := IG) (I' := I) (n := ∞) x).mdifferentiableAt
      (by simp)
  have hle : (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤
      (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M)) x).ker := by
    intro v hv
    obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ x).1 hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, InfinitesimalAction.fundamental_apply,
      fundamentalVectorField_apply]
    have hcomp := mfderiv_comp_apply_of_eq (1 : G) hq horb (one_smul G x) ξ
    have hconst : (Quotient.mk (MulAction.orbitRel G M) ∘ fun g : G ↦ g • x) =
        fun _ : G ↦ Quotient.mk (MulAction.orbitRel G M) x :=
      funext fun g ↦ Quotient.sound ⟨g, rfl⟩
    rw [hconst, mfderiv_const, zero_apply] at hcomp
    exact hcomp.symm
  have hker := (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
    (Quotient.mk (MulAction.orbitRel G M)) x).toLinearMap.finrank_ker_eq_sub_of_surjective
    (surjective_mfderiv_quotientMk_freeProperQuotient IG I G x)
  have hran := (FreeProperQuotient.isotropy_eq_bot_and_finrank_orbitTangent IG I G x).2
  rw [show finrank ℝ (TangentSpace I x) = finrank ℝ E from rfl,
    show finrank ℝ (TangentSpace 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M) x)) =
      finrank ℝ (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) from rfl,
    finrank_fin_fun] at hker
  have : FiniteDimensional ℝ (TangentSpace I x) := ‹FiniteDimensional ℝ E›
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

variable (IG) in
/-- **Pointwise vertical kernel without completeness assumptions.** A tangent vector `v` at `x`
lies in the kernel of the differential of the orbit projection if and only if it is the value at `x`
of the fundamental vector field of some `ξ : GroupLieAlgebra IG G`. -/
theorem mem_ker_mfderiv_quotientMk_freeProperQuotient_iff {x : M} {v : TangentSpace I x} :
    letI := freeProperQuotientChartedSpace IG I G M
    v ∈ (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x).ker ↔
      ∃ ξ : GroupLieAlgebra IG G, fundamentalVectorField I ξ x = v := by
  obtain ⟨_, -⟩ := FreeProperQuotient.finiteDimensional_and_finrank_le IG I G x
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  let := freeProperQuotientChartedSpace IG I G M
  rw [ker_mfderiv_quotientMk_freeProperQuotient IG I G x, InfinitesimalAction.mem_orbitTangent_iff]
  simp only [InfinitesimalAction.fundamental_apply]

/-- **The quotient manifold theorem.** Let a real Lie group `G` act smoothly, freely, and properly
on a finite-dimensional boundaryless smooth manifold `M`. Then the orbit space
`MulAction.orbitRel.Quotient G M`, retaining its quotient topology, carries a smooth manifold
structure of dimension `finrank ℝ E - finrank ℝ EG` for which the orbit projection is a smooth
submersion. -/
theorem exists_freeProperQuotient_isSubmersion
    {EG HG E H : Type*}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (IG : ModelWithCorners ℝ EG HG) (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (G M : Type*)
    [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MulAction G M] [ContMDiffSMul IG I ∞ G M] [IsCancelSMul G M] [ProperSMul G M] :
    ∃ cs : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      Manifold.IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) :=
  ⟨freeProperQuotientChartedSpace IG I G M, isManifold_freeProperQuotient IG I G M,
    isSubmersion_quotientMk_freeProperQuotient IG I G M⟩

/-! ### Smooth descent and equivariant maps -/

section Descent

variable {EN HN N : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {I' : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  {m : ℕ∞ω} {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x}

variable (IG) in
/-- **Pointwise smooth descent to the free proper orbit space.** For `m ≤ ∞`, the descent of a
`G`-invariant map `f : M → N` is `C^m` at the orbit of `x` if and only if `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff (hm : m ≤ ∞) {x : M} :
    letI := freeProperQuotientChartedSpace IG I G M
    ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I' m
      (MulAction.orbitRelQuotientLift f hf) (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I I' m f x := by
  let := freeProperQuotientChartedSpace IG I G M
  have hsub := (isSubmersion_quotientMk_freeProperQuotient IG I G M).isSubmersionAt x
  rw [← hsub.contMDiffAt_comp_iff hm, MulAction.orbitRelQuotientLift_comp_mk]

variable (IG) in
/-- **Global smooth descent to the free proper orbit space.** For `m ≤ ∞`, the descent of a
`G`-invariant map `f : M → N` is `C^m` if and only if `f` is `C^m`. -/
theorem contMDiff_orbitRelQuotientLift_freeProperQuotient_iff (hm : m ≤ ∞) :
    letI := freeProperQuotientChartedSpace IG I G M
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I' m
      (MulAction.orbitRelQuotientLift f hf) ↔ ContMDiff I I' m f := by
  let := freeProperQuotientChartedSpace IG I G M
  rw [← (isSubmersion_quotientMk_freeProperQuotient IG I G M).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulAction.orbitRelQuotientLift_comp_mk]

end Descent

section Equivariant

variable {EG' HG' E' H' : Type*}
  [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [TopologicalSpace HG']
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {IG' : ModelWithCorners ℝ EG' HG'} {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {G' M' : Type*}
  [TopologicalSpace G'] [ChartedSpace HG' G'] [Group G'] [LieGroup IG' ∞ G']
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [IsCancelSMul G' M'] [ProperSMul G' M']

variable (IG IG') in
/-- An equivariant `C^m` map (`m ≤ ∞`) between manifolds carrying free proper smooth Lie group
actions descends to a `C^m` map between their orbit spaces. -/
theorem contMDiff_orbitRelQuotientMap_freeProperQuotient {m : ℕ∞ω} (hm : m ≤ ∞)
    {σ : G → G'} {φ : M →ₑ[σ] M'} (hφ : ContMDiff I I' m φ) :
    letI := freeProperQuotientChartedSpace IG I G M
    letI := freeProperQuotientChartedSpace IG' I' G' M'
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ EG') → ℝ) m (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace IG I G M
  let := freeProperQuotientChartedSpace IG' I' G' M'
  rw [← (isSubmersion_quotientMk_freeProperQuotient IG I G M).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_quotientMk_freeProperQuotient IG' I' G' M').of_le hm).comp hφ

end Equivariant

/-! ### Uniqueness and compatibility with discrete quotients -/

section Uniqueness

variable {EB HB B : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {JB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]

variable (IG) in
/-- **Uniqueness of quotient manifolds.** Any surjective smooth submersion `q : M → B` whose fibres
are the `G`-orbits induces a canonical diffeomorphism `M ⧸ G ≃ₘ B` commuting with the
projections. -/
def freeProperQuotientDiffeomorphOfIsSubmersion {q : M → B}
    (hq : Manifold.IsSubmersion I JB ∞ q) (hsurj : Surjective q)
    (horb : ∀ x y : M, q x = q y ↔ ∃ g : G, g • x = y) :
    letI := freeProperQuotientChartedSpace IG I G M
    MulAction.orbitRel.Quotient G M ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ), JB⟯ B :=
  Equiv.diffeomorphOfSubmersions (cM := freeProperQuotientChartedSpace IG I G M)
    ((Quotient.congrRight fun x y ↦ MulAction.orbitRel_apply.trans
      ((MulAction.mem_orbit_iff.trans (horb y x).symm).trans (eq_comm.trans Setoid.ker_def.symm)))
      |>.trans (Setoid.quotientKerEquivOfSurjective q hsurj))
    (isSubmersion_quotientMk_freeProperQuotient IG I G M) Quotient.mk_surjective hq
    (funext fun _ ↦ rfl)

/-- `freeProperQuotientDiffeomorphOfIsSubmersion` acts on orbits by descending `q`. -/
@[simp]
theorem freeProperQuotientDiffeomorphOfIsSubmersion_mk {q : M → B}
    (hq : Manifold.IsSubmersion I JB ∞ q) (hsurj : Surjective q)
    (horb : ∀ x y : M, q x = q y ↔ ∃ g : G, g • x = y) (x : M) :
    freeProperQuotientDiffeomorphOfIsSubmersion IG hq hsurj horb
      (Quotient.mk (MulAction.orbitRel G M) x) = q x := by
  let := freeProperQuotientChartedSpace IG I G M
  rw [freeProperQuotientDiffeomorphOfIsSubmersion, Equiv.diffeomorphOfSubmersions_apply]
  rfl

/-- The inverse of `freeProperQuotientDiffeomorphOfIsSubmersion` sends `q x` back to the orbit of
`x`. -/
@[simp]
theorem freeProperQuotientDiffeomorphOfIsSubmersion_symm_apply {q : M → B}
    (hq : Manifold.IsSubmersion I JB ∞ q) (hsurj : Surjective q)
    (horb : ∀ x y : M, q x = q y ↔ ∃ g : G, g • x = y) (x : M) :
    letI := freeProperQuotientChartedSpace IG I G M
    (freeProperQuotientDiffeomorphOfIsSubmersion IG hq hsurj horb).symm (q x) =
      Quotient.mk (MulAction.orbitRel G M) x := by
  let := freeProperQuotientChartedSpace IG I G M
  rw [← freeProperQuotientDiffeomorphOfIsSubmersion_mk (IG := IG) hq hsurj horb x,
    Diffeomorph.symm_apply_apply]

variable (IG) in
/-- Any charted-space structure on `MulAction.orbitRel.Quotient G M` for which the orbit projection
is a smooth submersion is canonically diffeomorphic to `freeProperQuotientChartedSpace` by the
identity map. -/
theorem exists_diffeomorph_freeProperQuotient_apply_eq_self
    (a : ChartedSpace HB (MulAction.orbitRel.Quotient G M))
    (ha : letI := a; Manifold.IsSubmersion I JB ∞ (Quotient.mk (MulAction.orbitRel G M))) :
    ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) JB
        (MulAction.orbitRel.Quotient G M) _ (freeProperQuotientChartedSpace IG I G M)
        (MulAction.orbitRel.Quotient G M) _ a ∞,
      ∀ q, e q = q :=
  ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion
    (freeProperQuotientChartedSpace IG I G M) a
    (isSubmersion_quotientMk_freeProperQuotient IG I G M) Quotient.mk_surjective ha

variable (IG I G M) in
/-- **Compatibility with discrete-action quotients.** When the action of `G` on `M` is also properly
discontinuous (for instance when `G` is discrete, via `ProperSMul.properlyDiscontinuousSMul`),
`freeProperQuotientChartedSpace` is canonically diffeomorphic by the identity to Mathlib's
pushed-forward atlas `MulAction.instChartedSpaceQuotient`. -/
theorem exists_diffeomorph_freeProperQuotient_instChartedSpaceQuotient_apply_eq_self
    [ProperlyDiscontinuousSMul G M] :
    haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
    haveI : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := IG) (I' := I) ∞
    ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I
        (MulAction.orbitRel.Quotient G M) _ (freeProperQuotientChartedSpace IG I G M)
        (MulAction.orbitRel.Quotient G M) _
        (MulAction.instChartedSpaceQuotient (H := H) (G := G) (M := M)) ∞,
      ∀ q, e q = q := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := IG) (I' := I) ∞
  have : ContMDiffConstSMul I ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := IG)⟩
  refine exists_diffeomorph_freeProperQuotient_apply_eq_self IG
    (MulAction.instChartedSpaceQuotient (H := H) (G := G) (M := M)) ?_
  have hl := isLocalDiffeomorph_quotientMk (I := I) (n := ∞) (G := G) (M := M)
  exact (hl.contMDiff.isSubmersionOfComplement_of_surjective_mfderiv ENat.LEInfty.out
    fun x ↦ ((hl x).isInvertible_mfderiv (by simp)).surjective).isSubmersion

end Uniqueness

end QuotientManifold

end TauCeti
