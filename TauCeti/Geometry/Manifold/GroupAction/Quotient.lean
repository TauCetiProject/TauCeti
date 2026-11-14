/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.Descent
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# The quotient manifold theorem for free proper Lie group actions

Let a real Lie group `G` modeled on a Banach space `EG` act freely (`IsCancelSMul G M`), properly
(`ProperSMul G M`), and smoothly (`ContMDiffSMul IG I ∞ G M`) on a finite-dimensional smooth
boundaryless real manifold `M` (so `G` is automatically finite-dimensional whenever `M` is
nonempty). This file equips the orbit space `MulAction.orbitRel.Quotient G M`, with its quotient
topology, with a smooth manifold structure of dimension `dim M - dim G`
(`TauCeti.freeProperQuotientChartedSpace`, `TauCeti.isManifold_freeProperQuotient`) for which:

* the orbit projection `Quotient.mk (MulAction.orbitRel G M) : M → MulAction.orbitRel.Quotient G M`
  is a smooth submersion with complement the model space of `G`
  (`TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
  `TauCeti.isSubmersion_quotientMk_freeProperQuotient`);
* the vertical tangent space `(mfderiv ... (Quotient.mk _) x).ker` at every point `x : M` is the
  orbit tangent space `(InfinitesimalAction.fundamental IG G I M).orbitTangent x`
  (`TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`);
* the smooth structure is unique: any charted-space structure on the orbit space making the orbit
  projection a smooth submersion has the same maximal atlas
  (`TauCeti.maximalAtlas_freeProperQuotient_eq`), and any surjective smooth submersion `π : M → P`
  whose fibres are the `G`-orbits induces a smooth diffeomorphism from the orbit space onto `P`
  (`TauCeti.freeProperQuotientDiffeomorph`);
* invariant maps descend smoothly (`TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`),
  descended maps with kernel `𝔤 · x` are smooth immersions
  (`TauCeti.isImmersion_orbitRelQuotientLift_freeProperQuotient_iff`), and equivariant smooth maps
  induce smooth maps of orbit spaces (`TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`);
* every orbit admits an open neighbourhood `W` carrying a smooth `G`-equivariant map
  `u : π⁻¹(W) → G` whose associated principal-bundle chart `TauCeti.orbitTrivialization` is smooth
  with smooth inverse (`TauCeti.contMDiffOn_orbitTrivialization_freeProperQuotient`,
  `TauCeti.contMDiffOn_orbitTrivialization_symm_freeProperQuotient`,
  `TauCeti.exists_contMDiffOn_orbitTrivialization_freeProperQuotient`).

No separation or second-countability hypotheses are assumed on `G` or `M`: `G` is Hausdorff as a
Lie group (`ModelWithCorners.t2Space_of_lieGroup`), `M` is Hausdorff by properness of the action
(`t2Space_of_properSMul_of_t1Group`), and Hausdorffness as well as second countability of the orbit
space are supplied by Mathlib's `ProperSMul.t2Space_quotient_orbitRel` and
`ContinuousConstSMul.secondCountableTopology` whenever present upstairs. Empty `M` is allowed:
slice charts are indexed by `x : M`, so `FiniteDimensional ℝ EG` and `dim G ≤ dim M` are derived
from `x` whenever a slice is constructed, and all universal statements hold vacuously when `M` is
empty.

## Main declarations

* `TauCeti.exists_isLocalDiffeomorphOn_injOn_smul_slice`: at a free point `x` of a proper smooth
  action, a slice `τ` on an open neighbourhood `U` of `0` in `ℝ^{dim M - dim G}` with `τ 0 = x`
  whose slice map `(g, u) ↦ g • τ u` is injective and a local diffeomorphism on `G × U`.
* `TauCeti.freeProperQuotientChartedSpace`: the slice-chart atlas on
  `MulAction.orbitRel.Quotient G M` (not a global instance, as `IG` and `I` are not determined by
  the quotient type).
* `TauCeti.isManifold_freeProperQuotient`: smoothness of the slice-chart atlas.
* `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient` and
  `TauCeti.isSubmersion_quotientMk_freeProperQuotient`: the orbit projection is a smooth
  submersion.
* `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`: the kernel of the differential of the orbit
  projection is the orbit tangent space.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: existential form of the quotient manifold
  theorem.
* `TauCeti.maximalAtlas_freeProperQuotient_eq` and `TauCeti.freeProperQuotientDiffeomorph`:
  uniqueness of the smooth structure on the quotient.
* `TauCeti.contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.isImmersion_orbitRelQuotientLift_freeProperQuotient_iff`, and
  `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`: smooth descent and functoriality.
* `TauCeti.contMDiffOn_orbitTrivialization_freeProperQuotient`,
  `TauCeti.contMDiffOn_orbitTrivialization_symm_freeProperQuotient`, and
  `TauCeti.exists_contMDiffOn_orbitTrivialization_freeProperQuotient`: smooth local equivariant
  trivializations of the orbit projection.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorems 4.31
  and 21.10 (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto (2003),
  Theorem 1.21.
-/

public section

noncomputable section

open Function Filter Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] lieGroupOne
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### Free points and Euclidean slice tubes -/

section SliceTube

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M]

omit [IsManifold I ∞ M] in
private theorem hasMFDerivAt_mulInvariantExp_smul_smul_of_eq_zero [T2Space G] [CompleteSpace EG]
    {x : M} {ξ : GroupLieAlgebra IG G}
    (hξ : (fundamentalVectorField I ξ x : E) = 0) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ mulInvariantExp (I := IG) (s • ξ) • x) t 0 := by
  have : ContMDiffSMul IG I 1 G M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
  set γ : ℝ → M := fun s ↦ mulInvariantExp (I := IG) (s • ξ) • x
  have hγ0 : ∀ u : ℝ, u = 0 → HasMFDerivAt 𝓘(ℝ, ℝ) I γ u 0 := by
    rintro _ rfl
    have h0x : mulInvariantExp (I := IG) ((0 : ℝ) • ξ) • x = x := by simp
    have hξ0 : (fundamentalVectorField I ξ (mulInvariantExp (I := IG) ((0 : ℝ) • ξ) • x) : E) =
        0 := (congrArg (fun y : M ↦ (fundamentalVectorField I ξ y : E)) h0x).trans hξ
    have h0map : (1 : ℝ →L[ℝ] ℝ).smulRight (fundamentalVectorField I ξ (γ 0)) = 0 :=
      ContinuousLinearMap.ext_ring (by simpa [γ] using hξ0)
    exact (isMIntegralCurve_mulInvariantExp_smul_smul (I := IG) (I' := I) ξ x 0).congr_mfderiv h0map
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ s - t) t (ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id t).sub_const t).hasMFDerivAt
  have hsub : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ γ (s - t)) t 0 :=
    ((hγ0 (t - t) (sub_self t)).comp (f := fun s : ℝ ↦ s - t) t hshift).congr_mfderiv
      (ContinuousLinearMap.zero_comp _)
  have hsmul : MDifferentiableAt I I (fun y : M ↦ mulInvariantExp (I := IG) (t • ξ) • y)
      (γ (t - t)) :=
    (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) (n := 1) _).mdifferentiableAt
      one_ne_zero
  have hfun : ((fun y : M ↦ mulInvariantExp (I := IG) (t • ξ) • y) ∘ fun s : ℝ ↦ γ (s - t)) = γ :=
    funext fun s ↦ by simp [γ, ← mul_smul, ← mulInvariantExp_add_smul]
  exact hfun ▸ (hsmul.hasMFDerivAt.comp t hsub).congr_mfderiv (ContinuousLinearMap.comp_zero _)

/-- At a point with trivial stabilizer under a smooth Lie group action, the isotropy Lie algebra
vanishes. Neither Hausdorffness nor boundarylessness of `M` is needed: when `ξ_M(x) = 0`, the
exponential orbit curve `t ↦ exp(t ξ) • x` has zero derivative everywhere, hence is constant near
`0` in a chart around `x`, forcing `exp(t ξ) = 1` near `0` and thus `ξ = 0`. -/
theorem isotropy_fundamental_eq_bot_of_stabilizer_eq_bot [CompleteSpace EG] [CompleteSpace E]
    {x : M} (hx : MulAction.stabilizer G x = ⊥) :
    (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  refine (LieSubalgebra.eq_bot_iff _).2 fun ξ hξ ↦ ?_
  rw [InfinitesimalAction.mem_isotropy_iff, InfinitesimalAction.fundamental_apply] at hξ
  set γ : ℝ → M := fun t ↦ mulInvariantExp (I := IG) (t • ξ) • x
  have hγd : ∀ t : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t 0 :=
    hasMFDerivAt_mulInvariantExp_smul_smul_of_eq_zero hξ
  -- In the chart around `x`, `extChartAt I x ∘ γ` has zero derivative on a ball around `0`.
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
    ((hγd 0).continuousAt.preimage_mem_nhds ((chartAt H x).open_source.mem_nhds (by simp [γ])))
  have hf (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) ε) :
      HasFDerivAt (extChartAt I x ∘ γ) (0 : ℝ →L[ℝ] E) t :=
    (((mdifferentiableAt_extChartAt (hball ht)).hasMFDerivAt.comp t (hγd t)).congr_mfderiv
      (ContinuousLinearMap.comp_zero _)).hasFDerivAt
  have h_one (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) ε) :
      mulInvariantExp (I := IG) (t • ξ) = 1 := by
    have heq := (convex_ball (0 : ℝ) ε).is_const_of_fderivWithin_eq_zero
      (fun s hs ↦ (hf s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hf s hs).hasFDerivWithinAt.fderivWithin
        (Metric.isOpen_ball.uniqueDiffWithinAt hs))
      ht (Metric.mem_ball_self hε)
    have heq' : extChartAt I x (γ t) = extChartAt I x x := by simpa [γ] using heq
    have hγt : γ t = x :=
      (extChartAt I x).injOn (by rw [extChartAt_source]; exact hball ht)
        (mem_extChartAt_source x) heq'
    exact Subgroup.mem_bot.1 (hx ▸ MulAction.mem_stabilizer_iff.2 hγt)
  have hev : (fun t : ℝ ↦ mulInvariantExp (I := IG) (t • ξ)) =ᶠ[𝓝 0] fun _ ↦ (1 : G) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hε) h_one
  have h0 := DFunLike.congr_fun (hev.mfderiv_eq.symm.trans
    (hasMFDerivAt_mulInvariantExp_smul_zero (I := IG) (G := G) ξ).mfderiv) (1 : ℝ)
  rw [mfderiv_const] at h0
  have h1 : (1 : ℝ) • ξ = 0 := h0.symm
  rwa [one_smul] at h1

/-- At a point with trivial stabilizer under a smooth Lie group action, the orbit tangent space has
the dimension of the acting Lie group. -/
theorem finrank_orbitTangent_fundamental_of_stabilizer_eq_bot [CompleteSpace EG] [CompleteSpace E]
    {x : M} (hx : MulAction.stabilizer G x = ⊥) :
    finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) = finrank ℝ EG := by
  rw [(InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x
    (isotropy_fundamental_eq_bot_of_stabilizer_eq_bot hx)]
  exact finrank_tangentSpace (I := IG) (1 : G)

include IG I in
/-- A finite-dimensional manifold having a point with trivial stabilizer under a smooth Lie group
action has dimension at least the `finrank` of the acting group's model space. -/
theorem finrank_le_of_stabilizer_eq_bot [FiniteDimensional ℝ E]
    {x : M} (hx : MulAction.stabilizer G x = ⊥) :
    finrank ℝ EG ≤ finrank ℝ E := by
  by_cases hEG : FiniteDimensional ℝ EG
  · rw [← finrank_orbitTangent_fundamental_of_stabilizer_eq_bot (IG := IG) (I := I) hx,
      ← finrank_tangentSpace (I := I) x]
    exact Submodule.finrank_le _
  · rw [Module.finrank_of_not_finite hEG]
    exact Nat.zero_le _

variable (IG G I M) in
include IG G I M in
/-- A nonempty finite-dimensional manifold carrying a free smooth Lie group action has dimension at
least the `finrank` of the acting group's model space. -/
theorem finrank_le_of_isCancelSMul [FiniteDimensional ℝ E] [IsCancelSMul G M] [Nonempty M] :
    finrank ℝ EG ≤ finrank ℝ E := by
  obtain ⟨x⟩ := ‹Nonempty M›
  exact finrank_le_of_stabilizer_eq_bot (IG := IG) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)

/-- **Euclidean slice tubes at free points of proper actions.** Let `x : M` have trivial stabilizer
under a proper smooth action of a real Lie group `G` on a finite-dimensional boundaryless manifold
`M`. Then there exist an open neighbourhood `U` of `0` in `Fin (dim M - dim G) → ℝ` and a smooth
slice `τ` on `U` with `τ 0 = x` such that the slice map `(g, u) ↦ g • τ u` is injective and a smooth
local diffeomorphism at every point of `G × U`. -/
theorem exists_isLocalDiffeomorphOn_injOn_smul_slice [CompleteSpace EG] [FiniteDimensional ℝ E]
    [I.Boundaryless] [ProperSMul G M] {x : M} (hx : MulAction.stabilizer G x = ⊥) :
    ∃ (U : TopologicalSpace.Opens (Fin (finrank ℝ E - finrank ℝ EG) → ℝ))
      (τ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M),
      (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ U ∧
      τ 0 = x ∧
      ContMDiffOn 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞ τ U ∧
      InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • τ p.2)
        (univ ×ˢ (U : Set _)) ∧
      IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
        (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • τ p.2)
        (univ ×ˢ (U : Set _)) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hiso := isotropy_fundamental_eq_bot_of_stabilizer_eq_bot (IG := IG) (I := I) hx
  have : FiniteDimensional ℝ (GroupLieAlgebra IG G) :=
    Module.Finite.of_injective ((InfinitesimalAction.fundamental IG G I M).eval x)
      ((InfinitesimalAction.isotropy_eq_bot_iff _ x).1 hiso)
  have : FiniteDimensional ℝ EG := ‹FiniteDimensional ℝ (GroupLieAlgebra IG G)›
  -- Choose a complement `W` of `𝔤 · x` in `T_x M = E` and identify it with `ℝ^{dim M - dim G}`.
  obtain ⟨W, hW⟩ :
      ∃ W : Submodule ℝ E, IsCompl ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) W :=
    Submodule.exists_isCompl _
  have hdim : finrank ℝ (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) = finrank ℝ W := by
    have hsum : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) +
        finrank ℝ W = finrank ℝ E := Submodule.finrank_add_eq_of_isCompl hW
    have hle := finrank_le_of_stabilizer_eq_bot (IG := IG) (I := I) hx
    rw [finrank_orbitTangent_fundamental_of_stabilizer_eq_bot hx] at hsum
    rw [Module.finrank_fin_fun]
    omega
  let eW : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ≃L[ℝ] W :=
    (LinearEquiv.ofFinrankEq _ _ hdim).toContinuousLinearEquiv
  let aff : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → E := fun v ↦ extChartAt I x x + (eW v : E)
  let τ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M := fun v ↦ (extChartAt I x).symm (aff v)
  have haff : ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) 𝓘(ℝ, E) ∞ aff :=
    (contDiff_const.add (W.subtypeL.comp eW.toContinuousLinearMap).contDiff).contMDiff
  have h0V : (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ aff ⁻¹' (extChartAt I x).target := by
    simp [aff]
  have hVopen : IsOpen (aff ⁻¹' (extChartAt I x).target) :=
    (isOpen_extChartAt_target x).preimage haff.continuous
  have hτ_on : ContMDiffOn 𝓘(ℝ, _) I ∞ τ (aff ⁻¹' (extChartAt I x).target) :=
    (contMDiffOn_extChartAt_symm x).comp haff.contMDiffOn fun _ hv ↦ hv
  have hτ0 : τ 0 = x := by simp [τ, aff]
  -- Transport `isLocalDiffeomorphAt_smul_extChartAt_symm` from `G × W` to `G × ℝ^{dim M - dim G}`.
  have hlocW := isLocalDiffeomorphAt_smul_extChartAt_symm (I := IG) (I' := I) (G := G) hiso hW
  have hprod : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, _)) (IG.prod 𝓘(ℝ, W)) ∞
      (Prod.map id eW) ((1 : G), (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) :=
    ((Diffeomorph.refl IG G ∞).isLocalDiffeomorph 1).prodMap
      (eW.toDiffeomorph.isLocalDiffeomorph 0)
  have hloc0 : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, _)) I ∞ (fun p : G × _ ↦ p.1 • τ p.2) (1, 0) :=
    IsLocalDiffeomorphAt.comp (hg := by simpa using hlocW) (hf := hprod)
  -- Local injectivity at `(1, 0)` upgrades by properness to injectivity on a tube `G × U₁`.
  obtain ⟨t, ht, hinj_loc⟩ := hloc0.exists_mem_nhds_injOn
  obtain ⟨U₁, hU₁, hinj₁⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice
    (hτ_on.contMDiffAt (hVopen.mem_nhds h0V)).continuousAt (hτ0.symm ▸ hx) ht hinj_loc
  obtain ⟨U₀, hU₀_sub, hU₀_open, h0U₀⟩ := mem_nhds_iff.1 (Filter.inter_mem
    (Filter.inter_mem (hVopen.mem_nhds h0V) hU₁) hloc0.eventually_forall_smul_slice)
  refine ⟨⟨U₀, hU₀_open⟩, τ, h0U₀, hτ0, hτ_on.mono fun _ hv ↦ (hU₀_sub hv).1.1,
    hinj₁.mono (prod_mono_right fun _ hv ↦ (hU₀_sub hv).1.2),
    fun ⟨⟨g, _⟩, _, hv⟩ ↦ (hU₀_sub hv).2 g⟩

end SliceTube

/-! ### The smooth atlas on the orbit space -/

namespace FreeProperQuotient

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

variable (IG G I) in
/-- The open slice parameter domain around `0` in `Fin (dim M - dim G) → ℝ` chosen for `x : M`. -/
private def sliceDomain (x : M) :
    TopologicalSpace.Opens (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) :=
  (exists_isLocalDiffeomorphOn_injOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose

variable (IG G I) in
/-- The smooth transverse slice through `x : M`. -/
private def slice (x : M) : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M :=
  (exists_isLocalDiffeomorphOn_injOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose

private theorem zero_mem_sliceDomain (x : M) :
    (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ sliceDomain IG G I x :=
  (exists_isLocalDiffeomorphOn_injOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose_spec.1

private theorem slice_zero (x : M) : slice IG G I x 0 = x :=
  (exists_isLocalDiffeomorphOn_injOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose_spec.2.1

private theorem contMDiffOn_slice (x : M) :
    ContMDiffOn 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞
      (slice IG G I x) (sliceDomain IG G I x) :=
  (exists_isLocalDiffeomorphOn_injOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose_spec.2.2.1

private theorem injOn_smul_slice (x : M) :
    InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • slice IG G I x p.2)
      (univ ×ˢ (sliceDomain IG G I x : Set _)) :=
  (exists_isLocalDiffeomorphOn_injOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose_spec.2.2.2.1

private theorem isLocalDiffeomorphOn_smul_slice (x : M) :
    IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
      (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • slice IG G I x p.2)
      (univ ×ˢ (sliceDomain IG G I x : Set _)) :=
  (exists_isLocalDiffeomorphOn_injOn_smul_slice (IG := IG) (G := G) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)).choose_spec.choose_spec.2.2.2.2

variable (IG G I) in
/-- The orbit-space chart parametrization `u ↦ ⟦slice x u⟧` associated with `x : M`. -/
private def sliceChart (x : M) :
    sliceDomain IG G I x → MulAction.orbitRel.Quotient G M :=
  fun u ↦ Quotient.mk (MulAction.orbitRel G M) (slice IG G I x u)

private theorem isOpenEmbedding_sliceChart (x : M) :
    IsOpenEmbedding (sliceChart IG G I x) :=
  MulAction.isOpenEmbedding_quotientMk_slice (sliceDomain IG G I x).isOpen
    (injOn_smul_slice (IG := IG) (I := I) x)
    (isLocalDiffeomorphOn_smul_slice (IG := IG) (I := I) x).isLocalHomeomorphOn

private theorem preimage_quotientMk_range_sliceChart (x : M) :
    Quotient.mk (MulAction.orbitRel G M) ⁻¹' range (sliceChart IG G I x) =
      (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • slice IG G I x p.2) ''
        (univ ×ˢ (sliceDomain IG G I x : Set _)) := by
  ext y
  simp only [sliceChart, mem_preimage, mem_range, Subtype.exists, mem_image, Prod.exists,
    mem_prod, mem_univ, true_and]
  refine ⟨fun ⟨s, hs, hsy⟩ ↦ ?_, fun ⟨g, s, hs, hy⟩ ↦
    ⟨s, hs, hy ▸ MulAction.orbitRel.Quotient.quotient_smul_eq.symm⟩⟩
  obtain ⟨g, hg⟩ :=
    MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hsy.symm))
  exact ⟨g, s, hs, hg⟩

private theorem exists_sliceChart_eq (q : MulAction.orbitRel.Quotient G M) :
    ∃ (x : M) (u : sliceDomain IG G I x), sliceChart IG G I x u = q :=
  Quotient.inductionOn q fun x ↦
    ⟨x, ⟨0, zero_mem_sliceDomain x⟩, by simp [sliceChart, slice_zero]⟩

private theorem exists_contMDiffAt_transition_sliceChart (x y : M)
    (u : sliceDomain IG G I x) (v : sliceDomain IG G I y)
    (huv : sliceChart IG G I x u = sliceChart IG G I y v) :
    ∃ T : sliceDomain IG G I x → sliceDomain IG G I y,
      ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ T u ∧
      sliceChart IG G I y ∘ T =ᶠ[𝓝 u] sliceChart IG G I x := by
  have hf : ContMDiffAt 𝓘(ℝ, _) I ∞ (fun u' : sliceDomain IG G I x ↦ slice IG G I x u') u :=
    ((contMDiffOn_slice (IG := IG) (G := G) (I := I) x u u.2).contMDiffAt
      ((sliceDomain IG G I x).isOpen.mem_nhds u.2)).comp u contMDiff_subtype_val.contMDiffAt
  obtain ⟨t, ht, -, hmem⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff
    (sliceDomain IG G I y).isOpen (injOn_smul_slice (IG := IG) (I := I) y)
    (isLocalDiffeomorphOn_smul_slice (IG := IG) (I := I) y) hf v.2 huv.symm
  let := Classical.decPred (· ∈ sliceDomain IG G I y)
  let T : sliceDomain IG G I x → sliceDomain IG G I y :=
    fun u' ↦ if h : t u' ∈ sliceDomain IG G I y then ⟨t u', h⟩ else v
  have hT_val : Subtype.val ∘ T =ᶠ[𝓝 u] t := by
    filter_upwards [hmem] with u' hu'
    have hmem_y : t u' ∈ sliceDomain IG G I y := hu'.1
    simp [T, hmem_y]
  refine ⟨T, (TauCeti.ContMDiffAt.subtypeVal_comp_iff (sliceDomain IG G I y) T u).1
    (ht.congr_of_eventuallyEq hT_val), ?_⟩
  filter_upwards [hT_val, hmem] with u' hTu' hu'
  simp only [comp_apply, sliceChart] at hTu' ⊢
  rw [hTu']
  exact (hu'.2 (t u') hu'.1).2 rfl

end FreeProperQuotient

section QuotientManifold

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners ℝ EG HG)
  (G : Type*) [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- The smooth atlas on the orbit space `MulAction.orbitRel.Quotient G M` of a free proper smooth
Lie group action, glued from transverse Euclidean slice charts of dimension `dim M - dim G`. It
uses the quotient topology and is not registered as a global instance because the models `IG` and
`I` cannot be inferred from the quotient type alone. -/
@[instance_reducible]
def freeProperQuotientChartedSpace :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding
    (FreeProperQuotient.isOpenEmbedding_sliceChart (IG := IG) (G := G) (I := I) (M := M))
    (FreeProperQuotient.exists_sliceChart_eq (IG := IG) (G := G) (I := I) (M := M))

/-- **The orbit space of a free proper smooth Lie group action is a smooth manifold.** -/
theorem isManifold_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding
    (FreeProperQuotient.isOpenEmbedding_sliceChart (IG := IG) (G := G) (I := I) (M := M))
    (FreeProperQuotient.exists_sliceChart_eq (IG := IG) (G := G) (I := I) (M := M))
    (FreeProperQuotient.exists_contMDiffAt_transition_sliceChart
      (IG := IG) (G := G) (I := I) (M := M))

private theorem contMDiffAt_and_surjective_mfderiv_quotientMk (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiffAt I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (Quotient.mk (MulAction.orbitRel G M)) x ∧
      Surjective (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M)) x) := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient IG G I M
  let J := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  set π := Quotient.mk (MulAction.orbitRel G M)
  let U := FreeProperQuotient.sliceDomain IG G I x
  let τ := FreeProperQuotient.slice IG G I x
  let u₀ : U := ⟨0, FreeProperQuotient.zero_mem_sliceDomain x⟩
  let Ψ : U × G → M := fun p ↦ p.2 • τ p.1
  -- `Ψ (u, g) = g • τ u` is a local diffeomorphism at `(0, 1)` sending `(0, 1)` to `x`.
  have hswap : IsLocalDiffeomorphAt (J.prod IG) (IG.prod J) ∞ Prod.swap (u₀, (1 : G)) :=
    (Diffeomorph.prodComm J IG U G ∞).isLocalDiffeomorph (u₀, 1)
  have hinc : IsLocalDiffeomorphAt (IG.prod J) (IG.prod J) ∞
      (Prod.map id (Subtype.val : U → _)) ((1 : G), u₀) :=
    ((Diffeomorph.refl IG G ∞).isLocalDiffeomorph 1).prodMap
      (isLocalDiffeomorph_subtype_val (I := J) (n := ∞) (U := U) u₀)
  have hΨ : IsLocalDiffeomorphAt (J.prod IG) I ∞ Ψ (u₀, 1) :=
    IsLocalDiffeomorphAt.comp
      (hg := FreeProperQuotient.isLocalDiffeomorphOn_smul_slice (IG := IG) (I := I) x
        ⟨(1, 0), mem_univ _, u₀.2⟩)
      (hf := IsLocalDiffeomorphAt.comp (hg := hinc) (hf := hswap))
  have hΨ0 : Ψ (u₀, 1) = x := by simp [Ψ, u₀, τ, FreeProperQuotient.slice_zero]
  -- Composed with `Ψ`, the orbit projection is `Prod.fst` followed by the slice chart embedding.
  have hcomp : π ∘ Ψ = FreeProperQuotient.sliceChart IG G I x ∘ Prod.fst :=
    funext fun _ ↦ MulAction.orbitRel.Quotient.quotient_smul_eq
  have hchart : IsLocalDiffeomorph J J ∞ (FreeProperQuotient.sliceChart IG G I x) :=
    isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
      (FreeProperQuotient.isOpenEmbedding_sliceChart (IG := IG) (G := G) (I := I) (M := M))
      (FreeProperQuotient.exists_sliceChart_eq (IG := IG) (G := G) (I := I) (M := M))
      (FreeProperQuotient.exists_contMDiffAt_transition_sliceChart
        (IG := IG) (G := G) (I := I) (M := M)) x
  have hsub : Manifold.IsSubmersionAtOfComplement EG (J.prod IG) J ∞ (π ∘ Ψ) (u₀, 1) := by
    rw [hcomp]
    exact (hchart u₀).comp_isSubmersionAtOfComplement
      (Manifold.isSubmersionOfComplement_fst.isSubmersionAt (u₀, 1))
  rw [← hΨ0]
  refine ⟨?_, LinearMap.range_eq_top.1 ((hΨ.range_mfderiv_comp (g := π) (by simp)).symm.trans
    (LinearMap.range_eq_top.2 (hsub.surjective_mfderiv (by simp))))⟩
  have hinv0 : hΨ.localInverse (Ψ (u₀, 1)) = (u₀, 1) :=
    hΨ.localInverse_left_inv hΨ.localInverse_mem_target
  refine ((hinv0 ▸ hsub.contMDiffAt).comp (Ψ (u₀, 1))
    hΨ.localInverse_isLocalDiffeomorphAt.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards [hΨ.localInverse_eventuallyEq_right] with y hy
  simp only [comp_apply] at hy ⊢
  rw [hy, id]

/-- The orbit projection of a free proper smooth Lie group action is smooth. -/
theorem contMDiff_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG G I M
  exact fun x ↦ (contMDiffAt_and_surjective_mfderiv_quotientMk IG G I M x).1

/-- **The orbit projection of a free proper smooth Lie group action is a smooth submersion** with
complement the model space `EG` of `G`. -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    Manifold.IsSubmersionOfComplement EG I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient IG G I M
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  refine Manifold.isSubmersionOfComplement_iff.2 fun x ↦ ?_
  have hx := IsCancelSMul.stabilizer_eq_bot (G := G) x
  have hiso := isotropy_fundamental_eq_bot_of_stabilizer_eq_bot (IG := IG) (I := I) hx
  have : FiniteDimensional ℝ (GroupLieAlgebra IG G) :=
    Module.Finite.of_injective ((InfinitesimalAction.fundamental IG G I M).eval x)
      ((InfinitesimalAction.isotropy_eq_bot_iff _ x).1 hiso)
  have : FiniteDimensional ℝ EG := ‹FiniteDimensional ℝ (GroupLieAlgebra IG G)›
  have hle := finrank_le_of_stabilizer_eq_bot (IG := IG) (I := I) hx
  let eF : (Fin (finrank ℝ E - finrank ℝ (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) → ℝ) ≃L[ℝ] EG :=
    (LinearEquiv.ofFinrankEq _ _
      (by rw [Module.finrank_fin_fun, Module.finrank_fin_fun]; omega)).toContinuousLinearEquiv
  exact (Manifold.IsSubmersionAtOfComplement.congr_F eF).mp
    ((contMDiff_quotientMk_freeProperQuotient IG G I M).contMDiffOn
      |>.isSubmersionAtOfComplement_of_surjective_mfderiv isOpen_univ (mem_univ x) (by simp)
        (contMDiffAt_and_surjective_mfderiv_quotientMk IG G I M x).2)

/-- **The orbit projection of a free proper smooth Lie group action is a smooth submersion.** -/
theorem isSubmersion_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    Manifold.IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG G I M
  exact (isSubmersionOfComplement_quotientMk_freeProperQuotient IG G I M).isSubmersion

variable {IG G I M} in
/-- **Vertical tangent spaces of the orbit projection.** At every point `x : M`, the kernel of the
differential of the orbit projection `M → MulAction.orbitRel.Quotient G M` is the orbit tangent
space `(InfinitesimalAction.fundamental IG G I M).orbitTangent x`. -/
theorem ker_mfderiv_quotientMk_freeProperQuotient (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient IG G I M
  set J := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  set π := Quotient.mk (MulAction.orbitRel G M)
  -- Every orbit tangent vector comes from the orbit map `g ↦ g • x`, on which `π` is constant.
  have hle : (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤
      (mfderiv I J π x).ker := by
    intro v hv
    obtain ⟨ξ, rfl⟩ := ((InfinitesimalAction.fundamental IG G I M).mem_orbitTangent_iff x).1 hv
    rw [InfinitesimalAction.fundamental_apply, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    have hπd : MDifferentiableAt I J π x :=
      ((contMDiff_quotientMk_freeProperQuotient IG G I M) x).mdifferentiableAt (by simp)
    have hconst : π ∘ (fun g : G ↦ g • x) = fun _ : G ↦ π x :=
      funext fun _ ↦ MulAction.orbitRel.Quotient.quotient_smul_eq
    refine (congrArg (mfderiv I J π x) (fundamentalVectorField_apply ξ x)).trans
      ((mfderiv_comp_apply_of_eq (1 : G) hπd
        (ContMDiffSMul.mdifferentiableAt_smul_const x 1) (one_smul G x) ξ).symm.trans ?_)
    rw [hconst, mfderiv_const, zero_apply]
  -- Both subspaces have dimension `dim G` by rank-nullity for the surjective differential `dπ_x`.
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hsurj := (contMDiffAt_and_surjective_mfderiv_quotientMk IG G I M x).2
  have hrn := LinearMap.finrank_range_add_finrank_ker (mfderiv I J π x).toLinearMap
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_tangentSpace (I := J),
    finrank_tangentSpace (I := I), Module.finrank_fin_fun] at hrn
  have hdimG := finrank_orbitTangent_fundamental_of_stabilizer_eq_bot (IG := IG) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)
  have hle_dim := finrank_le_of_stabilizer_eq_bot (IG := IG) (I := I)
    (IsCancelSMul.stabilizer_eq_bot (G := G) x)
  rw [hdimG]
  -- `ContinuousLinearMap.ker` is definitionally `LinearMap.ker` of `toLinearMap`, matching `hrn`.
  change finrank ℝ EG = finrank ℝ (LinearMap.ker (mfderiv I J π x).toLinearMap)
  omega

/-- **The quotient manifold theorem.** Let a real Lie group `G` modeled on a Banach space `EG` act
freely, properly, and smoothly on a finite-dimensional smooth boundaryless real manifold `M`. Then
the orbit space `MulAction.orbitRel.Quotient G M`, with its quotient topology, carries a smooth
manifold structure of dimension `dim M - dim G` for which the orbit projection is a smooth
submersion whose vertical tangent space at every `x : M` is the orbit tangent space `𝔤 · x`. -/
theorem exists_freeProperQuotient_isSubmersion :
    ∃ c : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M),
      letI := c
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      Manifold.IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (Quotient.mk (MulAction.orbitRel G M)) ∧
      ∀ x : M,
        (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
          (Quotient.mk (MulAction.orbitRel G M)) x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x :=
  ⟨freeProperQuotientChartedSpace IG G I M,
    isManifold_freeProperQuotient IG G I M,
    isSubmersion_quotientMk_freeProperQuotient IG G I M,
    ker_mfderiv_quotientMk_freeProperQuotient⟩

/-! ### Uniqueness, smooth descent, and functoriality -/

variable {G I M}

/-- **Uniqueness of the smooth atlas on the orbit space.** Any charted-space structure on
`MulAction.orbitRel.Quotient G M` modeled on `Fin (dim M - dim G) → ℝ` for which the orbit
projection is a smooth submersion has the same maximal atlas as
`freeProperQuotientChartedSpace IG G I M`. -/
theorem maximalAtlas_freeProperQuotient_eq
    {c : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M)}
    (hsub : letI := c; Manifold.IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M))) :
    (letI := freeProperQuotientChartedSpace IG G I M;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) =
    (letI := c;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) :=
  Manifold.IsSubmersion.maximalAtlas_eq
    (isSubmersion_quotientMk_freeProperQuotient IG G I M) hsub Quotient.mk_surjective

/-- **Uniqueness of quotient manifolds up to canonical diffeomorphism.** If `π : M → P` is a
surjective smooth submersion onto any smooth manifold `P` whose fibres are the `G`-orbits, then
`MulAction.orbitRel.Quotient G M` is canonically diffeomorphic to `P` via `⟦x⟧ ↦ π x`. -/
def freeProperQuotientDiffeomorph {F HP P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace HP] {J : ModelWithCorners ℝ F HP} [TopologicalSpace P] [ChartedSpace HP P]
    {π : M → P} (hπ : Manifold.IsSubmersion I J ∞ π) (hsurj : Surjective π)
    (hfib : ∀ x y : M, π x = π y ↔ MulAction.orbitRel G M x y) :
    letI := freeProperQuotientChartedSpace IG G I M
    (MulAction.orbitRel.Quotient G M) ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ), J⟯ P :=
  letI := freeProperQuotientChartedSpace IG G I M
  ({ toFun := MulAction.orbitRelQuotientLift π fun g x ↦
       (hfib (g • x) x).2 (MulAction.orbitRel_apply.2 (MulAction.mem_orbit x g))
     invFun z := Quotient.mk (MulAction.orbitRel G M) (surjInv hsurj z)
     left_inv := Quotient.ind fun x ↦ by
       rw [MulAction.orbitRelQuotientLift_mk]
       exact Quotient.sound ((hfib (surjInv hsurj (π x)) x).1 (surjInv_eq hsurj (π x)))
     right_inv z :=
       (MulAction.orbitRelQuotientLift_mk (surjInv hsurj z)).trans
         (surjInv_eq hsurj z) } : MulAction.orbitRel.Quotient G M ≃ P).diffeomorphOfSubmersions
    (isSubmersion_quotientMk_freeProperQuotient IG G I M) Quotient.mk_surjective le_rfl hπ
    MulAction.orbitRelQuotientLift_comp_mk

/-- `freeProperQuotientDiffeomorph` sends the orbit `⟦x⟧` to `π x`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_mk {F HP P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace HP] {J : ModelWithCorners ℝ F HP} [TopologicalSpace P] [ChartedSpace HP P]
    {π : M → P} (hπ : Manifold.IsSubmersion I J ∞ π) (hsurj : Surjective π)
    (hfib : ∀ x y : M, π x = π y ↔ MulAction.orbitRel G M x y) (x : M) :
    freeProperQuotientDiffeomorph IG hπ hsurj hfib (Quotient.mk (MulAction.orbitRel G M) x) =
      π x := by
  simp [freeProperQuotientDiffeomorph]

/-- The inverse of `freeProperQuotientDiffeomorph` sends `π x` back to the orbit `⟦x⟧`. -/
@[simp]
theorem freeProperQuotientDiffeomorph_symm_apply {F HP P : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace HP] {J : ModelWithCorners ℝ F HP} [TopologicalSpace P]
    [ChartedSpace HP P] {π : M → P} (hπ : Manifold.IsSubmersion I J ∞ π) (hsurj : Surjective π)
    (hfib : ∀ x y : M, π x = π y ↔ MulAction.orbitRel G M x y) (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    (freeProperQuotientDiffeomorph IG hπ hsurj hfib).symm (π x) =
      Quotient.mk (MulAction.orbitRel G M) x := by
  let := freeProperQuotientChartedSpace IG G I M
  exact (freeProperQuotientDiffeomorph IG hπ hsurj hfib).toEquiv.symm_apply_eq.2
    (freeProperQuotientDiffeomorph_mk IG hπ hsurj hfib x).symm

/-- For `m ≤ ∞`, the descent of a `G`-invariant map `f : M → N` to the free proper orbit manifold
is `C^m` at the orbit of `x` if and only if `f` is `C^m` at `x`. -/
theorem contMDiffAt_orbitRelQuotientLift_freeProperQuotient_iff
    {F HN N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ F HN} [TopologicalSpace N] [ChartedSpace HN N]
    {m : ℕ∞ω} (hm : m ≤ ∞) {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} {x : M} :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) J m
        (MulAction.orbitRelQuotientLift f hf) (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I J m f x := by
  let := freeProperQuotientChartedSpace IG G I M
  have hsub := (isSubmersion_quotientMk_freeProperQuotient IG G I M).isSubmersionAt x
  rw [← hsub.contMDiffAt_comp_iff hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- **Smooth universal property of free proper quotients.** For `m ≤ ∞`, the descent of a
`G`-invariant map `f : M → N` to the orbit manifold is `C^m` if and only if `f` is `C^m`. -/
theorem contMDiff_orbitRelQuotientLift_freeProperQuotient_iff
    {F HN N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ F HN} [TopologicalSpace N] [ChartedSpace HN N]
    {m : ℕ∞ω} (hm : m ≤ ∞) {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) J m
        (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I J m f := by
  let := freeProperQuotientChartedSpace IG G I M
  rw [← (isSubmersion_quotientMk_freeProperQuotient IG G I M).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- **Immersion criterion for maps descended to a free proper quotient.** The descent of a
`G`-invariant map `f : M → N` into a finite-dimensional boundaryless smooth manifold `N` is a
smooth immersion if and only if `f` is smooth and `ker (df_x) = 𝔤 · x` for every `x : M`. -/
theorem isImmersion_orbitRelQuotientLift_freeProperQuotient_iff
    {F HN N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace HN] {J : ModelWithCorners ℝ F HN} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]
    {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} :
    letI := freeProperQuotientChartedSpace IG G I M
    Manifold.IsImmersion 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) J ∞
        (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I J ∞ f ∧
        ∀ x : M, (mfderiv I J f x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient IG G I M
  rw [(isSubmersion_quotientMk_freeProperQuotient IG G I M).isImmersion_iff_ker_mfderiv_comp
    Quotient.mk_surjective (by simp), MulAction.orbitRelQuotientLift_comp_mk]
  exact and_congr_right' (forall_congr' fun x ↦ by
    rw [ker_mfderiv_quotientMk_freeProperQuotient x])

/-- **Functoriality of free proper quotients.** For `m ≤ ∞`, an equivariant `C^m` map between
manifolds carrying free proper smooth Lie group actions induces a `C^m` map between their orbit
manifolds. -/
theorem contMDiff_orbitRelQuotientMap_freeProperQuotient
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [CompleteSpace EK]
    {HK : Type*} [TopologicalSpace HK] (IK : ModelWithCorners ℝ EK HK)
    {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K] [LieGroup IK ∞ K]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ F HN} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N] [MulAction K N]
    [ContMDiffSMul IK J ∞ K N] [ProperSMul K N] [IsCancelSMul K N]
    {m : ℕ∞ω} (hm : m ≤ ∞) {σ : G → K} {φ : M →ₑ[σ] N} (hφ : ContMDiff I J m φ) :
    letI := freeProperQuotientChartedSpace IG G I M
    letI := freeProperQuotientChartedSpace IK K J N
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ F - finrank ℝ EK) → ℝ) m (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace IG G I M
  let := freeProperQuotientChartedSpace IK K J N
  rw [← (isSubmersion_quotientMk_freeProperQuotient IG G I M).contMDiff_comp_iff
    Quotient.mk_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_quotientMk_freeProperQuotient IK K J N).of_le hm).comp hφ

/-! ### Smooth local equivariant trivializations -/

/-- The orbit trivialization `TauCeti.orbitTrivialization` associated with a smooth equivariant map
`u : π⁻¹(W) → G` is smooth on its source. -/
theorem contMDiffOn_orbitTrivialization_freeProperQuotient
    {W : Set (MulAction.orbitRel.Quotient G M)} (hW : IsOpen W) {u : M → G}
    (hu : ContMDiffOn I IG ∞ u (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W))
    (hu_smul : ∀ (g : G), ∀ y ∈ Quotient.mk (MulAction.orbitRel G M) ⁻¹' W, u (g • y) = g * u y) :
    letI := freeProperQuotientChartedSpace IG G I M
    haveI := topologicalGroup_of_lieGroup IG ∞ (G := G)
    ContMDiffOn I (𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ).prod IG) ∞
      (orbitTrivialization W hW u hu.continuousOn hu_smul)
      (orbitTrivialization W hW u hu.continuousOn hu_smul).source := by
  let := freeProperQuotientChartedSpace IG G I M
  have := topologicalGroup_of_lieGroup IG ∞ (G := G)
  rw [(orbitTrivialization W hW u hu.continuousOn hu_smul).source_eq, orbitTrivialization_baseSet]
  exact ((contMDiff_quotientMk_freeProperQuotient IG G I M).contMDiffOn.prodMk hu).congr
    fun y _ ↦ orbitTrivialization_apply y

/-- The inverse of the orbit trivialization `TauCeti.orbitTrivialization` associated with a smooth
equivariant map `u : π⁻¹(W) → G` is smooth on its target `W ×ˢ univ`. -/
theorem contMDiffOn_orbitTrivialization_symm_freeProperQuotient
    {W : Set (MulAction.orbitRel.Quotient G M)} (hW : IsOpen W) {u : M → G}
    (hu : ContMDiffOn I IG ∞ u (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W))
    (hu_smul : ∀ (g : G), ∀ y ∈ Quotient.mk (MulAction.orbitRel G M) ⁻¹' W, u (g • y) = g * u y) :
    letI := freeProperQuotientChartedSpace IG G I M
    haveI := topologicalGroup_of_lieGroup IG ∞ (G := G)
    ContMDiffOn (𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ).prod IG) I ∞
      (orbitTrivialization W hW u hu.continuousOn hu_smul).toOpenPartialHomeomorph.symm
      (orbitTrivialization W hW u hu.continuousOn hu_smul).target := by
  let := freeProperQuotientChartedSpace IG G I M
  have := topologicalGroup_of_lieGroup IG ∞ (G := G)
  rw [(orbitTrivialization W hW u hu.continuousOn hu_smul).target_eq, orbitTrivialization_baseSet]
  rintro ⟨q, g⟩ ⟨hqW, -⟩
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective q
  -- Choose a smooth local section `s` of the submersion `π` near `⟦y⟧`.
  obtain ⟨V, hV, hyV, s, -, hs, hπs⟩ :=
    ((isSubmersion_quotientMk_freeProperQuotient IG G I M).isSubmersionAt
      y).exists_contMDiffOn_section
  let J := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  have hmem : (W ∩ V) ×ˢ (univ : Set G) ∈ 𝓝 (Quotient.mk (MulAction.orbitRel G M) y, g) :=
    ((hW.inter hV).prod isOpen_univ).mem_nhds ⟨⟨hqW, hyV⟩, mem_univ g⟩
  have hs_at : ContMDiffAt (J.prod IG) I ∞ (fun p : _ × G ↦ s p.1)
      (Quotient.mk (MulAction.orbitRel G M) y, g) :=
    (hs.contMDiffAt (hV.mem_nhds hyV)).comp (Quotient.mk (MulAction.orbitRel G M) y, g)
      contMDiffAt_fst
  have hW_pre : IsOpen (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W) :=
    hW.preimage (contMDiff_quotientMk_freeProperQuotient IG G I M).continuous
  have hsyW : s (Quotient.mk (MulAction.orbitRel G M) y) ∈
      Quotient.mk (MulAction.orbitRel G M) ⁻¹' W := by
    rw [mem_preimage, hπs _ hyV]
    exact hqW
  have hu_at : ContMDiffAt (J.prod IG) IG ∞ (fun p : _ × G ↦ u (s p.1))
      (Quotient.mk (MulAction.orbitRel G M) y, g) :=
    (hu.contMDiffAt (hW_pre.mem_nhds hsyW)).comp (Quotient.mk (MulAction.orbitRel G M) y, g) hs_at
  have hformula : ContMDiffAt (J.prod IG) I ∞
      (fun p : _ × G ↦ (p.2 * (u (s p.1))⁻¹) • s p.1)
      (Quotient.mk (MulAction.orbitRel G M) y, g) :=
    (contMDiffAt_snd.mul hu_at.inv).smul hs_at
  refine (hformula.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hmem] with p hp
  rcases p with ⟨q', g'⟩
  obtain ⟨⟨hq'W, hq'V⟩, -⟩ := hp
  have hsq' : Quotient.mk (MulAction.orbitRel G M) (s q') ∈ W := by simpa [hπs q' hq'V] using hq'W
  conv_lhs => rw [← hπs q' hq'V]
  rw [orbitTrivialization_symm_apply_mk hsq' g']

/-- **Smooth local principal trivializations around every orbit.** Around every point `x : M` of a
free proper smooth Lie group action, there exist an open neighbourhood `W` of the orbit `⟦x⟧` and a
smooth map `u : M → G` on `π⁻¹(W)` with `u x = 1` and `u (g • y) = g * u y` on `π⁻¹(W)` whose orbit
trivialization `TauCeti.orbitTrivialization` is smooth with smooth inverse on the orbit manifold. -/
theorem exists_contMDiffOn_orbitTrivialization_freeProperQuotient (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    haveI := topologicalGroup_of_lieGroup IG ∞ (G := G)
    ∃ (W : Set (MulAction.orbitRel.Quotient G M)) (hW : IsOpen W) (u : M → G)
      (hu : ContMDiffOn I IG ∞ u (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W))
      (hu_smul : ∀ (g : G), ∀ y ∈ Quotient.mk (MulAction.orbitRel G M) ⁻¹' W, u (g • y) = g * u y),
      Quotient.mk (MulAction.orbitRel G M) x ∈ W ∧
      u x = 1 ∧
      ContMDiffOn I (𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ).prod IG) ∞
        (orbitTrivialization W hW u hu.continuousOn hu_smul)
        (orbitTrivialization W hW u hu.continuousOn hu_smul).source ∧
      ContMDiffOn (𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ).prod IG) I ∞
        (orbitTrivialization W hW u hu.continuousOn hu_smul).toOpenPartialHomeomorph.symm
        (orbitTrivialization W hW u hu.continuousOn hu_smul).target := by
  let := freeProperQuotientChartedSpace IG G I M
  have := topologicalGroup_of_lieGroup IG ∞ (G := G)
  let U := FreeProperQuotient.sliceDomain IG G I x
  let τ := FreeProperQuotient.slice IG G I x
  let ψ := FreeProperQuotient.sliceChart IG G I x
  have : Nonempty (G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) := ⟨(1, 0)⟩
  let Φ := (FreeProperQuotient.isLocalDiffeomorphOn_smul_slice (IG := IG) (I := I)
    x).partialDiffeomorphOfInjOn (isOpen_univ.prod U.isOpen)
      (FreeProperQuotient.injOn_smul_slice (IG := IG) (I := I) x)
  have hΦ_src : Φ.source = univ ×ˢ (U : Set _) :=
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source _ _ _
  have hΦ_coe : ⇑Φ = fun p : G × _ ↦ p.1 • τ p.2 :=
    IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn _ _ _
  have hpre : Quotient.mk (MulAction.orbitRel G M) ⁻¹' range ψ = Φ.target :=
    (FreeProperQuotient.preimage_quotientMk_range_sliceChart (IG := IG) (G := G) (I := I) x).trans
      (IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target _ _ _).symm
  let u : M → G := fun y ↦ (Φ.symm y).1
  have hu_apply {p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)} (hp : p ∈ Φ.source) :
      u (Φ p) = p.1 := congrArg Prod.fst (Φ.left_inv hp)
  have h10 : ((1 : G), (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) ∈ Φ.source :=
    hΦ_src ▸ ⟨mem_univ _, FreeProperQuotient.zero_mem_sliceDomain x⟩
  have hΦ10 : Φ (1, 0) = x := by simp [hΦ_coe, τ, FreeProperQuotient.slice_zero]
  have hW : IsOpen (range ψ) := (FreeProperQuotient.isOpenEmbedding_sliceChart x).isOpen_range
  have hu : ContMDiffOn I IG ∞ u (Quotient.mk (MulAction.orbitRel G M) ⁻¹' range ψ) :=
    hpre ▸ contMDiff_fst.comp_contMDiffOn Φ.contMDiffOn_invFun
  have hu_smul (g : G) (y : M) (hy : y ∈ Quotient.mk (MulAction.orbitRel G M) ⁻¹' range ψ) :
      u (g • y) = g * u y := by
    rw [hpre] at hy
    have hsymm_mem : Φ.symm y ∈ univ ×ˢ (U : Set _) := hΦ_src ▸ Φ.map_target hy
    have hright : (Φ.symm y).1 • τ (Φ.symm y).2 = y := by
      have h := Φ.right_inv hy
      -- `Φ.toPartialEquiv` and `Φ.toPartialEquiv.symm` agree definitionally with `Φ` and `Φ.symm`.
      change Φ (Φ.symm y) = y at h
      rwa [hΦ_coe] at h
    have hg_mem : (g * (Φ.symm y).1, (Φ.symm y).2) ∈ Φ.source :=
      hΦ_src ▸ ⟨mem_univ _, hsymm_mem.2⟩
    have hΦg : Φ (g * (Φ.symm y).1, (Φ.symm y).2) = g • y := by
      rw [hΦ_coe]; exact (mul_smul _ _ _).trans (congrArg (g • ·) hright)
    exact hΦg ▸ hu_apply hg_mem
  exact ⟨range ψ, hW, u, hu, hu_smul,
    ⟨⟨0, FreeProperQuotient.zero_mem_sliceDomain x⟩, by
      simp [ψ, FreeProperQuotient.sliceChart, FreeProperQuotient.slice_zero]⟩,
    hΦ10 ▸ hu_apply h10,
    contMDiffOn_orbitTrivialization_freeProperQuotient IG hW hu hu_smul,
    contMDiffOn_orbitTrivialization_symm_freeProperQuotient IG hW hu hu_smul⟩

end QuotientManifold

end TauCeti
