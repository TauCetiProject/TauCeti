/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Period
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Bijection
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.DeckGroup
public import TauCeti.Geometry.Manifold.Topology
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Topology.SeparatedMap
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The period-kernel cover of a closed one-form

The cover associated to the kernel of the period homomorphism is connected and regular. Its deck
group is the actual image of the period homomorphism, with no discreteness or injectivity
assumption. Pulling back the smooth atlas along the covering projection makes the projection a
local diffeomorphism, and the pulled-back form is exact.

The construction uses the subgroup-cover classification and the period exactness criterion.
Our universal-cover action prepends inverse loops; consequently the deck transformation labelled
by the period of a loop is the transformation represented by its inverse.

## References

* M. Farber, *Topology of Closed One-Forms*, Section 1.1.
* A. Hatcher, *Algebraic Topology*, Section 1.3.
-/

public section
noncomputable section

open scoped Manifold ContDiff
open Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- The connected covering of the basepoint component associated to the kernel of the periods.
For a path-connected manifold its projection is surjective onto the entire manifold. -/
abbrev PeriodCover (θ : SmoothForm I M ℝ 1) (x : M) :=
  UniversalCover.SubgroupQuotient x
    ((periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker)

namespace PeriodCover

variable (θ : SmoothForm I M ℝ 1) (x : M)

/-- The endpoint projection of the period-kernel cover. -/
abbrev proj : PeriodCover θ x → M :=
  UniversalCover.subgroupQuotientProj x
    ((periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker)

/-- The period-kernel projection is a covering map. -/
theorem isCoveringMap_proj : IsCoveringMap (proj θ x) := by
  let : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  exact UniversalCover.isCoveringMap_subgroupQuotientProj x _

/-- The lifted smooth atlas on the period-kernel cover. -/
noncomputable instance : ChartedSpace H (PeriodCover θ x) :=
  (isCoveringMap_proj θ x).isLocalHomeomorph.chartedSpaceComap

/-- The atlas pulled back from the base makes the period cover a smooth manifold. -/
instance : IsManifold I ∞ (PeriodCover θ x) :=
  (isCoveringMap_proj θ x).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- Covering spaces of Hausdorff manifolds are Hausdorff. -/
instance : T2Space (PeriodCover θ x) := (isCoveringMap_proj θ x).t2Space

/-- The projection is a smooth local diffeomorphism for the lifted atlas. -/
theorem isLocalDiffeomorph_proj : IsLocalDiffeomorph I I ∞ (proj θ x) :=
  (isCoveringMap_proj θ x).isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap

/-- The period-kernel cover is regular over a path-connected base. -/
theorem isRegular_proj [PreconnectedSpace M] : Deck.IsRegular (proj θ x) := by
  let : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  let : ConnectedSpace M := ⟨⟨x⟩⟩
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  exact (UniversalCover.isRegular_subgroupQuotientProj_iff_normal x _).2 inferInstance

/-- Identify actual deck transformations with actual periods. The inverse in the final factor
compensates for the universal-cover convention of prepending inverse loops. -/
def deckEquiv [PreconnectedSpace M] :
    deck (proj θ x) ≃* (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.range :=
by
  letI : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  letI : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  letI : ConnectedSpace M := ⟨⟨x⟩⟩
  letI : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  exact (UniversalCover.deckSubgroupQuotientProjEquivOfNormal x _).symm |>.trans
    (QuotientGroup.quotientKerEquivRange
      (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight) |>.trans
    (MulEquiv.inv _)

/-- The deck transformation labelled by the period of `g` sends a quotient representative
`e` to the representative `g⁻¹ • e`, hence prepends the loop `g`. -/
-- Run before the period label simplifies to its path integral.
@[simp↓]
theorem deckEquiv_symm_period_apply [PreconnectedSpace M]
    (g : FundamentalGroup M x) (e : UniversalCover x) :
    ((deckEquiv θ x).symm
      ⟨(periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight g,
        ⟨g, rfl⟩⟩).1 (Quotient.mk'' e) = Quotient.mk'' (g⁻¹ • e) := by
  let : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  let : ConnectedSpace M := ⟨⟨x⟩⟩
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  have hd : (deckEquiv θ x).symm
      ⟨(periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight g, ⟨g, rfl⟩⟩ =
      UniversalCover.deckSubgroupQuotientProjEquivOfNormal x
        (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker
        (QuotientGroup.mk g⁻¹) := by
    apply (deckEquiv θ x).injective
    rw [MulEquiv.apply_symm_apply]
    simp only [deckEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    simp only [AddMonoidHom.toMultiplicativeRight_apply_apply, periodHom_apply, toMul_ofMul,
      QuotientGroup.mk_inv, map_inv, QuotientGroup.quotientKerEquivRange_apply_mk,
      MulEquiv.inv_apply, inv_inv]
  rw [hd]
  exact UniversalCover.deckSubgroupQuotientProjEquivOfNormal_mk_apply x _ g⁻¹ e

/-- Pullback of a closed smooth real one-form to its period-kernel cover is exact. -/
theorem mpullback_mem_exactForms (hθ : θ ∈ closedForms I M 1) :
    SmoothForm.mpullback (proj θ x) (isLocalDiffeomorph_proj θ x).contMDiff θ ∈
      exactForms I (PeriodCover θ x) 1 := by
  let : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  let b := UniversalCover.SubgroupQuotient.basepoint x
    (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker
  rw [mpullback_mem_exactForms_one_iff_periodHom_map_eq_zero
    (isLocalDiffeomorph_proj θ x).contMDiff hθ b]
  have transport (y : M) (hy : proj θ x b = y)
      (hz : ∀ γ : FundamentalGroup (PeriodCover θ x) b,
        periodHom (θ : RoughForm I M ℝ 1) y
          (Additive.ofMul (FundamentalGroup.mapOfEq
            ⟨proj θ x, (isCoveringMap_proj θ x).continuous⟩ hy γ)) = 0) :
      ∀ γ : FundamentalGroup (PeriodCover θ x) b,
        periodHom (θ : RoughForm I M ℝ 1) (proj θ x b)
          (Additive.ofMul (FundamentalGroup.map
            ⟨proj θ x, (isCoveringMap_proj θ x).continuous⟩ b γ)) = 0 := by
    subst y
    simpa only [FundamentalGroup.mapOfEq_rfl] using hz
  apply transport x (UniversalCover.subgroupQuotientProj_basepoint x _)
  intro γ
  have hr := UniversalCover.range_mapOfEq_subgroupQuotientProj x
    (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker
  have hg : FundamentalGroup.mapOfEq (x := b)
      ⟨proj θ x, (isCoveringMap_proj θ x).continuous⟩
      (UniversalCover.subgroupQuotientProj_basepoint x _) γ ∈
      (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker :=
    hr.le ⟨γ, rfl⟩
  exact congrArg Multiplicative.toAdd hg

/-- The pulled-back form is the differential of a smooth real function. -/
theorem exists_primitive (hθ : θ ∈ closedForms I M 1) :
    ∃ f : PeriodCover θ x → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      mextDeriv (RoughForm.ofFunction I f) = mpullback I I (proj θ x) θ := by
  have hex := mpullback_mem_exactForms θ x hθ
  rw [exactForms_succ, LinearMap.mem_range] at hex
  obtain ⟨ψ, hψ⟩ := hex
  have hs := ψ.isSmoothForm
  rw [RoughForm.eq_ofFunction (ψ : RoughForm I (PeriodCover θ x) ℝ 0),
    isSmoothForm_ofFunction_iff] at hs
  refine ⟨fun y ↦ (ψ : RoughForm I (PeriodCover θ x) ℝ 0) y 0, hs, ?_⟩
  rw [← RoughForm.eq_ofFunction]
  simpa only [mextDerivₗ_apply, SmoothForm.coe_mpullback] using congrArg Subtype.val hψ

end PeriodCover
end TauCeti
