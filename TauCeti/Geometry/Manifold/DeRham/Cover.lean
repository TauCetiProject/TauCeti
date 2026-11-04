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
public import TauCeti.Geometry.Manifold.Instances.UniversalCover
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The period-kernel cover of a closed one-form

The cover associated to the kernel of the period homomorphism is connected and regular. Its deck
group is the actual image of the period homomorphism, with no discreteness or injectivity
assumption. Pulling back the smooth atlas along the covering projection makes the projection a
local diffeomorphism, and the pulled-back form is exact.

More generally, the pullback to a subgroup cover is exact precisely when the defining subgroup
lies in the period kernel (`mpullback_mem_exactForms_subgroupQuotient_iff`).

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

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- The connected covering of the basepoint component associated to the kernel of the periods.
For a path-connected manifold its projection is surjective onto the entire manifold. -/
abbrev PeriodCover (θ : SmoothForm I M ℝ 1) (x : M) :=
  UniversalCover.SubgroupQuotient x
    ((periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker)

/-- Pullback to a subgroup cover is exact precisely when the subgroup lies in the period kernel. -/
theorem mpullback_mem_exactForms_subgroupQuotient_iff
    (θ : SmoothForm I M ℝ 1) (x : M) (K : Subgroup (FundamentalGroup M x))
    (hθ : θ ∈ closedForms I M 1) :
    letI : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
    letI : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
    SmoothForm.mpullback (UniversalCover.subgroupQuotientProj x K)
      (UniversalCover.isLocalDiffeomorph_subgroupQuotientProj x K).contMDiff θ ∈
        exactForms I (UniversalCover.SubgroupQuotient x K) 1 ↔
      K ≤ (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  let b := UniversalCover.SubgroupQuotient.basepoint x K
  rw [mpullback_mem_exactForms_one_iff_periodHom_map_eq_zero
    (UniversalCover.isLocalDiffeomorph_subgroupQuotientProj x K).contMDiff hθ b]
  have transport (y : M) (hy : UniversalCover.subgroupQuotientProj x K b = y) :
      (∀ γ : FundamentalGroup (UniversalCover.SubgroupQuotient x K) b,
        periodHom (θ : RoughForm I M ℝ 1) (UniversalCover.subgroupQuotientProj x K b)
          (Additive.ofMul (FundamentalGroup.map
            ⟨UniversalCover.subgroupQuotientProj x K,
              UniversalCover.continuous_subgroupQuotientProj x K⟩ b γ)) = 0) ↔
      ∀ γ : FundamentalGroup (UniversalCover.SubgroupQuotient x K) b,
        periodHom (θ : RoughForm I M ℝ 1) y
          (Additive.ofMul (FundamentalGroup.mapOfEq
            ⟨UniversalCover.subgroupQuotientProj x K,
              UniversalCover.continuous_subgroupQuotientProj x K⟩ hy γ)) = 0 := by
    subst y
    simp only [FundamentalGroup.mapOfEq_rfl]
  rw [transport x (UniversalCover.subgroupQuotientProj_basepoint x K)]
  conv_rhs => rw [← UniversalCover.range_mapOfEq_subgroupQuotientProj x K]
  constructor
  · intro hz g hg
    obtain ⟨γ, rfl⟩ := hg
    rw [MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply, ofAdd_eq_one]
    exact hz γ
  · intro hK γ
    have hg := hK (MonoidHom.mem_range.2 ⟨γ, rfl⟩)
    simpa only [MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply,
      ofAdd_eq_one] using hg

namespace PeriodCover

variable (θ : SmoothForm I M ℝ 1) (x : M)

/-- The endpoint projection of the period-kernel cover. -/
abbrev proj : PeriodCover θ x → M :=
  UniversalCover.subgroupQuotientProj x
    ((periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker)

/-- The period-kernel projection is a covering map. -/
theorem isCoveringMap_proj : IsCoveringMap (proj θ x) := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  exact UniversalCover.isCoveringMap_subgroupQuotientProj x _

/-- The lifted atlas on the period cover. The period form determines the real model `I`,
which instance search cannot recover from an arbitrary subgroup cover alone. -/
noncomputable instance : ChartedSpace H (PeriodCover θ x) :=
  letI : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  letI : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  UniversalCover.instChartedSpaceSubgroupQuotient x _

/-- The atlas pulled back from the base makes the period cover a smooth manifold. -/
instance : IsManifold I ∞ (PeriodCover θ x) := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  exact inferInstanceAs (IsManifold I ∞ (UniversalCover.SubgroupQuotient x _))

/-- Covering spaces of Hausdorff manifolds are Hausdorff. -/
instance : T2Space (PeriodCover θ x) := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  exact inferInstanceAs (T2Space (UniversalCover.SubgroupQuotient x _))

/-- The projection is a smooth local diffeomorphism for the lifted atlas. -/
theorem isLocalDiffeomorph_proj : IsLocalDiffeomorph I I ∞ (proj θ x) := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  exact UniversalCover.isLocalDiffeomorph_subgroupQuotientProj x _

/-- The period-kernel cover is regular over a path-connected base. -/
theorem isRegular_proj [PreconnectedSpace M] : Deck.IsRegular (proj θ x) := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  let : Nonempty M := ⟨x⟩
  let : PathConnectedSpace M := I.pathConnectedSpace M
  exact (UniversalCover.isRegular_subgroupQuotientProj_iff_normal x _).2 inferInstance

/-- Identify actual deck transformations with actual periods. The inverse in the final factor
compensates for the universal-cover convention of prepending inverse loops. -/
def deckEquiv [PreconnectedSpace M] :
    deck (proj θ x) ≃* (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.range :=
  letI : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  letI : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  letI : Nonempty M := ⟨x⟩
  letI : PathConnectedSpace M := I.pathConnectedSpace M
  (UniversalCover.deckSubgroupQuotientProjEquivOfNormal x _).symm |>.trans
    (QuotientGroup.quotientKerEquivRange
      (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight) |>.trans
    (MulEquiv.inv _)

/-- A deck transformation represented by `g` has the inverse of the period label of `g`. -/
@[simp]
theorem deckEquiv_deckSubgroupQuotientProjEquivOfNormal_mk
    [PreconnectedSpace M] (g : FundamentalGroup M x) :
    letI : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
    letI : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
    letI : Nonempty M := ⟨x⟩
    letI : PathConnectedSpace M := I.pathConnectedSpace M
    deckEquiv θ x (UniversalCover.deckSubgroupQuotientProjEquivOfNormal x
      (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker (QuotientGroup.mk g)) =
      ((periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.rangeRestrict g)⁻¹ := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  let : Nonempty M := ⟨x⟩
  let : PathConnectedSpace M := I.pathConnectedSpace M
  simp only [deckEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    QuotientGroup.quotientKerEquivRange_apply_mk, MulEquiv.inv_apply]
  apply Subtype.ext
  simp only [Subgroup.coe_inv, MonoidHom.coe_rangeRestrict]

/-- The deck transformation labelled by the period of `g` sends a quotient representative
`e` to the representative `g⁻¹ • e`, hence prepends the loop `g`. -/
theorem deckEquiv_symm_period_apply [PreconnectedSpace M]
    (g : FundamentalGroup M x) (e : UniversalCover x) :
    ((deckEquiv θ x).symm
      ⟨(periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight g,
        ⟨g, rfl⟩⟩).1 (Quotient.mk'' e) = Quotient.mk'' (g⁻¹ • e) := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  let : Nonempty M := ⟨x⟩
  let : PathConnectedSpace M := I.pathConnectedSpace M
  have hd : (deckEquiv θ x).symm
      ⟨(periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight g, ⟨g, rfl⟩⟩ =
      UniversalCover.deckSubgroupQuotientProjEquivOfNormal x
        (periodHom (θ : RoughForm I M ℝ 1) x).toMultiplicativeRight.ker
        (QuotientGroup.mk g⁻¹) := by
    apply (deckEquiv θ x).injective
    rw [MulEquiv.apply_symm_apply]
    rw [deckEquiv_deckSubgroupQuotientProjEquivOfNormal_mk]
    apply Subtype.ext
    simp only [MonoidHom.coe_rangeRestrict, map_inv, inv_inv]
  rw [hd]
  exact UniversalCover.deckSubgroupQuotientProjEquivOfNormal_mk_apply x _ g⁻¹ e

/-- Pullback of a closed smooth real one-form to its period-kernel cover is exact. -/
theorem mpullback_mem_exactForms (hθ : θ ∈ closedForms I M 1) :
    SmoothForm.mpullback (proj θ x) (isLocalDiffeomorph_proj θ x).contMDiff θ ∈
      exactForms I (PeriodCover θ x) 1 := by
  let : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  exact (mpullback_mem_exactForms_subgroupQuotient_iff θ x _ hθ).2 le_rfl

/-- The pulled-back form is the differential of a smooth real function. -/
theorem exists_primitive (hθ : θ ∈ closedForms I M 1) :
    ∃ f : PeriodCover θ x → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      mextDeriv (RoughForm.ofFunction I f) = mpullback I I (proj θ x) θ := by
  simpa only [SmoothForm.coe_mpullback] using
    exists_contMDiff_mextDeriv_eq_of_mem_exactForms I (mpullback_mem_exactForms θ x hθ)

end PeriodCover
end TauCeti
