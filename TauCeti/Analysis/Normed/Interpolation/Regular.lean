/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.Normed.Module.Dual.Adjoint

/-!
# Regular couples, regularization, and the dual couple

A compatible couple `(X₀, X₁)` of normed spaces is *regular* (also called a *density couple*) if
its intersection `X₀ ∩ X₁` is dense in both `X₀` and `X₁`. Regularity is the exact condition under
which restriction to the intersection embeds both continuous duals `X₀*` and `X₁*` injectively into
`(X₀ ∩ X₁)*`, so that `(X₀*, X₁*)` is itself a compatible couple.

Every compatible couple `(X₀, X₁)` admits a *regularization* `(X₀°, X₁°)`: the closures
`CompatibleCouple.fstClosure` and `CompatibleCouple.sndClosure` of `X₀ ∩ X₁` inside `X₀` and `X₁`,
embedded into the same ambient space. Passing to the regularization isometrically preserves the
intersection (`CompatibleCouple.regularizeInterEquiv`), produces a regular couple
(`CompatibleCouple.isRegular_regularize`), and induces a norm-nonincreasing injection on sum spaces
(`CompatibleCouple.regularizeSumMap`).

For a regular couple `C`, precomposition with `C.interFst` and `C.interSnd` embeds `StrongDual 𝕜 X₀`
and `StrongDual 𝕜 X₁` injectively into `StrongDual 𝕜 C.inter`, forming the dual couple `C.dual`.
The continuous duals of the sum and intersection of `C` are then identified isometrically with the
intersection and sum of `C.dual`:

* `CompatibleCouple.sumDualEquivDualInter`: `StrongDual 𝕜 C.SumSpace ≃ₗᵢ[𝕜] (C.dual hC).inter`,
  valid over any nontrivially normed field without completeness hypotheses;
* `CompatibleCouple.dualSumEquivInterDual`: `(C.dual hC).SumSpace ≃ₗᵢ[𝕜] StrongDual 𝕜 C.inter`,
  proved over `RCLike` scalars by extending a functional on `C.inter ≤ X₀ × X₁` without increasing
  its norm via Hahn–Banach and splitting the extension across the `ℓ^∞`-normed product.

Finally, for any nontrivial normed space `E`, the couple `(C₀(ℕ, E), ℓ^∞(ℕ, E))` embedded in
`ℓ^∞(ℕ, E)` (`c0LpInftyCouple`) witnesses that density in one endpoint does not imply regularity:
its intersection surjects onto `C₀(ℕ, E)` yet is closed and proper in `ℓ^∞(ℕ, E)`, so the couple is
not regular and restriction from `(ℓ^∞(ℕ, E))*` to the dual of the intersection is not injective.

## Main declarations

* `TauCeti.CompatibleCouple.IsRegular`: density of `X₀ ∩ X₁` in both `X₀` and `X₁`.
* `TauCeti.CompatibleCouple.fstClosure`, `TauCeti.CompatibleCouple.sndClosure`,
  `TauCeti.CompatibleCouple.regularize`: the endpoint closures `(X₀°, X₁°)` and regularized couple.
* `TauCeti.CompatibleCouple.regularizeInterEquiv`: isometric identification of `(X₀° ∩ X₁°)` with
  `X₀ ∩ X₁`.
* `TauCeti.CompatibleCouple.isRegular_iff_injective_precomp`: over `RCLike` scalars, a couple is
  regular iff both restriction maps `X_j* → (X₀ ∩ X₁)*` are injective.
* `TauCeti.CompatibleCouple.dual`: the dual couple `(X₀*, X₁*)` inside `(X₀ ∩ X₁)*`.
* `TauCeti.CompatibleCouple.sumDualEquivDualInter`: `(X₀ + X₁)* ≃ₗᵢ[𝕜] X₀* ∩ X₁*`.
* `TauCeti.CompatibleCouple.dualSumEquivInterDual`: `X₀* + X₁* ≃ₗᵢ[𝕜] (X₀ ∩ X₁)*`.
* `TauCeti.CompatibleCouple.c0LpInftyCouple`,
  `TauCeti.CompatibleCouple.not_isRegular_c0LpInftyCouple`: the non-regular couple `(c₀, ℓ^∞)`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §2.7 (Theorem 2.7.1) and §4.2.
* M. Cwikel, *Lecture Notes on Duality and Interpolation*, Definition 1.3 and Theorem 1.6.
-/

public noncomputable section

open Filter Set Topology
open scoped ENNReal ZeroAtInfty

namespace TauCeti.CompatibleCouple

section Regularity

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-- Exchanging the endpoints of a compatible couple exchanges the coordinates of its intersection
isometrically. -/
def swapInterEquiv : C.swap.inter ≃ₗᵢ[𝕜] C.inter where
  toFun x := ⟨(x.1.2, x.1.1), (C.mem_inter_iff.2 (C.swap.mem_inter_iff.1 x.2).symm)⟩
  invFun x := ⟨(x.1.2, x.1.1), (C.swap.mem_inter_iff.2 (C.mem_inter_iff.1 x.2).symm)⟩
  left_inv x := by apply Subtype.ext; ext <;> rfl
  right_inv x := by apply Subtype.ext; ext <;> rfl
  map_add' _ _ := by apply Subtype.ext; ext <;> rfl
  map_smul' _ _ := by apply Subtype.ext; ext <;> rfl
  norm_map' x := by
    rw [C.norm_inter, C.swap.norm_inter]
    exact max_comm _ _

theorem interFst_swapInterEquiv (x : C.swap.inter) :
    C.interFst (C.swapInterEquiv x) = C.swap.interSnd x := by
  simp [swapInterEquiv]

theorem interSnd_swapInterEquiv (x : C.swap.inter) :
    C.interSnd (C.swapInterEquiv x) = C.swap.interFst x := by
  simp [swapInterEquiv]

@[simp]
theorem swapInterEquiv_symm : C.swapInterEquiv.symm = C.swap.swapInterEquiv := by
  ext x <;> rfl

/-- A compatible couple is *regular* (or a *density couple*) if its intersection `X₀ ∩ X₁` is
dense in both `X₀` and `X₁`. -/
structure IsRegular : Prop where
  /-- The intersection is dense in the first endpoint space. -/
  denseRange_interFst : DenseRange C.interFst
  /-- The intersection is dense in the second endpoint space. -/
  denseRange_interSnd : DenseRange C.interSnd

variable {C} in
theorem isRegular_iff : C.IsRegular ↔ DenseRange C.interFst ∧ DenseRange C.interSnd :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

variable {C} in
/-- Reversing the endpoints of a regular couple preserves regularity. -/
theorem IsRegular.swap (hC : C.IsRegular) : C.swap.IsRegular where
  denseRange_interFst := by
    have hcomp : ⇑C.swap.interFst = ⇑C.interSnd ∘ ⇑C.swapInterEquiv :=
      funext fun x => (C.interSnd_swapInterEquiv x).symm
    rw [DenseRange, hcomp, Set.range_comp, C.swapInterEquiv.surjective.range_eq, Set.image_univ]
    exact hC.denseRange_interSnd
  denseRange_interSnd := by
    have hcomp : ⇑C.swap.interSnd = ⇑C.interFst ∘ ⇑C.swapInterEquiv :=
      funext fun x => (C.interFst_swapInterEquiv x).symm
    rw [DenseRange, hcomp, Set.range_comp, C.swapInterEquiv.surjective.range_eq, Set.image_univ]
    exact hC.denseRange_interFst

@[simp]
theorem isRegular_swap_iff : C.swap.IsRegular ↔ C.IsRegular :=
  ⟨fun h => h.swap, fun h => h.swap⟩

/-- For the diagonal couple `(X, X)`, both projections from the intersection are surjective, so the
couple is regular. -/
@[simp]
theorem isRegular_refl (𝕜 X : Type*) [NormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    (refl 𝕜 X).IsRegular where
  denseRange_interFst := Function.Surjective.denseRange fun x =>
    ⟨⟨(x, x), (refl 𝕜 X).mem_inter_iff.2 (by simp)⟩, by simp⟩
  denseRange_interSnd := Function.Surjective.denseRange fun x =>
    ⟨⟨(x, x), (refl 𝕜 X).mem_inter_iff.2 (by simp)⟩, by simp⟩

/-! ### Regularization -/

/-- The norm closure `X₀°` of the intersection `X₀ ∩ X₁` inside the first endpoint `X₀`. -/
def fstClosure : Submodule 𝕜 X₀ :=
  C.interFst.range.topologicalClosure

/-- The norm closure `X₁°` of the intersection `X₀ ∩ X₁` inside the second endpoint `X₁`. -/
def sndClosure : Submodule 𝕜 X₁ :=
  C.interSnd.range.topologicalClosure

instance : IsClosed (C.fstClosure : Set X₀) :=
  Submodule.isClosed_topologicalClosure _

instance : IsClosed (C.sndClosure : Set X₁) :=
  Submodule.isClosed_topologicalClosure _

theorem interFst_mem_fstClosure (x : C.inter) : C.interFst x ∈ C.fstClosure :=
  C.interFst.range.le_topologicalClosure ⟨x, rfl⟩

theorem interSnd_mem_sndClosure (x : C.inter) : C.interSnd x ∈ C.sndClosure :=
  C.interSnd.range.le_topologicalClosure ⟨x, rfl⟩

/-- A compatible couple is regular if and only if both endpoint closures equal the whole endpoint
spaces. -/
theorem isRegular_iff_fstClosure_eq_top_and_sndClosure_eq_top :
    C.IsRegular ↔ C.fstClosure = ⊤ ∧ C.sndClosure = ⊤ := by
  rw [isRegular_iff, fstClosure, sndClosure, ← Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.dense_iff_topologicalClosure_eq_top]
  rfl

/-- The *regularization* `(X₀°, X₁°)` of a compatible couple, replacing each endpoint by the norm
closure of the intersection inside it. -/
def regularize : CompatibleCouple 𝕜 C.fstClosure C.sndClosure V where
  embed₀ := C.embed₀.comp C.fstClosure.subtypeL
  embed₁ := C.embed₁.comp C.sndClosure.subtypeL
  embed₀_injective := C.embed₀_injective.comp Subtype.val_injective
  embed₁_injective := C.embed₁_injective.comp Subtype.val_injective

@[simp]
theorem regularize_embed₀ : C.regularize.embed₀ = C.embed₀.comp C.fstClosure.subtypeL := (rfl)

@[simp]
theorem regularize_embed₁ : C.regularize.embed₁ = C.embed₁.comp C.sndClosure.subtypeL := (rfl)

private theorem regularize_inter_to_inter (y : C.regularize.inter) :
    (y.1.1.1, y.1.2.1) ∈ C.inter := by
  have hy := C.regularize.mem_inter_iff.1 y.2
  rw [regularize_embed₀, regularize_embed₁, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.subtypeL_apply] at hy
  exact C.mem_inter_iff.2 hy

private theorem fst_mem_fstClosure (x : C.inter) : x.1.1 ∈ C.fstClosure := by
  rw [← C.interFst_apply x]
  exact C.interFst_mem_fstClosure x

private theorem snd_mem_sndClosure (x : C.inter) : x.1.2 ∈ C.sndClosure := by
  rw [← C.interSnd_apply x]
  exact C.interSnd_mem_sndClosure x

private theorem inter_to_regularize_inter (x : C.inter) :
    ((⟨x.1.1, fst_mem_fstClosure C x⟩ : C.fstClosure),
      (⟨x.1.2, snd_mem_sndClosure C x⟩ : C.sndClosure)) ∈ C.regularize.inter := by
  rw [C.regularize.mem_inter_iff, regularize_embed₀, regularize_embed₁,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.subtypeL_apply]
  exact C.mem_inter_iff.1 x.2

/-- Passing to the regularization does not change the intersection: `(X₀° ∩ X₁°) ≃ₗᵢ[𝕜] X₀ ∩ X₁`. -/
def regularizeInterEquiv : C.regularize.inter ≃ₗᵢ[𝕜] C.inter where
  toFun y := ⟨(y.1.1.1, y.1.2.1), regularize_inter_to_inter C y⟩
  invFun x := ⟨(⟨x.1.1, fst_mem_fstClosure C x⟩, ⟨x.1.2, snd_mem_sndClosure C x⟩),
    inter_to_regularize_inter C x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' y := by
    rw [C.norm_inter, C.regularize.norm_inter]
    rfl

theorem interFst_regularizeInterEquiv (y : C.regularize.inter) :
    C.interFst (C.regularizeInterEquiv y) = (C.regularize.interFst y : X₀) := by
  rw [C.interFst_apply, C.regularize.interFst_apply]
  rfl

theorem interSnd_regularizeInterEquiv (y : C.regularize.inter) :
    C.interSnd (C.regularizeInterEquiv y) = (C.regularize.interSnd y : X₁) := by
  rw [C.interSnd_apply, C.regularize.interSnd_apply]
  rfl

theorem coe_interFst_regularizeInterEquiv_symm (x : C.inter) :
    (C.regularize.interFst (C.regularizeInterEquiv.symm x) : X₀) = C.interFst x := by
  rw [C.regularize.interFst_apply, C.interFst_apply]
  rfl

theorem coe_interSnd_regularizeInterEquiv_symm (x : C.inter) :
    (C.regularize.interSnd (C.regularizeInterEquiv.symm x) : X₁) = C.interSnd x := by
  rw [C.regularize.interSnd_apply, C.interSnd_apply]
  rfl

/-- The regularization of any compatible couple is regular. -/
@[simp]
theorem isRegular_regularize : C.regularize.IsRegular where
  denseRange_interFst := by
    refine C.fstClosure.isEmbedding_subtypeL.isInducing.dense_iff.2 fun z => ?_
    have hz : (z : X₀) ∈ closure (Set.range C.interFst) := by
      have hz' : (z : X₀) ∈ (C.interFst.range.topologicalClosure : Set X₀) := z.2
      rwa [Submodule.topologicalClosure_coe] at hz'
    have hrange : (⇑C.fstClosure.subtypeL ∘ ⇑C.regularize.interFst) =
        ⇑C.interFst ∘ ⇑C.regularizeInterEquiv :=
      funext fun y => (C.interFst_regularizeInterEquiv y).symm
    rwa [← Set.range_comp, hrange, Set.range_comp, C.regularizeInterEquiv.surjective.range_eq,
      Set.image_univ]
  denseRange_interSnd := by
    refine C.sndClosure.isEmbedding_subtypeL.isInducing.dense_iff.2 fun z => ?_
    have hz : (z : X₁) ∈ closure (Set.range C.interSnd) := by
      have hz' : (z : X₁) ∈ (C.interSnd.range.topologicalClosure : Set X₁) := z.2
      rwa [Submodule.topologicalClosure_coe] at hz'
    have hrange : (⇑C.sndClosure.subtypeL ∘ ⇑C.regularize.interSnd) =
        ⇑C.interSnd ∘ ⇑C.regularizeInterEquiv :=
      funext fun y => (C.interSnd_regularizeInterEquiv y).symm
    rwa [← Set.range_comp, hrange, Set.range_comp, C.regularizeInterEquiv.surjective.range_eq,
      Set.image_univ]

section RegularizeSum

variable [ContinuousAdd V]

private theorem regularizeSum_compat (y : C.regularize.inter) :
    C.fstToSum.comp C.fstClosure.subtypeL (C.regularize.interFst y) =
      C.sndToSum.comp C.sndClosure.subtypeL (C.regularize.interSnd y) := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.subtypeL_apply, ← C.interFst_regularizeInterEquiv, ← C.interSnd_regularizeInterEquiv]
  exact C.fstToSum_interFst (C.regularizeInterEquiv y)

/-- The canonical norm-nonincreasing injection from the sum space `X₀° + X₁°` of the regularization
into `X₀ + X₁`. -/
def regularizeSumMap : C.regularize.SumSpace →L[𝕜] C.SumSpace :=
  C.regularize.sumLift (C.fstToSum.comp C.fstClosure.subtypeL)
    (C.sndToSum.comp C.sndClosure.subtypeL) (regularizeSum_compat C)

@[simp]
theorem regularizeSumMap_fstToSum (x₀ : C.fstClosure) :
    C.regularizeSumMap (C.regularize.fstToSum x₀) = C.fstToSum x₀ :=
  C.regularize.sumLift_fstToSum _ _ (regularizeSum_compat C) x₀

@[simp]
theorem regularizeSumMap_sndToSum (x₁ : C.sndClosure) :
    C.regularizeSumMap (C.regularize.sndToSum x₁) = C.sndToSum x₁ :=
  C.regularize.sumLift_sndToSum _ _ (regularizeSum_compat C) x₁

@[simp]
theorem sumSpaceEmbed_regularizeSumMap (u : C.regularize.SumSpace) :
    C.sumSpaceEmbed (C.regularizeSumMap u) = C.regularize.sumSpaceEmbed u := by
  obtain ⟨x₀, x₁, rfl⟩ := C.regularize.exists_fstToSum_add_sndToSum_eq u
  simp

theorem regularizeSumMap_injective : Function.Injective C.regularizeSumMap := fun u v h =>
  C.regularize.sumSpace_ext <| by
    rw [← C.sumSpaceEmbed_regularizeSumMap, h, C.sumSpaceEmbed_regularizeSumMap]

theorem norm_regularizeSumMap_le [T1Space V] (u : C.regularize.SumSpace) :
    ‖C.regularizeSumMap u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨x₀, x₁, rfl, hx⟩ := C.regularize.norm_sumSpace_lt_iff.1 hr
  rw [map_add, regularizeSumMap_fstToSum, regularizeSumMap_sndToSum]
  exact (C.norm_fstToSum_add_sndToSum_le x₀ x₁).trans_lt hx

end RegularizeSum

end Regularity

/-! ### The dual couple and duality of sum and intersection -/

section Dual

private theorem injective_precomp_of_denseRange {𝕜 E F : Type*} [NormedField 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F] {T : E →L[𝕜] F} (hT : DenseRange T) :
    Function.Injective (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :=
  fun f g hfg => DFunLike.coe_injective <|
    hT.equalizer f.continuous g.continuous (funext fun x => DFunLike.congr_fun hfg x)

private theorem injective_precomp_iff_denseRange {𝕜 E F : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) :
    Function.Injective (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) ↔
      DenseRange T := by
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot,
    ContinuousLinearMap.ker_precomp_eq_orthogonalBilin_range,
    ← Submodule.dense_iff_orthogonalBilin_topDualPairing_flip_eq_bot, LinearMap.coe_range,
    ContinuousLinearMap.coe_coe]
  rfl

section NontriviallyNormedField

variable {𝕜 X₀ X₁ V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

-- Supplying the `NormedAddCommGroup`/`NormedSpace`/`AddCommGroup` projections explicitly (all
-- definitionally equal to `ContinuousLinearMap`'s direct instances) ensures that dot-notation
-- projections such as `(C.dual hC).inter` and `(C.dual hC).SumSpace` unify immediately under
-- `module` without unfolding opaque `C.inter`.
/-- **The dual couple of a regular couple.** When `X₀ ∩ X₁` is dense in both `X₀` and `X₁`,
restriction of continuous linear functionals to `X₀ ∩ X₁` embeds `StrongDual 𝕜 X₀` and
`StrongDual 𝕜 X₁` injectively into `StrongDual 𝕜 C.inter`. -/
def dual (hC : C.IsRegular) :
    @CompatibleCouple 𝕜 _ (StrongDual 𝕜 X₀) (StrongDual 𝕜 X₁) (StrongDual 𝕜 C.inter)
      NormedAddCommGroup.toAddCommGroup.toAddCommMonoid NormedSpace.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      NormedAddCommGroup.toAddCommGroup.toAddCommMonoid NormedSpace.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      AddCommGroup.toAddCommMonoid inferInstance inferInstance where
  embed₀ := ContinuousLinearMap.precomp 𝕜 C.interFst
  embed₁ := ContinuousLinearMap.precomp 𝕜 C.interSnd
  embed₀_injective := injective_precomp_of_denseRange hC.denseRange_interFst
  embed₁_injective := injective_precomp_of_denseRange hC.denseRange_interSnd

@[simp]
theorem dual_embed₀ (hC : C.IsRegular) :
    (C.dual hC).embed₀ = ContinuousLinearMap.precomp 𝕜 C.interFst := (rfl)

@[simp]
theorem dual_embed₁ (hC : C.IsRegular) :
    (C.dual hC).embed₁ = ContinuousLinearMap.precomp 𝕜 C.interSnd := (rfl)

section SumDual

private theorem dualInter_compat (hC : C.IsRegular) (f : (C.dual hC).inter) (x : C.inter) :
    ((C.dual hC).interFst f) (C.interFst x) = ((C.dual hC).interSnd f) (C.interSnd x) := by
  rw [(C.dual hC).interFst_apply, (C.dual hC).interSnd_apply]
  simpa [dual_embed₀, dual_embed₁] using DFunLike.congr_fun ((C.dual hC).mem_inter_iff.1 f.2) x

variable [ContinuousAdd V]

private theorem sumDual_mem_inter (hC : C.IsRegular) (Λ : StrongDual 𝕜 C.SumSpace) :
    (Λ.comp C.fstToSum, Λ.comp C.sndToSum) ∈ (C.dual hC).inter := by
  rw [mem_inter_iff, dual_embed₀, dual_embed₁]
  ext x
  exact congrArg Λ (C.fstToSum_interFst x)

private theorem sumDual_left_inv (hC : C.IsRegular) (Λ : StrongDual 𝕜 C.SumSpace) :
    (let g : (C.dual hC).inter :=
      ⟨(Λ.comp C.fstToSum, Λ.comp C.sndToSum), sumDual_mem_inter C hC Λ⟩
    C.sumLift ((C.dual hC).interFst g) ((C.dual hC).interSnd g) (dualInter_compat C hC g)) = Λ :=
  let g : (C.dual hC).inter :=
    ⟨(Λ.comp C.fstToSum, Λ.comp C.sndToSum), sumDual_mem_inter C hC Λ⟩
  (C.sumLift_unique _ _ (dualInter_compat C hC g)
    ((C.dual hC).interFst_apply g).symm ((C.dual hC).interSnd_apply g).symm).symm

private theorem sumDual_right_inv (hC : C.IsRegular) (f : (C.dual hC).inter) :
    (⟨((C.sumLift ((C.dual hC).interFst f) ((C.dual hC).interSnd f)
        (dualInter_compat C hC f)).comp C.fstToSum,
      (C.sumLift ((C.dual hC).interFst f) ((C.dual hC).interSnd f)
        (dualInter_compat C hC f)).comp C.sndToSum),
      sumDual_mem_inter C hC _⟩ : (C.dual hC).inter) = f := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [C.sumLift_comp_fstToSum, (C.dual hC).interFst_apply]
  · dsimp only
    rw [C.sumLift_comp_sndToSum, (C.dual hC).interSnd_apply]

private theorem norm_sumDual_to_dualInter_le (hC : C.IsRegular) (Λ : StrongDual 𝕜 C.SumSpace) :
    ‖(⟨(Λ.comp C.fstToSum, Λ.comp C.sndToSum), sumDual_mem_inter C hC Λ⟩ :
      (C.dual hC).inter)‖ ≤ ‖Λ‖ := by
  rw [norm_inter]
  refine max_le ?_ ?_
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ) fun x₀ =>
      (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (C.norm_fstToSum_le x₀) (norm_nonneg Λ))
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ) fun x₁ =>
      (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (C.norm_sndToSum_le x₁) (norm_nonneg Λ))

private theorem norm_sumLift_dualInter_le [T1Space V] (hC : C.IsRegular) (f : (C.dual hC).inter) :
    ‖C.sumLift ((C.dual hC).interFst f) ((C.dual hC).interSnd f) (dualInter_compat C hC f)‖ ≤
      ‖f‖ := by
  set Λ := C.sumLift ((C.dual hC).interFst f) ((C.dual hC).interSnd f) (dualInter_compat C hC f)
  refine Λ.opNorm_le_bound (norm_nonneg f) fun u => ?_
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  by_cases hf0 : ‖f‖ = 0
  · have hf₀ : (C.dual hC).interFst f = 0 :=
      norm_le_zero_iff.1 (((C.dual hC).norm_interFst_le f).trans_eq hf0)
    have hf₁ : (C.dual hC).interSnd f = 0 :=
      norm_le_zero_iff.1 (((C.dual hC).norm_interSnd_le f).trans_eq hf0)
    obtain ⟨x₀, x₁, rfl⟩ := C.exists_fstToSum_add_sndToSum_eq u
    rw [hf0, zero_mul, zero_add]
    simpa [Λ, hf₀, hf₁] using hε
  have hfpos : 0 < ‖f‖ := (norm_nonneg f).lt_of_ne' hf0
  obtain ⟨x₀, x₁, rfl, hlt⟩ :=
    C.norm_sumSpace_lt_iff.1 (lt_add_of_pos_right ‖u‖ (div_pos hε hfpos))
  have hval : Λ (C.fstToSum x₀ + C.sndToSum x₁) =
      (C.dual hC).interFst f x₀ + (C.dual hC).interSnd f x₁ := by
    simp [Λ]
  calc ‖Λ (C.fstToSum x₀ + C.sndToSum x₁)‖
      ≤ ‖(C.dual hC).interFst f x₀‖ + ‖(C.dual hC).interSnd f x₁‖ := by
        rw [hval]
        exact norm_add_le _ _
    _ ≤ ‖(C.dual hC).interFst f‖ * ‖x₀‖ + ‖(C.dual hC).interSnd f‖ * ‖x₁‖ :=
        add_le_add (((C.dual hC).interFst f).le_opNorm x₀) (((C.dual hC).interSnd f).le_opNorm x₁)
    _ ≤ ‖f‖ * ‖x₀‖ + ‖f‖ * ‖x₁‖ :=
        add_le_add (mul_le_mul_of_nonneg_right ((C.dual hC).norm_interFst_le f) (norm_nonneg x₀))
          (mul_le_mul_of_nonneg_right ((C.dual hC).norm_interSnd_le f) (norm_nonneg x₁))
    _ = ‖f‖ * (‖x₀‖ + ‖x₁‖) := (mul_add _ _ _).symm
    _ < ‖f‖ * (‖C.fstToSum x₀ + C.sndToSum x₁‖ + ε / ‖f‖) :=
        mul_lt_mul_of_pos_left hlt hfpos
    _ = ‖f‖ * ‖C.fstToSum x₀ + C.sndToSum x₁‖ + ε := by
        rw [mul_add, mul_div_cancel₀ _ hfpos.ne']

/-- **Duality of the sum space (Bergh–Löfström, Theorem 2.7.1).** For a regular couple `C`,
restricting a continuous linear functional on `X₀ + X₁` to `X₀` and `X₁` identifies
`StrongDual 𝕜 C.SumSpace` isometrically with the intersection `X₀* ∩ X₁*` of the dual couple. -/
def sumDualEquivDualInter [T1Space V] (hC : C.IsRegular) :
    StrongDual 𝕜 C.SumSpace ≃ₗᵢ[𝕜] (C.dual hC).inter :=
  LinearIsometryEquiv.ofBounds
    { toFun Λ := ⟨(Λ.comp C.fstToSum, Λ.comp C.sndToSum), sumDual_mem_inter C hC Λ⟩
      invFun f := C.sumLift ((C.dual hC).interFst f) ((C.dual hC).interSnd f)
        (dualInter_compat C hC f)
      left_inv := sumDual_left_inv C hC
      right_inv := sumDual_right_inv C hC
      map_add' _ _ := by apply Subtype.ext; ext x <;> rfl
      map_smul' _ _ := by apply Subtype.ext; ext x <;> rfl }
    (norm_sumDual_to_dualInter_le C hC) (norm_sumLift_dualInter_le C hC)

theorem interFst_sumDualEquivDualInter [T1Space V] (hC : C.IsRegular)
    (Λ : StrongDual 𝕜 C.SumSpace) :
    (C.dual hC).interFst (C.sumDualEquivDualInter hC Λ) = Λ.comp C.fstToSum := by
  rw [(C.dual hC).interFst_apply]
  rfl

theorem interSnd_sumDualEquivDualInter [T1Space V] (hC : C.IsRegular)
    (Λ : StrongDual 𝕜 C.SumSpace) :
    (C.dual hC).interSnd (C.sumDualEquivDualInter hC Λ) = Λ.comp C.sndToSum := by
  rw [(C.dual hC).interSnd_apply]
  rfl

@[simp]
theorem sumDualEquivDualInter_symm_fstToSum [T1Space V] (hC : C.IsRegular)
    (f : (C.dual hC).inter) (x₀ : X₀) :
    (C.sumDualEquivDualInter hC).symm f (C.fstToSum x₀) = (C.dual hC).interFst f x₀ :=
  C.sumLift_fstToSum _ _ (dualInter_compat C hC f) x₀

@[simp]
theorem sumDualEquivDualInter_symm_sndToSum [T1Space V] (hC : C.IsRegular)
    (f : (C.dual hC).inter) (x₁ : X₁) :
    (C.sumDualEquivDualInter hC).symm f (C.sndToSum x₁) = (C.dual hC).interSnd f x₁ :=
  C.sumLift_sndToSum _ _ (dualInter_compat C hC f) x₁

end SumDual

end NontriviallyNormedField

/-- A functional `f` of positive norm attains a positive real value exceeding `‖f‖ - δ` at some
unit vector. -/
private theorem exists_unit_apply_eq_ofReal {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : StrongDual 𝕜 E) (hf : 0 < ‖f‖) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : E, ‖y‖ ≤ 1 ∧ ∃ c : ℝ, 0 ≤ c ∧ ‖f‖ - δ < c ∧ f y = (c : 𝕜) := by
  set r := max 0 (‖f‖ - δ / 2)
  have hr₀ : 0 ≤ r := le_max_left _ _
  have hr : r < ‖f‖ := max_lt hf (by linarith)
  obtain ⟨x, hx⟩ := f.exists_mul_lt_of_lt_opNorm hr₀ hr
  have hx0 : 0 < ‖x‖ := by
    by_contra hle
    have hxz : ‖x‖ = 0 := le_antisymm (not_lt.1 hle) (norm_nonneg x)
    have hfx : f x = 0 := by rw [norm_eq_zero.1 hxz, map_zero]
    rw [hxz, mul_zero, hfx, norm_zero] at hx
    exact lt_irrefl 0 hx
  obtain ⟨a, ha, hfa⟩ := RCLike.exists_norm_eq_mul_self (f x)
  refine ⟨((‖x‖⁻¹ : ℝ) : 𝕜) • a • x, ?_, ‖f x‖ / ‖x‖, by positivity, ?_, ?_⟩
  · rw [norm_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hx0), ha, one_mul,
      inv_mul_cancel₀ hx0.ne']
  · have hlt : r < ‖f x‖ / ‖x‖ := (lt_div_iff₀ hx0).2 hx
    have hle : ‖f‖ - δ / 2 ≤ r := le_max_right _ _
    linarith
  · rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hfa, div_eq_inv_mul,
      RCLike.ofReal_mul]

/-- On an `ℓ^∞`-normed product `X₀ × X₁`, the operator norm of a continuous linear functional is
at least the sum of the norms of its restrictions to the two factors. -/
private theorem norm_comp_inl_add_norm_comp_inr_le {𝕜 X₀ X₁ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
    (Ψ : StrongDual 𝕜 (X₀ × X₁)) :
    ‖Ψ.comp (ContinuousLinearMap.inl 𝕜 X₀ X₁)‖ +
      ‖Ψ.comp (ContinuousLinearMap.inr 𝕜 X₀ X₁)‖ ≤ ‖Ψ‖ := by
  set f₀ := Ψ.comp (ContinuousLinearMap.inl 𝕜 X₀ X₁)
  set f₁ := Ψ.comp (ContinuousLinearMap.inr 𝕜 X₀ X₁)
  have hf₀_le : ‖f₀‖ ≤ ‖Ψ‖ :=
    f₀.opNorm_le_bound (norm_nonneg Ψ) fun x₀ => by simpa [f₀] using Ψ.le_opNorm (x₀, 0)
  have hf₁_le : ‖f₁‖ ≤ ‖Ψ‖ :=
    f₁.opNorm_le_bound (norm_nonneg Ψ) fun x₁ => by simpa [f₁] using Ψ.le_opNorm (0, x₁)
  rcases (norm_nonneg f₀).eq_or_lt with h0 | h0
  · linarith
  rcases (norm_nonneg f₁).eq_or_lt with h1 | h1
  · linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨y₀, hy₀, c₀, hc₀, hlt₀, hval₀⟩ := exists_unit_apply_eq_ofReal f₀ h0 (half_pos hε)
  obtain ⟨y₁, hy₁, c₁, hc₁, hlt₁, hval₁⟩ := exists_unit_apply_eq_ofReal f₁ h1 (half_pos hε)
  have hy : ‖(y₀, y₁)‖ ≤ 1 := by simp [Prod.norm_def, hy₀, hy₁]
  have hΨy : Ψ (y₀, y₁) = ((c₀ + c₁ : ℝ) : 𝕜) := by
    have hsplit : ((y₀, y₁) : X₀ × X₁) =
        ContinuousLinearMap.inl 𝕜 X₀ X₁ y₀ + ContinuousLinearMap.inr 𝕜 X₀ X₁ y₁ := by
      ext <;> simp
    have hadd : Ψ (y₀, y₁) = f₀ y₀ + f₁ y₁ := by
      rw [hsplit, map_add]
      rfl
    rw [hadd, hval₀, hval₁, RCLike.ofReal_add]
  have hnorm : c₀ + c₁ ≤ ‖Ψ‖ := by
    calc c₀ + c₁ = ‖((c₀ + c₁ : ℝ) : 𝕜)‖ := by
          rw [RCLike.norm_ofReal, abs_of_nonneg (add_nonneg hc₀ hc₁)]
      _ = ‖Ψ (y₀, y₁)‖ := by rw [hΨy]
      _ ≤ ‖Ψ‖ * ‖(y₀, y₁)‖ := Ψ.le_opNorm _
      _ ≤ ‖Ψ‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg Ψ)
      _ = ‖Ψ‖ := mul_one _
  linarith

section RCLike

variable {𝕜 X₀ X₁ V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-- Over `RCLike` scalars, a compatible couple is regular if and only if both restriction maps
`X₀* → (X₀ ∩ X₁)*` and `X₁* → (X₀ ∩ X₁)*` are injective. -/
theorem isRegular_iff_injective_precomp :
    C.IsRegular ↔
      Function.Injective
          (ContinuousLinearMap.precomp 𝕜 C.interFst : StrongDual 𝕜 X₀ →L[𝕜] StrongDual 𝕜 C.inter) ∧
        Function.Injective
          (ContinuousLinearMap.precomp 𝕜 C.interSnd :
            StrongDual 𝕜 X₁ →L[𝕜] StrongDual 𝕜 C.inter) := by
  rw [isRegular_iff, injective_precomp_iff_denseRange, injective_precomp_iff_denseRange]

private theorem norm_dualSum_sumSpaceEmbed_le (hC : C.IsRegular) (u : (C.dual hC).SumSpace) :
    ‖(C.dual hC).sumSpaceEmbed u‖ ≤ ‖u‖ := by
  refine ((C.dual hC).le_norm_sumSpace_iff).2 fun f₀ f₁ h => ?_
  subst h
  rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  calc ‖((C.dual hC).embed₀ f₀ + (C.dual hC).embed₁ f₁) x‖
      ≤ ‖f₀ (C.interFst x)‖ + ‖f₁ (C.interSnd x)‖ := norm_add_le _ _
    _ ≤ ‖f₀‖ * ‖C.interFst x‖ + ‖f₁‖ * ‖C.interSnd x‖ :=
        add_le_add (f₀.le_opNorm _) (f₁.le_opNorm _)
    _ ≤ ‖f₀‖ * ‖x‖ + ‖f₁‖ * ‖x‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (C.norm_interFst_le x) (norm_nonneg f₀))
          (mul_le_mul_of_nonneg_left (C.norm_interSnd_le x) (norm_nonneg f₁))
    _ = (‖f₀‖ + ‖f₁‖) * ‖x‖ := (add_mul _ _ _).symm

private theorem exists_dualSum_eq_and_norm_le (hC : C.IsRegular) (φ : StrongDual 𝕜 C.inter) :
    ∃ u : (C.dual hC).SumSpace, (C.dual hC).sumSpaceEmbed u = φ ∧ ‖u‖ ≤ ‖φ‖ := by
  obtain ⟨Ψ, hΨ, hnorm⟩ := exists_extension_norm_eq C.inter φ
  set f₀ : StrongDual 𝕜 X₀ := Ψ.comp (ContinuousLinearMap.inl 𝕜 X₀ X₁)
  set f₁ : StrongDual 𝕜 X₁ := Ψ.comp (ContinuousLinearMap.inr 𝕜 X₀ X₁)
  refine ⟨(C.dual hC).fstToSum f₀ + (C.dual hC).sndToSum f₁, ?_, ?_⟩
  · rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum]
    ext x
    have hsplit : (x : X₀ × X₁) =
        ContinuousLinearMap.inl 𝕜 X₀ X₁ (C.interFst x) +
          ContinuousLinearMap.inr 𝕜 X₀ X₁ (C.interSnd x) := by
      ext <;> simp
    calc ((C.dual hC).embed₀ f₀ + (C.dual hC).embed₁ f₁) x
        = f₀ (C.interFst x) + f₁ (C.interSnd x) := rfl
      _ = Ψ (x : X₀ × X₁) := by rw [hsplit, map_add]; rfl
      _ = φ x := hΨ x
  · calc ‖(C.dual hC).fstToSum f₀ + (C.dual hC).sndToSum f₁‖
        ≤ ‖f₀‖ + ‖f₁‖ := (C.dual hC).norm_fstToSum_add_sndToSum_le f₀ f₁
      _ ≤ ‖Ψ‖ := norm_comp_inl_add_norm_comp_inr_le Ψ
      _ = ‖φ‖ := hnorm

private def dualSumLinearEquiv (hC : C.IsRegular) :
    (C.dual hC).SumSpace ≃ₗ[𝕜] StrongDual 𝕜 C.inter :=
  LinearEquiv.ofBijective ((C.dual hC).sumSpaceEmbed.toLinearMap)
    ⟨(C.dual hC).sumSpaceEmbed_injective,
      fun φ => let ⟨u, hu, _⟩ := exists_dualSum_eq_and_norm_le C hC φ; ⟨u, hu⟩⟩

private theorem norm_dualSumLinearEquiv_symm_le (hC : C.IsRegular) (φ : StrongDual 𝕜 C.inter) :
    ‖(dualSumLinearEquiv C hC).symm φ‖ ≤ ‖φ‖ := by
  obtain ⟨u, rfl, hu⟩ := exists_dualSum_eq_and_norm_le C hC φ
  have hsymm : (dualSumLinearEquiv C hC).symm ((C.dual hC).sumSpaceEmbed u) = u :=
    (dualSumLinearEquiv C hC).symm_apply_apply u
  exact (congrArg norm hsymm).le.trans hu

/-- **Duality of the intersection (Bergh–Löfström, Theorem 2.7.1).** For a regular couple `C` over
`RCLike` scalars, the ambient embedding `(X₀* + X₁*) → (X₀ ∩ X₁)*` is a surjective linear isometry:
every continuous linear functional on `X₀ ∩ X₁` decomposes as `f₀|_inter + f₁|_inter` with
`inf (‖f₀‖ + ‖f₁‖) = ‖φ‖`. -/
def dualSumEquivInterDual (hC : C.IsRegular) :
    (C.dual hC).SumSpace ≃ₗᵢ[𝕜] StrongDual 𝕜 C.inter :=
  LinearIsometryEquiv.ofBounds (dualSumLinearEquiv C hC)
    (norm_dualSum_sumSpaceEmbed_le C hC) (norm_dualSumLinearEquiv_symm_le C hC)

@[simp]
theorem dualSumEquivInterDual_apply (hC : C.IsRegular) (u : (C.dual hC).SumSpace) :
    C.dualSumEquivInterDual hC u = (C.dual hC).sumSpaceEmbed u := (rfl)

theorem dualSumEquivInterDual_fstToSum (hC : C.IsRegular) (f₀ : StrongDual 𝕜 X₀) :
    C.dualSumEquivInterDual hC ((C.dual hC).fstToSum f₀) = f₀.comp C.interFst :=
  (C.dual hC).sumSpaceEmbed_fstToSum f₀

theorem dualSumEquivInterDual_sndToSum (hC : C.IsRegular) (f₁ : StrongDual 𝕜 X₁) :
    C.dualSumEquivInterDual hC ((C.dual hC).sndToSum f₁) = f₁.comp C.interSnd :=
  (C.dual hC).sumSpaceEmbed_sndToSum f₁

end RCLike

end Dual

/-! ### Non-regular example: `(c₀(ℕ, E), ℓ^∞(ℕ, E))` -/

section Counterexample

variable (𝕜 E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The compatible couple `(C₀(ℕ, E), ℓ^∞(ℕ, E))` inside `ℓ^∞(ℕ, E)`, whose intersection is
`C₀(ℕ, E)`: dense in the first endpoint and closed in the second. -/
def c0LpInftyCouple :
    CompatibleCouple 𝕜 C₀(ℕ, E) (lp (fun _ : ℕ ↦ E) ∞) (lp (fun _ : ℕ ↦ E) ∞) where
  embed₀ := (ZeroAtInftyContinuousMap.toLpInfty 𝕜).toContinuousLinearMap
  embed₁ := ContinuousLinearMap.id 𝕜 _
  embed₀_injective := (ZeroAtInftyContinuousMap.toLpInfty 𝕜).injective
  embed₁_injective := Function.injective_id

/-- The first projection from the intersection of `(c₀(ℕ, E), ℓ^∞(ℕ, E))` onto `c₀(ℕ, E)` is
surjective. -/
theorem surjective_c0LpInftyCouple_interFst :
    Function.Surjective (c0LpInftyCouple 𝕜 E).interFst := fun f =>
  ⟨⟨(f, ZeroAtInftyContinuousMap.toLpInfty 𝕜 f),
    (c0LpInftyCouple 𝕜 E).mem_inter_iff.2 rfl⟩, by simp⟩

/-- The intersection of `(c₀(ℕ, E), ℓ^∞(ℕ, E))` is dense in the first endpoint `c₀(ℕ, E)`. -/
theorem denseRange_c0LpInftyCouple_interFst :
    DenseRange (c0LpInftyCouple 𝕜 E).interFst :=
  (surjective_c0LpInftyCouple_interFst 𝕜 E).denseRange

/-- When `E` is nontrivial, the intersection of `(c₀(ℕ, E), ℓ^∞(ℕ, E))` is not dense in the second
endpoint `ℓ^∞(ℕ, E)`: any nonzero constant sequence `e` has distance at least `‖e‖ / 2` from every
null sequence. -/
theorem not_denseRange_c0LpInftyCouple_interSnd [Nontrivial E] :
    ¬ DenseRange (c0LpInftyCouple 𝕜 E).interSnd := by
  intro hd
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have he0 : 0 < ‖e‖ := norm_pos_iff.2 he
  let u : lp (fun _ : ℕ ↦ E) ∞ :=
    ⟨fun _ => e, memℓp_infty ⟨‖e‖, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩⟩
  obtain ⟨y, ⟨x, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 (hd u) (‖e‖ / 2) (half_pos he0)
  have hx : ZeroAtInftyContinuousMap.toLpInfty 𝕜 x.1.1 = x.1.2 :=
    (c0LpInftyCouple 𝕜 E).mem_inter_iff.1 x.2
  have hlim : Tendsto (fun n : ℕ => ‖x.1.1 n‖) atTop (𝓝 0) := by
    simpa using (zero_at_infty x.1.1).norm
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (half_pos he0))).exists
  have hcoord :
      ‖(u - (c0LpInftyCouple 𝕜 E).interSnd x) n‖ ≤ ‖u - (c0LpInftyCouple 𝕜 E).interSnd x‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero _ n
  have hsub : ‖e‖ - ‖x.1.1 n‖ ≤ ‖(u - (c0LpInftyCouple 𝕜 E).interSnd x) n‖ := by
    have hval : (u - (c0LpInftyCouple 𝕜 E).interSnd x) n = e - x.1.1 n := by
      rw [lp.coeFn_sub, Pi.sub_apply, interSnd_apply, ← hx,
        ZeroAtInftyContinuousMap.toLpInfty_apply]
    rw [hval]
    exact norm_sub_norm_le e (x.1.1 n)
  rw [dist_eq_norm] at hy
  linarith

/-- When `E` is nontrivial, the couple `(c₀(ℕ, E), ℓ^∞(ℕ, E))` is not regular. -/
theorem not_isRegular_c0LpInftyCouple [Nontrivial E] : ¬ (c0LpInftyCouple 𝕜 E).IsRegular :=
  fun h => not_denseRange_c0LpInftyCouple_interSnd 𝕜 E h.denseRange_interSnd

/-- Over `RCLike` scalars and for nontrivial `E`, restriction from `(ℓ^∞(ℕ, E))*` to the continuous
dual of the intersection of `(c₀(ℕ, E), ℓ^∞(ℕ, E))` is not injective. -/
theorem not_injective_precomp_c0LpInftyCouple_interSnd {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E] :
    ¬ Function.Injective
      (ContinuousLinearMap.precomp 𝕜 (c0LpInftyCouple 𝕜 E).interSnd :
        StrongDual 𝕜 (lp (fun _ : ℕ ↦ E) ∞) →L[𝕜]
          StrongDual 𝕜 (c0LpInftyCouple 𝕜 E).inter) := fun hinj =>
  not_isRegular_c0LpInftyCouple 𝕜 E <|
    ((c0LpInftyCouple 𝕜 E).isRegular_iff_injective_precomp).2
      ⟨injective_precomp_of_denseRange (denseRange_c0LpInftyCouple_interFst 𝕜 E), hinj⟩

end Counterexample

end TauCeti.CompatibleCouple
