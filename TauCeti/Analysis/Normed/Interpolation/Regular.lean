/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Module.Dual.Adjoint
import TauCeti.Analysis.Normed.Module.Dual.Basic

/-!
# Regular couples, regularization, and the dual couple

A compatible couple `(X₀, X₁)` of normed spaces is *regular* (a *density couple*) if `X₀ ∩ X₁` is
dense in both `X₀` and `X₁`, making restriction to `X₀ ∩ X₁` embed `X₀*` and `X₁*` injectively into
`(X₀ ∩ X₁)*` (`CompatibleCouple.dual`).

Every couple admits a *regularization* `(X₀°, X₁°)` (`regularize`) via the closures `fstClosure` and
`sndClosure` of `X₀ ∩ X₁` in `X₀` and `X₁`, with `regularizeInterEquiv`, `isRegular_regularize`, and
`regularizeSumMap`. For a regular couple `C`, `sumDualEquivDualInter` identifies
`StrongDual 𝕜 C.SumSpace` with `(C.dual hC).inter` and `dualSumEquivInterDual` identifies
`(C.dual hC).SumSpace` with `StrongDual 𝕜 C.inter` over `RCLike`. See
`TauCeti.Analysis.Normed.Interpolation.C0LpInfty` for a one-sided dense non-regular counterexample.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §2.7 (Theorem 2.7.1) and §4.2.
* M. Cwikel, *Lecture Notes on Duality and Interpolation*, Definition 1.3 and Theorem 1.6.
-/

public noncomputable section

open Filter Set Topology

namespace TauCeti.CompatibleCouple

section Regularity

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] (C : CompatibleCouple 𝕜 X₀ X₁ V)

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
    rw [DenseRange, ← C.interSwap.surjective.range_comp,
      show ⇑C.swap.interFst ∘ ⇑C.interSwap = ⇑C.interSnd from funext C.interFst_interSwap]
    exact hC.denseRange_interSnd
  denseRange_interSnd := by
    rw [DenseRange, ← C.interSwap.surjective.range_comp,
      show ⇑C.swap.interSnd ∘ ⇑C.interSwap = ⇑C.interFst from funext C.interSnd_interSwap]
    exact hC.denseRange_interFst

@[simp] theorem isRegular_swap_iff : C.swap.IsRegular ↔ C.IsRegular :=
  ⟨IsRegular.swap, IsRegular.swap⟩

/-- For the diagonal couple `(X, X)`, both projections from the intersection are surjective, so the
couple is regular. -/
@[simp] theorem isRegular_refl (𝕜 X : Type*) [NormedField 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] : (refl 𝕜 X).IsRegular where
  denseRange_interFst := Function.Surjective.denseRange fun x =>
    ⟨⟨(x, x), (refl 𝕜 X).mem_inter_iff.2 (by simp)⟩, by simp⟩
  denseRange_interSnd := Function.Surjective.denseRange fun x =>
    ⟨⟨(x, x), (refl 𝕜 X).mem_inter_iff.2 (by simp)⟩, by simp⟩

/-! ### Regularization -/

/-- The norm closure `X₀°` of the intersection `X₀ ∩ X₁` inside the first endpoint `X₀`. -/
def fstClosure : Submodule 𝕜 X₀ := C.interFst.range.topologicalClosure
/-- The norm closure `X₁°` of the intersection `X₀ ∩ X₁` inside the second endpoint `X₁`. -/
def sndClosure : Submodule 𝕜 X₁ := C.interSnd.range.topologicalClosure

theorem fstClosure_def : C.fstClosure = C.interFst.range.topologicalClosure := (rfl)
theorem sndClosure_def : C.sndClosure = C.interSnd.range.topologicalClosure := (rfl)

instance : IsClosed (C.fstClosure : Set X₀) := Submodule.isClosed_topologicalClosure _
instance : IsClosed (C.sndClosure : Set X₁) := Submodule.isClosed_topologicalClosure _

@[simp] theorem coe_fstClosure : (C.fstClosure : Set X₀) = closure (Set.range C.interFst) := by
  rw [fstClosure_def, Submodule.topologicalClosure_coe, LinearMap.coe_range,
    ContinuousLinearMap.coe_coe]
@[simp] theorem coe_sndClosure : (C.sndClosure : Set X₁) = closure (Set.range C.interSnd) := by
  rw [sndClosure_def, Submodule.topologicalClosure_coe, LinearMap.coe_range,
    ContinuousLinearMap.coe_coe]
theorem mem_fstClosure_iff {x : X₀} : x ∈ C.fstClosure ↔ x ∈ closure (Set.range C.interFst) := by
  rw [← SetLike.mem_coe, C.coe_fstClosure]
theorem mem_sndClosure_iff {x : X₁} : x ∈ C.sndClosure ↔ x ∈ closure (Set.range C.interSnd) := by
  rw [← SetLike.mem_coe, C.coe_sndClosure]
theorem fstClosure_le {S : Submodule 𝕜 X₀} (hS : Set.range C.interFst ⊆ S)
    (hc : IsClosed (S : Set X₀)) : C.fstClosure ≤ S :=
  C.interFst.range.topologicalClosure_minimal (fun _ hx => hS hx) hc
theorem sndClosure_le {S : Submodule 𝕜 X₁} (hS : Set.range C.interSnd ⊆ S)
    (hc : IsClosed (S : Set X₁)) : C.sndClosure ≤ S :=
  C.interSnd.range.topologicalClosure_minimal (fun _ hx => hS hx) hc
theorem interFst_mem_fstClosure (x : C.inter) : C.interFst x ∈ C.fstClosure :=
  C.interFst.range.le_topologicalClosure ⟨x, rfl⟩
theorem interSnd_mem_sndClosure (x : C.inter) : C.interSnd x ∈ C.sndClosure :=
  C.interSnd.range.le_topologicalClosure ⟨x, rfl⟩

/-- A compatible couple is regular if and only if both endpoint closures equal `⊤`. -/
theorem isRegular_iff_fstClosure_eq_top_and_sndClosure_eq_top :
    C.IsRegular ↔ C.fstClosure = ⊤ ∧ C.sndClosure = ⊤ := by
  rw [isRegular_iff, fstClosure, sndClosure, ← Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.dense_iff_topologicalClosure_eq_top]; rfl

/-- The *regularization* `(X₀°, X₁°)` of a compatible couple, replacing each endpoint by the norm
closure of the intersection inside it. -/
def regularize : CompatibleCouple 𝕜 C.fstClosure C.sndClosure V where
  embed₀ := C.embed₀.comp C.fstClosure.subtypeL
  embed₁ := C.embed₁.comp C.sndClosure.subtypeL
  embed₀_injective := C.embed₀_injective.comp Subtype.val_injective
  embed₁_injective := C.embed₁_injective.comp Subtype.val_injective

@[simp] theorem regularize_embed₀ : C.regularize.embed₀ = C.embed₀.comp C.fstClosure.subtypeL :=
  (rfl)
@[simp] theorem regularize_embed₁ : C.regularize.embed₁ = C.embed₁.comp C.sndClosure.subtypeL :=
  (rfl)

/-- Passing to the regularization does not change the intersection: `(X₀° ∩ X₁°) ≃ₗᵢ[𝕜] X₀ ∩ X₁`. -/
def regularizeInterEquiv : C.regularize.inter ≃ₗᵢ[𝕜] C.inter where
  toFun y := ⟨(y.1.1.1, y.1.2.1), by simpa [C.mem_inter_iff] using C.regularize.mem_inter_iff.1 y.2⟩
  invFun x := ⟨(⟨x.1.1, C.interFst_apply x ▸ C.interFst_mem_fstClosure x⟩,
    ⟨x.1.2, C.interSnd_apply x ▸ C.interSnd_mem_sndClosure x⟩),
    by simpa [C.regularize.mem_inter_iff] using C.mem_inter_iff.1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := by rw [C.norm_inter, C.regularize.norm_inter]; rfl

@[simp] theorem coe_regularizeInterEquiv_fst (y : C.regularize.inter) :
    (C.regularizeInterEquiv y : X₀ × X₁).1 = (y : C.fstClosure × C.sndClosure).1 := (rfl)
@[simp] theorem coe_regularizeInterEquiv_snd (y : C.regularize.inter) :
    (C.regularizeInterEquiv y : X₀ × X₁).2 = (y : C.fstClosure × C.sndClosure).2 := (rfl)
@[simp] theorem coe_regularizeInterEquiv_symm_fst (x : C.inter) :
    ((C.regularizeInterEquiv.symm x : C.fstClosure × C.sndClosure).1 : X₀) = (x : X₀ × X₁).1 :=
  (rfl)
@[simp] theorem coe_regularizeInterEquiv_symm_snd (x : C.inter) :
    ((C.regularizeInterEquiv.symm x : C.fstClosure × C.sndClosure).2 : X₁) = (x : X₀ × X₁).2 :=
  (rfl)
theorem interFst_regularizeInterEquiv (y : C.regularize.inter) :
    C.interFst (C.regularizeInterEquiv y) = (C.regularize.interFst y : X₀) := by simp
theorem interSnd_regularizeInterEquiv (y : C.regularize.inter) :
    C.interSnd (C.regularizeInterEquiv y) = (C.regularize.interSnd y : X₁) := by simp
theorem coe_interFst_regularizeInterEquiv_symm (x : C.inter) :
    (C.regularize.interFst (C.regularizeInterEquiv.symm x) : X₀) = C.interFst x := by simp
theorem coe_interSnd_regularizeInterEquiv_symm (x : C.inter) :
    (C.regularize.interSnd (C.regularizeInterEquiv.symm x) : X₁) = C.interSnd x := by simp

/-- The regularization of any compatible couple is regular. -/
@[simp] theorem isRegular_regularize : C.regularize.IsRegular where
  denseRange_interFst := C.fstClosure.isEmbedding_subtypeL.isInducing.dense_iff.2 fun z => by
    rw [← Set.range_comp, show ⇑C.fstClosure.subtypeL ∘ ⇑C.regularize.interFst =
      ⇑C.interFst ∘ ⇑C.regularizeInterEquiv from funext fun y =>
        (C.interFst_regularizeInterEquiv y).symm,
      Set.range_comp, C.regularizeInterEquiv.surjective.range_eq, Set.image_univ]
    exact Submodule.topologicalClosure_coe C.interFst.range ▸ z.2
  denseRange_interSnd := C.sndClosure.isEmbedding_subtypeL.isInducing.dense_iff.2 fun z => by
    rw [← Set.range_comp, show ⇑C.sndClosure.subtypeL ∘ ⇑C.regularize.interSnd =
      ⇑C.interSnd ∘ ⇑C.regularizeInterEquiv from funext fun y =>
        (C.interSnd_regularizeInterEquiv y).symm,
      Set.range_comp, C.regularizeInterEquiv.surjective.range_eq, Set.image_univ]
    exact Submodule.topologicalClosure_coe C.interSnd.range ▸ z.2

section RegularizeSum

variable [ContinuousAdd V]

theorem regularizeSum_compat (y : C.regularize.inter) :
    C.fstToSum (C.fstClosure.subtypeL (C.regularize.interFst y)) =
      C.sndToSum (C.sndClosure.subtypeL (C.regularize.interSnd y)) := by
  rw [Submodule.subtypeL_apply, Submodule.subtypeL_apply, ← C.interFst_regularizeInterEquiv,
    ← C.interSnd_regularizeInterEquiv]
  exact C.fstToSum_interFst (C.regularizeInterEquiv y)

/-- The canonical norm-nonincreasing injection from `X₀° + X₁°` into `X₀ + X₁`. -/
def regularizeSumMap : C.regularize.SumSpace →L[𝕜] C.SumSpace :=
  C.regularize.sumLift (C.fstToSum.comp C.fstClosure.subtypeL)
    (C.sndToSum.comp C.sndClosure.subtypeL) C.regularizeSum_compat

theorem regularizeSumMap_eq_sumLift : C.regularizeSumMap =
    C.regularize.sumLift (C.fstToSum.comp C.fstClosure.subtypeL)
      (C.sndToSum.comp C.sndClosure.subtypeL) C.regularizeSum_compat := (rfl)
@[simp] theorem regularizeSumMap_fstToSum (x₀ : C.fstClosure) :
    C.regularizeSumMap (C.regularize.fstToSum x₀) = C.fstToSum x₀ :=
  C.regularize.sumLift_fstToSum _ _ C.regularizeSum_compat x₀
@[simp] theorem regularizeSumMap_sndToSum (x₁ : C.sndClosure) :
    C.regularizeSumMap (C.regularize.sndToSum x₁) = C.sndToSum x₁ :=
  C.regularize.sumLift_sndToSum _ _ C.regularizeSum_compat x₁
@[simp] theorem sumSpaceEmbed_regularizeSumMap (u : C.regularize.SumSpace) :
    C.sumSpaceEmbed (C.regularizeSumMap u) = C.regularize.sumSpaceEmbed u := by
  obtain ⟨x₀, x₁, rfl⟩ := C.regularize.exists_fstToSum_add_sndToSum_eq u; simp
theorem regularizeSumMap_injective : Function.Injective C.regularizeSumMap := fun _ _ h =>
  C.regularize.sumSpace_ext <| by
    rw [← C.sumSpaceEmbed_regularizeSumMap, h, C.sumSpaceEmbed_regularizeSumMap]
theorem norm_regularizeSumMap_le (u : C.regularize.SumSpace) : ‖C.regularizeSumMap u‖ ≤ ‖u‖ :=
  le_of_forall_gt fun _ hr => by
    obtain ⟨x₀, x₁, rfl, hx⟩ := C.regularize.norm_sumSpace_lt_iff.1 hr
    simpa using (C.norm_fstToSum_add_sndToSum_le x₀ x₁).trans_lt hx

end RegularizeSum

end Regularity

/-! ### The dual couple and duality of sum and intersection -/

section Dual

section NontriviallyNormedField

variable {𝕜 X₀ X₁ V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] (C : CompatibleCouple 𝕜 X₀ X₁ V)

-- Explicit projections (all defeq to `ContinuousLinearMap`'s direct instances) let `(C.dual hC)`
-- dot-notation unify immediately under `module` without unfolding opaque `C.inter`.
/-- **The dual couple of a regular couple.** When `X₀ ∩ X₁` is dense in both `X₀` and `X₁`,
restriction to `X₀ ∩ X₁` embeds `StrongDual 𝕜 X₀` and `StrongDual 𝕜 X₁` injectively into
`StrongDual 𝕜 C.inter`. -/
def dual (hC : C.IsRegular) :
    @CompatibleCouple 𝕜 _ (StrongDual 𝕜 X₀) (StrongDual 𝕜 X₁) (StrongDual 𝕜 C.inter)
      NormedAddCommGroup.toAddCommGroup.toAddCommMonoid NormedSpace.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      NormedAddCommGroup.toAddCommGroup.toAddCommMonoid NormedSpace.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      AddCommGroup.toAddCommMonoid inferInstance inferInstance where
  embed₀ := ContinuousLinearMap.precomp 𝕜 C.interFst
  embed₁ := ContinuousLinearMap.precomp 𝕜 C.interSnd
  embed₀_injective := ContinuousLinearMap.injective_precomp_of_denseRange hC.denseRange_interFst
  embed₁_injective := ContinuousLinearMap.injective_precomp_of_denseRange hC.denseRange_interSnd

@[simp] theorem dual_embed₀ (hC : C.IsRegular) :
    (C.dual hC).embed₀ = ContinuousLinearMap.precomp 𝕜 C.interFst := (rfl)
@[simp] theorem dual_embed₁ (hC : C.IsRegular) :
    (C.dual hC).embed₁ = ContinuousLinearMap.precomp 𝕜 C.interSnd := (rfl)

section SumDual

private theorem dualInter_compat (hC : C.IsRegular) (f : (C.dual hC).inter) (x : C.inter) :
    ((C.dual hC).interFst f) (C.interFst x) = ((C.dual hC).interSnd f) (C.interSnd x) := by
  rw [(C.dual hC).interFst_apply, (C.dual hC).interSnd_apply]
  simpa [dual_embed₀, dual_embed₁] using DFunLike.congr_fun ((C.dual hC).mem_inter_iff.1 f.2) x

variable [ContinuousAdd V]

private theorem sumDual_mem_inter (hC : C.IsRegular) (Λ : StrongDual 𝕜 C.SumSpace) :
    (Λ.comp C.fstToSum, Λ.comp C.sndToSum) ∈ (C.dual hC).inter := by
  rw [mem_inter_iff, dual_embed₀, dual_embed₁]; ext x; exact congrArg Λ (C.fstToSum_interFst x)
private theorem norm_sumLift_dualInter_le (hC : C.IsRegular) (f : (C.dual hC).inter) :
    ‖C.sumLift ((C.dual hC).interFst f) ((C.dual hC).interSnd f) (dualInter_compat C hC f)‖ ≤
      ‖f‖ := by
  set Λ := C.sumLift ((C.dual hC).interFst f) ((C.dual hC).interSnd f) (dualInter_compat C hC f)
  refine Λ.opNorm_le_bound (norm_nonneg f) fun u => le_of_forall_pos_lt_add fun ε hε => ?_
  by_cases hf0 : ‖f‖ = 0
  · have hf₀ := norm_le_zero_iff.1 (((C.dual hC).norm_interFst_le f).trans_eq hf0)
    have hf₁ := norm_le_zero_iff.1 (((C.dual hC).norm_interSnd_le f).trans_eq hf0)
    obtain ⟨x₀, x₁, rfl⟩ := C.exists_fstToSum_add_sndToSum_eq u
    simpa [Λ, hf0, hf₀, hf₁] using hε
  have hfpos : 0 < ‖f‖ := (norm_nonneg f).lt_of_ne' hf0
  obtain ⟨x₀, x₁, rfl, hlt⟩ :=
    C.norm_sumSpace_lt_iff.1 (lt_add_of_pos_right ‖u‖ (div_pos hε hfpos))
  calc ‖Λ (C.fstToSum x₀ + C.sndToSum x₁)‖
      ≤ ‖(C.dual hC).interFst f x₀‖ + ‖(C.dual hC).interSnd f x₁‖ := by
        simpa [Λ] using norm_add_le ((C.dual hC).interFst f x₀) ((C.dual hC).interSnd f x₁)
    _ ≤ ‖(C.dual hC).interFst f‖ * ‖x₀‖ + ‖(C.dual hC).interSnd f‖ * ‖x₁‖ :=
        add_le_add (((C.dual hC).interFst f).le_opNorm x₀) (((C.dual hC).interSnd f).le_opNorm x₁)
    _ ≤ ‖f‖ * (‖x₀‖ + ‖x₁‖) := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right ((C.dual hC).norm_interFst_le f)
            (norm_nonneg x₀))
          (mul_le_mul_of_nonneg_right ((C.dual hC).norm_interSnd_le f) (norm_nonneg x₁))
    _ < ‖f‖ * (‖C.fstToSum x₀ + C.sndToSum x₁‖ + ε / ‖f‖) := mul_lt_mul_of_pos_left hlt hfpos
    _ = ‖f‖ * ‖C.fstToSum x₀ + C.sndToSum x₁‖ + ε := by rw [mul_add, mul_div_cancel₀ _ hfpos.ne']

/-- **Duality of the sum space (Bergh–Löfström, Theorem 2.7.1).** For a regular couple `C`,
restricting a continuous linear functional on `X₀ + X₁` to `X₀` and `X₁` identifies
`StrongDual 𝕜 C.SumSpace` isometrically with `X₀* ∩ X₁*`. -/
def sumDualEquivDualInter (hC : C.IsRegular) :
    StrongDual 𝕜 C.SumSpace ≃ₗᵢ[𝕜] (C.dual hC).inter where
  toFun Λ := ⟨(Λ.comp C.fstToSum, Λ.comp C.sndToSum), sumDual_mem_inter C hC Λ⟩
  invFun f := C.sumLift ((C.dual hC).interFst f) ((C.dual hC).interSnd f) (dualInter_compat C hC f)
  left_inv _ := (C.sumLift_unique _ _ _ (by simp) (by simp)).symm
  right_inv _ := Subtype.ext <| Prod.ext
    (by dsimp only; rw [C.sumLift_comp_fstToSum, (C.dual hC).interFst_apply])
    (by dsimp only; rw [C.sumLift_comp_sndToSum, (C.dual hC).interSnd_apply])
  map_add' _ _ := by apply Subtype.ext; ext x <;> rfl
  map_smul' _ _ := by apply Subtype.ext; ext x <;> rfl
  norm_map' Λ := by
    rw [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    set f : (C.dual hC).inter := ⟨(Λ.comp C.fstToSum, Λ.comp C.sndToSum), sumDual_mem_inter C hC Λ⟩
    refine le_antisymm (by
      rw [norm_inter]; exact max_le
        (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ) fun x₀ =>
          (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (C.norm_fstToSum_le x₀) (norm_nonneg Λ)))
        (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ) fun x₁ =>
          (Λ.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (C.norm_sndToSum_le x₁) (norm_nonneg Λ)))) ?_
    have hΛ : Λ = C.sumLift ((C.dual hC).interFst f) ((C.dual hC).interSnd f)
        (dualInter_compat C hC f) :=
      C.sumLift_unique _ _ _ ((C.dual hC).interFst_apply f).symm ((C.dual hC).interSnd_apply f).symm
    exact (congrArg norm hΛ).le.trans (norm_sumLift_dualInter_le C hC f)

@[simp] theorem coe_sumDualEquivDualInter_fst (hC : C.IsRegular) (Λ : StrongDual 𝕜 C.SumSpace) :
    (C.sumDualEquivDualInter hC Λ : StrongDual 𝕜 X₀ × StrongDual 𝕜 X₁).1 = Λ.comp C.fstToSum :=
  (rfl)
@[simp] theorem coe_sumDualEquivDualInter_snd (hC : C.IsRegular) (Λ : StrongDual 𝕜 C.SumSpace) :
    (C.sumDualEquivDualInter hC Λ : StrongDual 𝕜 X₀ × StrongDual 𝕜 X₁).2 = Λ.comp C.sndToSum :=
  (rfl)
theorem interFst_sumDualEquivDualInter (hC : C.IsRegular) (Λ : StrongDual 𝕜 C.SumSpace) :
    (C.dual hC).interFst (C.sumDualEquivDualInter hC Λ) = Λ.comp C.fstToSum := by simp
theorem interSnd_sumDualEquivDualInter (hC : C.IsRegular) (Λ : StrongDual 𝕜 C.SumSpace) :
    (C.dual hC).interSnd (C.sumDualEquivDualInter hC Λ) = Λ.comp C.sndToSum := by simp
@[simp] theorem sumDualEquivDualInter_symm_fstToSum (hC : C.IsRegular) (f : (C.dual hC).inter)
    (x₀ : X₀) : (C.sumDualEquivDualInter hC).symm f (C.fstToSum x₀) = (C.dual hC).interFst f x₀ :=
  C.sumLift_fstToSum _ _ (dualInter_compat C hC f) x₀
@[simp] theorem sumDualEquivDualInter_symm_sndToSum (hC : C.IsRegular) (f : (C.dual hC).inter)
    (x₁ : X₁) : (C.sumDualEquivDualInter hC).symm f (C.sndToSum x₁) = (C.dual hC).interSnd f x₁ :=
  C.sumLift_sndToSum _ _ (dualInter_compat C hC f) x₁

end SumDual

end NontriviallyNormedField

section RCLike

variable {𝕜 X₀ X₁ V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-- Over `RCLike` scalars, a compatible couple is regular if and only if both restriction maps
`X₀* → (X₀ ∩ X₁)*` and `X₁* → (X₀ ∩ X₁)*` are injective. -/
theorem isRegular_iff_injective_precomp : C.IsRegular ↔
    Function.Injective (ContinuousLinearMap.precomp 𝕜 C.interFst :
      StrongDual 𝕜 X₀ →L[𝕜] StrongDual 𝕜 C.inter) ∧
    Function.Injective (ContinuousLinearMap.precomp 𝕜 C.interSnd :
      StrongDual 𝕜 X₁ →L[𝕜] StrongDual 𝕜 C.inter) := by simp [isRegular_iff]

private theorem norm_dualSum_sumSpaceEmbed_le (hC : C.IsRegular) (u : (C.dual hC).SumSpace) :
    ‖(C.dual hC).sumSpaceEmbed u‖ ≤ ‖u‖ := by
  refine ((C.dual hC).le_norm_sumSpace_iff).2 fun f₀ f₁ h => ?_
  subst h; rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  calc ‖((C.dual hC).embed₀ f₀ + (C.dual hC).embed₁ f₁) x‖
      ≤ ‖f₀ (C.interFst x)‖ + ‖f₁ (C.interSnd x)‖ := norm_add_le _ _
    _ ≤ ‖f₀‖ * ‖C.interFst x‖ + ‖f₁‖ * ‖C.interSnd x‖ :=
        add_le_add (f₀.le_opNorm _) (f₁.le_opNorm _)
    _ ≤ (‖f₀‖ + ‖f₁‖) * ‖x‖ := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (C.norm_interFst_le x) (norm_nonneg f₀))
          (mul_le_mul_of_nonneg_left (C.norm_interSnd_le x) (norm_nonneg f₁))
private theorem exists_dualSum_eq_and_norm_le (hC : C.IsRegular) (φ : StrongDual 𝕜 C.inter) :
    ∃ u : (C.dual hC).SumSpace, (C.dual hC).sumSpaceEmbed u = φ ∧ ‖u‖ ≤ ‖φ‖ := by
  obtain ⟨Ψ, hΨ, hnorm⟩ := exists_extension_norm_eq C.inter φ
  set f₀ : StrongDual 𝕜 X₀ := Ψ.comp (ContinuousLinearMap.inl 𝕜 X₀ X₁)
  set f₁ : StrongDual 𝕜 X₁ := Ψ.comp (ContinuousLinearMap.inr 𝕜 X₀ X₁)
  refine ⟨(C.dual hC).fstToSum f₀ + (C.dual hC).sndToSum f₁, ?_,
    ((C.dual hC).norm_fstToSum_add_sndToSum_le f₀ f₁).trans
      ((StrongDual.norm_comp_inl_add_norm_comp_inr_le Ψ).trans_eq hnorm)⟩
  rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum]; ext x
  simpa [f₀, f₁] using (Ψ.comp_inl_add_comp_inr (x : X₀ × X₁)).trans (hΨ x)
private def dualSumLinearEquiv (hC : C.IsRegular) :
    (C.dual hC).SumSpace ≃ₗ[𝕜] StrongDual 𝕜 C.inter :=
  LinearEquiv.ofBijective ((C.dual hC).sumSpaceEmbed.toLinearMap)
    ⟨(C.dual hC).sumSpaceEmbed_injective,
      fun φ => let ⟨u, hu, _⟩ := exists_dualSum_eq_and_norm_le C hC φ; ⟨u, hu⟩⟩

/-- **Duality of the intersection (Bergh–Löfström, Theorem 2.7.1).** For a regular couple `C` over
`RCLike`, the ambient embedding `(X₀* + X₁*) → (X₀ ∩ X₁)*` is a surjective linear isometry. -/
def dualSumEquivInterDual (hC : C.IsRegular) :
    (C.dual hC).SumSpace ≃ₗᵢ[𝕜] StrongDual 𝕜 C.inter where
  toLinearEquiv := dualSumLinearEquiv C hC
  norm_map' u := le_antisymm (norm_dualSum_sumSpaceEmbed_le C hC u) <| by
    obtain ⟨v, hv, hle⟩ := exists_dualSum_eq_and_norm_le C hC ((C.dual hC).sumSpaceEmbed u)
    exact (C.dual hC).sumSpaceEmbed_injective hv ▸ hle

@[simp] theorem dualSumEquivInterDual_apply (hC : C.IsRegular) (u : (C.dual hC).SumSpace) :
    C.dualSumEquivInterDual hC u = (C.dual hC).sumSpaceEmbed u := (rfl)
theorem dualSumEquivInterDual_fstToSum (hC : C.IsRegular) (f₀ : StrongDual 𝕜 X₀) :
    C.dualSumEquivInterDual hC ((C.dual hC).fstToSum f₀) = f₀.comp C.interFst :=
  (C.dual hC).sumSpaceEmbed_fstToSum f₀
theorem dualSumEquivInterDual_sndToSum (hC : C.IsRegular) (f₁ : StrongDual 𝕜 X₁) :
    C.dualSumEquivInterDual hC ((C.dual hC).sndToSum f₁) = f₁.comp C.interSnd :=
  (C.dual hC).sumSpaceEmbed_sndToSum f₁
@[simp] theorem sumSpaceEmbed_dualSumEquivInterDual_symm (hC : C.IsRegular)
    (φ : StrongDual 𝕜 C.inter) :
    (C.dual hC).sumSpaceEmbed ((C.dualSumEquivInterDual hC).symm φ) = φ :=
  (C.dualSumEquivInterDual hC).apply_symm_apply φ
@[simp] theorem dualSumEquivInterDual_symm_comp_interFst (hC : C.IsRegular) (f₀ : StrongDual 𝕜 X₀) :
    (C.dualSumEquivInterDual hC).symm (f₀.comp C.interFst) = (C.dual hC).fstToSum f₀ :=
  (C.dualSumEquivInterDual hC).symm_apply_eq.2 (C.dualSumEquivInterDual_fstToSum hC f₀).symm
@[simp] theorem dualSumEquivInterDual_symm_comp_interSnd (hC : C.IsRegular) (f₁ : StrongDual 𝕜 X₁) :
    (C.dualSumEquivInterDual hC).symm (f₁.comp C.interSnd) = (C.dual hC).sndToSum f₁ :=
  (C.dualSumEquivInterDual hC).symm_apply_eq.2 (C.dualSumEquivInterDual_sndToSum hC f₁).symm

end RCLike

end Dual

end TauCeti.CompatibleCouple
