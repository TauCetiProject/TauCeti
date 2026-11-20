/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
public import TauCeti.Analysis.Normed.Module.Dual.Prod

/-!
# The dual couple and the duals of the sum and the intersection

Let `(X₀, X₁)` be a compatible couple of normed spaces over `ℝ` or `ℂ`. Restricting functionals
to the intersection gives continuous linear maps `X₀* → (X₀ ∩ X₁)*` and `X₁* → (X₀ ∩ X₁)*`. When
the couple is regular, that is, `X₀ ∩ X₁` is dense in `X₀` and in `X₁`
(`TauCeti.CompatibleCouple.IsRegular`), both maps are injective, so `(X₀*, X₁*)` is a compatible
couple with ambient space `(X₀ ∩ X₁)*`: the *dual couple* `TauCeti.CompatibleCouple.dual`. Its
intersection consists of the pairs `(f₀, f₁)` that agree on `X₀ ∩ X₁`, and its sum of the
functionals `f₀ + f₁` on `X₀ ∩ X₁`.

The duality theorem for sums and intersections (Bergh–Löfström, Theorem 2.7.1) identifies these
two spaces isometrically with the duals of the sum and of the intersection:

* `(X₀ + X₁)* = X₀* ∩ X₁*` (`TauCeti.CompatibleCouple.interDualEquiv`): a functional on the sum
  is the same as a pair of functionals on the endpoints agreeing on the intersection, and its norm
  is the larger of their norms (`TauCeti.CompatibleCouple.opNorm_sumLift`), because the sum norm
  is the quotient of the `ℓ¹` norm on `X₀ × X₁`;
* `(X₀ ∩ X₁)* = X₀* + X₁*` (`TauCeti.CompatibleCouple.sumDualEquiv`): the canonical map
  `f₀ + f₁ ↦ (f₀ + f₁)|_{X₀ ∩ X₁}` from the sum of the dual couple is a surjective isometry. The
  intersection carries the maximum norm of `X₀ × X₁`, whose dual norm is the `ℓ¹` norm
  (`StrongDual.norm_eq_norm_comp_inl_add_norm_comp_inr`), so the Hahn–Banach theorem writes
  every functional on `X₀ ∩ X₁` as `f₀ + f₁` with `‖f₀‖ + ‖f₁‖` equal to its norm.

Neither identification needs completeness. The dual couple is the setting of Calderón's duality
theorem `([X₀, X₁]_θ)* = [X₀*, X₁*]^θ` for the complex method, and of the corresponding duality
for the real method, both of which are stated for regular couples.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §2.7 (Theorem 2.7.1).
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §1
  (Definition 1.3).
-/

public noncomputable section

namespace TauCeti.CompatibleCouple

/-! ### The dual of the sum -/

section SumDual

variable {𝕜 X₀ X₁ V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-- The inclusion of the first space in the sum has norm at most `1`. -/
theorem opNorm_fstToSum_le : ‖C.fstToSum‖ ≤ 1 :=
  C.fstToSum.opNorm_le_bound zero_le_one fun x => by simpa using C.norm_fstToSum_le x

/-- The inclusion of the second space in the sum has norm at most `1`. -/
theorem opNorm_sndToSum_le : ‖C.sndToSum‖ ≤ 1 :=
  C.sndToSum.opNorm_le_bound zero_le_one fun x => by simpa using C.norm_sndToSum_le x

variable {W : Type*} [SeminormedAddCommGroup W] [NormedSpace 𝕜 W] (T₀ : X₀ →L[𝕜] W)
  (T₁ : X₁ →L[𝕜] W) (h : ∀ x : C.inter, T₀ (C.interFst x) = T₁ (C.interSnd x))

/-- The extension `x₀ + x₁ ↦ T₀ x₀ + T₁ x₁` to the sum space has norm `max ‖T₀‖ ‖T₁‖`. For
functionals this is the isometry `(X₀ + X₁)* = X₀* ∩ X₁*` (Bergh–Löfström, Theorem 2.7.1). -/
theorem opNorm_sumLift : ‖C.sumLift T₀ T₁ h‖ = max ‖T₀‖ ‖T₁‖ := by
  have hM : 0 ≤ max ‖T₀‖ ‖T₁‖ := le_max_of_le_left (norm_nonneg _)
  refine le_antisymm ((C.sumLift T₀ T₁ h).opNorm_le_bound hM fun u =>
    (C.le_mul_norm_sumSpace_iff hM).2 fun x₀ x₁ hx => ?_) (max_le ?_ ?_)
  · rw [← hx, map_add, sumLift_fstToSum, sumLift_sndToSum, mul_add]
    exact norm_add_le_of_le ((T₀.le_opNorm x₀).trans (by gcongr; exact le_max_left _ _))
      ((T₁.le_opNorm x₁).trans (by gcongr; exact le_max_right _ _))
  · calc ‖T₀‖ = ‖(C.sumLift T₀ T₁ h).comp C.fstToSum‖ := by rw [sumLift_comp_fstToSum]
      _ ≤ ‖C.sumLift T₀ T₁ h‖ * ‖C.fstToSum‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖C.sumLift T₀ T₁ h‖ := mul_le_of_le_one_right (ContinuousLinearMap.opNorm_nonneg _)
        C.opNorm_fstToSum_le
  · calc ‖T₁‖ = ‖(C.sumLift T₀ T₁ h).comp C.sndToSum‖ := by rw [sumLift_comp_sndToSum]
      _ ≤ ‖C.sumLift T₀ T₁ h‖ * ‖C.sndToSum‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖C.sumLift T₀ T₁ h‖ := mul_le_of_le_one_right (ContinuousLinearMap.opNorm_nonneg _)
        C.opNorm_sndToSum_le

end SumDual

/-! ### The dual couple -/

variable {𝕜 X₀ X₁ V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-- The dual couple `(X₀*, X₁*)` of a regular couple, inside the dual `(X₀ ∩ X₁)*` of the
intersection: a functional on `X₀` or `X₁` is sent to its restriction to `X₀ ∩ X₁`, which
determines it because the intersection is dense in each endpoint. -/
-- The three duals are given the structures of their normed spaces, rather than the generic ones
-- of continuous linear maps, so that the constructions of `CompatibleCouple`, which take normed
-- endpoints and an additive group as ambient space, apply to the dual couple.
def dual (hC : C.IsRegular) :
    @CompatibleCouple 𝕜 _ (StrongDual 𝕜 X₀) (StrongDual 𝕜 X₁) (StrongDual 𝕜 C.inter)
      NormedAddCommGroup.toAddCommGroup.toAddCommMonoid NormedSpace.toModule
      UniformSpace.toTopologicalSpace NormedAddCommGroup.toAddCommGroup.toAddCommMonoid
      NormedSpace.toModule UniformSpace.toTopologicalSpace
      NormedAddCommGroup.toAddCommGroup.toAddCommMonoid NormedSpace.toModule
      UniformSpace.toTopologicalSpace where
  embed₀ := ContinuousLinearMap.precomp 𝕜 C.interFst
  embed₁ := ContinuousLinearMap.precomp 𝕜 C.interSnd
  embed₀_injective f g hfg := DFunLike.coe_injective <|
    hC.denseRange_interFst.equalizer f.continuous g.continuous congr($hfg)
  embed₁_injective f g hfg := DFunLike.coe_injective <|
    hC.denseRange_interSnd.equalizer f.continuous g.continuous congr($hfg)

variable {C} {hC : C.IsRegular}

@[simp]
theorem dual_embed₀_apply (f : StrongDual 𝕜 X₀) (x : C.inter) :
    (C.dual hC).embed₀ f x = f (C.interFst x) :=
  (rfl)

@[simp]
theorem dual_embed₁_apply (f : StrongDual 𝕜 X₁) (x : C.inter) :
    (C.dual hC).embed₁ f x = f (C.interSnd x) :=
  (rfl)

/-- The intersection of the dual couple consists of the pairs of functionals that agree on the
intersection `X₀ ∩ X₁`. -/
theorem mem_dual_inter_iff {f : StrongDual 𝕜 X₀ × StrongDual 𝕜 X₁} :
    f ∈ (C.dual hC).inter ↔ ∀ x : C.inter, f.1 (C.interFst x) = f.2 (C.interSnd x) := by
  simp only [mem_inter_iff, ContinuousLinearMap.ext_iff, dual_embed₀_apply, dual_embed₁_apply]

/-! ### The dual of the sum -/

section InterDual

variable [ContinuousAdd V]

/-- The dual of the sum is the intersection of the duals (Bergh–Löfström, Theorem 2.7.1): a pair
`(f₀, f₁)` of functionals agreeing on `X₀ ∩ X₁` is sent to the functional `x₀ + x₁ ↦ f₀ x₀ + f₁ x₁`
on `X₀ + X₁`, and every functional on the sum arises from the pair of its restrictions. Norms are
preserved: the norm on the intersection of the dual couple is `max ‖f₀‖ ‖f₁‖`. -/
def interDualEquiv (hC : C.IsRegular) : (C.dual hC).inter ≃ₗᵢ[𝕜] StrongDual 𝕜 C.SumSpace where
  toFun f := C.sumLift (f : StrongDual 𝕜 X₀ × StrongDual 𝕜 X₁).1
    (f : StrongDual 𝕜 X₀ × StrongDual 𝕜 X₁).2 (mem_dual_inter_iff.1 f.2)
  invFun L := ⟨(L.comp C.fstToSum, L.comp C.sndToSum),
    mem_dual_inter_iff.2 fun x => by simpa using congrArg L (C.fstToSum_interFst x)⟩
  left_inv f := by ext <;> simp
  right_inv L := by ext <;> simp
  map_add' f g := by ext <;> simp
  map_smul' c f := by ext <;> simp
  norm_map' f := by simp [opNorm_sumLift, Prod.norm_def]

@[simp]
theorem interDualEquiv_fstToSum (f : (C.dual hC).inter) (x : X₀) :
    interDualEquiv hC f (C.fstToSum x) = (f : StrongDual 𝕜 X₀ × StrongDual 𝕜 X₁).1 x :=
  C.sumLift_fstToSum _ _ _ x

@[simp]
theorem interDualEquiv_sndToSum (f : (C.dual hC).inter) (x : X₁) :
    interDualEquiv hC f (C.sndToSum x) = (f : StrongDual 𝕜 X₀ × StrongDual 𝕜 X₁).2 x :=
  C.sumLift_sndToSum _ _ _ x

@[simp]
theorem coe_interDualEquiv_symm (L : StrongDual 𝕜 C.SumSpace) :
    ((interDualEquiv hC).symm L : StrongDual 𝕜 X₀ × StrongDual 𝕜 X₁) =
      (L.comp C.fstToSum, L.comp C.sndToSum) :=
  (rfl)

end InterDual

/-! ### The dual of the intersection -/

section SumDualEquiv

/-- The restriction of `f₀ + f₁` to the intersection has norm at most `‖f₀‖ + ‖f₁‖`. -/
private theorem norm_dual_embed₀_add_embed₁_le (f₀ : StrongDual 𝕜 X₀) (f₁ : StrongDual 𝕜 X₁) :
    ‖(C.dual hC).embed₀ f₀ + (C.dual hC).embed₁ f₁‖ ≤ ‖f₀‖ + ‖f₁‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => by
    rw [add_apply, dual_embed₀_apply, dual_embed₁_apply, add_mul]
    exact norm_add_le_of_le ((f₀.le_opNorm _).trans (by gcongr; exact C.norm_interFst_le x))
      ((f₁.le_opNorm _).trans (by gcongr; exact C.norm_interSnd_le x))

/-- Every functional `φ` on the intersection is the restriction of `f₀ + f₁` for functionals
`f₀`, `f₁` on the endpoints with `‖f₀‖ + ‖f₁‖ ≤ ‖φ‖`: extend `φ` from `X₀ ∩ X₁ ⊆ X₀ × X₁` to
`X₀ × X₁` without increasing its norm, and restrict to the two factors. In particular the
infimum defining the norm of `φ` in the sum of the dual couple is attained. -/
theorem exists_dual_fstToSum_add_sndToSum_eq (φ : StrongDual 𝕜 C.inter) :
    ∃ f₀ f₁, (C.dual hC).sumSpaceEmbed ((C.dual hC).fstToSum f₀ + (C.dual hC).sndToSum f₁) = φ ∧
      ‖f₀‖ + ‖f₁‖ ≤ ‖φ‖ := by
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_extension_norm_eq C.inter φ
  refine ⟨Φ.comp (ContinuousLinearMap.inl 𝕜 X₀ X₁), Φ.comp (ContinuousLinearMap.inr 𝕜 X₀ X₁),
    ContinuousLinearMap.ext fun x => ?_, ?_⟩
  · rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, add_apply, dual_embed₀_apply,
      dual_embed₁_apply, ← hΦ x, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ← map_add]
    simp
  · rw [← hΦn, StrongDual.norm_eq_norm_comp_inl_add_norm_comp_inr]

/-- The norm of an element of the sum of the dual couple is the norm of the functional it
defines on the intersection. -/
theorem norm_dual_sumSpaceEmbed (u : (C.dual hC).SumSpace) :
    ‖(C.dual hC).sumSpaceEmbed u‖ = ‖u‖ := by
  refine le_antisymm ?_ ?_
  · simpa using ((C.dual hC).le_mul_norm_sumSpace_iff zero_le_one).2 fun f₀ f₁ hf => by
      simpa [← hf] using norm_dual_embed₀_add_embed₁_le f₀ f₁
  · obtain ⟨f₀, f₁, hf, hfn⟩ := exists_dual_fstToSum_add_sndToSum_eq ((C.dual hC).sumSpaceEmbed u)
    rw [← (C.dual hC).sumSpaceEmbed_injective hf]
    exact ((C.dual hC).norm_fstToSum_add_sndToSum_le f₀ f₁).trans (hf ▸ hfn)

private theorem dual_sumSpaceEmbed_surjective :
    Function.Surjective (C.dual hC).sumSpaceEmbed := fun φ => by
  obtain ⟨f₀, f₁, hf, -⟩ := exists_dual_fstToSum_add_sndToSum_eq (hC := hC) φ
  exact ⟨_, hf⟩

/-- The dual of the intersection is the sum of the duals (Bergh–Löfström, Theorem 2.7.1): the map
`f₀ + f₁ ↦ (f₀ + f₁)|_{X₀ ∩ X₁}` from the sum of the dual couple is a surjective isometry onto
`(X₀ ∩ X₁)*`. It is the embedding `sumSpaceEmbed` of the dual couple
(`TauCeti.CompatibleCouple.coe_sumDualEquiv`). -/
def sumDualEquiv (hC : C.IsRegular) : (C.dual hC).SumSpace ≃ₗᵢ[𝕜] StrongDual 𝕜 C.inter where
  toLinearEquiv := LinearEquiv.ofBijective (C.dual hC).sumSpaceEmbed.toLinearMap
    ⟨(C.dual hC).sumSpaceEmbed_injective, dual_sumSpaceEmbed_surjective⟩
  norm_map' := norm_dual_sumSpaceEmbed

theorem coe_sumDualEquiv : ⇑(sumDualEquiv hC) = (C.dual hC).sumSpaceEmbed :=
  (rfl)

@[simp]
theorem sumDualEquiv_fstToSum (f : StrongDual 𝕜 X₀) (x : C.inter) :
    sumDualEquiv hC ((C.dual hC).fstToSum f) x = f (C.interFst x) := by
  simp [coe_sumDualEquiv]

@[simp]
theorem sumDualEquiv_sndToSum (f : StrongDual 𝕜 X₁) (x : C.inter) :
    sumDualEquiv hC ((C.dual hC).sndToSum f) x = f (C.interSnd x) := by
  simp [coe_sumDualEquiv]

end SumDualEquiv

end TauCeti.CompatibleCouple
