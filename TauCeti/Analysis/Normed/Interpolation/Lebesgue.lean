/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
public import TauCeti.MeasureTheory.Function.Lp.L1AddLinfty

/-!
# The Lebesgue couple `(L^{p₀}, L^{p₁})`

For `1 ≤ p₀, p₁ ≤ ∞` the Lebesgue spaces `L^{p₀}(μ; E)` and `L^{p₁}(μ; E)` form a compatible
couple, `TauCeti.CompatibleCouple.lebesgue`, inside the common ambient space `L¹ + L^∞`
(`TauCeti.L1AddLinfty`). This is the couple whose complex and real interpolation spaces are the
`Lᵖ` and Lorentz spaces (Bergh–Löfström, Chapter 5). Its intersection is `L^{p₀} ∩ L^{p₁}`, the
pairs of functions agreeing almost everywhere (`TauCeti.CompatibleCouple.mem_lebesgue_inter_iff`),
and its sum is `L^{p₀} + L^{p₁}`, in which two decompositions agree exactly when their sums agree
almost everywhere (`TauCeti.CompatibleCouple.lebesgue_fstToSum_add_sndToSum_eq_iff`). At the
exponents `1` and `∞` the couple has the same decompositions as `TauCeti.CompatibleCouple.l1Linfty`,
so the embedding of its sum space into `L¹ + L^∞` is a surjective isometry
(`TauCeti.CompatibleCouple.lebesgue_one_top_sumSpaceEmbed_surjective`,
`TauCeti.CompatibleCouple.norm_lebesgue_one_top_sumSpaceEmbed`).

For `p₀ ≤ p ≤ p₁` the space `Lᵖ` is an intermediate space of the couple: there are continuous
injections

`L^{p₀} ∩ L^{p₁} → Lᵖ → L^{p₀} + L^{p₁}`,

`TauCeti.CompatibleCouple.lebesgueInterToLp` and `TauCeti.CompatibleCouple.lpToLebesgueSum`, of
norm at most `1` and `2` respectively, compatible with the embeddings into `L¹ + L^∞`, reducing to
the canonical maps at the endpoints `p = p₀` and `p = p₁`, and composing to the canonical
inclusion of the intersection into the sum
(`TauCeti.CompatibleCouple.lpToLebesgueSum_lebesgueInterToLp`). The norm bounds are
`‖f‖_p ≤ max (‖f‖_{p₀}, ‖f‖_{p₁})` (`MeasureTheory.eLpNorm_le_max_of_le_of_le`) and the
decomposition `Lᵖ ⊆ L^{p₀} + L^{p₁}` with both parts of norm at most `‖f‖_p`
(`MeasureTheory.Lp.exists_add_ae_eq_of_le_of_le`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §2.3 and §5.1.
-/

public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable (𝕜 E : Type*) {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (p₀ p₁ : ℝ≥0∞) [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]

/-- The Lebesgue couple `(L^{p₀}, L^{p₁})` for `1 ≤ p₀, p₁ ≤ ∞`, with both spaces embedded in the
common ambient space `L¹ + L^∞` by `TauCeti.L1AddLinfty.ofLp`. -/
def lebesgue : CompatibleCouple 𝕜 (Lp E p₀ μ) (Lp E p₁ μ) (L1AddLinfty 𝕜 E μ) where
  embed₀ := L1AddLinfty.ofLp
  embed₁ := L1AddLinfty.ofLp
  embed₀_injective := L1AddLinfty.ofLp_injective
  embed₁_injective := L1AddLinfty.ofLp_injective

variable {𝕜 E μ p₀ p₁}

@[simp]
theorem lebesgue_embed₀ : (lebesgue 𝕜 E μ p₀ p₁).embed₀ = L1AddLinfty.ofLp :=
  (rfl)

@[simp]
theorem lebesgue_embed₁ : (lebesgue 𝕜 E μ p₀ p₁).embed₁ = L1AddLinfty.ofLp :=
  (rfl)

/-- The intersection of the Lebesgue couple consists of the pairs of functions that agree almost
everywhere: it is `L^{p₀} ∩ L^{p₁}`. -/
theorem mem_lebesgue_inter_iff {x : Lp E p₀ μ × Lp E p₁ μ} :
    x ∈ (lebesgue 𝕜 E μ p₀ p₁).inter ↔ ⇑x.1 =ᵐ[μ] ⇑x.2 := by
  rw [mem_inter_iff, lebesgue_embed₀, lebesgue_embed₁, L1AddLinfty.ofLp_eq_ofLp_iff]

/-- Two decompositions `f₀ + f₁` and `g₀ + g₁` give the same element of `L^{p₀} + L^{p₁}` exactly
when the sums agree almost everywhere. -/
theorem lebesgue_fstToSum_add_sndToSum_eq_iff {f₀ g₀ : Lp E p₀ μ} {f₁ g₁ : Lp E p₁ μ} :
    (lebesgue 𝕜 E μ p₀ p₁).fstToSum f₀ + (lebesgue 𝕜 E μ p₀ p₁).sndToSum f₁ =
        (lebesgue 𝕜 E μ p₀ p₁).fstToSum g₀ + (lebesgue 𝕜 E μ p₀ p₁).sndToSum g₁ ↔
      ⇑f₀ + ⇑f₁ =ᵐ[μ] ⇑g₀ + ⇑g₁ := by
  simp only [← (lebesgue 𝕜 E μ p₀ p₁).sumSpaceEmbed_injective.eq_iff,
    ← (l1Linfty 𝕜 E μ).sumSpaceEmbed_injective.eq_iff, map_add, sumSpaceEmbed_fstToSum,
    sumSpaceEmbed_sndToSum, lebesgue_embed₀, lebesgue_embed₁, L1AddLinfty.sumSpaceEmbed_ofLp]
  exact L1AddLinfty.lpToAmbient_add_lpToAmbient_eq_add_iff 𝕜

/-- The Lebesgue couple `(L¹, L^∞)` and `l1Linfty` have the same decompositions: the embedding of
the sum space of the former into `L¹ + L^∞` sends `g + h` to `g + h`. -/
theorem lebesgue_one_top_sumSpaceEmbed_fstToSum_add_sndToSum (g : Lp E 1 μ) (h : Lp E ∞ μ) :
    (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
        ((lebesgue 𝕜 E μ 1 ∞).fstToSum g + (lebesgue 𝕜 E μ 1 ∞).sndToSum h) =
      (l1Linfty 𝕜 E μ).fstToSum g + (l1Linfty 𝕜 E μ).sndToSum h := by
  rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, lebesgue_embed₀,
    lebesgue_embed₁, L1AddLinfty.ofLp_eq_fstToSum, L1AddLinfty.ofLp_eq_sndToSum]

/-- The embedding of the sum space of the Lebesgue couple `(L¹, L^∞)` into `L¹ + L^∞` is
surjective. -/
theorem lebesgue_one_top_sumSpaceEmbed_surjective :
    Function.Surjective (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed := fun u => by
  obtain ⟨g, h, hgh⟩ := (l1Linfty 𝕜 E μ).exists_fstToSum_add_sndToSum_eq u
  exact ⟨_, (lebesgue_one_top_sumSpaceEmbed_fstToSum_add_sndToSum g h).trans hgh⟩

/-- The embedding of the sum space of the Lebesgue couple `(L¹, L^∞)` into `L¹ + L^∞` is
norm-preserving. -/
theorem norm_lebesgue_one_top_sumSpaceEmbed (v : (lebesgue 𝕜 E μ 1 ∞).SumSpace) :
    ‖(lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v‖ = ‖v‖ := by
  refine le_antisymm ((lebesgue 𝕜 E μ 1 ∞).le_norm_sumSpace_iff.2 fun g h hgh => ?_)
    ((l1Linfty 𝕜 E μ).le_norm_sumSpace_iff.2 fun g h hgh => ?_)
  · rw [← hgh, lebesgue_one_top_sumSpaceEmbed_fstToSum_add_sndToSum]
    exact norm_fstToSum_add_sndToSum_le _ g h
  · rw [← (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective
      ((lebesgue_one_top_sumSpaceEmbed_fstToSum_add_sndToSum g h).trans hgh)]
    exact norm_fstToSum_add_sndToSum_le _ g h

section Intermediate

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inclusion `Lᵖ → L^{p₀} + L^{p₁}` for `p₀ ≤ p ≤ p₁`, of norm at most `2`
(`TauCeti.CompatibleCouple.norm_lpToLebesgueSum_le`): `f` is sent to `g + h` for a decomposition
`f = g + h` with `g ∈ L^{p₀}` and `h ∈ L^{p₁}`. -/
def lpToLebesgueSum (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    Lp E p μ →L[𝕜] (lebesgue 𝕜 E μ p₀ p₁).SumSpace :=
  (lebesgue 𝕜 E μ p₀ p₁).toSum (L1AddLinfty.ofLp : Lp E p μ →L[𝕜] L1AddLinfty 𝕜 E μ) 2
    fun f => by
      obtain ⟨g, h, hgh, hg, hh⟩ := Lp.exists_add_ae_eq_of_le_of_le f h₀ h₁
      refine ⟨(lebesgue 𝕜 E μ p₀ p₁).fstToSum g + (lebesgue 𝕜 E μ p₀ p₁).sndToSum h, ?_,
        (norm_fstToSum_add_sndToSum_le _ _ _).trans (by linarith)⟩
      apply (l1Linfty 𝕜 E μ).sumSpace_ext
      simpa only [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, lebesgue_embed₀,
        lebesgue_embed₁, L1AddLinfty.sumSpaceEmbed_ofLp, ContinuousLinearMap.coe_coe] using
        (L1AddLinfty.lpToAmbient_add_lpToAmbient_eq_iff 𝕜).2 hgh

@[simp]
theorem sumSpaceEmbed_lpToLebesgueSum (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    (lebesgue 𝕜 E μ p₀ p₁).sumSpaceEmbed (lpToLebesgueSum h₀ h₁ f) = L1AddLinfty.ofLp f :=
  sumSpaceEmbed_toSum _ _ _ _ f

theorem norm_lpToLebesgueSum_le (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    ‖(lpToLebesgueSum h₀ h₁ f : (lebesgue 𝕜 E μ p₀ p₁).SumSpace)‖ ≤ 2 * ‖f‖ :=
  norm_toSum_le _ _ _ _ f

theorem lpToLebesgueSum_injective (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    Function.Injective (lpToLebesgueSum h₀ h₁ : Lp E p μ → (lebesgue 𝕜 E μ p₀ p₁).SumSpace) :=
  toSum_injective _ _ _ _ L1AddLinfty.ofLp_injective

omit [Fact (1 ≤ p)] in
private theorem memLp_inter_fst (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (x : (lebesgue 𝕜 E μ p₀ p₁).inter) :
    MemLp (x : Lp E p₀ μ × Lp E p₁ μ).1 p μ :=
  (Lp.memLp _).of_le_of_le ((Lp.memLp (x : Lp E p₀ μ × Lp E p₁ μ).2).ae_eq
      (mem_lebesgue_inter_iff.1 x.2).symm)
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne' h₀ h₁

omit [Fact (1 ≤ p)] in
private theorem norm_toLp_inter_fst_le (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁)
    (x : (lebesgue 𝕜 E μ p₀ p₁).inter) : ‖(memLp_inter_fst h₀ h₁ x).toLp _‖ ≤ ‖x‖ := by
  rw [Lp.norm_toLp, norm_inter]
  have h := eLpNorm_le_max_of_le_of_le (f := (x : Lp E p₀ μ × Lp E p₁ μ).1) (μ := μ)
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne' h₀ h₁
  rw [eLpNorm_congr_ae (p := p₁) (mem_lebesgue_inter_iff.1 x.2)] at h
  calc (eLpNorm (x : Lp E p₀ μ × Lp E p₁ μ).1 p μ).toReal
      ≤ (max (eLpNorm (x : Lp E p₀ μ × Lp E p₁ μ).1 p₀ μ)
          (eLpNorm (x : Lp E p₀ μ × Lp E p₁ μ).2 p₁ μ)).toReal :=
        ENNReal.toReal_mono (max_lt (Lp.memLp _).eLpNorm_lt_top (Lp.memLp _).eLpNorm_lt_top).ne h
    _ = max ‖(x : Lp E p₀ μ × Lp E p₁ μ).1‖ ‖(x : Lp E p₀ μ × Lp E p₁ μ).2‖ := by
      rw [ENNReal.toReal_max (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)]
      simp [Lp.norm_def]

/-- The inclusion `L^{p₀} ∩ L^{p₁} → Lᵖ` for `p₀ ≤ p ≤ p₁`, of norm at most `1`
(`TauCeti.CompatibleCouple.norm_lebesgueInterToLp_le`). -/
def lebesgueInterToLp (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    (lebesgue 𝕜 E μ p₀ p₁).inter →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun x := (memLp_inter_fst h₀ h₁ x).toLp _
      map_add' x y := by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_add _ _)
      map_smul' c x := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_smul _ _) }
    1 fun x => (norm_toLp_inter_fst_le h₀ h₁ x).trans_eq (one_mul _).symm

theorem coeFn_lebesgueInterToLp (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (x : (lebesgue 𝕜 E μ p₀ p₁).inter) :
    ⇑(lebesgueInterToLp h₀ h₁ x) =ᵐ[μ] ⇑(x : Lp E p₀ μ × Lp E p₁ μ).1 :=
  (memLp_inter_fst h₀ h₁ x).coeFn_toLp

theorem norm_lebesgueInterToLp_le (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁)
    (x : (lebesgue 𝕜 E μ p₀ p₁).inter) : ‖lebesgueInterToLp h₀ h₁ x‖ ≤ ‖x‖ :=
  norm_toLp_inter_fst_le h₀ h₁ x

theorem lebesgueInterToLp_injective (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    Function.Injective (lebesgueInterToLp h₀ h₁ : (lebesgue 𝕜 E μ p₀ p₁).inter → Lp E p μ) := by
  intro x y hxy
  have h₀' : ⇑(x : Lp E p₀ μ × Lp E p₁ μ).1 =ᵐ[μ] ⇑(y : Lp E p₀ μ × Lp E p₁ μ).1 :=
    (coeFn_lebesgueInterToLp h₀ h₁ x).symm.trans
      (hxy ▸ coeFn_lebesgueInterToLp h₀ h₁ y)
  refine Subtype.ext (Prod.ext (Lp.ext h₀') (Lp.ext ?_))
  exact (mem_lebesgue_inter_iff.1 x.2).symm.trans (h₀'.trans (mem_lebesgue_inter_iff.1 y.2))

/-- The inclusion `L^{p₀} ∩ L^{p₁} → Lᵖ` is compatible with the embeddings into `L¹ + L^∞`. -/
@[simp]
theorem ofLp_lebesgueInterToLp (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (x : (lebesgue 𝕜 E μ p₀ p₁).inter) :
    (L1AddLinfty.ofLp (lebesgueInterToLp h₀ h₁ x) : L1AddLinfty 𝕜 E μ) =
      L1AddLinfty.ofLp (x : Lp E p₀ μ × Lp E p₁ μ).1 :=
  L1AddLinfty.ofLp_eq_ofLp_iff.2 (coeFn_lebesgueInterToLp h₀ h₁ x)

/-- At the endpoint `p = p₀`, the inclusion `L^{p₀} ∩ L^{p₁} → Lᵖ` is the canonical one. -/
theorem lebesgueInterToLp_eq_interFst (h₁ : p₀ ≤ p₁) (x : (lebesgue 𝕜 E μ p₀ p₁).inter) :
    lebesgueInterToLp le_rfl h₁ x = (lebesgue 𝕜 E μ p₀ p₁).interFst x := by
  rw [interFst_apply]
  exact Lp.ext (coeFn_lebesgueInterToLp le_rfl h₁ x)

/-- At the endpoint `p = p₁`, the inclusion `L^{p₀} ∩ L^{p₁} → Lᵖ` is the canonical one. -/
theorem lebesgueInterToLp_eq_interSnd (h₀ : p₀ ≤ p₁) (x : (lebesgue 𝕜 E μ p₀ p₁).inter) :
    lebesgueInterToLp h₀ le_rfl x = (lebesgue 𝕜 E μ p₀ p₁).interSnd x := by
  rw [interSnd_apply]
  exact Lp.ext ((coeFn_lebesgueInterToLp h₀ le_rfl x).trans (mem_lebesgue_inter_iff.1 x.2))

/-- At the endpoint `p = p₀`, the inclusion `Lᵖ → L^{p₀} + L^{p₁}` is the canonical one. -/
theorem lpToLebesgueSum_eq_fstToSum (h₁ : p₀ ≤ p₁) (f : Lp E p₀ μ) :
    lpToLebesgueSum le_rfl h₁ f = (lebesgue 𝕜 E μ p₀ p₁).fstToSum f :=
  sumSpace_ext _ (by simp)

/-- At the endpoint `p = p₁`, the inclusion `Lᵖ → L^{p₀} + L^{p₁}` is the canonical one. -/
theorem lpToLebesgueSum_eq_sndToSum (h₀ : p₀ ≤ p₁) (f : Lp E p₁ μ) :
    lpToLebesgueSum h₀ le_rfl f = (lebesgue 𝕜 E μ p₀ p₁).sndToSum f :=
  sumSpace_ext _ (by simp)

/-- The inclusions `L^{p₀} ∩ L^{p₁} → Lᵖ → L^{p₀} + L^{p₁}` compose to the canonical inclusion of
the intersection into the sum. -/
theorem lpToLebesgueSum_lebesgueInterToLp (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁)
    (x : (lebesgue 𝕜 E μ p₀ p₁).inter) :
    lpToLebesgueSum h₀ h₁ (lebesgueInterToLp h₀ h₁ x) =
      (lebesgue 𝕜 E μ p₀ p₁).fstToSum ((lebesgue 𝕜 E μ p₀ p₁).interFst x) :=
  sumSpace_ext _ (by simp)

end Intermediate

end TauCeti.CompatibleCouple
