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
almost everywhere (`TauCeti.CompatibleCouple.lebesgue_fstToSum_add_sndToSum_eq_iff`).

For `p₀ ≤ p ≤ p₁` the space `Lᵖ` is an intermediate space of the couple: there are continuous
injections

`L^{p₀} ∩ L^{p₁} → Lᵖ → L^{p₀} + L^{p₁}`,

`TauCeti.CompatibleCouple.lebesgueInterToLp` and `TauCeti.CompatibleCouple.lpToLebesgueSum`, both
of norm at most `2`, compatible with the embeddings into `L¹ + L^∞`, and composing to the canonical
inclusion of the intersection into the sum
(`TauCeti.CompatibleCouple.lpToLebesgueSum_lebesgueInterToLp`). The first comes from the
pointwise bound `‖f‖ ^ p ≤ M ^ (p - p₀) ‖f‖ ^ {p₀} + M ^ (p - p₁) ‖f‖ ^ {p₁}` with
`M = max (‖f‖_{p₀}, ‖f‖_{p₁})`, the second from splitting `f` at the level `‖f‖_p`.

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
  rw [← (lebesgue 𝕜 E μ p₀ p₁).sumSpaceEmbed_injective.eq_iff, map_add, map_add,
    sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, sumSpaceEmbed_fstToSum,
    sumSpaceEmbed_sndToSum, ← L1AddLinfty.toAEEqFun_injective.eq_iff, map_add, map_add]
  simp only [lebesgue_embed₀, lebesgue_embed₁, L1AddLinfty.toAEEqFun_ofLp, AEEqFun.ext_iff]
  exact ⟨fun h => (AEEqFun.coeFn_add _ _).symm.trans (h.trans (AEEqFun.coeFn_add _ _)),
    fun h => (AEEqFun.coeFn_add _ _).trans (h.trans (AEEqFun.coeFn_add _ _).symm)⟩

section Intermediate

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_sumSpaceEmbed_eq_and_norm_le (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    ∃ u : (lebesgue 𝕜 E μ p₀ p₁).SumSpace,
      (lebesgue 𝕜 E μ p₀ p₁).sumSpaceEmbed u = L1AddLinfty.ofLp f ∧ ‖u‖ ≤ 2 * ‖f‖ := by
  obtain ⟨g, h, hgh, hg, hh⟩ := Lp.exists_add_ae_eq_of_le_of_le f h₀ h₁
  refine ⟨(lebesgue 𝕜 E μ p₀ p₁).fstToSum g + (lebesgue 𝕜 E μ p₀ p₁).sndToSum h, ?_,
    (norm_fstToSum_add_sndToSum_le _ _ _).trans (by linarith)⟩
  apply L1AddLinfty.toAEEqFun_injective
  rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, map_add]
  simp only [lebesgue_embed₀, lebesgue_embed₁, L1AddLinfty.toAEEqFun_ofLp]
  exact AEEqFun.ext ((AEEqFun.coeFn_add _ _).trans hgh)

/-- The inclusion `Lᵖ → L^{p₀} + L^{p₁}` for `p₀ ≤ p ≤ p₁`, of norm at most `2`
(`TauCeti.CompatibleCouple.norm_lpToLebesgueSum_le`): `f` is sent to `g + h` for a decomposition
`f = g + h` with `g ∈ L^{p₀}` and `h ∈ L^{p₁}`. -/
def lpToLebesgueSum (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    Lp E p μ →L[𝕜] (lebesgue 𝕜 E μ p₀ p₁).SumSpace :=
  LinearMap.mkContinuous
    { toFun f := (exists_sumSpaceEmbed_eq_and_norm_le h₀ h₁ f).choose
      map_add' f g := sumSpace_ext _ <|
        (exists_sumSpaceEmbed_eq_and_norm_le h₀ h₁ (f + g)).choose_spec.1.trans <| by
          simp only [map_add, (exists_sumSpaceEmbed_eq_and_norm_le h₀ h₁ f).choose_spec.1,
            (exists_sumSpaceEmbed_eq_and_norm_le h₀ h₁ g).choose_spec.1]
      map_smul' c f := sumSpace_ext _ <|
        (exists_sumSpaceEmbed_eq_and_norm_le h₀ h₁ (c • f)).choose_spec.1.trans <| by
          simp only [RingHom.id_apply, map_smul,
            (exists_sumSpaceEmbed_eq_and_norm_le h₀ h₁ f).choose_spec.1] }
    2 fun f => (exists_sumSpaceEmbed_eq_and_norm_le h₀ h₁ f).choose_spec.2

@[simp]
theorem sumSpaceEmbed_lpToLebesgueSum (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    (lebesgue 𝕜 E μ p₀ p₁).sumSpaceEmbed (lpToLebesgueSum h₀ h₁ f) = L1AddLinfty.ofLp f :=
  (exists_sumSpaceEmbed_eq_and_norm_le h₀ h₁ f).choose_spec.1

theorem norm_lpToLebesgueSum_le (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    ‖(lpToLebesgueSum h₀ h₁ f : (lebesgue 𝕜 E μ p₀ p₁).SumSpace)‖ ≤ 2 * ‖f‖ :=
  (exists_sumSpaceEmbed_eq_and_norm_le h₀ h₁ f).choose_spec.2

theorem lpToLebesgueSum_injective (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    Function.Injective (lpToLebesgueSum h₀ h₁ : Lp E p μ → (lebesgue 𝕜 E μ p₀ p₁).SumSpace) :=
  fun f g h => L1AddLinfty.ofLp_injective (𝕜 := 𝕜) <| by
    rw [← sumSpaceEmbed_lpToLebesgueSum h₀ h₁, h, sumSpaceEmbed_lpToLebesgueSum]

omit [Fact (1 ≤ p)] in
private theorem memLp_inter_fst (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (x : (lebesgue 𝕜 E μ p₀ p₁).inter) :
    MemLp (x : Lp E p₀ μ × Lp E p₁ μ).1 p μ :=
  (Lp.memLp _).of_le_of_le ((Lp.memLp (x : Lp E p₀ μ × Lp E p₁ μ).2).ae_eq
      (mem_lebesgue_inter_iff.1 x.2).symm)
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne' h₀ h₁

omit [Fact (1 ≤ p)] in
private theorem norm_toLp_inter_fst_le (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁)
    (x : (lebesgue 𝕜 E μ p₀ p₁).inter) : ‖(memLp_inter_fst h₀ h₁ x).toLp _‖ ≤ 2 * ‖x‖ := by
  rw [Lp.norm_toLp, norm_inter]
  have h := eLpNorm_le_two_mul_max_of_le_of_le
    (Lp.aestronglyMeasurable (x : Lp E p₀ μ × Lp E p₁ μ).1) Fact.out h₀ h₁
  rw [eLpNorm_congr_ae (p := p₁) (mem_lebesgue_inter_iff.1 x.2)] at h
  calc (eLpNorm (x : Lp E p₀ μ × Lp E p₁ μ).1 p μ).toReal
      ≤ (2 * max (eLpNorm (x : Lp E p₀ μ × Lp E p₁ μ).1 p₀ μ)
          (eLpNorm (x : Lp E p₀ μ × Lp E p₁ μ).2 p₁ μ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
          (max_lt (Lp.memLp _).eLpNorm_lt_top (Lp.memLp _).eLpNorm_lt_top).ne) h
    _ = 2 * max ‖(x : Lp E p₀ μ × Lp E p₁ μ).1‖ ‖(x : Lp E p₀ μ × Lp E p₁ μ).2‖ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_max (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)]
      simp [Lp.norm_def]

/-- The inclusion `L^{p₀} ∩ L^{p₁} → Lᵖ` for `p₀ ≤ p ≤ p₁`, of norm at most `2`
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
    2 (norm_toLp_inter_fst_le h₀ h₁)

theorem coeFn_lebesgueInterToLp (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (x : (lebesgue 𝕜 E μ p₀ p₁).inter) :
    ⇑(lebesgueInterToLp h₀ h₁ x) =ᵐ[μ] ⇑(x : Lp E p₀ μ × Lp E p₁ μ).1 :=
  (memLp_inter_fst h₀ h₁ x).coeFn_toLp

theorem norm_lebesgueInterToLp_le (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁)
    (x : (lebesgue 𝕜 E μ p₀ p₁).inter) : ‖lebesgueInterToLp h₀ h₁ x‖ ≤ 2 * ‖x‖ :=
  norm_toLp_inter_fst_le h₀ h₁ x

/-- The inclusion `L^{p₀} ∩ L^{p₁} → Lᵖ` is compatible with the embeddings into `L¹ + L^∞`. -/
@[simp]
theorem ofLp_lebesgueInterToLp (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (x : (lebesgue 𝕜 E μ p₀ p₁).inter) :
    (L1AddLinfty.ofLp (lebesgueInterToLp h₀ h₁ x) : L1AddLinfty 𝕜 E μ) =
      L1AddLinfty.ofLp (x : Lp E p₀ μ × Lp E p₁ μ).1 :=
  L1AddLinfty.ofLp_eq_ofLp_iff.2 (coeFn_lebesgueInterToLp h₀ h₁ x)

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
