/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The star operation on `Lp`

Mathlib equips `Lp R p μ` with the pointwise involution `star` when `R` is a normed star group.
This file records that this involution is additive, isometric and, over a star module,
conjugate-linear. Thus `Lp R p μ` is a star additive monoid and a star module for every exponent
`p`, and a normed star group for `1 ≤ p`. Over `ℂ` the involution is pointwise complex
conjugation of classes of functions; these laws are part of the C⋆-algebra structure of `L∞`.
Over any `RCLike` field, a class almost everywhere equal to a real-valued function is fixed by
`star` (`MeasureTheory.Lp.star_eq_self_of_ae_eq_ofReal`).

In addition, over any normed field `𝕜` with a norm-preserving additive star involution, pointwise
scalar multiplication by `star ∘ f` preserves almost-everywhere strong measurability and `MemLp`
membership whenever `u : α → E` is almost-everywhere strongly measurable, without requiring any
measurability hypothesis on `f` (`MeasureTheory.aestronglyMeasurable_star_smul_iff`,
`MeasureTheory.memLp_star_smul_iff`).
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α R 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

instance instStarAddMonoid : StarAddMonoid (Lp R p μ) where
  star_add f g := by
    ext
    filter_upwards [coeFn_star (f + g), coeFn_add f g, coeFn_star f, coeFn_star g,
      coeFn_add (star f) (star g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₂, h₃, h₄, h₅, Pi.star_apply, Pi.add_apply, star_add]

instance instNormedStarGroup [Fact (1 ≤ p)] : NormedStarGroup (Lp R p μ) where
  norm_star_le f := by rw [norm_def, norm_def, eLpNorm_congr_ae (coeFn_star f), eLpNorm_star]

instance instStarModule [NormedRing 𝕜] [Star 𝕜] [Module 𝕜 R] [IsBoundedSMul 𝕜 R]
    [StarModule 𝕜 R] : StarModule 𝕜 (Lp R p μ) where
  star_smul c f := by
    ext
    filter_upwards [coeFn_star (c • f), coeFn_smul c f, coeFn_smul (star c) (star f),
      coeFn_star f] with x h₁ h₂ h₃ h₄
    simp only [h₁, h₂, h₃, h₄, Pi.star_apply, Pi.smul_apply, star_smul]

/-- A class almost everywhere equal to a real-valued function is real: `star f = f`. -/
theorem star_eq_self_of_ae_eq_ofReal [RCLike 𝕜] {f : Lp 𝕜 p μ} {u : α → ℝ}
    (hf : f =ᵐ[μ] fun x ↦ (u x : 𝕜)) : star f = f := by
  ext
  filter_upwards [coeFn_star f, hf] with x h₁ h₂
  simp [h₁, h₂]

end MeasureTheory.Lp

namespace MeasureTheory

section StarSMul

variable {𝕜 E : Type*} [NormedField 𝕜] [StarAddMonoid 𝕜] [NormedStarGroup 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private def starPairMap (q : {r : E × E // ∃ c : 𝕜, r.2 = c • r.1}) : E :=
  letI := Classical.propDecidable
  if q.1.1 = 0 then 0 else star q.2.choose • q.1.1

omit [NormedStarGroup 𝕜] in
private theorem starPairMap_apply {x : E} {c : 𝕜}
    (h : (x, c • x) ∈ {r : E × E | ∃ c : 𝕜, r.2 = c • r.1}) :
    starPairMap (𝕜 := 𝕜) ⟨(x, c • x), h⟩ = star c • x := by
  dsimp [starPairMap]
  split_ifs with hx
  · simp [hx]
  · rw [smul_left_injective 𝕜 hx h.choose_spec.symm]

private theorem continuous_starPairMap :
    Continuous (starPairMap (𝕜 := 𝕜) (E := E)) := by
  rw [Metric.continuous_iff]
  rintro ⟨⟨x₀, y₀⟩, hp₀⟩ ε hε
  obtain ⟨c₀, rfl⟩ : ∃ c₀ : 𝕜, y₀ = c₀ • x₀ := hp₀
  have hC : 0 < 1 + 2 * ‖c₀‖ := by positivity
  refine ⟨ε / (1 + 2 * ‖c₀‖), div_pos hε hC, ?_⟩
  rintro ⟨⟨x, y⟩, hp⟩ hdist
  obtain ⟨c, rfl⟩ : ∃ c : 𝕜, y = c • x := hp
  rw [starPairMap_apply, starPairMap_apply, _root_.dist_eq_norm]
  have hd : max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ < ε / (1 + 2 * ‖c₀‖) := by
    simpa [Subtype.dist_eq, Prod.dist_eq, _root_.dist_eq_norm] using hdist
  have hx : ‖x - x₀‖ ≤ max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := le_max_left _ _
  have hy : ‖c • x - c₀ • x₀‖ ≤ max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := le_max_right _ _
  have hdiff : (c - c₀) • x = (c • x - c₀ • x₀) - c₀ • (x - x₀) := by
    rw [sub_smul, smul_sub, sub_sub_sub_cancel_right]
  have hbound : ‖star c • x - star c₀ • x₀‖ ≤
      (1 + 2 * ‖c₀‖) * max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := by
    calc ‖star c • x - star c₀ • x₀‖
        = ‖(star c - star c₀) • x + star c₀ • (x - x₀)‖ := by
          rw [sub_smul, smul_sub, sub_add_sub_cancel]
      _ ≤ ‖(star c - star c₀) • x‖ + ‖star c₀ • (x - x₀)‖ := norm_add_le _ _
      _ = ‖star (c - c₀)‖ * ‖x‖ + ‖star c₀‖ * ‖x - x₀‖ := by
          rw [← star_sub, norm_smul, norm_smul]
      _ = ‖(c - c₀) • x‖ + ‖c₀‖ * ‖x - x₀‖ := by
          rw [norm_star, norm_star, ← norm_smul]
      _ ≤ (‖c • x - c₀ • x₀‖ + ‖c₀ • (x - x₀)‖) + ‖c₀‖ * ‖x - x₀‖ := by
          gcongr; rw [hdiff]; exact norm_sub_le _ _
      _ = ‖c • x - c₀ • x₀‖ + 2 * ‖c₀‖ * ‖x - x₀‖ := by
          rw [norm_smul]; ring
      _ ≤ 1 * max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ +
          2 * ‖c₀‖ * max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := by
          gcongr; linarith
      _ = (1 + 2 * ‖c₀‖) * max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := by ring
  exact hbound.trans_lt ((lt_div_iff₀' hC).1 hd)

section Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Over a normed field `𝕜` with a norm-preserving additive star involution, if `u : α → E` and
`t ↦ f t • u t` are almost-everywhere strongly measurable, then so is `t ↦ star (f t) • u t`
(with no measurability hypothesis on `f`). -/
theorem aestronglyMeasurable_star_smul_of_aestronglyMeasurable {f : α → 𝕜} {u : α → E}
    (hu : AEStronglyMeasurable u μ)
    (hfu : AEStronglyMeasurable (fun t ↦ f t • u t) μ) :
    AEStronglyMeasurable (fun t ↦ star (f t) • u t) μ := by
  let g : α → {r : E × E // ∃ c : 𝕜, r.2 = c • r.1} :=
    fun t ↦ ⟨(u t, f t • u t), f t, rfl⟩
  have hg : AEStronglyMeasurable g μ :=
    Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.1 (hu.prodMk hfu)
  exact (continuous_starPairMap.comp_aestronglyMeasurable hg).congr
    (Filter.Eventually.of_forall fun _ ↦ starPairMap_apply _)

/-- Over a normed field `𝕜` with a norm-preserving additive star involution, for an
almost-everywhere strongly measurable vector function `u : α → E`, `t ↦ star (f t) • u t` is
almost-everywhere strongly measurable if and only if `t ↦ f t • u t` is. -/
theorem aestronglyMeasurable_star_smul_iff {f : α → 𝕜} {u : α → E}
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun t ↦ star (f t) • u t) μ ↔
      AEStronglyMeasurable (fun t ↦ f t • u t) μ :=
  ⟨fun h ↦ by
      simpa only [Pi.star_apply, star_star] using
        aestronglyMeasurable_star_smul_of_aestronglyMeasurable (f := star f) hu h,
    aestronglyMeasurable_star_smul_of_aestronglyMeasurable hu⟩

/-- Over a normed field `𝕜` with a norm-preserving additive star involution, if `u : α → E` is
almost-everywhere strongly measurable and `t ↦ f t • u t` belongs to `MemLp · p μ`, then
`t ↦ star (f t) • u t` also belongs to `MemLp · p μ` (with no measurability hypothesis on `f`). -/
theorem memLp_star_smul_of_memLp {p : ℝ≥0∞} {f : α → 𝕜} {u : α → E}
    (hu : AEStronglyMeasurable u μ) (hfu : MemLp (fun t ↦ f t • u t) p μ) :
    MemLp (fun t ↦ star (f t) • u t) p μ := by
  refine hfu.of_le_mul (c := 1)
    (aestronglyMeasurable_star_smul_of_aestronglyMeasurable hu hfu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [one_mul, norm_smul, norm_smul, norm_star]

/-- Over a normed field `𝕜` with a norm-preserving additive star involution, for an
almost-everywhere strongly measurable vector function `u : α → E`, `t ↦ star (f t) • u t`
belongs to `MemLp · p μ` if and only if `t ↦ f t • u t` does. -/
theorem memLp_star_smul_iff {p : ℝ≥0∞} {f : α → 𝕜} {u : α → E}
    (hu : AEStronglyMeasurable u μ) :
    MemLp (fun t ↦ star (f t) • u t) p μ ↔ MemLp (fun t ↦ f t • u t) p μ :=
  ⟨fun h ↦ by
      simpa only [Pi.star_apply, star_star] using memLp_star_smul_of_memLp (f := star f) hu h,
    memLp_star_smul_of_memLp hu⟩

end Measure

end StarSMul

end MeasureTheory
