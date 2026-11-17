/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable

/-!
# The star operation on `Lp`

Mathlib equips `Lp R p μ` with the pointwise involution `star` when `R` is a normed star group.
This file records that this involution is additive, isometric and, over a star module,
conjugate-linear. Thus `Lp R p μ` is a star additive monoid and a star module for every exponent
`p`, and a normed star group for `1 ≤ p`. Over `ℂ` the involution is pointwise complex
conjugation of classes of functions; these laws are part of the C⋆-algebra structure of `L∞`.
Over any `RCLike` field, a class almost everywhere equal to a real-valued function is fixed by
`star` (`MeasureTheory.Lp.star_eq_self_of_ae_eq_ofReal`).

In addition, over any normed field `𝕜` with a norm-preserving additive star involution and a normed
`𝕜`-space `E`, pointwise scalar multiplication by `star ∘ f` preserves `MemLp` membership whenever
`u : α → E` is almost-everywhere strongly measurable, without requiring any measurability
hypothesis on `f` (`MeasureTheory.memLp_star_smul_of_memLp`, `MeasureTheory.memLp_star_smul_iff`).
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
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {α : Type*} [MeasurableSpace α] {μ : Measure α}

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

end StarSMul

end MeasureTheory
