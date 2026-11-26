/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Topology.ApproximateUnit

/-!
# Characters along approximate units

Every nonunital character `φ : A →ₙₐ[𝕜] 𝕜` of a normed algebra with summable geometric series
(in particular, any Banach algebra) is automatically continuous and contractive
(`NonUnitalAlgHom.instContinuousLinearMapClass`, `NonUnitalAlgHom.norm_toStrongDual_le`). When
`A` admits a left or right approximate identity—or a two-sided `Filter.IsApproximateUnit`—a nonzero
character tends to `1` along that filter, and if the approximate unit is eventually bounded by `1`,
then `‖φ.toStrongDual‖ = 1`.

## Main results

* `NonUnitalAlgHom.tendsto_one_of_tendsto_mul_right`,
  `NonUnitalAlgHom.tendsto_one_of_tendsto_mul_left`,
  `NonUnitalAlgHom.tendsto_one_of_isApproximateUnit`: a nonzero character tends to `1` along any
  one-sided approximate identity or `Filter.IsApproximateUnit`.
* `NonUnitalAlgHom.norm_toStrongDual_eq_one_of_tendsto_one`,
  `NonUnitalAlgHom.norm_toStrongDual_eq_one_of_tendsto_mul_right`,
  `NonUnitalAlgHom.norm_toStrongDual_eq_one_of_tendsto_mul_left`,
  `NonUnitalAlgHom.norm_toStrongDual_eq_one_of_isApproximateUnit`: a nonzero character has operator
  norm `1` when the approximate identity is eventually contained in the closed unit ball.
-/

public section

open Filter Topology

namespace NonUnitalAlgHom

section NormedField

variable {𝕜 A F : Type*} [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [HasSummableGeomSeries A]

section Class

variable [FunLike F A 𝕜] [NonUnitalAlgHomClass F 𝕜 A 𝕜]

/-- If `e * a → a` along `l` for an element `a` not in the kernel of a character `φ`, then
`φ e → 1` along `l`. -/
theorem tendsto_one_of_tendsto_mul_right {l : Filter A} {φ : F} {a : A} (ha : φ a ≠ 0)
    (he : Tendsto (· * a) l (𝓝 a)) : Tendsto φ l (𝓝 1) := by
  have hmul : Tendsto (fun e ↦ φ e * φ a) l (𝓝 (φ a)) := by
    simpa only [Function.comp_def, map_mul] using ((map_continuous φ).tendsto a).comp he
  simpa only [Function.comp_def, mul_inv_cancel_right₀ ha, mul_inv_cancel₀ ha] using
    ((continuous_mul_const (φ a)⁻¹).tendsto (φ a)).comp hmul

/-- If `a * e → a` along `l` for an element `a` not in the kernel of a character `φ`, then
`φ e → 1` along `l`. -/
theorem tendsto_one_of_tendsto_mul_left {l : Filter A} {φ : F} {a : A} (ha : φ a ≠ 0)
    (he : Tendsto (a * ·) l (𝓝 a)) : Tendsto φ l (𝓝 1) := by
  have hmul : Tendsto (fun e ↦ φ a * φ e) l (𝓝 (φ a)) := by
    simpa only [Function.comp_def, map_mul] using ((map_continuous φ).tendsto a).comp he
  simpa only [Function.comp_def, inv_mul_cancel_left₀ ha, inv_mul_cancel₀ ha] using
    ((continuous_const_mul (φ a)⁻¹).tendsto (φ a)).comp hmul

end Class

/-- Along any two-sided approximate unit `l`, a nonzero character `φ` tends to `1`. -/
theorem tendsto_one_of_isApproximateUnit {l : Filter A} (hl : l.IsApproximateUnit)
    {φ : A →ₙₐ[𝕜] 𝕜} (hφ : φ ≠ 0) : Tendsto φ l (𝓝 1) := by
  obtain ⟨a, ha⟩ : ∃ a, φ a ≠ 0 := by simpa [DFunLike.ext_iff] using hφ
  exact tendsto_one_of_tendsto_mul_right ha (hl.tendsto_mul_right a)

end NormedField

section NontriviallyNormedField

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [HasSummableGeomSeries A]

/-- If a character `φ` tends to `1` along a proper filter `l` eventually contained in the closed
unit ball, then `φ` has operator norm `1`. -/
theorem norm_toStrongDual_eq_one_of_tendsto_one {l : Filter A} [l.NeBot]
    {φ : A →ₙₐ[𝕜] 𝕜} (ht : Tendsto φ l (𝓝 1)) (hb : ∀ᶠ e in l, ‖e‖ ≤ 1) :
    ‖φ.toStrongDual‖ = 1 := by
  refine le_antisymm (norm_toStrongDual_le φ) ?_
  have h1 : Tendsto (fun e ↦ ‖φ e‖) l (𝓝 1) := by simpa only [norm_one] using ht.norm
  refine le_of_tendsto h1 ?_
  filter_upwards [hb] with e he
  exact (φ.toStrongDual.le_opNorm e).trans <|
    (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (mul_one _)

/-- Every nonzero character of a normed algebra with summable geometric series admitting a left
approximate identity bounded by `1` has operator norm `1`. -/
theorem norm_toStrongDual_eq_one_of_tendsto_mul_right {l : Filter A} [l.NeBot]
    {φ : A →ₙₐ[𝕜] 𝕜} (hφ : φ ≠ 0) (hb : ∀ᶠ e in l, ‖e‖ ≤ 1)
    (he : ∀ a, Tendsto (· * a) l (𝓝 a)) : ‖φ.toStrongDual‖ = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, φ a ≠ 0 := by simpa [DFunLike.ext_iff] using hφ
  exact norm_toStrongDual_eq_one_of_tendsto_one
    (tendsto_one_of_tendsto_mul_right ha (he a)) hb

/-- Every nonzero character of a normed algebra with summable geometric series admitting a right
approximate identity bounded by `1` has operator norm `1`. -/
theorem norm_toStrongDual_eq_one_of_tendsto_mul_left {l : Filter A} [l.NeBot]
    {φ : A →ₙₐ[𝕜] 𝕜} (hφ : φ ≠ 0) (hb : ∀ᶠ e in l, ‖e‖ ≤ 1)
    (he : ∀ a, Tendsto (a * ·) l (𝓝 a)) : ‖φ.toStrongDual‖ = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, φ a ≠ 0 := by simpa [DFunLike.ext_iff] using hφ
  exact norm_toStrongDual_eq_one_of_tendsto_one
    (tendsto_one_of_tendsto_mul_left ha (he a)) hb

/-- Every nonzero character of a normed algebra with summable geometric series admitting a
two-sided approximate unit eventually bounded by `1` has operator norm `1`. -/
theorem norm_toStrongDual_eq_one_of_isApproximateUnit {l : Filter A} (hl : l.IsApproximateUnit)
    {φ : A →ₙₐ[𝕜] 𝕜} (hφ : φ ≠ 0) (hb : ∀ᶠ e in l, ‖e‖ ≤ 1) :
    ‖φ.toStrongDual‖ = 1 :=
  have := hl.neBot
  norm_toStrongDual_eq_one_of_tendsto_one (tendsto_one_of_isApproximateUnit hl hφ) hb

end NontriviallyNormedField

end NonUnitalAlgHom
