/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Character.Basic
public import TauCeti.Topology.ApproximateUnit

/-!
# Nonunital characters and approximate units

On a complete normed algebra `A` over a normed field `𝕜`, every algebraic nonunital character
`φ : A →ₙₐ[𝕜] 𝕜` is automatically contractive and hence continuous, bundled as
`φ.toContinuousLinearMap : StrongDual 𝕜 A` with `‖φ.toContinuousLinearMap‖ ≤ 1` in
`TauCeti.Analysis.Normed.Algebra.Character.Basic`. This file determines the behavior of `φ` along
approximate identities:

* Along any left, right, or two-sided approximate identity, a nonzero character converges to `1`:
  choosing `a` with `φ a ≠ 0`, continuity gives `φ (e * a) = φ e * φ a → φ a`, and canceling `φ a`
  in `𝕜` yields `φ e → 1`.
* Consequently, when `A` admits a left, right, or two-sided approximate identity eventually in the
  closed unit ball, every nonzero algebraic character `φ : A →ₙₐ[𝕜] 𝕜` has operator norm equal to
  `1` (`NonUnitalAlgHom.norm_toContinuousLinearMap_of_tendsto_mul_right`,
  `NonUnitalAlgHom.norm_toContinuousLinearMap_of_tendsto_mul_left`,
  `NonUnitalAlgHom.norm_toContinuousLinearMap_of_isApproximateUnit`).

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., §VII.9, Proposition 9.6.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
-/

public section

open Filter Topology

namespace NonUnitalAlgHom

section NormedField

variable {𝕜 A F : Type*} [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A] [FunLike F A 𝕜] [NonUnitalAlgHomClass F 𝕜 A 𝕜]

/-- Along any left approximate identity `e i * a → a`, a nonzero character `φ` tends to `1`. -/
theorem tendsto_one_of_tendsto_mul_right {ι : Type*} {l : Filter ι} {e : ι → A} {φ : F}
    (hφ : ∃ a, φ a ≠ 0) (he : ∀ a, Tendsto (fun i => e i * a) l (𝓝 a)) :
    Tendsto (fun i => φ (e i)) l (𝓝 1) := by
  obtain ⟨a, ha⟩ := hφ
  have hmul : Tendsto (fun i => φ (e i) * φ a) l (𝓝 (φ a)) := by
    simpa only [Function.comp_def, map_mul] using ((map_continuous φ).tendsto a).comp (he a)
  simpa only [mul_inv_cancel_right₀ ha, mul_inv_cancel₀ ha] using hmul.mul_const (φ a)⁻¹

/-- Along any right approximate identity `a * e i → a`, a nonzero character `φ` tends to `1`. -/
theorem tendsto_one_of_tendsto_mul_left {ι : Type*} {l : Filter ι} {e : ι → A} {φ : F}
    (hφ : ∃ a, φ a ≠ 0) (he : ∀ a, Tendsto (fun i => a * e i) l (𝓝 a)) :
    Tendsto (fun i => φ (e i)) l (𝓝 1) := by
  obtain ⟨a, ha⟩ := hφ
  have hmul : Tendsto (fun i => φ a * φ (e i)) l (𝓝 (φ a)) := by
    simpa only [Function.comp_def, map_mul] using ((map_continuous φ).tendsto a).comp (he a)
  simpa only [inv_mul_cancel_left₀ ha, inv_mul_cancel₀ ha] using hmul.const_mul (φ a)⁻¹

/-- Along any two-sided approximate unit `l`, a nonzero character `φ` tends to `1`. -/
theorem tendsto_one_of_isApproximateUnit {l : Filter A} (hl : l.IsApproximateUnit) {φ : F}
    (hφ : ∃ a, φ a ≠ 0) : Tendsto φ l (𝓝 1) :=
  tendsto_one_of_tendsto_mul_right hφ hl.tendsto_mul_right

end NormedField

section NontriviallyNormedField

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A]

/-- If `A` has a left approximate identity eventually in the closed unit ball, every nonzero
character `φ : A →ₙₐ[𝕜] 𝕜` has operator norm `1`. -/
theorem norm_toContinuousLinearMap_of_tendsto_mul_right {ι : Type*} {l : Filter ι} [l.NeBot]
    {e : ι → A} (he1 : ∀ᶠ i in l, ‖e i‖ ≤ 1) (he : ∀ a, Tendsto (fun i => e i * a) l (𝓝 a))
    {φ : A →ₙₐ[𝕜] 𝕜} (hφ : φ ≠ 0) : ‖φ.toContinuousLinearMap‖ = 1 := by
  have hφ' : ∃ a, φ a ≠ 0 := by
    rwa [ne_eq, DFunLike.ext_iff, not_forall] at hφ
  refine le_antisymm (norm_toContinuousLinearMap_le φ) ?_
  have hlim : Tendsto (fun i => ‖φ (e i)‖) l (𝓝 1) := by
    simpa only [norm_one] using (tendsto_one_of_tendsto_mul_right hφ' he).norm
  refine le_of_tendsto hlim (he1.mono fun i hi => ?_)
  calc ‖φ (e i)‖ = ‖φ.toContinuousLinearMap (e i)‖ := by rw [toContinuousLinearMap_apply]
    _ ≤ ‖φ.toContinuousLinearMap‖ * ‖e i‖ := φ.toContinuousLinearMap.le_opNorm (e i)
    _ ≤ ‖φ.toContinuousLinearMap‖ := mul_le_of_le_one_right (norm_nonneg _) hi

/-- If `A` has a right approximate identity eventually in the closed unit ball, every nonzero
character `φ : A →ₙₐ[𝕜] 𝕜` has operator norm `1`. -/
theorem norm_toContinuousLinearMap_of_tendsto_mul_left {ι : Type*} {l : Filter ι} [l.NeBot]
    {e : ι → A} (he1 : ∀ᶠ i in l, ‖e i‖ ≤ 1) (he : ∀ a, Tendsto (fun i => a * e i) l (𝓝 a))
    {φ : A →ₙₐ[𝕜] 𝕜} (hφ : φ ≠ 0) : ‖φ.toContinuousLinearMap‖ = 1 := by
  have hφ' : ∃ a, φ a ≠ 0 := by
    rwa [ne_eq, DFunLike.ext_iff, not_forall] at hφ
  refine le_antisymm (norm_toContinuousLinearMap_le φ) ?_
  have hlim : Tendsto (fun i => ‖φ (e i)‖) l (𝓝 1) := by
    simpa only [norm_one] using (tendsto_one_of_tendsto_mul_left hφ' he).norm
  refine le_of_tendsto hlim (he1.mono fun i hi => ?_)
  calc ‖φ (e i)‖ = ‖φ.toContinuousLinearMap (e i)‖ := by rw [toContinuousLinearMap_apply]
    _ ≤ ‖φ.toContinuousLinearMap‖ * ‖e i‖ := φ.toContinuousLinearMap.le_opNorm (e i)
    _ ≤ ‖φ.toContinuousLinearMap‖ := mul_le_of_le_one_right (norm_nonneg _) hi

/-- If `A` has a two-sided approximate unit eventually in the closed unit ball, every nonzero
character `φ : A →ₙₐ[𝕜] 𝕜` has operator norm `1`. -/
theorem norm_toContinuousLinearMap_of_isApproximateUnit {l : Filter A} (hl : l.IsApproximateUnit)
    (hl1 : ∀ᶠ u in l, ‖u‖ ≤ 1) {φ : A →ₙₐ[𝕜] 𝕜} (hφ : φ ≠ 0) :
    ‖φ.toContinuousLinearMap‖ = 1 := by
  have := hl.neBot
  exact norm_toContinuousLinearMap_of_tendsto_mul_right hl1 hl.tendsto_mul_right hφ

end NontriviallyNormedField

end NonUnitalAlgHom
