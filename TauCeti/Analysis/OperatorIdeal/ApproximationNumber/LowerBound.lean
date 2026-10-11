/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Lower bounds for approximation numbers from coercive subspaces

The approximation number `aₙ(T)` is an infimum, so upper bounds come from exhibiting a single
approximant of rank at most `n`. Lower bounds come from subspaces on which `T` is bounded below:
if `V` is a subspace of rank greater than `n` and `c ‖x‖ ≤ ‖T x‖` for every `x ∈ V`, then
`c ≤ aₙ(T)`. Indeed, any map `R` of rank at most `n` vanishes at some nonzero `x ∈ V`, and then
`c ‖x‖ ≤ ‖T x‖ = ‖(T - R) x‖ ≤ ‖T - R‖ ‖x‖`.

This is the easy half of the min–max description of approximation numbers. The file proves it in
three forms: for a subspace of rank greater than `n`, for the span of a linearly independent
family of more than `n` vectors, and, over `ℝ` or `ℂ`, with the lower bound required only on the
unit vectors of the subspace. No completeness or inner product is needed.

## Main declarations

* `ContinuousLinearMap.le_singularValue_of_lt_rank`: a lower bound `c ‖x‖ ≤ ‖T x‖` on a subspace
  of rank greater than `n` gives `c ≤ aₙ(T)`.
* `ContinuousLinearMap.le_singularValue_of_linearIndependent`: the same for the span of a linearly
  independent family of more than `n` vectors.
* `ContinuousLinearMap.le_singularValue_of_lt_rank_of_norm_eq_one`: the same with the lower bound
  `c ≤ ‖T x‖` on unit vectors only.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

section NormedSpace

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Coercive-subspace lower bound.** If `T` satisfies `c ‖x‖ ≤ ‖T x‖` on a subspace `V` of rank
greater than `n`, then `c ≤ aₙ(T)`. -/
theorem le_singularValue_of_lt_rank {T : E →L[𝕜] F} {n : ℕ} {V : Submodule 𝕜 E}
    (hV : n < Module.rank 𝕜 V) {c : ℝ} (hc : ∀ x ∈ V, c * ‖x‖ ≤ ‖T x‖) :
    c ≤ T.singularValue n := by
  refine (Real.le_coe_toNNReal c).trans <| NNReal.coe_le_coe.mpr <|
    le_singularValue_iff.mpr fun R hR ↦ ?_
  rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm]
  -- The restriction of `R` to `V` has rank at most `n < rank V`, so it is not injective.
  obtain ⟨x, hxV, hx0, hRx⟩ : ∃ x ∈ V, x ≠ 0 ∧ R x = 0 := by
    by_contra! h
    have hinj : Function.Injective ((R : E →ₗ[𝕜] F) ∘ₗ V.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨x, hx⟩ hRx
      by_contra hne
      exact h x hx (by simpa using hne) hRx
    have hle : Module.rank 𝕜 (LinearMap.range ((R : E →ₗ[𝕜] F) ∘ₗ V.subtype)) ≤ n :=
      (Submodule.rank_mono (LinearMap.range_comp_le_range _ _)).trans hR
    rw [← Cardinal.lift_le_nat_iff, lift_rank_range_of_injective _ hinj,
      Cardinal.lift_le_nat_iff] at hle
    exact hV.not_ge hle
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hx0)
  calc c * ‖x‖ ≤ ‖T x‖ := hc x hxV
    _ = ‖(T - R) x‖ := by simp [hRx]
    _ ≤ ‖T - R‖ * ‖x‖ := (T - R).le_opNorm x

/-- **Independent-family lower bound.** If `T` satisfies `c ‖x‖ ≤ ‖T x‖` on the span of a linearly
independent family of more than `n` vectors, then `c ≤ aₙ(T)`. -/
theorem le_singularValue_of_linearIndependent {T : E →L[𝕜] F} {ι : Type*} [Fintype ι]
    {v : ι → E} (hv : LinearIndependent 𝕜 v) {n : ℕ} (hn : n < Fintype.card ι) {c : ℝ}
    (hc : ∀ x ∈ Submodule.span 𝕜 (Set.range v), c * ‖x‖ ≤ ‖T x‖) : c ≤ T.singularValue n := by
  have := Module.Finite.span_of_finite 𝕜 (Set.finite_range v)
  refine le_singularValue_of_lt_rank ?_ hc
  rw [← Module.finrank_eq_rank, finrank_span_eq_card hv]
  exact_mod_cast hn

end NormedSpace

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Unit-vector lower bound.** If `c ≤ ‖T x‖` for every unit vector `x` of a subspace of rank
greater than `n`, then `c ≤ aₙ(T)`. -/
theorem le_singularValue_of_lt_rank_of_norm_eq_one {T : E →L[𝕜] F} {n : ℕ}
    {V : Submodule 𝕜 E} (hV : n < Module.rank 𝕜 V) {c : ℝ}
    (hc : ∀ x ∈ V, ‖x‖ = 1 → c ≤ ‖T x‖) : c ≤ T.singularValue n := by
  refine le_singularValue_of_lt_rank hV fun x hxV ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  -- Apply the hypothesis to the unit vector `‖x‖⁻¹ • x` of `V`.
  have h := hc _ (V.smul_mem (‖x‖⁻¹ : 𝕜) hxV) (norm_smul_inv_norm hx0)
  rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm] at h
  rwa [le_inv_mul_iff₀ (norm_pos_iff.mpr hx0), mul_comm] at h

end RCLike

end ContinuousLinearMap
