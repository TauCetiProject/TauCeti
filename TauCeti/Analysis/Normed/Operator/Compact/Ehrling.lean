/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Ehrling's inequality

Let `i : X → Y` be a compact linear operator and `j : Y → Z` an injective continuous linear map.
Ehrling's inequality says that the `Y`-norm of `i x` is bounded by an arbitrarily small multiple
of the `X`-norm of `x` plus a multiple of the weaker `Z`-norm of `j (i x)`: for every `ε > 0`
there is `C` with

`‖i x‖ ≤ ε * ‖x‖ + C * ‖j (i x)‖` for all `x`.

The typical instance is a chain of Sobolev spaces `W^{k,p} ⊆ W^{l,p} ⊆ Lᵖ` on a compact base with
`k > l`, where the first inclusion is compact by Rellich's theorem. The inequality is then the
interpolation bound `‖u‖_{W^{l,p}} ≤ ε ‖u‖_{W^{k,p}} + C_ε ‖u‖_{Lᵖ}`.

Its main use is in a priori estimates. An estimate `‖x‖ ≤ C * ‖T x‖ + ‖i x‖` whose error term
is measured in an intermediate norm can be rewritten with the error term in any weaker norm
(`IsCompactOperator.exists_norm_le_of_compact_estimate`). For elliptic estimates on a compact
base this replaces the lower-order Sobolev norm by any weaker norm of the Sobolev scale.

No completeness is assumed, the domain and the intermediate space may be seminormed, and the
scalar field is any nontrivially normed field.

## Main declarations

* `IsCompactOperator.exists_norm_le_mul_norm_add_mul_norm`: Ehrling's inequality.
* `IsCompactOperator.exists_norm_le_of_compact_estimate`: weakening the norm of the error term
  in an a priori estimate.

## References

* G. Ehrling, *On a type of eigenvalue problem for certain elliptic differential operators*,
  Math. Scand. **2** (1954), 267–285.
* J.-L. Lions, *Quelques méthodes de résolution des problèmes aux limites non linéaires*,
  Dunod, 1969, Chapitre 1, Lemme 5.1.
-/

public section

namespace IsCompactOperator

open Filter
open scoped Topology

variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable {i : X →ₗ[𝕜] Y} {j : Y →L[𝕜] Z}

/-- **Ehrling's inequality.** If `i : X → Y` is a compact operator and `j : Y → Z` is an injective
continuous linear map, then for every `ε > 0` there is `C ≥ 0` with
`‖i x‖ ≤ ε * ‖x‖ + C * ‖j (i x)‖` for all `x`. -/
theorem exists_norm_le_mul_norm_add_mul_norm (hi : IsCompactOperator i)
    (hj : Function.Injective j) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖i x‖ ≤ ε * ‖x‖ + C * ‖j (i x)‖ := by
  by_contra! hcon
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm 𝕜
  -- A failure of the bound with constant `n + 1`, rescaled so that `i x` lies in a fixed shell.
  have hshell : ∀ n : ℕ, ∃ x : X, ‖x‖ ≤ ε⁻¹ ∧ ‖a‖⁻¹ ≤ ‖i x‖ ∧
      ‖j (i x)‖ ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨u, hu⟩ := hcon (n + 1) (by positivity)
    have hu0 : ‖i u‖ ≠ 0 := (lt_of_le_of_lt (by positivity) hu).ne'
    obtain ⟨d, -, hdlt, hdge, -⟩ := rescale_to_shell_semi_normed ha one_pos hu0
    rw [norm_smul] at hdlt
    have hsmul : ‖d‖ * (ε * ‖u‖ + (n + 1) * ‖j (i u)‖) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hu.le (norm_nonneg d)).trans hdlt.le
    have hdu : 0 ≤ ‖d‖ * (ε * ‖u‖) := by positivity
    have hdj : 0 ≤ ‖d‖ * ((n + 1) * ‖j (i u)‖) := by positivity
    refine ⟨d • u, ?_, by rwa [map_smul, ← one_div], ?_⟩
    · rw [norm_smul, inv_eq_one_div, le_div_iff₀' hε]
      nlinarith
    · rw [map_smul, map_smul, norm_smul, le_div_iff₀ (by positivity)]
      nlinarith
  choose v hvbound hvge hjv using hshell
  obtain ⟨y, ψ, hψ, hy⟩ := hi.exists_subseq_tendsto hvbound
  have hjy : j y = 0 := tendsto_nhds_unique ((j.continuous.tendsto y).comp hy)
    (squeeze_zero_norm (fun n ↦ hjv (ψ n))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop))
  have hy0 : y = 0 := hj (by rw [hjy, map_zero])
  have hyge : ‖a‖⁻¹ ≤ ‖y‖ := ge_of_tendsto' hy.norm fun n ↦ hvge (ψ n)
  rw [hy0, norm_zero] at hyge
  exact hyge.not_gt (by positivity)

/-- **Weakening the error term of an a priori estimate.** If `i : X → Y` is compact,
`j : Y → Z` is injective and `‖x‖ ≤ C * ‖T x‖ + ‖i x‖` for all `x`, then the error term may be
measured in the weaker norm of `Z`: there is `D ≥ 0` with `‖x‖ ≤ 2 * C * ‖T x‖ + D * ‖j (i x)‖`
for all `x`. -/
theorem exists_norm_le_of_compact_estimate {F : Type*} [SeminormedAddCommGroup F]
    (hi : IsCompactOperator i) (hj : Function.Injective j) {T : X → F} {C : ℝ}
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖i x‖) :
    ∃ D, 0 ≤ D ∧ ∀ x, ‖x‖ ≤ 2 * C * ‖T x‖ + D * ‖j (i x)‖ := by
  obtain ⟨D, hD, h⟩ := hi.exists_norm_le_mul_norm_add_mul_norm hj (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨2 * D, by positivity, fun x ↦ by linarith [hbound x, h x]⟩

end IsCompactOperator
