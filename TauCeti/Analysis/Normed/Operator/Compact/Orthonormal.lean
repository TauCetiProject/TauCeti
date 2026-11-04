/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact operators on orthonormal families

A compact operator cannot send a bounded family onto large multiples of an orthonormal family. If
`T (v i) = μ i • w i` with `‖v i‖ ≤ C` and `w` orthonormal, then for every `δ > 0` only finitely
many indices satisfy `δ ≤ ‖μ i‖`; equivalently `μ i → 0` along the cofinite filter.

The special case `v = w` concerns an orthonormal family of eigenvectors of a compact operator:
only finitely many of them have an eigenvalue of norm at least `δ`, so the eigenvalues tend to
zero. No symmetry, completeness or spanning hypothesis is needed. This is the finiteness behind
spectral cutoffs of operators with compact resolvent: the compact resolvent `R(z)` acts on an
eigenvector for the eigenvalue `λ` as multiplication by `(z - λ)⁻¹`.

The proof compares distances: for distinct `i` and `j`, pairing `μ i • w i - μ j • w j` with `w i`
shows that its norm is at least `‖μ i‖`. Infinitely many large coefficients would therefore give a
bounded sequence whose images stay uniformly separated, which compactness forbids
(`IsCompactOperator.exists_dist_lt_of_norm_le`).

## Main results

* `IsCompactOperator.finite_setOf_le_norm_of_apply_eq_smul`: if `T (v i) = μ i • w i` with `v`
  bounded and `w` orthonormal, only finitely many `i` have `δ ≤ ‖μ i‖`.
* `IsCompactOperator.tendsto_cofinite_of_apply_eq_smul`: in that situation `μ i → 0` along the
  cofinite filter.
* `IsCompactOperator.finite_setOf_le_norm_of_orthonormal`,
  `IsCompactOperator.tendsto_cofinite_of_orthonormal`: the same for an orthonormal family of
  eigenvectors.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer, 1990, Chapter VII, §7.
-/

public section

open Filter
open scoped InnerProductSpace Topology

namespace IsCompactOperator

variable {𝕜 ι : Type*} [RCLike 𝕜]

section Bounded

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] {T : E →ₗ[𝕜] F} {v : ι → E} {w : ι → F} {μ : ι → 𝕜} {C : ℝ}

/-- If a compact operator sends a bounded family `v` to the multiples `μ i • w i` of an
orthonormal family `w`, then for every `δ > 0` only finitely many coefficients satisfy
`δ ≤ ‖μ i‖`. -/
theorem finite_setOf_le_norm_of_apply_eq_smul (hT : IsCompactOperator T) (hv : ∀ i, ‖v i‖ ≤ C)
    (hw : Orthonormal 𝕜 w) (hTv : ∀ i, T (v i) = μ i • w i) {δ : ℝ} (hδ : 0 < δ) :
    {i | δ ≤ ‖μ i‖}.Finite := by
  by_contra hinf
  let e := Set.Infinite.natEmbedding _ hinf
  obtain ⟨m, n, hmn, hlt⟩ := hT.exists_dist_lt_of_norm_le (u := fun k ↦ v (e k)) (fun _ ↦ hv _) hδ
  have hne : (e m : ι) ≠ e n := fun h ↦ hmn (e.injective (Subtype.ext h))
  refine hlt.not_ge ?_
  calc δ ≤ ‖μ (e m)‖ := (e m).2
    _ = ‖⟪w (e m), T (v (e m)) - T (v (e n))⟫_𝕜‖ := by
      simp [hTv, inner_sub_right, inner_smul_right, hw.2 hne, inner_self_eq_norm_sq_to_K, hw.1]
    _ ≤ dist (T (v (e m))) (T (v (e n))) := by
      simpa [dist_eq_norm, hw.1] using norm_inner_le_norm (𝕜 := 𝕜) (w (e m))
        (T (v (e m)) - T (v (e n)))

/-- If a compact operator sends a bounded family `v` to the multiples `μ i • w i` of an
orthonormal family `w`, then the coefficients `μ i` tend to zero along the cofinite filter. -/
theorem tendsto_cofinite_of_apply_eq_smul (hT : IsCompactOperator T) (hv : ∀ i, ‖v i‖ ≤ C)
    (hw : Orthonormal 𝕜 w) (hTv : ∀ i, T (v i) = μ i • w i) : Tendsto μ cofinite (𝓝 0) :=
  Metric.tendsto_nhds.2 fun _ hδ ↦ eventually_cofinite.2 <| by
    simpa [not_lt] using hT.finite_setOf_le_norm_of_apply_eq_smul hv hw hTv hδ

end Bounded

section Eigenvector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} {v : ι → E}
  {μ : ι → 𝕜}

/-- For an orthonormal family `v` of eigenvectors of a compact operator, with eigenvalues `μ i`,
only finitely many eigenvalues have norm at least `δ > 0`. -/
theorem finite_setOf_le_norm_of_orthonormal (hT : IsCompactOperator T) (hv : Orthonormal 𝕜 v)
    (hTv : ∀ i, T (v i) = μ i • v i) {δ : ℝ} (hδ : 0 < δ) : {i | δ ≤ ‖μ i‖}.Finite :=
  hT.finite_setOf_le_norm_of_apply_eq_smul (fun i ↦ (hv.1 i).le) hv hTv hδ

/-- The eigenvalues `μ i` attached to an orthonormal family `v` of eigenvectors of a compact
operator tend to zero along the cofinite filter. -/
theorem tendsto_cofinite_of_orthonormal (hT : IsCompactOperator T) (hv : Orthonormal 𝕜 v)
    (hTv : ∀ i, T (v i) = μ i • v i) : Tendsto μ cofinite (𝓝 0) :=
  hT.tendsto_cofinite_of_apply_eq_smul (fun i ↦ (hv.1 i).le) hv hTv

end Eigenvector

end IsCompactOperator
