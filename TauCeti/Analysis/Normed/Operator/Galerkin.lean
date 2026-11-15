/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Céa's lemma and the convergence of Galerkin approximations

Let `B` be a bounded bilinear form on a real normed space `E` with the coercivity bound
`C ‖x‖ ‖x‖ ≤ B x x`, `0 < C`, and let `u : E`. A **Galerkin approximation** of `u` in a subspace
`S` is a vector `w ∈ S` with `B (u - w) v = 0` for every `v ∈ S`. If `u` solves the variational
problem `B u v = ℓ v` for every `v : E`, a Galerkin approximation is a solution of the same problem
with both the unknown and the test vectors restricted to `S`; by the Lax–Milgram theorem it exists
and is unique when `S` is a closed subspace of a Hilbert space.

**Céa's lemma** says that the Galerkin approximation is a best approximation of `u` from `S` up to
the factor `‖B‖ / C`:

`‖u - w‖ ≤ ‖B‖ / C * ‖u - z‖` for every `z ∈ S`

(`ContinuousLinearMap.norm_sub_le_div_mul_norm_sub_of_apply_sub_eq_zero`). Consequently Galerkin
approximations in a family of subspaces that approximate `u` arbitrarily well converge to `u`
(`IsCoercive.tendsto_of_forall_apply_sub_eq_zero`). Neither symmetry of `B` nor completeness of
`E` is used. The subspaces may be the finite-dimensional spaces of a numerical scheme, or the
images of the Sobolev spaces of an exhaustion of a domain by smaller domains.

## Main declarations

* `ContinuousLinearMap.norm_sub_le_div_mul_norm_sub_of_apply_sub_eq_zero`: Céa's lemma.
* `IsCoercive.tendsto_of_forall_apply_sub_eq_zero`: convergence of Galerkin approximations.

## References

* J. Céa, *Approximation variationnelle des problèmes aux limites*, Ann. Inst. Fourier
  (Grenoble) **14** (1964), 345–444.
* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, North-Holland, 1978,
  Chapter 2 (Céa's lemma).
-/

public section

open Filter Topology

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

namespace ContinuousLinearMap

/-- **Céa's lemma.** Let `B` satisfy `C ‖x‖ ‖x‖ ≤ B x x` with `0 < C`, and let `w ∈ S` be a
Galerkin approximation of `u` in the subspace `S`: `B (u - w) v = 0` for every `v ∈ S`. Then `w`
approximates `u` as well as any vector of `S`, up to the factor `‖B‖ / C`. -/
theorem norm_sub_le_div_mul_norm_sub_of_apply_sub_eq_zero (B : E →L[ℝ] E →L[ℝ] ℝ) {C : ℝ}
    (hC : 0 < C) (hB : ∀ x, C * ‖x‖ * ‖x‖ ≤ B x x) {S : Submodule ℝ E} {u w z : E}
    (hw : w ∈ S) (hz : z ∈ S) (horth : ∀ v ∈ S, B (u - w) v = 0) :
    ‖u - w‖ ≤ ‖B‖ / C * ‖u - z‖ := by
  set e := u - w
  -- Galerkin orthogonality: `e` is `B`-orthogonal to `z - w ∈ S`.
  have hsplit : u - z + (z - w) = e := by simp only [e]; abel
  have hee : B e e = B e (u - z) :=
    calc B e e = B e (u - z + (z - w)) := by rw [hsplit]
      _ = B e (u - z) := by rw [map_add, horth _ (S.sub_mem hz hw), add_zero]
  have hle : C * ‖e‖ * ‖e‖ ≤ ‖B‖ * ‖e‖ * ‖u - z‖ :=
    (hB e).trans (hee ▸ (Real.le_norm_self _).trans (B.le_opNorm₂ e (u - z)))
  rcases (norm_nonneg e).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hC]
    exact le_of_mul_le_mul_right (by linarith) hpos

end ContinuousLinearMap

namespace IsCoercive

/-- **Convergence of Galerkin approximations.** Let `B` be coercive, and for every index `i` let
`J i : W i →ₗ[ℝ] E` be a linear map, whose range is the approximation space, and `w i : W i` such
that `J i (w i)` is a Galerkin approximation of `u`: `B (u - J i (w i)) (J i v) = 0` for every
`v : W i`. If the ranges of the `J i` approximate `u` arbitrarily well along a filter, then
`J i (w i)` tends to `u` along it. Taking for `J i` the inclusion of a subspace `S i` gives the same
statement for Galerkin approximations in subspaces. -/
theorem tendsto_of_forall_apply_sub_eq_zero {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B)
    {α : Type*} {l : Filter α} {W : α → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    (J : ∀ i, W i →ₗ[ℝ] E) {u : E} {w : ∀ i, W i}
    (horth : ∀ i (v : W i), B (u - J i (w i)) (J i v) = 0)
    (happrox : ∀ ε > 0, ∀ᶠ i in l, ∃ z, ‖u - J i z‖ < ε) :
    Tendsto (fun i => J i (w i)) l (𝓝 u) := by
  obtain ⟨C, hC, hlower⟩ := hB
  set K := ‖B‖ / C + 1
  have hK : 0 < K := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [happrox (ε / K) (div_pos hε hK)] with i ⟨z, hdist⟩
  have hcea := B.norm_sub_le_div_mul_norm_sub_of_apply_sub_eq_zero hC hlower
    (S := LinearMap.range (J i)) (LinearMap.mem_range_self _ (w i))
    (LinearMap.mem_range_self _ z) fun _ ⟨v, hv⟩ => hv ▸ horth i v
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
  calc ‖u - J i (w i)‖ ≤ ‖B‖ / C * ‖u - J i z‖ := hcea
    _ ≤ K * ‖u - J i z‖ := by gcongr; linarith
    _ < K * (ε / K) := by gcongr
    _ = ε := mul_div_cancel₀ ε hK.ne'

end IsCoercive
