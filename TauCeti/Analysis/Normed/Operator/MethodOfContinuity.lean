/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
public import TauCeti.Analysis.Normed.Operator.Basic

/-!
# The method of continuity

Let `E` be a Banach space, `F` a normed space, and `t ↦ L t` a family of continuous linear maps
`E →L[𝕜] F`, continuous in operator norm on a preconnected parameter set `S`. Suppose the family
satisfies an a priori estimate that is uniform in the parameter:

`‖x‖ ≤ C * ‖L t x‖` for every `t ∈ S` and every `x ∈ E`.

Then either every `L t`, `t ∈ S`, is surjective, or none is. So solvability of a single, simpler
problem (for instance one with constant coefficients) gives solvability along the whole family,
and the uniform estimate then makes every `L t` invertible with `‖(L t)⁻¹ y‖ ≤ C * ‖y‖`, the
inverse depending continuously on `t` in operator norm.

The proof is the classical one. If `L s` is surjective, the estimate makes it invertible with
inverse of norm at most `C`, and a Neumann series shows that every `M` with `C * ‖M - L s‖ < 1` is
invertible too (`ContinuousLinearMap.isInvertible_of_mul_norm_sub_lt`). The radius `1 / C` does
not depend on `s`, so the set of parameters where `L t` is surjective is both
open and closed in `S`; preconnectedness concludes.

This is the abstract step behind existence theorems for linear elliptic and parabolic equations
with variable coefficients: the a priori Schauder estimate along the path from the Laplacian or
the heat operator to the given operator, together with solvability at the starting point, gives
solvability at the end point.

## Main declarations

* `IsCompact.exists_forall_norm_le_mul_norm_apply`: on a compact parameter set, a priori estimates
  for each member of the family give one that is uniform in the parameter.
* `IsPreconnected.surjective_iff_of_forall_norm_le`: the method of continuity for a family on a
  preconnected parameter set.
* `IsPreconnected.isInvertible_of_forall_norm_le` and
  `IsPreconnected.continuousOn_inverse_of_forall_norm_le`: once one member is surjective, every
  member is invertible and the inverses depend continuously on the parameter.
* `ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap`: the classical statement for the
  segment `t ↦ (1 - t) L₀ + t L₁`, `t ∈ [0, 1]`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity) and its use in Theorem 6.8.
-/

public section

open Function Set Filter Topology

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace X]
  {S : Set X} {L : X → E →L[𝕜] F} {C : ℝ} {s t : X}

namespace IsCompact

omit [CompleteSpace E] in
/-- **A priori estimates are uniform on a compact parameter set.** Let `L` be a family of continuous
linear maps `E →L[𝕜] F`, continuous in operator norm on a compact set `S`, each of which satisfies
an a priori estimate `‖x‖ ≤ C t * ‖L t x‖`. Then one constant `C` serves for every `t ∈ S`. Near
each `t` the perturbation `L s - L t` is small compared with `1 / C t`, so `L s` satisfies the
estimate with constant `2 C t`, and finitely many such neighbourhoods cover `S`. -/
theorem exists_forall_norm_le_mul_norm_apply (hS : IsCompact S) (hL : ContinuousOn L S)
    (hC : ∀ t ∈ S, ∃ C : ℝ, ∀ x, ‖x‖ ≤ C * ‖L t x‖) :
    ∃ C : ℝ, ∀ t ∈ S, ∀ x, ‖x‖ ≤ C * ‖L t x‖ := by
  refine hS.induction_on (p := fun s ↦ ∃ C : ℝ, ∀ t ∈ s, ∀ x, ‖x‖ ≤ C * ‖L t x‖)
    ⟨0, fun _ h ↦ h.elim⟩ (fun s t hst ⟨C, hC⟩ ↦ ⟨C, fun r hr ↦ hC r (hst hr)⟩)
    (fun s t ⟨C₁, h₁⟩ ⟨C₂, h₂⟩ ↦ ⟨max C₁ C₂, fun r hr x ↦ hr.elim
      (fun hr ↦ (h₁ r hr x).trans (by gcongr; exact le_max_left _ _))
      (fun hr ↦ (h₂ r hr x).trans (by gcongr; exact le_max_right _ _))⟩) fun t ht ↦ ?_
  obtain ⟨C, hCt⟩ := hC t ht
  set D := max C 0
  have hD0 : 0 ≤ D := le_max_right _ _
  have hlim : Tendsto (fun s ↦ ‖L s - L t‖) (𝓝[S] t) (𝓝 0) := by
    simpa using tendsto_iff_norm_sub_tendsto_zero.1 (hL t ht).tendsto
  refine ⟨_, hlim.eventually (gt_mem_nhds (inv_pos.2 (by positivity : (0 : ℝ) < 2 * (D + 1)))),
    2 * D, fun s hs x ↦ ?_⟩
  -- `‖x‖ ≤ D ‖L t x‖ ≤ D ‖L s x‖ + D ‖L s - L t‖ ‖x‖ ≤ D ‖L s x‖ + ‖x‖ / 2`.
  have h₁ : ‖x‖ ≤ D * ‖L t x‖ :=
    (hCt x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h₂ : ‖L t x‖ ≤ ‖L s x‖ + ‖L s - L t‖ * ‖x‖ :=
    calc ‖L t x‖ = ‖L s x - (L s - L t) x‖ := by simp
      _ ≤ ‖L s x‖ + ‖(L s - L t) x‖ := norm_sub_le _ _
      _ ≤ ‖L s x‖ + ‖L s - L t‖ * ‖x‖ := by gcongr; exact (L s - L t).le_opNorm x
  have h₃ : D * (‖L s - L t‖ * ‖x‖) ≤ ‖x‖ / 2 := by
    have hs' : ‖L s - L t‖ * (2 * (D + 1)) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hs.le (by positivity : (0 : ℝ) ≤ 2 * (D + 1))
      rwa [inv_mul_cancel₀ (by positivity)] at h
    nlinarith [norm_nonneg x, norm_nonneg (L s - L t)]
  nlinarith [mul_le_mul_of_nonneg_left h₂ hD0]

end IsCompact

namespace IsPreconnected

/-- **The method of continuity.** Let `E` be a Banach space and `L` a family of continuous linear
maps `E →L[𝕜] F`, continuous in operator norm on a preconnected set `S`, satisfying the uniform
a priori estimate `‖x‖ ≤ C * ‖L t x‖` for `t ∈ S`. Then for `s, t ∈ S`, `L s` is surjective if
and only if `L t` is. -/
theorem surjective_iff_of_forall_norm_le (hS : IsPreconnected S) (hL : ContinuousOn L S)
    (hC : ∀ t ∈ S, ∀ x, ‖x‖ ≤ C * ‖L t x‖) (hs : s ∈ S) (ht : t ∈ S) :
    Surjective (L s) ↔ Surjective (L t) := by
  refine hS.induction₂ (fun s t ↦ Surjective (L s) ↔ Surjective (L t)) (fun s hs ↦ ?_)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) (fun _ _ _ _ h ↦ h.symm) hs ht
  -- Near `s`, each of `L s` and `L t` is a perturbation of the other of size less than `1 / C`.
  have hlim : Tendsto (fun t ↦ C * ‖L t - L s‖) (𝓝[S] s) (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 (hL s hs).tendsto).const_mul C
  filter_upwards [hlim.eventually (gt_mem_nhds one_pos), self_mem_nhdsWithin] with t h ht
  exact ⟨fun h' ↦ (ContinuousLinearMap.isInvertible_of_mul_norm_sub_lt h' (hC s hs) h).surjective,
    fun h' ↦ (ContinuousLinearMap.isInvertible_of_mul_norm_sub_lt h' (hC t ht)
      (by rwa [norm_sub_rev])).surjective⟩

/-- **The method of continuity, invertible form.** Under the hypotheses of
`IsPreconnected.surjective_iff_of_forall_norm_le`, if one `L s`, `s ∈ S`, is surjective, then
every `L t`, `t ∈ S`, is invertible. Its inverse satisfies `‖(L t)⁻¹ y‖ ≤ C * ‖y‖` by
`ContinuousLinearMap.norm_inverse_apply_le_of_forall_norm_le`. -/
theorem isInvertible_of_forall_norm_le (hS : IsPreconnected S) (hL : ContinuousOn L S)
    (hC : ∀ t ∈ S, ∀ x, ‖x‖ ≤ C * ‖L t x‖) (hs : s ∈ S) (ht : t ∈ S) (h : Surjective (L s)) :
    (L t).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_surjective_of_forall_norm_le
    ((hS.surjective_iff_of_forall_norm_le hL hC hs ht).1 h) (hC t ht)

/-- Under the hypotheses of `IsPreconnected.surjective_iff_of_forall_norm_le`, if one `L s`,
`s ∈ S`, is surjective, then the inverses `(L t)⁻¹` depend continuously on `t ∈ S` in operator
norm. -/
theorem continuousOn_inverse_of_forall_norm_le (hS : IsPreconnected S) (hL : ContinuousOn L S)
    (hC : ∀ t ∈ S, ∀ x, ‖x‖ ≤ C * ‖L t x‖) (hs : s ∈ S) (h : Surjective (L s)) :
    ContinuousOn (fun t ↦ (L t).inverse) S := fun t ht ↦
  ((hS.isInvertible_of_forall_norm_le hL hC hs ht h).contDiffAt_map_inverse
    (n := 0)).continuousAt.comp_continuousWithinAt (hL t ht)

end IsPreconnected

namespace ContinuousLinearMap

/-- **The method of continuity** (Gilbarg–Trudinger, Theorem 5.2). Let `E` be a Banach space and
`L₀, L₁ : E →L[𝕜] F`. If the operators `L t = (1 - t) L₀ + t L₁` satisfy the a priori estimate
`‖x‖ ≤ C * ‖L t x‖` for every `t ∈ [0, 1]`, then `L₀` is surjective if and only if `L₁` is. -/
theorem surjective_iff_of_forall_norm_le_lineMap [NormedSpace ℝ F] [SMulCommClass 𝕜 ℝ F]
    {L₀ L₁ : E →L[𝕜] F}
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ C * ‖AffineMap.lineMap L₀ L₁ t x‖) :
    Surjective L₀ ↔ Surjective L₁ := by
  simpa using isPreconnected_Icc.surjective_iff_of_forall_norm_le
    AffineMap.lineMap_continuous.continuousOn hC (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)

end ContinuousLinearMap

end
