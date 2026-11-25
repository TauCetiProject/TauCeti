/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram

/-!
# Variational solutions with a lifting

Let `B` be a bounded bilinear form on a real seminormed space `H`, and let `S : V →L[ℝ] H`
map a complete real Hilbert space into `H`. If `B` is coercive on `V` through `S`, the
Lax–Milgram correction gives a bounded linear map from `(g, ℓ)` to `u = g + S w`, where
`B(u, S v) = ℓ v` for every `v : V`.

This is the lifting construction for nonhomogeneous boundary values: one takes `H = H¹(Ω)`,
`V = H¹₀(Ω)` and `S` the inclusion. It requires neither symmetry of `B` nor completeness of `H`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.2.1–§6.2.2.
-/

public section

noncomputable section

namespace IsCoercive

variable {H V : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {B : H →L[ℝ] H →L[ℝ] ℝ} {S : V →L[ℝ] H}

/-- The variational solution with lifting `g` and forcing `ℓ`, jointly bounded and linear in
these data. The correction solves the equation with forcing `ℓ - B(g, S ·)`. -/
def solutionWithLifting (h : IsCoercive (B.bilinearComp S S)) :
    (H × StrongDual ℝ V) →L[ℝ] H :=
  let T := S.comp h.solutionOfFunctional
  ((ContinuousLinearMap.id ℝ H) - T.comp (B.bilinearComp (.id ℝ H) S)).coprod T

/-- The solution with a lifting is the lifting plus the Lax–Milgram correction. -/
theorem solutionWithLifting_apply (h : IsCoercive (B.bilinearComp S S))
    (g : H) (ℓ : StrongDual ℝ V) :
    h.solutionWithLifting (g, ℓ) = g + S (h.solutionOfFunctional (ℓ - (B g).comp S)) := by
  have hB : B.bilinearComp (.id ℝ H) S g = (B g).comp S := by
    ext v
    simp [ContinuousLinearMap.bilinearComp_apply]
  simp [solutionWithLifting, hB, sub_eq_add_neg, add_comm, add_left_comm]

/-- The lifted solution satisfies the variational equation on the image of `S`. -/
@[simp]
theorem apply_solutionWithLifting (h : IsCoercive (B.bilinearComp S S))
    (g : H) (ℓ : StrongDual ℝ V) (v : V) :
    B (h.solutionWithLifting (g, ℓ)) (S v) = ℓ v := by
  rw [solutionWithLifting_apply, map_add, add_apply]
  have heq := h.apply_solutionOfFunctional_eq (ℓ - (B g).comp S) v
  simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply,
    ContinuousLinearMap.comp_apply] at heq
  linarith

/-- The lifted solution differs from its lifting by a vector in the image of `S`. -/
theorem solutionWithLifting_sub_mem_range (h : IsCoercive (B.bilinearComp S S))
    (g : H) (ℓ : StrongDual ℝ V) :
    h.solutionWithLifting (g, ℓ) - g ∈ Set.range S := by
  rw [solutionWithLifting_apply, add_sub_cancel_left]
  exact ⟨_, rfl⟩

/-- The boundary class and variational equation uniquely characterize the lifted solution. -/
theorem solutionWithLifting_eq_iff (h : IsCoercive (B.bilinearComp S S))
    {g u : H} {ℓ : StrongDual ℝ V} :
    h.solutionWithLifting (g, ℓ) = u ↔
      u - g ∈ Set.range S ∧ ∀ v : V, B u (S v) = ℓ v := by
  constructor
  · rintro rfl
    exact ⟨h.solutionWithLifting_sub_mem_range g ℓ, h.apply_solutionWithLifting g ℓ⟩
  · rintro ⟨⟨w, hw⟩, hu⟩
    have hwu : g + S w = u := by rw [hw]; abel
    have hwsol : w = h.solutionOfFunctional (ℓ - (B g).comp S) := by
      apply h.eq_solutionOfFunctional
      intro v
      have heq := hu v
      rw [← hwu, map_add, add_apply] at heq
      simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply,
        ContinuousLinearMap.comp_apply]
      linarith
    rw [solutionWithLifting_apply, ← hwsol, hwu]

/-- Liftings yield the same solution exactly when their difference lies in the image of `S`. -/
theorem solutionWithLifting_eq_iff_sub_mem_range (h : IsCoercive (B.bilinearComp S S))
    (g g' : H) (ℓ : StrongDual ℝ V) :
    h.solutionWithLifting (g, ℓ) = h.solutionWithLifting (g', ℓ) ↔
      g - g' ∈ Set.range S := by
  constructor
  · intro heq
    obtain ⟨w, hw⟩ := h.solutionWithLifting_sub_mem_range g ℓ
    obtain ⟨w', hw'⟩ := h.solutionWithLifting_sub_mem_range g' ℓ
    refine ⟨w' - w, ?_⟩
    rw [map_sub, hw, hw', heq]
    abel
  · rintro ⟨w, hw⟩
    apply h.solutionWithLifting_eq_iff.2
    obtain ⟨w', hw'⟩ := h.solutionWithLifting_sub_mem_range g' ℓ
    refine ⟨⟨w' - w, ?_⟩, h.apply_solutionWithLifting g' ℓ⟩
    rw [map_sub, hw, hw']
    abel

/-- Replacing the lifting `g` by the lifted solution for `(g, ℓ')` leaves the solution for
`(g, ℓ)` unchanged. -/
@[simp]
theorem solutionWithLifting_solutionWithLifting (h : IsCoercive (B.bilinearComp S S))
    (g : H) (ℓ' ℓ : StrongDual ℝ V) :
    h.solutionWithLifting (h.solutionWithLifting (g, ℓ'), ℓ) =
      h.solutionWithLifting (g, ℓ) :=
  (h.solutionWithLifting_eq_iff_sub_mem_range _ _ ℓ).2
    (h.solutionWithLifting_sub_mem_range g ℓ')

/-- A zero lifting gives the homogeneous-boundary Lax–Milgram solution. -/
@[simp]
theorem solutionWithLifting_zero (h : IsCoercive (B.bilinearComp S S))
    (ℓ : StrongDual ℝ V) :
    h.solutionWithLifting (0, ℓ) = S (h.solutionOfFunctional ℓ) := by
  simp [solutionWithLifting_apply]

/-- A lifting in the image of `S` gives the homogeneous-boundary solution. -/
@[simp]
theorem solutionWithLifting_map (h : IsCoercive (B.bilinearComp S S))
    (w : V) (ℓ : StrongDual ℝ V) :
    h.solutionWithLifting (S w, ℓ) = S (h.solutionOfFunctional ℓ) := by
  rw [← h.solutionWithLifting_zero ℓ]
  exact (h.solutionWithLifting_eq_iff_sub_mem_range _ _ ℓ).2 ⟨w, by simp⟩

variable (h : IsCoercive (B.bilinearComp S S)) {C : ℝ} (hC : 0 < C)
  (hlower : ∀ v : V, C * ‖v‖ ^ 2 ≤ B (S v) (S v))

include hC hlower

/-- Quantitative bound for the correction, including the norm of the inclusion map. -/
theorem norm_solutionWithLifting_sub_le (g : H) (ℓ : StrongDual ℝ V) :
    ‖h.solutionWithLifting (g, ℓ) - g‖ ≤
      ‖S‖ * ((‖ℓ‖ + ‖B‖ * ‖g‖ * ‖S‖) / C) := by
  let w := h.solutionOfFunctional (ℓ - (B g).comp S)
  have hw : C * ‖w‖ ^ 2 ≤ (‖ℓ‖ + ‖B‖ * ‖g‖ * ‖S‖) * ‖w‖ := by
    have heq := h.apply_solutionOfFunctional_eq (ℓ - (B g).comp S) w
    simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply,
      ContinuousLinearMap.comp_apply] at heq
    have hB := B.le_opNorm₂ g (S w)
    have hS := S.le_opNorm w
    have hℓ := ℓ.le_opNorm w
    rw [Real.norm_eq_abs] at hB hℓ
    calc
      C * ‖w‖ ^ 2 ≤ ℓ w - B g (S w) := (hlower w).trans_eq heq
      _ ≤ ‖ℓ‖ * ‖w‖ + ‖B‖ * ‖g‖ * ‖S w‖ := by
        linarith [le_abs_self (ℓ w), neg_abs_le (B g (S w))]
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left hS (mul_nonneg (norm_nonneg B) (norm_nonneg g))]
  have hwnorm : ‖w‖ ≤ (‖ℓ‖ + ‖B‖ * ‖g‖ * ‖S‖) / C := by
    rw [le_div_iff₀ hC]
    rcases eq_or_lt_of_le (norm_nonneg w) with hzero | hpos
    · rw [← hzero, zero_mul]
      positivity
    · nlinarith [hw]
  rw [solutionWithLifting_apply, add_sub_cancel_left]
  exact (S.le_opNorm w).trans (mul_le_mul_of_nonneg_left hwnorm (norm_nonneg S))

/-- Bound for the solution in terms of both data and an explicit coercivity constant. -/
theorem norm_solutionWithLifting_apply_le (g : H) (ℓ : StrongDual ℝ V) :
    ‖h.solutionWithLifting (g, ℓ)‖ ≤
      ‖g‖ + ‖S‖ * ((‖ℓ‖ + ‖B‖ * ‖g‖ * ‖S‖) / C) := by
  calc
    _ ≤ ‖h.solutionWithLifting (g, ℓ) - g‖ + ‖g‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith [h.norm_solutionWithLifting_sub_le hC hlower g ℓ]

/-- Operator-norm bound for the jointly linear lifting solution map. -/
theorem norm_solutionWithLifting_le :
    ‖h.solutionWithLifting‖ ≤ 1 + ‖S‖ * ((1 + ‖B‖ * ‖S‖) / C) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  calc
    _ ≤ ‖p.1‖ + ‖S‖ * ((‖p.2‖ + ‖B‖ * ‖p.1‖ * ‖S‖) / C) :=
      h.norm_solutionWithLifting_apply_le hC hlower p.1 p.2
    _ ≤ ‖p‖ + ‖S‖ * ((‖p‖ + ‖B‖ * ‖p‖ * ‖S‖) / C) := by
      gcongr
      · exact norm_fst_le p
      · exact norm_snd_le p
      · exact norm_fst_le p
    _ = _ := by ring

end IsCoercive
