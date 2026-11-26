/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Variational solutions with a lifting

Let `B` be a bounded bilinear form on a real seminormed space `H`, and let `S : V →L[ℝ] H`
map a complete real Hilbert space into `H`. If `B` is coercive on `V` through `S`, the
Lax–Milgram correction gives a bounded linear map from `(g, ℓ)` to `u = g + S w`, where
`B(u, S v) = ℓ v` for every `v : V`.

This is the lifting construction for nonhomogeneous boundary values: one takes `H = H¹(Ω)`,
`V = H¹₀(Ω)` and `S` the inclusion. It requires neither symmetry of `B` nor completeness of `H`.

## Dirichlet's principle

For a symmetric form the solution is also characterized variationally. Put
`J(w) = B(g + S w, g + S w) / 2 - ℓ w` on `V`, the energy of the candidate `g + S w`. If `B` is
nonnegative on the image of `S`, then `w₀` minimizes `J` exactly when `u = g + S w₀` solves
`B(u, S v) = ℓ v` for every `v : V` (`ContinuousLinearMap.isMinOn_iff_forall_apply_eq`): along
`w₀ + d` the energy changes by `B(u, S d) - ℓ d + B(S d, S d) / 2`, whose first-order part vanishes
for every direction `d` exactly at a solution. When `B` is moreover coercive on `V` through `S`,
the minimizers are exactly the `w₀` with `g + S w₀` the lifted solution
(`IsCoercive.isMinOn_iff_solutionWithLifting_eq`). When `S` is injective, as for the inclusion of
a subspace, `w` is determined by `u = g + S w`, and minimizing `J` is minimizing
`B(u, u) / 2 - ℓ (u - g)` over the affine space `g + S V`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.2.1–§6.2.2, and §2.2.5, Theorem 17
  (Dirichlet's principle for Poisson's equation).
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {H V : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Dirichlet's principle.** Let `B` be a symmetric bounded bilinear form on `H`, nonnegative on
the image of `S : V →L[ℝ] H`. For a lifting `g : H` and a forcing `ℓ`, the energy
`J(w) = B(g + S w, g + S w) / 2 - ℓ w` has a minimum on `V` at `w₀` exactly when `u = g + S w₀`
solves the variational equation `B(u, S v) = ℓ v` for every `v : V`. -/
theorem isMinOn_iff_forall_apply_eq (B : H →L[ℝ] H →L[ℝ] ℝ) (S : V →L[ℝ] H)
    (hsymm : ∀ x y, B x y = B y x) (hnonneg : ∀ w, 0 ≤ B (S w) (S w)) (g : H)
    (ℓ : StrongDual ℝ V) (w₀ : V) :
    IsMinOn (fun w => B (g + S w) (g + S w) / 2 - ℓ w) Set.univ w₀ ↔
      ∀ v, B (g + S w₀) (S v) = ℓ v := by
  -- Along `w₀ + d` the energy changes by `B(u, S d) - ℓ d + B(S d, S d) / 2`, `u = g + S w₀`.
  have hexp (d : V) : B (g + S (w₀ + d)) (g + S (w₀ + d)) / 2 - ℓ (w₀ + d) =
      (B (g + S w₀) (g + S w₀) / 2 - ℓ w₀) + (B (g + S w₀) (S d) - ℓ d) +
        B (S d) (S d) / 2 := by
    rw [map_add S, ← add_assoc, map_add ℓ]
    generalize g + S w₀ = u
    rw [B.map_add, add_apply, (B u).map_add, (B (S d)).map_add, hsymm (S d) u]
    ring
  rw [isMinOn_univ_iff]
  constructor
  · intro hmin v
    -- The change along `t v` is the quadratic `t (B(u, S v) - ℓ v) + t² B(S v, S v) / 2 ≥ 0`, so
    -- its linear coefficient vanishes.
    have hq (t : ℝ) :
        0 ≤ B (S v) (S v) / 2 * (t * t) + (B (g + S w₀) (S v) - ℓ v) * t + 0 := by
      have h := hmin (w₀ + t • v)
      simp only [hexp, map_smul, smul_apply, smul_eq_mul] at h
      nlinarith
    have hd := discrim_le_zero hq
    rw [discrim, mul_zero, sub_zero] at hd
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hd (sq_nonneg _)))
  · intro hsol w
    have h := hexp (w - w₀)
    rw [add_sub_cancel, hsol] at h
    simp only [h]
    linarith [hnonneg (w - w₀)]

end ContinuousLinearMap

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

/-- **Dirichlet's principle for the lifted solution.** Let `B` be symmetric and coercive on `V`
through `S`. Then `w₀` minimizes the energy `J(w) = B(g + S w, g + S w) / 2 - ℓ w` on `V` exactly
when `g + S w₀` is the lifted solution for `(g, ℓ)`. -/
theorem isMinOn_iff_solutionWithLifting_eq (h : IsCoercive (B.bilinearComp S S))
    (hsymm : ∀ x y, B x y = B y x) (g : H) (ℓ : StrongDual ℝ V) (w₀ : V) :
    IsMinOn (fun w => B (g + S w) (g + S w) / 2 - ℓ w) Set.univ w₀ ↔
      h.solutionWithLifting (g, ℓ) = g + S w₀ := by
  have hnonneg (w : V) : 0 ≤ B (S w) (S w) := by
    simpa only [ContinuousLinearMap.bilinearComp_apply] using h.apply_self_nonneg w
  rw [B.isMinOn_iff_forall_apply_eq S hsymm hnonneg, h.solutionWithLifting_eq_iff,
    add_sub_cancel_left]
  exact (and_iff_right (Set.mem_range_self w₀)).symm

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
