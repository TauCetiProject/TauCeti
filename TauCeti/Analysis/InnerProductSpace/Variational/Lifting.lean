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

end IsCoercive
