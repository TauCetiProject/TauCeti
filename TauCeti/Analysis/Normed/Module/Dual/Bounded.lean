/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A bounded-functional separation criterion

On a finite-dimensional vector space, if the linear functionals bounded by a function `N`
separate points, then every linear functional is bounded by `N`. No topology on the vector
space or completeness of the scalar field is required. This applies in particular to spectral
norms over incomplete fields, where continuity of all linear maps cannot be assumed.

The argument is Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §2.3.1, Proposition 2.
The formal proof adapts William Coram's `Module.Dual.exists_bound_of_forall_exists_ne_zero`
in `PhD/TauCeti/Code/RigidAnalyticGeometry/WeaklyStable.lean` at commit
`eefb3d91f34b27d0bc7822140fa85fecae029884` of <https://github.com/WilliamCoram/PhD>.
-/

public section

namespace Module.Dual

/-- If the functionals bounded by `N` separate points of a finite-dimensional space, every
functional is bounded by `N`. The function `N` need not itself be a norm. -/
theorem exists_bound_of_forall_exists_ne_zero {K : Type*} [NormedField K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ψ : Module.Dual K V) (N : V → ℝ)
    (h : ∀ x : V, x ≠ 0 → ∃ φ : Module.Dual K V,
      (∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * N y) ∧ φ x ≠ 0) :
    ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C * N y := by
  let W : Submodule K (Module.Dual K V) :=
    { carrier := {φ | ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * N y}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro φ₁ φ₂ ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
        exact ⟨C₁ + C₂, fun y ↦ (norm_add_le _ _).trans
          (by rw [add_mul]; exact add_le_add (h₁ y) (h₂ y))⟩
      smul_mem' := by
        rintro a φ ⟨C, hC⟩
        exact ⟨‖a‖ * C, fun y ↦ by
          simpa [norm_mul, mul_assoc] using
            mul_le_mul_of_nonneg_left (hC y) (norm_nonneg a)⟩ }
  -- By the carrier definition, membership in W is exactly the boundedness condition in h.
  have htop : W = ⊤ := by
    simpa only [Submodule.span_eq] using
      (Submodule.span_eq_top_of_ne_zero (s := (W : Set (Module.Dual K V))) h)
  have hψ : ψ ∈ W := by rw [htop]; exact Submodule.mem_top
  -- Unfolding membership in W recovers the required bound for ψ.
  exact hψ

end Module.Dual
