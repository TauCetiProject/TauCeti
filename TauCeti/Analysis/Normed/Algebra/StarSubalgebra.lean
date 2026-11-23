/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Self-adjoint contractions of the closure of a star subalgebra

In a normed star algebra over `ℝ` or `ℂ`, the self-adjoint contractions of the norm closure of a
star subalgebra `S` are exactly the norm limits of self-adjoint contractions of `S`
(`StarSubalgebra.closure_selfAdjoint_unitBall`). The continuous map
`a ↦ (max 1 ‖b‖)⁻¹ • b`, with `b = 2⁻¹ • (a + a⋆)` the real part of `a`, sends `S` into its
self-adjoint contractions and fixes every self-adjoint contraction.

This lets an approximation by elements of the norm closure of `S`, such as the continuous
functional calculus of elements of `S`, be replaced by one through elements of `S` itself without
losing self-adjointness or the norm bound; the Kaplansky density theorem uses it this way.
-/

public section

namespace StarSubalgebra

variable {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
  [StarModule 𝕜 A] [ContinuousStar A]

/-- In a normed star algebra, the closure of the self-adjoint contractions of a star subalgebra
`S` is the set of self-adjoint contractions of the closure of `S`. -/
theorem closure_selfAdjoint_unitBall (S : StarSubalgebra 𝕜 A) :
    closure {x | x ∈ S ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1} =
      {x | x ∈ closure (S : Set A) ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1} := by
  refine subset_antisymm (closure_minimal
    (fun x ⟨hx, hxsa, hx₁⟩ => ⟨subset_closure hx, hxsa, hx₁⟩)
    (isClosed_closure.inter (isClosed_setOfPred_isSelfAdjoint.inter
      (isClosed_le continuous_norm continuous_const)))) ?_
  rintro z ⟨hz, hzsa, hz₁⟩
  -- The continuous map `a ↦ (max 1 ‖b‖)⁻¹ • b`, with `b = 2⁻¹ • (a + a⋆)`, sends `S` to its
  -- self-adjoint contractions and fixes `z`.
  let re : A → A := fun a => (2⁻¹ : 𝕜) • (a + star a)
  let g : A → A := fun a => (((max 1 ‖re a‖)⁻¹ : ℝ) : 𝕜) • re a
  have hmax (a : A) : 0 < max 1 ‖re a‖ := zero_lt_one.trans_le (le_max_left _ _)
  have hre : Continuous re := by fun_prop
  have hg : Continuous g := (RCLike.continuous_ofReal.comp
    ((continuous_const.max (continuous_norm.comp hre)).inv₀ fun a => (hmax a).ne')).smul hre
  have h2 : IsSelfAdjoint (2⁻¹ : 𝕜) := by simp [IsSelfAdjoint]
  have hgz : g z = z := by
    have hrez : re z = z := by
      simp only [re]
      rw [hzsa.star_eq, ← two_smul 𝕜 z, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    simp [g, hrez, max_eq_left hz₁]
  refine hgz ▸ map_mem_closure hg hz fun a ha => ⟨?_, ?_, ?_⟩
  · exact SMulMemClass.smul_mem _ (SMulMemClass.smul_mem _ (add_mem ha (star_mem ha)))
  · exact IsSelfAdjoint.smul (RCLike.conj_ofReal _) (h2.smul (.add_star_self a))
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (hmax a).le)]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hmax a).le

end StarSubalgebra
