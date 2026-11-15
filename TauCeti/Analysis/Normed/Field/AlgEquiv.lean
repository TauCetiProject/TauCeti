/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique

/-!
# Algebraic automorphisms preserve the extended norm

An automorphism of an algebraic normed extension of a complete nontrivially normed field
preserves the norm, by uniqueness of multiplicative algebra norms. In particular it extends
continuously to the completion. No ultrametric hypothesis is needed.
-/

public section

namespace AlgEquiv

/-- Automorphisms of an algebraic normed extension of a complete nontrivially normed field
are isometries. -/
theorem isometry_of_isAlgebraic {K M : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] [NormedField M] [NormedAlgebra K M]
    [Algebra.IsAlgebraic K M] (σ : M ≃ₐ[K] M) : Isometry σ := by
  let f : MulAlgebraNorm K M :=
    { toFun := fun x ↦ ‖σ x‖
      map_zero' := by simp
      add_le' := fun x y ↦ by simpa using norm_add_le (σ x) (σ y)
      neg' := fun x ↦ by simp
      map_one' := by simp
      map_mul' := fun x y ↦ by simp [norm_mul]
      eq_zero_of_map_eq_zero' := fun x hx ↦ σ.injective (by simpa using hx)
      smul' := fun r x ↦ by simp [norm_smul] }
  apply AddMonoidHomClass.isometry_of_norm σ
  intro x
  exact congrArg (fun g : MulAlgebraNorm K M ↦ g x) (f.unique (NormedAlgebra.toMulAlgebraNorm K M))

end AlgEquiv
