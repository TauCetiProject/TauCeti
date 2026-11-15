/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Regularity of solutions to first-order ODEs

This file contains the basic regularity theorem that a solution of a first-order equation gains one
derivative over a right-hand side that is already differentiable on its range. The parameter
set only needs unique derivatives, so the result also applies at closed interval endpoints. It
holds over any nontrivially normed field and for finite or infinite order of differentiability.
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

/-- A solution of a first-order equation with a `C^n` right-hand side is `C^(n + 1)`
within any parameter set with unique derivatives. The order `n` may be infinite: a solution
of an equation with a smooth right-hand side is smooth. -/
theorem contDiffOn_succ_of_hasDerivWithinAt_comp {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞} {f : 𝕜 → F} {v : F → F} {s : Set 𝕜}
    {u : Set F} (hs : UniqueDiffOn 𝕜 s) (hv : ContDiffOn 𝕜 n v u) (hfu : MapsTo f s u)
    (hf : ∀ t ∈ s, HasDerivWithinAt f (v (f t)) s t) :
    ContDiffOn 𝕜 (n + 1) f s := by
  have key (m : ℕ) (hm : m ≤ n + 1) : ContDiffOn 𝕜 m f s := by
    induction m with
    | zero => exact contDiffOn_zero.mpr fun t ht ↦ (hf t ht).continuousWithinAt
    | succ m ih =>
      have hmn : (m : ℕ∞) ≤ n := by simpa using hm
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin hs]
      refine ⟨fun t ht ↦ (hf t ht).differentiableWithinAt, by simp, ?_⟩
      exact ((hv.of_le (mod_cast hmn)).comp (ih (hmn.trans le_self_add)) hfu).congr
        fun t ht ↦ (hf t ht).derivWithin (hs t ht)
  exact_mod_cast contDiffOn_iff_forall_nat_le.mpr key

end TauCeti

end
