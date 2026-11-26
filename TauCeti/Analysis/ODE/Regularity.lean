/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Regularity of solutions to first-order ODEs

This file contains the basic regularity theorem that a solution of a first-order equation gains one
derivative over a right-hand side that is already differentiable on its range. The parameter
set only needs unique derivatives, so the result also applies at closed interval endpoints. It
holds over any nontrivially normed field and for finite or infinite order of differentiability.
A solution of a time-dependent equation `x' = X(t, x)` with a jointly `C^n` right-hand side is
`C^(n + 1)` (`TauCeti.contDiff_succ_of_hasDerivAt`); in particular it is `C¹` when the right-hand
side is jointly continuous (`TauCeti.contDiff_one_of_hasDerivAt`).
The same holds for a linear equation `f' = A_t f` whose coefficient `A` is `C^n` in `t`
(`TauCeti.contDiff_succ_of_hasDerivAt_clm_apply`).
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

/-- A solution of a time-dependent first-order equation `x' = X(t, x)` with a jointly `C^n`
right-hand side is `C^(n + 1)`: the curve `t ↦ (t, x t)` solves the autonomous equation of the
vector field `(t, y) ↦ (1, X(t, y))`. The order `n` may be infinite. -/
theorem contDiff_succ_of_hasDerivAt {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞} {X : 𝕜 → F → F} {x : 𝕜 → F}
    (hX : ContDiff 𝕜 n (Function.uncurry X)) (hx : ∀ t, HasDerivAt x (X t (x t)) t) :
    ContDiff 𝕜 (n + 1) x := by
  have h := contDiffOn_succ_of_hasDerivWithinAt_comp (f := fun t ↦ (t, x t)) (s := univ)
    (u := univ) (v := fun p ↦ ((1 : 𝕜), Function.uncurry X p)) uniqueDiffOn_univ
    (contDiff_const.prodMk hX).contDiffOn (mapsTo_univ _ _)
    fun t _ ↦ (HasDerivAt.prodMk (hasDerivAt_id t) (hx t)).hasDerivWithinAt
  exact contDiff_snd.comp (contDiffOn_univ.1 h)

/-- A solution of a time-dependent first-order equation `x' = X(t, x)` with a jointly continuous
right-hand side is `C¹`. -/
theorem contDiff_one_of_hasDerivAt {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {X : 𝕜 → F → F} {x : 𝕜 → F}
    (hX : Continuous (Function.uncurry X)) (hx : ∀ t, HasDerivAt x (X t (x t)) t) :
    ContDiff 𝕜 1 x := by
  simpa using contDiff_succ_of_hasDerivAt (n := 0) (contDiff_zero.2 hX) hx

/-- A solution of a linear equation `f' = A_t f` whose coefficient `A` is `C^n` is `C^(n + 1)`.
The order `n` may be infinite. -/
theorem contDiff_succ_of_hasDerivAt_clm_apply {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞} {A : 𝕜 → F →L[𝕜] F} {f : 𝕜 → F}
    (hA : ContDiff 𝕜 n A) (hf : ∀ t, HasDerivAt f (A t (f t)) t) :
    ContDiff 𝕜 (n + 1) f := by
  have key (m : ℕ) (hm : m ≤ n + 1) : ContDiff 𝕜 m f := by
    induction m with
    | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.2 fun t ↦ (hf t).continuousAt)
    | succ m ih =>
      have hmn : (m : ℕ∞) ≤ n := by simpa using hm
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun t ↦ (hf t).differentiableAt, by simp, ?_⟩
      rw [show deriv f = fun t ↦ A t (f t) from funext fun t ↦ (hf t).deriv]
      exact (hA.of_le (mod_cast hmn)).clm_apply (ih (hmn.trans le_self_add))
  exact_mod_cast contDiff_iff_forall_nat_le.mpr key

end TauCeti

end
