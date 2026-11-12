/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Degree tails in an internal direct sum

An integer-valued function on the indices defines a decreasing family of
submodules, formed by summing components above each natural cutoff. Membership
means that all components below the cutoff vanish, so these tails are separated.
The degree function need not be additive and the module need not be free.

## Attribution

Adapted from `Mei/Algebra/DirectSum/Degree/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0). Original copyright and author credit
are retained.
-/

public section

namespace TauCeti.DirectSum

open _root_.DirectSum

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M) (d : ι → ℤ)

/-- The submodule supported in degrees at least `n`. -/
def degreeTail (n : ℕ) : Submodule R M := ⨆ i, ⨆ (_ : (n : ℤ) ≤ d i), ℳ i

/-- The degree tail is the sum of its homogeneous components. -/
theorem degreeTail_def (n : ℕ) :
    degreeTail ℳ d n = ⨆ i, ⨆ (_ : (n : ℤ) ≤ d i), ℳ i := (rfl)

/-- A component above the cutoff lies in the degree tail. -/
theorem le_degreeTail {n : ℕ} {i : ι} (hi : (n : ℤ) ≤ d i) : ℳ i ≤ degreeTail ℳ d n :=
  le_iSup_of_le i (le_iSup_of_le hi le_rfl)

/-- Higher degree tails are smaller. -/
theorem degreeTail_antitone : Antitone (degreeTail ℳ d) := by
  intro m n hmn
  simp only [degreeTail_def, iSup_le_iff]
  intro i hi
  exact le_degreeTail ℳ d ((Int.ofNat_le.mpr hmn).trans hi)

variable [DecidableEq ι] [Decomposition ℳ]

/-- The degree-zero tail is the whole module if all negative components vanish. -/
@[simp]
theorem degreeTail_zero (hneg : ∀ i, d i < 0 → ℳ i = ⊥) : degreeTail ℳ d 0 = ⊤ := by
  apply top_unique
  rw [← (Decomposition.isInternal ℳ).submodule_iSup_eq_top]
  apply iSup_le
  intro i
  by_cases hi : 0 ≤ d i
  · exact le_degreeTail ℳ d (by exact_mod_cast hi)
  · rw [hneg i (lt_of_not_ge hi)]
    exact bot_le

/-- An element is in a degree tail exactly when its lower components vanish. -/
theorem mem_degreeTail_iff {n : ℕ} {x : M} :
    x ∈ degreeTail ℳ d n ↔ ∀ i, d i < n → (decompose ℳ x i : M) = 0 := by
  constructor
  · intro hx i hi
    rw [degreeTail_def] at hx
    refine Submodule.iSup_induction _ (motive := fun x => (decompose ℳ x i : M) = 0) hx
      (fun j x hx => ?_) (by simp) (fun x y hx hy => by simp [hx, hy])
    refine Submodule.iSup_induction _ (motive := fun x => (decompose ℳ x i : M) = 0) hx
      (fun hj x hx => ?_) (by simp) (fun x y hx hy => by simp [hx, hy])
    exact decompose_of_mem_ne ℳ hx (by intro h; subst j; omega)
  · intro hx
    classical
    rw [← sum_support_decompose ℳ x]
    apply Submodule.sum_mem
    intro i _
    by_cases hd : (n : ℤ) ≤ d i
    · exact le_degreeTail ℳ d hd (decompose ℳ x i).property
    · rw [hx i (lt_of_not_ge hd)]
      exact Submodule.zero_mem _

/-- Degree tails of an internal direct sum are separated. -/
theorem iInf_degreeTail_eq_bot : (⨅ n : ℕ, degreeTail ℳ d n) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  apply (decomposeLinearEquiv ℳ).injective
  apply _root_.DirectSum.ext
  intro i
  apply Subtype.ext
  have hxi : x ∈ degreeTail ℳ d ((d i).toNat + 1) :=
    (iInf_le (fun n => degreeTail ℳ d n) ((d i).toNat + 1)) hx
  have hi := (mem_degreeTail_iff ℳ d).mp hxi i (by omega)
  simpa only [decomposeLinearEquiv_apply, decompose_zero,
    _root_.DirectSum.zero_apply, ZeroMemClass.coe_zero] using hi

end TauCeti.DirectSum
