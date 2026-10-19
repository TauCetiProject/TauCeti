/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import Mathlib.Algebra.Algebra.Operations

/-!
# Positive-degree action on concentrated graded modules

A graded module concentrated in a single internal degree is annihilated by positive-degree
scalars. Concentration is preserved by graded surjections.
Such modules are the test targets for detecting the generating degrees of minimal
projective resolution terms via Ext. The algebra itself need not be nonnegatively graded.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for the concentrated targets of the diagonal Ext criterion.
-/

public section

namespace TauCeti.GradedModuleCat

open _root_.DirectSum

universe uk uA v

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- Positive-degree scalars annihilate any module concentrated in one internal degree. -/
theorem positive_smul_top_eq_bot_of_concentrated (N : GradedModuleCat.{v} 𝒜) (p : ℤ)
    (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥) :
    (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥ := by
  apply le_antisymm _ bot_le
  refine Submodule.smul_le.mpr fun a ha y hy ↦ ?_
  clear hy
  refine Submodule.iSup_induction _ (motive := fun a => a • y ∈ (⊥ : Submodule k N))
    ha (fun i a ha => ?_) (by simp)
    (fun a b ha hb => by simpa only [add_smul] using Submodule.add_mem _ ha hb)
  refine Submodule.iSup_induction _ (motive := fun a => a • y ∈ (⊥ : Submodule k N))
    ha (fun hi a ha => ?_) (by simp)
    (fun a b ha hb => by simpa only [add_smul] using Submodule.add_mem _ ha hb)
  induction y using DirectSum.Decomposition.inductionOn N.grading.piece with
  | zero => simp
  | add y z hy hz => simpa [smul_add] using Submodule.add_mem _ hy hz
  | @homogeneous q y =>
    by_cases hq : q = p
    · have hz := SetLike.GradedSMul.smul_mem (B := N.grading.piece) ha y.property
      simpa only [vadd_eq_add, hN (i + q) (by omega), Submodule.mem_bot] using hz
    · have hz : (y : N) = 0 := by simpa only [hN q hq, Submodule.mem_bot] using y.property
      simp [hz]

end TauCeti.GradedModuleCat
