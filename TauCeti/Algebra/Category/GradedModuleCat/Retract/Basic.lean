/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Retract
public import TauCeti.Algebra.Category.GradedModuleCat.Basic

/-!
# Basic properties of graded retracts

This file establishes elementary stability properties of retracts in `TauCeti.GradedModuleCat 𝒜`
without requiring free-module, augmentation, or PID hypotheses:

* `CategoryTheory.Retract.mem_positive_smul_top_iff`: membership in the positive-degree action
  `A₊ M` is preserved and reflected along a graded retract.
* `CategoryTheory.Retract.piece_eq_bot`: vanishing of a homogeneous piece passes to graded
  retracts.
-/

public section

open CategoryTheory

universe uk uA v

namespace CategoryTheory.Retract

open TauCeti TauCeti.GradedModuleCat

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- Along a graded retract, membership in the positive-degree action is preserved and reflected. -/
theorem mem_positive_smul_top_iff {M N : GradedModuleCat.{v} 𝒜} (r : Retract M N) {x : M} :
    r.i.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) ↔
      x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  refine ⟨fun hx ↦ ?_, map_mem_positive_smul_top r.i⟩
  have h := map_mem_positive_smul_top r.r hx
  have hri : r.r.hom (r.i.hom x) = x :=
    LinearMap.congr_fun (congrArg Hom.hom r.retract) x
  rwa [hri] at h

/-- Vanishing of a homogeneous piece passes to graded retracts. -/
theorem piece_eq_bot {M N : GradedModuleCat.{v} 𝒜} (r : Retract M N) {p : ℤ}
    (hp : N.grading.piece p = ⊥) : M.grading.piece p = ⊥ :=
  GradedModuleCat.piece_eq_bot_of_surjective r.r
    (Function.RightInverse.surjective fun x ↦
      LinearMap.congr_fun (congrArg Hom.hom r.retract) x) p hp

end CategoryTheory.Retract
