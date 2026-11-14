/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Module.Injective.Envelope.ModuleCat
public import TauCeti.CategoryTheory.Abelian.Injective.MinimalCoresolution

/-!
# Minimal injective coresolutions of modules

Every module has an injective envelope (`ModuleCat.exists_injective_and_isEssentialMono`), so every
object of `ModuleCat` has minimal injective coresolutions of every length
(`ModuleCat.exists_isMinimalInjectiveCoresolution`), by
`CategoryTheory.ComposableArrows.exists_isMinimalInjectiveCoresolution`.

## Main results

* `ModuleCat.exists_isMinimalInjectiveCoresolution`: every module has minimal injective
  coresolutions of every length.
-/

public section

open CategoryTheory

universe u v

/-- **Every module has minimal injective coresolutions of every length**, since every module has
an injective envelope. -/
theorem ModuleCat.exists_isMinimalInjectiveCoresolution {R : Type u} [Ring R] [Small.{v} R]
    (M : ModuleCat.{v} R) (n : ℕ) :
    ∃ E : ComposableArrows (ModuleCat.{v} R) (n + 1), E.IsMinimalInjectiveCoresolution ∧
      Nonempty (E.obj' 1 ≅ M) := by
  obtain ⟨E, hE, e, -⟩ := ComposableArrows.exists_isMinimalInjectiveCoresolution
    (Q := fun _ ↦ True)
    (fun X _ ↦ by
      obtain ⟨I, ι, hI, hι⟩ := ModuleCat.exists_injective_and_isEssentialMono X
      exact ⟨I, ι, hI, hι, trivial, trivial⟩) n trivial (X := M)
  exact ⟨E, hE, e⟩
