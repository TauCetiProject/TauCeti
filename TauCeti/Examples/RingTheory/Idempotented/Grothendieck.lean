/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import TauCeti.Data.Finsupp.Pointwise
public import TauCeti.RingTheory.Idempotented.Grothendieck

/-!
# Checks for the Grothendieck property of nondegenerate modules

* For `H = ⊕_{n ∈ ℕ} ℚ = ℕ →₀ ℚ` with the componentwise product, which has no identity element,
  `NondegMod ℚ H` is Grothendieck abelian, so it has enough injectives (Mathlib's
  `IsGrothendieckAbelian.enoughInjectives`).
* For a unital `H = A`, the separator `H • (A ⊕ A)` is nonzero when `A` is: it contains the image
  of `1 ∈ H`.
-/

public section

open CategoryTheory TauCeti

/-- Nondegenerate modules over `⊕_n ℚ` form a Grothendieck abelian category. -/
example : IsGrothendieckAbelian.{0} (NondegMod.{0} ℚ (ℕ →₀ ℚ)) := inferInstance

/-- Nondegenerate modules over `⊕_n ℚ` have enough injectives. -/
example : EnoughInjectives (NondegMod.{0} ℚ (ℕ →₀ ℚ)) := inferInstance

/-- For `H = ℚ`, the separator `H • (ℚ ⊕ ℚ)` is not the zero module: it contains `1 • 1`. -/
example : Nontrivial (NondegMod.nondegeneratePartRegular.{0} ℚ ℚ).obj := by
  refine ⟨⟨⟨((1 : ℚ) : Unitization ℚ ℚ) • equivShrink _ 1, inr_smul_mem_nondegeneratePart _ _⟩,
    0, fun h ↦ ?_⟩⟩
  have h' : ((1 : ℚ) : Unitization ℚ ℚ) • equivShrink _ 1 = (0 : Shrink.{0} (Unitization ℚ ℚ)) :=
    congrArg Subtype.val h
  have := congrArg (fun x ↦ (Shrink.linearEquiv (Unitization ℚ ℚ) (Unitization ℚ ℚ) x).snd) h'
  simp at this
