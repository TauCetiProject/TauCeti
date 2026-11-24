/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Category.ModuleCat.Abelian
import TauCeti.RingTheory.Almost.ProZero

/-!
# Examples of almost-pro-zero towers

These examples test almost-pro-zero diagrams:

* for a basic setup with `m ≠ V`, the constant tower `V ⧸ m` is almost-pro-zero but not pro-zero,
  so being almost-pro-zero is strictly weaker than being pro-zero;
* for the classical setup of a nontrivial ring `V`, the constant tower `V` is not
  almost-pro-zero;
* for the zero setup every tower is almost-pro-zero;
* the almost-pro-isomorphisms of towers of modules satisfy two-out-of-three.
-/

open CategoryTheory TauCeti TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type} [CommRing V]

-- For `m ≠ V` the constant tower `V ⧸ m` is almost-pro-zero but not pro-zero.
example (S : BasicSetup V) (h : S.ideal ≠ ⊤) :
    S.IsAlmostProZero ((Functor.const ℕᵒᵖ).obj (ModuleCat.of V (V ⧸ S.ideal))) ∧
      ¬ ((Functor.const ℕᵒᵖ).obj (ModuleCat.of V (V ⧸ S.ideal))).IsProZero := by
  refine ⟨isAlmostProZero_const_iff.mpr S.isAlmostZero_quotient, fun hF ↦ h ?_⟩
  rw [← isAlmostProZero_classical_iff (V := V), isAlmostProZero_const_iff,
    isAlmostZero_classical_iff] at hF
  exact Ideal.Quotient.subsingleton_iff.mp hF

-- For the classical setup of a nontrivial ring, the constant tower `V` is not almost-pro-zero.
example [Nontrivial V] :
    ¬ (classical V).IsAlmostProZero ((Functor.const ℕᵒᵖ).obj (ModuleCat.of V V)) := by
  rw [isAlmostProZero_const_iff, isAlmostZero_classical_iff]
  exact fun _ ↦ zero_ne_one (Subsingleton.elim (0 : V) 1)

-- For the zero setup every tower is almost-pro-zero.
example (F : ModuleTower.{0} V) : (zero V).IsAlmostProZero F :=
  isAlmostProZero_zero F

-- Almost-pro-isomorphisms of towers of modules satisfy two-out-of-three.
example (S : BasicSetup V) :
    (S.almostProIsomorphisms ℕᵒᵖ (ModuleCat.{0} V)).HasTwoOutOfThreeProperty :=
  inferInstance
