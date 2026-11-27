/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Projective.Category

/-!
# Examples of internal projectivity for almost modules

Multiplication by two on an infinite free almost module doubles a chosen coordinate through
the scalar factorization. The setup ideal supplies an internally projective almost module
through the finite factorization criterion. Over the zero setup every module admits a factorization
through the zero free module. Over the classical setup `ℤ/2` fails the lifting criterion.
-/

open CategoryTheory TauCeti.Almost TauCeti.Almost.Module

namespace TauCeti.Examples.Almost.Projective

-- Apply a factorization for the scalar `2` to the almost element with coefficient `3` at `5`.
example :
    let F := toAlmost (BasicSetup.classical ℚ)
    let A := F.obj (ModuleCat.of ℚ (ℕ →₀ ℚ))
    let element (x : ℕ →₀ ℚ) := F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ x))
    ∃ (I : Type) (u : A ⟶ F.obj (ModuleCat.of ℚ (I →₀ ℚ)))
      (v : F.obj (ModuleCat.of ℚ (I →₀ ℚ)) ⟶ A),
      element (Finsupp.single 5 3) ≫ u ≫ v = element (Finsupp.single 5 6) := by
  intro F A element
  have hA : isInternallyProjective A := isInternallyProjective_toAlmost (BasicSetup.classical ℚ) _
  obtain ⟨I, u, v, huv⟩ :=
    (isInternallyProjective_iff_factor (BasicSetup.classical ℚ) A).mp hA 2 (by simp)
  refine ⟨I, u, v, ?_⟩
  dsimp only [element]
  rw [huv, Linear.comp_smul, Category.comp_id, ← F.map_smul]
  congr 1
  apply ModuleCat.hom_ext
  norm_num [← LinearMap.toSpanSingleton_smul, Finsupp.smul_single, smul_eq_mul]

-- The setup ideal becomes internally projective without an ordinary projectivity assumption.
example {V : Type*} [CommRing V] (setup : BasicSetup V) :
    isInternallyProjective ((toAlmost setup).obj (ModuleCat.of V setup.ideal)) :=
  have h : setup.IsAlmostFiniteProjective V :=
    BasicSetup.isAlmostFiniteProjective_of_finite_of_projective setup
  (setup.isAlmostIso_subtype.isAlmostFiniteProjective_iff.mpr h).isInternallyProjective_toAlmost

-- The free module on the empty set gives the factorization for the zero setup.
example {V : Type*} [CommRing V] (M : ModuleCat V) :
    isInternallyProjective ((toAlmost (BasicSetup.zero V)).obj M) := by
  refine (isInternallyProjective_iff_factor _ _).mpr fun ε hε ↦ ?_
  have h : ε = 0 := by simpa using hε
  exact ⟨PEmpty, 0, 0, by simp [h]⟩

-- Classically the lifting condition fails on `ℤ/2`: projective `ℤ`-modules are torsion-free.
example : ¬ isInternallyProjective
    ((toAlmost (BasicSetup.classical ℤ)).obj (ModuleCat.of ℤ (ZMod 2))) := by
  simp only [isInternallyProjective_toAlmost_classical_iff]
  intro hP
  have : _root_.Module.Projective ℤ (ZMod 2) := hP
  have ht : IsSMulRegular ℤ (2 : ℤ) := .of_ne_zero two_ne_zero
  exact one_ne_zero (ht.of_flat (S := ZMod 2) (a₁ := 1) (a₂ := 0) (by decide))

end TauCeti.Examples.Almost.Projective
