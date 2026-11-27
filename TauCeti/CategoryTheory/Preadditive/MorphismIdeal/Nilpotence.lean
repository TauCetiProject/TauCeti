/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.RingTheory.Artinian.Defs
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Linear
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Mul
import Mathlib.RingTheory.Artinian.Module

/-!
# Detecting nilpotence of morphism ideals

A separator and a coseparator detect the zero morphism ideal through a single hom space.
When that space is Artinian, vanishing of the intersection of the powers there forces a
single power to vanish throughout the category.
-/

public section

open CategoryTheory

namespace TauCeti.MorphismIdeal

variable {C : Type*} [Category* C] [Preadditive C]

/-- In a linear category with a separator `G` and a coseparator `D`, an ideal is nilpotent
if the intersection of its powers on `Hom(G, D)` is zero and this hom module is Artinian. -/
theorem exists_pow_eq_bot_of_forall_mem_pow (I : MorphismIdeal C) (R : Type*) [Semiring R]
    [Linear R C] {G D : C} [IsArtinian R (G ⟶ D)] (hG : IsSeparator G) (hD : IsCoseparator D)
    (h : ∀ f : G ⟶ D, (∀ n : ℕ, f ∈ (I ^ n).hom G D) → f = 0) :
    ∃ n : ℕ, I ^ n = ⊥ := by
  have hpow {m n : ℕ} (hmn : m ≤ n) : I ^ n ≤ I ^ m :=
    pow_le_pow_right_of_le_one' (by rw [one_eq_top]; exact le_top) hmn
  -- Stabilize the chain on the hom space from the separator to the coseparator.
  let filtration : ℕ →o (Submodule R (G ⟶ D))ᵒᵈ :=
    ⟨fun n ↦ (I ^ n).homSubmodule R G D, fun _ _ hmn f hf ↦
      (MorphismIdeal.mem_homSubmodule R _ f).2
        (le_def.mp (hpow hmn) f ((MorphismIdeal.mem_homSubmodule R _ f).1 hf))⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes filtration
  have htest (f : G ⟶ D) (hf : f ∈ (I ^ n).hom G D) : f = 0 := by
    apply h f
    intro m
    obtain hmn | hnm := le_total m n
    · exact le_def.mp (hpow hmn) f hf
    · apply (MorphismIdeal.mem_homSubmodule R _ f).1
      have hm : (I ^ n).homSubmodule R G D = (I ^ m).homSubmodule R G D := hn m hnm
      rw [← hm]
      exact (MorphismIdeal.mem_homSubmodule R _ f).2 hf
  -- Precompose and postcompose with all test maps to detect an arbitrary morphism.
  refine ⟨n, le_antisymm (le_def.mpr fun X Y f hf ↦ mem_bot.mpr ?_) bot_le⟩
  apply (Preadditive.isSeparator_iff G).mp hG f
  intro g
  apply (Preadditive.isCoseparator_iff D).mp hD (g ≫ f)
  intro d
  exact htest _ ((I ^ n).comp_mem_right d ((I ^ n).comp_mem_left g hf))

end TauCeti.MorphismIdeal
