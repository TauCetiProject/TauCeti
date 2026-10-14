/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.Clopen
public import Mathlib.Analysis.Normed.Ring.Int

/-!
# Clopen measure examples

On a discrete two-point space, extension by zero distinguishes the inside and outside points,
and restriction removes exactly the Dirac mass outside the clopen. The complementary
restrictions retain both signed masses and recombination recovers the original measure.
The empty-clopen examples check the degenerate case without a nonemptiness hypothesis.
-/

public section

open TopologicalSpace AbstractMeasure
open scoped AbstractMeasure

namespace TauCeti

/-- Discrete topology used locally in the two-point examples. -/
local instance finTwoTopology : TopologicalSpace (Fin 2) := ⊥

/-- The topology in the two-point examples is discrete. -/
local instance finTwoDiscreteTopology : DiscreteTopology (Fin 2) := ⟨rfl⟩

private def s : Clopens (Fin 2) := ⟨{0}, isClopen_discrete _⟩

example : zeroExtendClopen s ℤ (.const s 7) (0 : Fin 2) = 7 := by
  exact zeroExtendClopen_apply_mem s ℤ _ ⟨0, rfl⟩

example : zeroExtendClopen s ℤ (.const s 7) (1 : Fin 2) = 0 := by
  exact zeroExtendClopen_apply_not_mem s ℤ _ (by simp [s])

example : zeroExtendClopen (⊥ : Clopens (Fin 2)) ℤ 0 = 0 := by simp

example : restrictClopen s ℤ
    ((2 : ℤ) • dirac ℤ (0 : Fin 2) - (3 : ℤ) • dirac ℤ (1 : Fin 2)) =
    (2 : ℤ) • dirac ℤ (⟨0, rfl⟩ : s) := by
  rw [map_sub, map_smul, map_smul, restrictClopen_dirac_mem s ℤ ⟨0, rfl⟩,
    restrictClopen_dirac_not_mem s ℤ (by simp [s])]
  simp

example : restrictClopen s ℤ (dirac ℤ (1 : Fin 2)) = 0 :=
  restrictClopen_dirac_not_mem s ℤ (by simp [s])

example {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : Type*} [NormedCommRing R]
    (μ : D(X, R)) : restrictClopen (⊥ : Clopens X) R μ = 0 := by simp

example : clopenDecomposition s ℤ
    ((2 : ℤ) • dirac ℤ (0 : Fin 2) - (3 : ℤ) • dirac ℤ (1 : Fin 2)) =
    ((2 : ℤ) • dirac ℤ (⟨0, rfl⟩ : s),
      -(3 : ℤ) • dirac ℤ (⟨1, by simp [← SetLike.mem_coe, Clopens.coe_compl, s]⟩ :
        (sᶜ : Clopens (Fin 2)))) := by
  rw [clopenDecomposition_apply]
  apply Prod.ext
  · dsimp only
    rw [map_sub, map_smul, map_smul, restrictClopen_dirac_mem s ℤ ⟨0, rfl⟩,
      restrictClopen_dirac_not_mem s ℤ (by simp [s])]
    simp
  · dsimp only
    rw [map_sub, map_smul, map_smul,
      restrictClopen_dirac_not_mem sᶜ ℤ (by simp [← SetLike.mem_coe, Clopens.coe_compl, s]),
      restrictClopen_dirac_mem sᶜ ℤ
        ⟨1, by simp [← SetLike.mem_coe, Clopens.coe_compl, s]⟩]
    simp

example : (clopenDecomposition s ℤ).symm
    (dirac ℤ (⟨0, rfl⟩ : s), dirac ℤ
      (⟨1, by simp [← SetLike.mem_coe, Clopens.coe_compl, s]⟩ : (sᶜ : Clopens (Fin 2)))) =
    dirac ℤ (0 : Fin 2) + dirac ℤ (1 : Fin 2) := by
  rw [clopenDecomposition_symm_apply]
  simp [ContinuousMap.subtypeVal]

example {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : Type*} [NormedCommRing R]
    (μ : D(X, R)) : clopenDecomposition (⊥ : Clopens X) R μ =
      ((0 : D((⊥ : Clopens X), R)), restrictClopen (⊥ : Clopens X)ᶜ R μ) := by simp

example {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : Type*} [NormedCommRing R]
    (μ : D(X, R)) : map (ContinuousMap.subtypeVal ((⊥ : Clopens X)ᶜ : Clopens X))
      (restrictClopen (⊥ : Clopens X)ᶜ R μ) = μ := by
  have h := map_subtype_restrictClopen_add_compl (⊥ : Clopens X) R μ
  simpa only [restrictClopen_bot, map_zero, zero_add] using h

end TauCeti
