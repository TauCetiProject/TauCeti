/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Basic

/-!
# Changing the generator at an elliptic point

A finite stabilizer of a point of the upper half-plane acts in the disc coordinate by rotations.
If two elements generate that stabilizer, the second is a power of the first with exponent
coprime to the stabilizer order. Its rotation factor is the same power of the first rotation
factor. Thus changing the primitive generator changes the labelled rotation, while the local
quotient coordinate `discCoordinate z τ ^ m` is unchanged.

This is the generator-change law for the cyclic local quotient model. The local model follows
Farkas--Kra, *Riemann Surfaces*, Chapter I §§4--5, and Katok, *Fuchsian Groups*, §2.4.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)

private theorem exists_coprime_zpow_of_stabilizer_generators
    (q r : stabilizer Γ z) (hq : zpowers q = ⊤) (hr : zpowers r = ⊤) :
    ∃ k : ℤ, k.gcd (Nat.card (stabilizer Γ z)) = 1 ∧ r = q ^ k := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hq.symm ▸ (mem_top r))
  refine ⟨k, ?_, hk.symm⟩
  have hmem : q ∈ zpowers r := by rw [hr]; trivial
  have hmem' : q ∈ zpowers (q ^ k) := by simpa only [hk] using hmem
  rw [mem_zpowers_zpow_iff, orderOf_eq_card_of_zpowers_eq_top hq] at hmem'
  exact hmem'

/-- Replacing a primitive elliptic generator by another raises its rotation factor to a
power coprime to the stabilizer order. This also gives the exact change in the action on every
disc coordinate. -/
theorem exists_discCoordinate_generator_transition
    (q r : stabilizer Γ z) (hq : zpowers q = ⊤) (hr : zpowers r = ⊤) :
    ∃ k : ℤ, k.gcd (Nat.card (stabilizer Γ z)) = 1 ∧ r = q ^ k ∧
      stabilizerDeriv Γ z r = (stabilizerDeriv Γ z q) ^ k ∧
      ∀ τ : ℍ, discCoordinate z (r • τ) =
        (stabilizerDeriv Γ z q) ^ k * discCoordinate z τ := by
  obtain ⟨k, hk, rfl⟩ := exists_coprime_zpow_of_stabilizer_generators Γ z q r hq hr
  refine ⟨k, hk, rfl, map_zpow _ _ _, ?_⟩
  intro τ
  rw [discCoordinate_stabilizer_smul, map_zpow]

end Subgroup
