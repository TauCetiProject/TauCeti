/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.RepresentationTheory.Invariants

/-!
# Character of the quotient action on invariants

For a finite normal subgroup whose order is invertible in the coefficient field, the character
of the quotient action on its invariant subspace is the average of the original character on
the corresponding coset. Thus that coset average is itself a character value.
-/

public section

namespace Representation

/-- The trace of `gN` on the `N`-invariants is the average of the character on `gN`. -/
theorem character_quotientToInvariants_mk {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Module.Finite k V] (ρ : Representation k G V)
    (N : Subgroup G) [N.Normal] [Fintype N] [Invertible (Fintype.card N : k)] (g : G) :
    (ρ.quotientToInvariants N).character (QuotientGroup.mk' N g) =
      (Nat.card N : k)⁻¹ * ∑ n : N, ρ.character (g * n) := by
  let σ : Representation k N V := ρ.comp N.subtype
  let I := σ.invariants
  let π : V →ₗ[k] I := σ.averageMap.codRestrict I σ.averageMap_invariant
  let f : Module.End k I := ρ.quotientToInvariants N (QuotientGroup.mk' N g)
  have hcomp : (I.subtype ∘ₗ f) ∘ₗ π = ρ g ∘ₗ σ.averageMap := by
    apply LinearMap.ext
    intro v
    exact IntertwiningMap.isIntertwining _ _ (ρ.quotientToInvariants_lift N) g (π v)
  have hπ : π ∘ₗ (I.subtype ∘ₗ f) = f := by
    apply LinearMap.ext
    intro v
    exact Subtype.ext (σ.averageMap_id _ (f v).property)
  calc
    _ = LinearMap.trace k I f := by rw [character]
    _ = LinearMap.trace k V (ρ g ∘ₗ σ.averageMap) := by
      rw [← hcomp, LinearMap.trace_comp_comm' π, hπ]
    _ = _ := by
      rw [σ.averageMap_eq_invOf_card_smul_norm, LinearMap.comp_smul, map_smul, smul_eq_mul,
        invOf_eq_inv, ← Nat.card_eq_fintype_card]
      congr 1
      simp only [norm, ← Module.End.mul_eq_comp, Finset.mul_sum, map_sum, character, map_mul,
        MonoidHom.comp_apply, Subgroup.subtype_apply, σ]

end Representation
