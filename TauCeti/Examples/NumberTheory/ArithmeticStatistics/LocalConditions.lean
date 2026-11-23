/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import TauCeti.NumberTheory.ArithmeticStatistics.LocalConditions

/-!
# Examples of local specifications

Squarefree integers are cut out by a nontrivial condition at every prime. In contrast, even
finitely many individually nonempty conditions can have no simultaneous global solution.
-/

open Filter Set

namespace TauCeti.LocalConditions

-- Require a nonzero residue modulo the square of each prime.
example :
    let σ : LocalConditions (fun (p : Nat.Primes) (n : ℤ) ↦ (n : ZMod (p.val ^ 2))) :=
      ⟨fun _ ↦ {0}ᶜ⟩
    σ.family = {n : ℤ | Squarefree n} ∧ ¬ σ.FinitelyMany := by
  intro σ
  constructor
  · ext n
    simp only [mem_family, σ, mem_compl_iff, mem_singleton_iff,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, Nat.Primes, Subtype.forall, mem_ofPred_eq,
      Int.squarefree_iff_prime_sq_not_dvd]
  · intro h
    have hproper (p : Nat.Primes) : σ.cond p ≠ Set.univ := by
      intro hp
      have hz : (0 : ZMod (p.val ^ 2)) ∈ σ.cond p := hp ▸ mem_univ _
      simp [σ] at hz
    have hfin : (Set.univ : Set Nat.Primes).Finite :=
      (σ.finitelyMany_iff.mp h).subset fun p _ ↦ hproper p
    exact Set.infinite_univ hfin

-- All localizations are the identity, but places 0 and 1 demand different values.
example :
    let σ : LocalConditions (fun (_ : ℕ) (x : Bool) ↦ x) :=
      ⟨fun
        | 0 => {false}
        | 1 => {true}
        | _ + 2 => Set.univ⟩
    σ.FinitelyMany ∧ (∀ v, (σ.cond v).Nonempty) ∧ ¬ σ.IsLargeRel (fun _ ↦ ∅) := by
  intro σ
  refine ⟨σ.finitelyMany_iff.mpr ?_, ?_, ?_⟩
  · refine (finite_lt_nat 2).subset ?_
    rintro (_ | _ | v) hv
    · decide
    · decide
    · exact (hv rfl).elim
  · rintro (_ | _ | v) <;> simp [σ]
  · have hempty : σ.family = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
      have h := σ.mem_family.mp hx
      have h₀ : x = false := h 0
      have h₁ : x = true := h 1
      cases h₀.symm.trans h₁
    intro h
    obtain ⟨_, hv⟩ := ((σ.isLargeRel_iff _).mp h).exists
    simp [hempty] at hv

end TauCeti.LocalConditions
