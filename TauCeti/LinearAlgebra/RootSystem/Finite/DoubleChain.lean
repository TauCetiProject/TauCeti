/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString

/-!
# Double root chains

For a finite crystallographic root pairing, a double chain `β, α + β, 2α + β` has
linearly independent step and initial roots, and ascending coefficient at least two.
A local bound on the string length determines its descending and ascending coefficients.
The exclusions `3α + β` and `α + 2β` needed in the Chevalley commutator formula follow
from these coefficients, without reducedness or a global Cartan-integer bound.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic]

/-- The step and initial roots of a double chain are linearly independent, even in a
non-reduced root pairing. -/
theorem linearIndependent_of_root_eq_add_of_root_eq_add {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) :
    LinearIndependent R ![P.root α, P.root β] := by
  let : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [P.linearIndependent_iff_coxeterWeightIn_ne_four ℤ]
  intro hw
  have hab := P.pairingIn_pairingIn_mem_set_of_isCrystallographic α β
  have hag := P.pairingIn_pairingIn_mem_set_of_isCrystallographic α γ
  have had := P.pairingIn_pairingIn_mem_set_of_isCrystallographic α δ
  have hbg := P.pairingIn_pairingIn_mem_set_of_isCrystallographic β γ
  have hbd := P.pairingIn_pairingIn_mem_set_of_isCrystallographic β δ
  have hga := pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := α) hγ
  have hda := pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := α) hδ
  have hgb := pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := β) hγ
  have hdb := pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := β) hδ
  have hgg := pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := γ) hγ
  have hgd := pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := δ) hγ
  have hdd := pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := δ) hδ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hab hag had hbg hbd
  simp only [coxeterWeightIn] at hw
  simp only [pairingIn_same] at hga hda hgb hdb hgg hdd
  rcases hab with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    obtain ⟨h₁, h₂⟩ := h <;> rw [h₁, h₂] at hw <;> norm_num at hw
  all_goals omega

/-- A double chain has ascending coefficient at least two at its initial root. -/
theorem two_le_chainTopCoeff_of_root_eq_add_of_root_eq_add {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) : 2 ≤ P.chainTopCoeff α β := by
  apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
    (P.linearIndependent_of_root_eq_add_of_root_eq_add hγ hδ)).1
  exact ⟨δ, by rw [hδ, hγ]; abel⟩

/-- A double chain whose ascending and descending coefficients sum to at most two
has descending coefficient zero. -/
theorem chainBotCoeff_eq_zero_of_chainBotCoeff_add_chainTopCoeff_le_two {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hlen : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2) :
    P.chainBotCoeff α β = 0 := by
  have := P.two_le_chainTopCoeff_of_root_eq_add_of_root_eq_add hγ hδ
  omega

/-- A double chain with ascending coefficient at most two has ascending coefficient two. -/
theorem chainTopCoeff_eq_two_of_chainTopCoeff_le_two {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (htop : P.chainTopCoeff α β ≤ 2) : P.chainTopCoeff α β = 2 :=
  htop.antisymm (P.two_le_chainTopCoeff_of_root_eq_add_of_root_eq_add hγ hδ)

/-- The sum `α + δ = 3α + β` is not a root if the `α`-string through `β` has top
coefficient at most two, where `γ = α + β` and `δ = α + γ`. -/
theorem root_add_root_notMem_range_root_of_chainTopCoeff_le_two {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (htop : P.chainTopCoeff α β ≤ 2) : P.root α + P.root δ ∉ Set.range P.root := by
  have hli := P.linearIndependent_of_root_eq_add_of_root_eq_add hγ hδ
  have hthree : P.root β + 3 • P.root α ∉ Set.range P.root := by
    rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli]
    omega
  have had : P.root α + P.root δ = P.root β + 3 • P.root α := by
    rw [hδ, hγ]
    module
  simpa only [had] using hthree

/-- If the `α`-string through `β` starts at `β` and has top coefficient two, then
`β + γ = α + 2β` is not a root, where `γ = α + β`. -/
theorem root_add_root_notMem_range_root_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
    {α β γ : ι} (hγ : P.root γ = P.root α + P.root β)
    (hbot : P.chainBotCoeff α β = 0) (htop : P.chainTopCoeff α β = 2) :
    P.root β + P.root γ ∉ Set.range P.root := by
  have hli : LinearIndependent R ![P.root α, P.root β] := by
    by_contra hli
    have := P.chainTopCoeff_of_not_linearIndependent hli
    omega
  have hrev := P.chainTopCoeff_eq_one_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
    hbot htop
  have htwo : P.root α + 2 • P.root β ∉ Set.range P.root := by
    rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
      (LinearIndependent.pair_symm_iff.mp hli), hrev]
    omega
  have hbg : P.root β + P.root γ = P.root α + 2 • P.root β := by
    rw [hγ]
    module
  simpa only [hbg] using htwo

end RootPairing
