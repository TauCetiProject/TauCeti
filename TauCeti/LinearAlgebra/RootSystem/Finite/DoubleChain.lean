/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString

/-!
# Double root chains

For a finite reduced crystallographic root pairing whose Cartan integers lie in
`{-2, -1, 0, 1, 2}`, a double chain `β, α + β, 2α + β` determines its descending
coefficients and the non-root sums needed in the Chevalley commutator formula.

The pairing bound is explicit rather than bundled in `RootPairing.IsNotG2`, since that
Mathlib class also requires irreducibility. Thus these results apply to reducible pairings
and integral root data as well. For an `IsNotG2` pairing, supply
`RootPairing.IsNotG2.pairingIn_mem_zero_one_two`. The exclusion of `β + (2α + β)`
requires no pairing bound.

The proofs use Mathlib's root-string identities and reducedness API.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  (hbound : ∀ i j, P.pairingIn ℤ i j ∈ ({-2, -1, 0, 1, 2} : Set ℤ))

include hbound

omit [P.IsReduced] in
/-- If every Cartan integer lies between minus two and two, each root string has
ascending and descending coefficients summing to at most two.
This generalizes Mathlib's `RootPairing.chainBotCoeff_add_chainTopCoeff_le_two` in
`Mathlib.LinearAlgebra.RootSystem.Finite.G2` from `IsNotG2` to an explicit pairing bound. -/
theorem chainBotCoeff_add_chainTopCoeff_le_two_of_pairing_bound (α β : ι) :
    P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2 := by
  by_cases hli : LinearIndependent R ![P.root α, P.root β]
  · rw [← Int.ofNat_le, Nat.cast_add, Nat.cast_ofNat,
      P.chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx hli]
    have := hbound (P.chainTopIdx α β) α
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    omega
  · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, hli]

/-- In a double chain with Cartan integers bounded by two, the descending coefficient
at the initial root is zero. -/
theorem chainBotCoeff_eq_zero_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) : P.chainBotCoeff α β = 0 := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have htop : 2 ≤ P.chainTopCoeff α β := by
    apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli).1
    exact ⟨δ, by rw [hδ, hγ]; abel⟩
  have := P.chainBotCoeff_add_chainTopCoeff_le_two_of_pairing_bound hbound α β
  omega

/-- In a double chain with Cartan integers bounded by two, the ascending coefficient
at the initial root is two. -/
theorem chainTopCoeff_eq_two_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) : P.chainTopCoeff α β = 2 := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hpos := P.one_le_chainTopCoeff_of_root_add_mem ⟨δ, hδ⟩
  have hstep := P.chainTopCoeff_of_add hli (hγ.trans (add_comm _ _))
  have htotal := P.chainBotCoeff_add_chainTopCoeff_le_two_of_pairing_bound hbound α β
  omega

omit hbound [Finite ι] [P.IsCrystallographic] in
/-- The sum `α + δ` is nonzero whenever `γ = α + β` and `δ = α + γ` are roots.
No bound on Cartan integers or root-string coefficients is needed. -/
theorem root_add_last_ne_zero_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) : P.root α + P.root δ ≠ 0 := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hind := LinearIndependent.pair_iff.mp hli
  intro hz
  have hz' : (3 : R) • P.root α + (1 : R) • P.root β = 0 := calc
    _ = P.root α + P.root δ := by rw [hδ, hγ]; module
    _ = 0 := hz
  have := (hind 3 1 hz').1
  norm_num at this

omit hbound [Finite ι] [P.IsCrystallographic] in
/-- If `γ = α + β` is a root, the sum `β + γ` is nonzero. -/
theorem root_initial_add_middle_ne_zero_of_double_chain {α β γ : ι}
    (hγ : P.root γ = P.root α + P.root β) : P.root β + P.root γ ≠ 0 := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hind := LinearIndependent.pair_iff.mp hli
  intro hz
  have hz' : (1 : R) • P.root α + (2 : R) • P.root β = 0 := calc
    _ = P.root β + P.root γ := by rw [hγ]; module
    _ = 0 := hz
  have := (hind 1 2 hz').1
  norm_num at this

omit hbound in
/-- If the `α`-string through `β` starts at `β` and has top coefficient two, then
`α + δ = 3α + β` and `β + γ = α + 2β` are neither roots nor zero, where
`γ = α + β` and `δ = 2α + β`. No bound on Cartan integers is needed. -/
theorem root_add_last_and_initial_add_middle_notMem_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
    {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hbot : P.chainBotCoeff α β = 0) (htop : P.chainTopCoeff α β = 2) :
    (P.root α + P.root δ ∉ Set.range P.root ∧ P.root α + P.root δ ≠ 0) ∧
      (P.root β + P.root γ ∉ Set.range P.root ∧ P.root β + P.root γ ≠ 0) := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hrev := P.chainTopCoeff_eq_one_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
    hbot htop
  have hthree : P.root β + 3 • P.root α ∉ Set.range P.root := by
    rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli, htop]
    omega
  have htwo : P.root α + 2 • P.root β ∉ Set.range P.root := by
    rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
      (LinearIndependent.pair_symm_iff.mp hli), hrev]
    omega
  have had : P.root α + P.root δ = P.root β + 3 • P.root α := by
    rw [hδ, hγ]
    module
  have hbg : P.root β + P.root γ = P.root α + 2 • P.root β := by
    rw [hγ]
    module
  exact ⟨⟨by simpa only [had] using hthree, P.root_add_last_ne_zero_of_double_chain hγ hδ⟩,
    ⟨by simpa only [hbg] using htwo, P.root_initial_add_middle_ne_zero_of_double_chain hγ⟩⟩

/-- The sum `α + δ`, where `δ = 2α + β` is the last root of a double chain with
Cartan integers bounded by two, is neither a root nor zero. -/
theorem root_add_last_notMem_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) :
    P.root α + P.root δ ∉ Set.range P.root ∧ P.root α + P.root δ ≠ 0 := by
  exact
    (root_add_last_and_initial_add_middle_notMem_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
      P hγ hδ (P.chainBotCoeff_eq_zero_of_double_chain hbound hγ hδ)
      (P.chainTopCoeff_eq_two_of_double_chain hbound hγ hδ)).1

/-- The sum `β + γ` of the initial and middle roots of a double chain with Cartan
integers bounded by two is neither a root nor zero. -/
theorem root_initial_add_middle_notMem_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) :
    P.root β + P.root γ ∉ Set.range P.root ∧ P.root β + P.root γ ≠ 0 := by
  exact
    (root_add_last_and_initial_add_middle_notMem_of_chainBotCoeff_eq_zero_of_chainTopCoeff_eq_two
      P hγ hδ (P.chainBotCoeff_eq_zero_of_double_chain hbound hγ hδ)
      (P.chainTopCoeff_eq_two_of_double_chain hbound hγ hδ)).2

omit hbound [Finite ι] [P.IsCrystallographic] in
/-- The sum of the initial and last roots of a double chain is twice its middle root,
and hence is neither a root nor zero. No bound on Cartan integers is needed. -/
theorem root_initial_add_last_notMem_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) :
    P.root β + P.root δ ∉ Set.range P.root ∧ P.root β + P.root δ ≠ 0 := by
  let : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  let : HasUniqueDiv M := .of_isTorsionFree R M
  have heq : P.root β + P.root δ = 2 • P.root γ := by
    rw [hδ, hγ]
    abel
  rw [heq]
  exact ⟨P.nsmul_notMem_range_root, smul_ne_zero (by decide : (2 : ℕ) ≠ 0) (P.ne_zero γ)⟩

end RootPairing
