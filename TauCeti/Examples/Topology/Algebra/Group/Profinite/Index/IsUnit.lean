/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Algebra.Group.Profinite.Index.IsUnit
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic

/-!
# Examples of invertible indices of open subgroups

For `ℓ ≠ p` the group `ℤ_p` has pro-order prime to `ℓ`, so the index `p ^ k` of each level
`p ^ k ℤ_p` is a unit of `𝔽_ℓ`; for `p = 2`, `ℓ = 5` and `k = 1` its inverse is `3`. A finite
cyclic group of order prime to `ℓ` behaves the same way, and the trivial group has invertible
indices in every commutative ring, including the zero ring. For `K = ℤ_ℓ` over `𝔽_ℓ` the level
`ℓ ℤ_ℓ` has index `ℓ = 0`, which is not a unit, and correspondingly `ℓ` has nonzero exponent in the
supernatural order of `ℤ_ℓ`.
-/

namespace TauCeti

example {p : ℕ} [Fact p.Prime] {ℓ : Nat.Primes} (h : (ℓ : ℕ) ≠ p) :
    (∀ U : OpenSubgroup (Multiplicative ℤ_[p]), IsUnit (U.toSubgroup.index : ZMod ℓ)) ∧
      ∀ k : ℕ, IsUnit ((p ^ k : ℕ) : ZMod ℓ) := by
  have hK : profiniteOrder (Multiplicative ℤ_[p]) ℓ = 0 := by
    rw [profiniteOrder_multiplicative_padicInt]
    exact Supernatural.primePower_apply_of_ne (fun h' ↦ h (congrArg Subtype.val h')) ⊤
  refine ⟨fun U ↦ U.isUnit_index_of_profiniteOrder_apply_eq_zero hK (by simp), fun k ↦ ?_⟩
  simpa using (padicIntLevel p k).toOpenSubgroup.isUnit_index_of_profiniteOrder_apply_eq_zero hK
    (Λ := ZMod ℓ) (by simp)

example : (padicIntLevel 2 1).toSubgroup.index = 2 ∧ ((2 : ℕ) : ZMod 5) * 3 = 1 :=
  ⟨by simp, by decide⟩

example {m : ℕ} [NeZero m] {ℓ : Nat.Primes} (h : ¬ (ℓ : ℕ) ∣ m)
    (U : OpenSubgroup (Multiplicative (ZMod m))) : IsUnit (U.toSubgroup.index : ZMod ℓ) := by
  refine U.isUnit_index_of_profiniteOrder_apply_eq_zero (ℓ := ℓ) ?_ (by simp)
  simpa [Nat.padicValNat_def] using multiplicity_eq_zero_of_not_dvd h

example {Λ : Type*} [CommRing Λ] (ℓ : Nat.Primes) (hΛ : IsNilpotent ((ℓ : ℕ) : Λ))
    (U : OpenSubgroup (Multiplicative (ZMod 1))) : IsUnit (U.toSubgroup.index : Λ) :=
  U.isUnit_index_of_profiniteOrder_apply_eq_zero (by simp [Nat.padicValNat_def]) hΛ

example (ℓ : ℕ) [Fact ℓ.Prime] : ¬ IsUnit ((padicIntLevel ℓ 1).toSubgroup.index : ZMod ℓ) := by
  simp

example (ℓ : ℕ) [Fact ℓ.Prime] :
    profiniteOrder (Multiplicative ℤ_[ℓ]) (⟨ℓ, Fact.out⟩ : Nat.Primes) ≠ 0 := by
  intro h
  have hunit := (profiniteOrder_apply_eq_zero_iff_forall_isUnit_index (Λ := ZMod ℓ)
    (by simp)).mp h (padicIntLevel ℓ 1).toOpenSubgroup
  simp at hunit

end TauCeti
