/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Dual.Rescaled

/-!
# Supersingular K3 lattices and the bound on the Artin invariant

Let `X` be a K3 surface over an algebraically closed field of characteristic `p > 0` whose Picard
lattice has rank `22`. Its Picard lattice is an even lattice of signature `(1, 21)`, and the
crystalline theory of Artin, Rudakov–Shafarevich and Ogus shows that its discriminant group is
`(ℤ/p)^{2σ}` for an integer `σ`, the *Artin invariant* of `X`. Following Rudakov–Shafarevich, an
even lattice of signature `(1, 0, 21)` whose discriminant group is killed by `p` and has order
`p^{2σ}` is a *supersingular K3 lattice* of characteristic `p` and Artin invariant `σ`
(`TauCeti.IntegralLattice.IsSupersingularK3Lattice`).

This file proves the lattice-theoretic half of the bound `1 ≤ σ ≤ 10` on the Artin invariant:

* An even lattice of signature `(1, 0, 21)` is never unimodular, since Milgram's theorem would
  force `8 ∣ 1 − 21 = −20`. Hence `σ ≥ 1`.
* The discriminant group of a lattice of rank `22` killed by `p` has order dividing `p^22`, so
  `σ ≤ 11`. If `σ = 11`, then `L = pLᵛ`, and when the level of `L` divides `p` the rescaled dual
  `Lᵛ(p)` is an even unimodular lattice of signature `(1, 0, 21)`, which is again impossible. For
  odd `p` the level condition holds automatically; for `p = 2` it is the parity of the rescaled
  form `B / 2` on `L = 2Lᵛ`, an extra input. Hence `σ ≤ 10`.
* The determinant of such a lattice is `−p^{2σ}`, negative because the negative index `21` is
  odd, so `σ` is determined by `L`.

## Main definitions and results

* `TauCeti.IntegralLattice.IsSupersingularK3Lattice`: `L` is a supersingular K3 lattice of
  characteristic `p` and Artin invariant `σ`.
* `TauCeti.IntegralLattice.not_isUnimodular_of_signature_eq_one_zero_twentyOne`: an even lattice
  of signature `(1, 0, 21)` is not unimodular.
* `TauCeti.IntegralLattice.IsSupersingularK3Lattice.determinant_eq`: the determinant is
  `−p^{2σ}`.
* `TauCeti.IntegralLattice.IsSupersingularK3Lattice.one_le`: `1 ≤ σ`.
* `TauCeti.IntegralLattice.IsSupersingularK3Lattice.le_ten` and
  `TauCeti.IntegralLattice.IsSupersingularK3Lattice.le_ten_of_odd`: `σ ≤ 10`, given the parity
  of `B / p` at `σ = 11`, which is automatic for odd `p`.
* `TauCeti.IntegralLattice.IsSupersingularK3Lattice.unique`: the Artin invariant is determined by
  the lattice and the characteristic.

## References

* A. N. Rudakov and I. R. Shafarevich, *Surfaces of type K3 over fields of finite
  characteristic*, §1.
* A. Ogus, *Supersingular K3 crystals*, §3.
* D. Huybrechts, *Lectures on K3 surfaces*, Chapter 17, Proposition 2.19.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- **An even lattice of signature `(1, 0, 21)` is not unimodular.** By Milgram's theorem an even
unimodular lattice has `8 ∣ t₊ − t₋`, while here `t₊ − t₋ = −20`. -/
theorem not_isUnimodular_of_signature_eq_one_zero_twentyOne (hL : L.IsEven)
    (hsig : L.signature = (1, 0, 21)) : ¬ L.IsUnimodular := by
  intro hU
  have h8 := L.eight_dvd_sigPos_sub_sigNeg_of_isUnimodular hL hU
  simp only [signature, Prod.mk.injEq] at hsig
  rw [hsig.1, hsig.2.2] at h8
  norm_num at h8

/-- **A supersingular K3 lattice of characteristic `p` and Artin invariant `σ`**: an even lattice
of signature `(1, 0, 21)` whose discriminant group is killed by `p` and has order `p^{2σ}`, so that
it is `(ℤ/p)^{2σ}` when `p` is prime. The Picard lattice of a K3 surface of Picard rank `22` in
characteristic `p` has this shape. -/
structure IsSupersingularK3Lattice (L : IntegralLattice V) (p σ : ℕ) : Prop where
  /-- The lattice is even. -/
  isEven : L.IsEven
  /-- The lattice has signature `(1, 0, 21)`. -/
  signature_eq : L.signature = (1, 0, 21)
  /-- The discriminant group is killed by `p`. -/
  nsmul_eq_zero : ∀ x : L.DiscriminantGroup, p • x = 0
  /-- The discriminant group has order `p^{2σ}`. -/
  natCard_discriminantGroup_eq : Nat.card L.DiscriminantGroup = p ^ (2 * σ)

/-- The defining characterization of `IsSupersingularK3Lattice`. -/
theorem isSupersingularK3Lattice_iff {p σ : ℕ} :
    L.IsSupersingularK3Lattice p σ ↔ L.IsEven ∧ L.signature = (1, 0, 21) ∧
      (∀ x : L.DiscriminantGroup, p • x = 0) ∧
        Nat.card L.DiscriminantGroup = p ^ (2 * σ) :=
  ⟨fun h ↦ ⟨h.isEven, h.signature_eq, h.nsmul_eq_zero, h.natCard_discriminantGroup_eq⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩⟩

namespace IsSupersingularK3Lattice

variable {p σ : ℕ} (h : L.IsSupersingularK3Lattice p σ)
include h

/-- The positive index of inertia of a supersingular K3 lattice is `1`. -/
theorem sigPos_eq : L.sigPos = 1 := by
  have := h.signature_eq
  simp only [signature, Prod.mk.injEq] at this
  exact this.1

/-- The null index of a supersingular K3 lattice is `0`. -/
theorem sigNull_eq : L.sigNull = 0 := by
  have := h.signature_eq
  simp only [signature, Prod.mk.injEq] at this
  exact this.2.1

/-- The negative index of inertia of a supersingular K3 lattice is `21`. -/
theorem sigNeg_eq : L.sigNeg = 21 := by
  have := h.signature_eq
  simp only [signature, Prod.mk.injEq] at this
  exact this.2.2

/-- A supersingular K3 lattice has rank `22`. -/
theorem finrank_eq : finrank ℚ V = 22 := by
  rw [← L.signature_sum_eq_finrank, h.sigPos_eq, h.sigNull_eq, h.sigNeg_eq]

/-- A supersingular K3 lattice is nondegenerate, its null index being `0`. -/
theorem isNondegenerate : L.IsNondegenerate := by
  exact ⟨by_contra fun hnd ↦ by
    simpa [h.sigNull_eq] using L.isDegenerate_iff_sigNull_pos.mp
      (L.isDegenerate_iff_not_nondegenerate.mpr hnd)⟩

/-- **The determinant of a supersingular K3 lattice is `−p^{2σ}`**: its absolute value is the
order of the discriminant group, and its sign is `(−1)^21`. -/
theorem determinant_eq : L.determinant = -(p : ℤ) ^ (2 * σ) := by
  rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, h.sigNeg_eq,
    ← IntegralLattice.natCard_discriminantGroup, h.natCard_discriminantGroup_eq]
  push_cast
  ring

/-- **The Artin invariant of a supersingular K3 lattice is positive**: `σ = 0` would make the
lattice unimodular. -/
theorem one_le : 1 ≤ σ := by
  refine Nat.one_le_iff_ne_zero.mpr fun hσ ↦
    not_isUnimodular_of_signature_eq_one_zero_twentyOne h.isEven h.signature_eq ?_
  rw [isUnimodular_iff_natCard_discriminantGroup_eq_one, h.natCard_discriminantGroup_eq, hσ,
    mul_zero, pow_zero]

/-- The characteristic of a supersingular K3 lattice is at least `2`: for `p ≤ 1` the order
`p^{2σ}` of the discriminant group would be `0` or `1`. -/
theorem one_lt_char : 1 < p := by
  have := h.isNondegenerate
  have hσ := h.one_le
  have hcard := h.natCard_discriminantGroup_eq
  by_contra hp
  interval_cases p
  · rw [zero_pow (by omega)] at hcard
    exact Nat.card_pos.ne' hcard
  · rw [one_pow] at hcard
    exact not_isUnimodular_of_signature_eq_one_zero_twentyOne h.isEven h.signature_eq
      ((isUnimodular_iff_natCard_discriminantGroup_eq_one L).mpr hcard)

/-- **The Artin invariant of a supersingular K3 lattice is determined by the lattice**: two
Artin invariants of `L` in the same characteristic agree, since `p > 1` and both give the
determinant. -/
theorem unique {τ : ℕ} (h' : L.IsSupersingularK3Lattice p τ) : σ = τ := by
  have hdet := h.determinant_eq.symm.trans h'.determinant_eq
  rw [neg_inj] at hdet
  have := Nat.pow_right_injective h.one_lt_char (by exact_mod_cast hdet)
  omega

/-- **The Artin invariant of a supersingular K3 lattice is at most `11`**: the discriminant group
of a lattice of rank `22` killed by `p` has order dividing `p^22`. -/
theorem le_eleven : σ ≤ 11 := by
  have := h.isNondegenerate
  have hdvd := L.natCard_discriminantGroup_dvd_pow_finrank p h.nsmul_eq_zero
  rw [h.natCard_discriminantGroup_eq, h.finrank_eq] at hdvd
  have := (Nat.pow_dvd_pow_iff_le_right h.one_lt_char).mp hdvd
  omega

/-- **The Artin invariant of a supersingular K3 lattice is at most `10`**, provided that at
`σ = 11` the level of `L` divides `p`. At `σ = 11` one has `L = pLᵛ`, and the level condition makes
the rescaled dual `Lᵛ(p)` an even unimodular lattice of signature `(1, 0, 21)`, which does not
exist. The hypothesis cannot be dropped at `p = 2`: the odd unimodular lattice `I_{1,21}` with its
form doubled is even, of signature `(1, 0, 21)`, with discriminant group `(ℤ/2)^22`. -/
theorem le_ten (hlev : σ = 11 → L.level ∣ p) : σ ≤ 10 := by
  have := h.isNondegenerate
  refine Nat.le_of_lt_succ (lt_of_le_of_ne h.le_eleven fun hσ ↦ ?_)
  have h8 := L.eight_dvd_sigPos_sub_sigNeg_of_natCard_eq_pow_finrank p (hlev hσ)
    (by rw [h.natCard_discriminantGroup_eq, h.finrank_eq, hσ])
  rw [h.sigPos_eq, h.sigNeg_eq] at h8
  norm_num at h8

/-- **In odd characteristic the Artin invariant of a supersingular K3 lattice is at most `10`.**
For odd `p` the level of an even lattice whose discriminant group is killed by `p` divides `p`. -/
theorem le_ten_of_odd (hp : Odd p) : σ ≤ 10 :=
  h.le_ten fun _ ↦ h.isEven.level_dvd_of_odd hp h.nsmul_eq_zero

end IsSupersingularK3Lattice

end TauCeti.IntegralLattice
