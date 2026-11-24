/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Milgram
public import TauCeti.LinearAlgebra.IntegralLattice.Level
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling

/-!
# The rescaled dual of an integral lattice

Let `L` be a nondegenerate integral lattice whose discriminant group `A_L = Lᵛ / L` is killed by
an integer `n`, so that `nLᵛ ⊆ L`. Then the dual carrier `Lᵛ` with the rescaled form `n · B` is
again an integral lattice, the *rescaled dual* `Lᵛ(n)`. It is the lattice through which the
boundary case `L = nLᵛ` of an `n`-elementary lattice reduces to a unimodular one:

* `Lᵛ(n)` is even exactly when the level of `L` divides `n`;
* if `#A_L = n^r`, `r` the rank, then `L = nLᵛ` and `Lᵛ(n)` is unimodular;
* for `n ≠ 0` it has the signature of `L`.

Together with Milgram's theorem for even unimodular lattices this gives the congruence
`t₊ − t₋ ≡ 0 (mod 8)` for every lattice of level dividing `n` whose discriminant group has order
`n^r`. For odd `n`, an even lattice whose discriminant group is killed by `n` automatically has
level dividing `n` (`TauCeti.IntegralLattice.IsEven.level_dvd_of_odd`), so that hypothesis is a
genuine restriction only for even `n` (among primes, only at `p = 2`). These are the
boundary clauses of Nikulin's existence conditions for `p`-elementary lattices, and they are the
lattice-theoretic step behind the bound on the Artin invariant of a supersingular K3 surface.

## Main definitions and results

* `TauCeti.IntegralLattice.rescaledDual`: the rescaled dual `Lᵛ(n)`.
* `TauCeti.IntegralLattice.isEven_rescaledDual_iff`: `Lᵛ(n)` is even exactly when the level of
  `L` divides `n`.
* `TauCeti.IntegralLattice.isUnimodular_rescaledDual`: if `#A_L = n^r`, then `Lᵛ(n)` is
  unimodular.
* `TauCeti.IntegralLattice.signature_rescaledDual`: for `n ≠ 0`, `Lᵛ(n)` has the signature of
  `L`; `sigPos_rescaledDual`, `sigNull_rescaledDual` and `sigNeg_rescaledDual` give its parts.
* `TauCeti.IntegralLattice.eight_dvd_sigPos_sub_sigNeg_of_natCard_eq_pow_finrank`: if the level
  of `L` divides `n` and `#A_L = n^r`, then `8 ∣ t₊ − t₋`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.3 and
  Theorem 3.6.2.
* A. N. Rudakov and I. R. Shafarevich, *Surfaces of type K3 over fields of finite
  characteristic*, §1.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

section RescaledDual

variable (L : IntegralLattice V) [L.IsNondegenerate] (n : ℕ)

/-- **The rescaled dual `Lᵛ(n)`**: the dual carrier `Lᵛ` with the form `n · B`. It is an integral
lattice when `n` kills the discriminant group, since then `nLᵛ ⊆ L` and
`n · B(x, y) = B(x, n y) ∈ ℤ` for `x, y ∈ Lᵛ`. -/
noncomputable def rescaledDual (hn : ∀ x : L.DiscriminantGroup, n • x = 0) : IntegralLattice V :=
  ofSubmodule L.dualCarrier ((n : ℚ) • L.form) (L.isSymm.smul _) fun x hx ↦ by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    -- `n B(x, y) = B(y, n x)` with `y ∈ Lᵛ` and `n x ∈ L`.
    have h := (LinearMap.BilinForm.mem_dualSubmodule _).mp hy _
      (L.nsmul_mem_carrier n hn ⟨x, hx⟩)
    rw [map_nsmul, nsmul_eq_mul, L.isSymm.eq] at h
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact h

variable (hn : ∀ x : L.DiscriminantGroup, n • x = 0)

/-- The carrier of `Lᵛ(n)` is the dual carrier of `L`. -/
@[simp]
theorem rescaledDual_carrier : (L.rescaledDual n hn).carrier = L.dualCarrier :=
  ofSubmodule_carrier ..

/-- The form of `Lᵛ(n)` is `n · B`. -/
@[simp]
theorem rescaledDual_form : (L.rescaledDual n hn).form = (n : ℚ) • L.form :=
  ofSubmodule_form ..

/-- The norm of `Lᵛ(n)` is `n` times the norm of `L`. -/
@[simp]
theorem rescaledDual_norm (x : V) : (L.rescaledDual n hn).norm x = n * L.norm x := by
  simp [norm_apply]

/-- **`Lᵛ(n)` is even exactly when the level of `L` divides `n`**: both say that
`n · B(x, x) ∈ 2ℤ` for every `x ∈ Lᵛ`. -/
theorem isEven_rescaledDual_iff : (L.rescaledDual n hn).IsEven ↔ L.level ∣ n := by
  rw [isEven_iff_forall_norm, ← Int.natCast_dvd_natCast, level_dvd_iff]
  constructor
  · intro h x hx
    obtain ⟨z, hz⟩ := h ⟨x, by rwa [rescaledDual_carrier]⟩
    exact ⟨z, by rwa [rescaledDual_norm] at hz⟩
  · intro h x
    obtain ⟨z, hz⟩ := h x (by simpa using x.property)
    exact ⟨z, by rwa [rescaledDual_norm, ← Int.cast_natCast]⟩

/-- **If `#A_L = n^r`, `r` the rank, then `Lᵛ(n)` is unimodular.** In that case `L = nLᵛ`, so a
vector pairing integrally with `Lᵛ` under `n · B` pairs integrally with `L` under `B`. -/
theorem isUnimodular_rescaledDual (hcard : Nat.card L.DiscriminantGroup = n ^ finrank ℚ V) :
    (L.rescaledDual n hn).IsUnimodular := by
  rw [isUnimodular_iff_dualCarrier_le, rescaledDual_carrier]
  intro v hv
  rw [LinearMap.BilinForm.mem_dualSubmodule] at hv
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := L.exists_mem_dualCarrier_eq_nsmul n hn hcard hx
  have h := hv y (by rwa [rescaledDual_carrier])
  rw [rescaledDual_form, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at h
  rwa [map_nsmul, nsmul_eq_mul]

/-- For `n ≠ 0`, the rescaled dual `Lᵛ(n)` has the positive index of inertia of `L`. -/
theorem sigPos_rescaledDual (hn0 : n ≠ 0) : (L.rescaledDual n hn).sigPos = L.sigPos := by
  rw [← sigPos_smul_of_pos (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn0)) L]
  simp only [IntegralLattice.sigPos, rescaledDual_form, smul_form, Int.cast_natCast]

/-- For `n ≠ 0`, the rescaled dual `Lᵛ(n)` has the negative index of inertia of `L`. -/
theorem sigNeg_rescaledDual (hn0 : n ≠ 0) : (L.rescaledDual n hn).sigNeg = L.sigNeg := by
  rw [← sigNeg_smul_of_pos (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn0)) L]
  simp only [IntegralLattice.sigNeg, rescaledDual_form, smul_form, Int.cast_natCast]

/-- For `n ≠ 0`, the rescaled dual `Lᵛ(n)` has the null index of `L`. -/
theorem sigNull_rescaledDual (hn0 : n ≠ 0) : (L.rescaledDual n hn).sigNull = L.sigNull := by
  have h : (L.rescaledDual n hn).radical = ((n : ℤ) • L).radical := by
    ext x
    simp only [mem_radical_iff, rescaledDual_form, smul_form, Int.cast_natCast]
  rw [sigNull, h, ← sigNull, sigNull_smul (Int.natCast_ne_zero.mpr hn0)]

/-- For `n ≠ 0`, the rescaled dual `Lᵛ(n)` has the signature of `L`. -/
theorem signature_rescaledDual (hn0 : n ≠ 0) :
    (L.rescaledDual n hn).signature = L.signature := by
  rw [signature, sigPos_rescaledDual L n hn hn0, sigNull_rescaledDual L n hn hn0,
    sigNeg_rescaledDual L n hn hn0, signature]

omit hn in
/-- **Milgram's congruence at the boundary `L = nLᵛ`.** If the level of `L` divides `n` and the
discriminant group has order `n^r`, `r` the rank, then `t₊ − t₋ ≡ 0 (mod 8)`: the rescaled dual
`Lᵛ(n)` is an even unimodular lattice with the signature of `L`. -/
theorem eight_dvd_sigPos_sub_sigNeg_of_natCard_eq_pow_finrank (hlev : L.level ∣ n)
    (hcard : Nat.card L.DiscriminantGroup = n ^ finrank ℚ V) :
    (8 : ℤ) ∣ L.sigPos - L.sigNeg := by
  have hn : ∀ x : L.DiscriminantGroup, n • x = 0 := fun x ↦
    AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mp
      (L.exponent_discriminantGroup_dvd_level.trans hlev) x
  rcases eq_or_ne n 0 with rfl | hn0
  · -- For `n = 0` the rank is `0`, since `#A_L` is positive.
    have hr : finrank ℚ V = 0 := by
      by_contra hr
      rw [zero_pow hr] at hcard
      exact Nat.card_pos.ne' hcard
    have hsum := L.signature_sum_eq_finrank
    have hpos : L.sigPos = 0 := by omega
    have hneg : L.sigNeg = 0 := by omega
    simp [hpos, hneg]
  · rw [← L.sigPos_rescaledDual n hn hn0, ← L.sigNeg_rescaledDual n hn hn0]
    exact (L.rescaledDual n hn).eight_dvd_sigPos_sub_sigNeg_of_isUnimodular
      ((L.isEven_rescaledDual_iff n hn).mpr hlev) (L.isUnimodular_rescaledDual n hn hcard)

end RescaledDual

end TauCeti.IntegralLattice
