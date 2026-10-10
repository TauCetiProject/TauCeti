/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Basic
import TauCeti.NumberTheory.Padics.PadicNorm

/-!
# Numerical forms of the local Euler characteristic formula

For a finite smooth discrete Galois representation over a finite extension of `ℚ_p`, the local
Euler characteristic and the normalized absolute value of the coefficient order are positive
rational numbers. This file converts their equality into the usual cardinality formula

```text
#H¹ = #H⁰ · #H² · p ^ ([F : ℚ_p] v_p(#A)).
```

For coefficients over `𝔽_ℓ`, `ℓ` any prime, that equality is equivalent to the corresponding
formula in dimensions, `dim H¹ = dim H⁰ + dim H² + [F : ℚ_p] v_p(#A)`, whose last term vanishes
unless `ℓ = p`. These results separate the final elementary calculation from the representation-
theoretic proof of the equality of the two invariants.

## Main results

* `natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm`: the
  cardinality formula following from `χ_F(A) = φ_F(A)`.
* `localEulerCharacteristic_eq_localCardNorm_iff_finrank`: `χ_F(A) = φ_F(A)` in dimensions, over
  `𝔽_ℓ` for every prime `ℓ`.
* `finrank_continuousCohomology_one_eq_add_of_localEulerCharacteristic_eq_localCardNorm`: its
  `𝔽_p`-dimension form, `dim H¹ = dim H⁰ + dim H² + [F : ℚ_p] dim A`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable (p : ℕ) [Fact p.Prime]
  {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [FinitePadicExtension F p]

/-- **The cardinality form of the local Euler characteristic formula.** Equality of the local
Euler characteristic and the normalized absolute value of the coefficient order implies
`#H¹ = #H⁰ · #H² · p ^ ([F : ℚ_p] v_p(#A))`. -/
theorem natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm
    (n : ℕ) [NeZero n] (A : GalRep n F) [Finite A.V]
    [Fact (IsSmoothDiscrete (ZMod n) A)]
    (h : localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne n)) A = localCardNorm p A) :
    Nat.card (continuousCohomology 1 A) =
      Nat.card (continuousCohomology 0 A) * Nat.card (continuousCohomology 2 A) *
        p ^ (Module.finrank ℚ_[p] F * padicValNat p (Nat.card A.V)) := by
  have h₁ : Finite (continuousCohomology 1 A) :=
    finite_H (Nat.cast_ne_zero.2 (NeZero.ne n)) A Fact.out (by omega)
  have hcard₁ : 0 < Nat.card (continuousCohomology 1 A) := Nat.card_pos
  have hA : 0 < Nat.card A.V := Nat.card_pos
  have hq := congrArg (fun x : Units.posSubgroup ℚ ↦ ((x.1 : ℚ))) h
  simp only [localEulerCharacteristic_coe, localCardNorm_coe] at hq
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hA.ne'),
    ← padicValRat_of_nat] at hq
  norm_num [zpow_neg, zpow_natCast] at hq
  field_simp [hcard₁.ne', (Fact.out : p.Prime).ne_zero] at hq
  have hq' :
      (Nat.card (continuousCohomology 1 A) : ℚ) =
        Nat.card (continuousCohomology 0 A) * Nat.card (continuousCohomology 2 A) *
          (p : ℚ) ^ (Module.finrank ℚ_[p] F * padicValNat p (Nat.card A.V)) := by
    rw [mul_comm (Module.finrank ℚ_[p] F) (padicValNat p (Nat.card A.V)), pow_mul]
    exact hq.symm
  exact_mod_cast hq'

/-- **The `𝔽_ℓ`-dimension form of the local Euler characteristic formula.** For a prime `ℓ` and
a finite smooth discrete representation `A` over `𝔽_ℓ`, `χ_F(A) = φ_F(A)` holds exactly when
`dim H¹ = dim H⁰ + dim H² + [F : ℚ_p] v_p(#A)`. For `ℓ ≠ p` the last term is zero. -/
theorem localEulerCharacteristic_eq_localCardNorm_iff_finrank (ℓ : ℕ) [Fact ℓ.Prime]
    (A : GalRep ℓ F) [Finite A.V] [Fact (IsSmoothDiscrete (ZMod ℓ) A)] :
    localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne ℓ)) A = localCardNorm p A ↔
      Module.finrank (ZMod ℓ) (continuousCohomology 1 A) =
        Module.finrank (ZMod ℓ) (continuousCohomology 0 A) +
          Module.finrank (ZMod ℓ) (continuousCohomology 2 A) +
            Module.finrank ℚ_[p] F * padicValNat p (Nat.card A.V) := by
  have h₀ : Finite (continuousCohomology 0 A) :=
    finite_H (Nat.cast_ne_zero.2 (NeZero.ne ℓ)) A Fact.out (by omega)
  have h₁ : Finite (continuousCohomology 1 A) :=
    finite_H (Nat.cast_ne_zero.2 (NeZero.ne ℓ)) A Fact.out (by omega)
  have h₂ : Finite (continuousCohomology 2 A) :=
    finite_H (Nat.cast_ne_zero.2 (NeZero.ne ℓ)) A Fact.out (by omega)
  have : Module.Finite (ZMod ℓ) A.V := Module.Finite.of_finite
  have : Module.Finite (ZMod ℓ) (continuousCohomology 0 A) := Module.Finite.of_finite
  have : Module.Finite (ZMod ℓ) (continuousCohomology 1 A) := Module.Finite.of_finite
  have : Module.Finite (ZMod ℓ) (continuousCohomology 2 A) := Module.Finite.of_finite
  rw [Subtype.ext_iff, Units.ext_iff, localEulerCharacteristic_coe, localCardNorm_coe]
  simp only [Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := continuousCohomology _ A),
    Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := A.V), Nat.card_zmod, Nat.cast_pow]
  rw [padicNorm.prime_pow p Fact.out]
  generalize Module.finrank (ZMod ℓ) (continuousCohomology 0 A) = a
  generalize Module.finrank (ZMod ℓ) (continuousCohomology 1 A) = b
  generalize Module.finrank (ZMod ℓ) (continuousCohomology 2 A) = c
  generalize padicValNat p _ = v
  have hℓ1 : (1 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  rw [← zpow_natCast _ (Module.finrank _ _), ← zpow_mul, ← pow_add, ← zpow_natCast,
    ← zpow_natCast _ b, ← zpow_sub₀ (by positivity), zpow_right_inj₀ (by positivity) hℓ1.ne']
  zify
  constructor <;> intro h <;> linarith

/-- **The `𝔽_p`-dimension form of the local Euler characteristic formula.** Equality of the local
Euler characteristic and the normalized absolute value of the coefficient order implies
`dim H¹ = dim H⁰ + dim H² + [F : ℚ_p] dim A`. -/
theorem finrank_continuousCohomology_one_eq_add_of_localEulerCharacteristic_eq_localCardNorm
    (A : GalRep p F) [Finite A.V] [Fact (IsSmoothDiscrete (ZMod p) A)]
    (h : localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne p)) A = localCardNorm p A) :
    Module.finrank (ZMod p) (continuousCohomology 1 A) =
      Module.finrank (ZMod p) (continuousCohomology 0 A) +
        Module.finrank (ZMod p) (continuousCohomology 2 A) +
          Module.finrank ℚ_[p] F * Module.finrank (ZMod p) A.V := by
  have : Module.Finite (ZMod p) A.V := Module.Finite.of_finite
  rw [(localEulerCharacteristic_eq_localCardNorm_iff_finrank p p A).1 h,
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := A.V), Nat.card_zmod, padicValNat.prime_pow]

end TauCeti.ClassFieldTheory
