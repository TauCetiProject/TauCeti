/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.ClassNumberOne

/-!
# Ring class fields of imaginary quadratic orders of class number one

Let `K` be an imaginary quadratic field and `O_f = ℤ + f 𝓞 K`
(`GlobalNumberFields.intAddMulOrder K f`) its order of conductor `f ≥ 1`. Combining Artin
reciprocity for the ring class field (`ringClassArtinEquiv`, `subsingleton_gal_ringClassField_iff`,
`ringClassField_eq_bot_iff`) with the local-factor classification of imaginary quadratic orders of
class number one (`NumberFieldOrder.subsingleton_pic_intAddMulOrder_iff`) characterizes when the
ring class field `ringClassField (intAddMulOrder K f)` is trivial over `K`: `𝓞 K` is a principal
ideal domain and `(discr K, f)` is `(D, 1)`, `(D, 2)` with `D ≡ 1 (mod 8)`, `(-3, 2)`, `(-3, 3)`,
or `(-4, 2)`.

## Main results

* `TauCeti.ClassFieldTheory.subsingleton_gal_ringClassField_intAddMulOrder_iff`: characterization
  of imaginary quadratic orders `ℤ + f 𝓞 K` with trivial
  `Gal(ringClassField (intAddMulOrder K f) / K)`.
* `TauCeti.ClassFieldTheory.ringClassField_intAddMulOrder_eq_bot_iff`: classification of imaginary
  quadratic orders `ℤ + f 𝓞 K` whose ring class field equals `K`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (Theorem 7.24) and §9 (Theorem 9.18).
* G. S. Kopp and J. C. Lagarias, *Ray class groups and ray class fields for orders of number
  fields*, Ess. Number Th. 4 (2025), arXiv:2212.09177v3, Theorem 1.1.
-/

public noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

/-- In an imaginary quadratic field `K`, the Galois group
`Gal(ringClassField (intAddMulOrder K f) / K)` is trivial iff `𝓞 K` is a principal ideal domain and
`(discr K, f)` is one of `(D, 1)`, `(D, 2)` with `D ≡ 1 (mod 8)`, `(-3, 2)`, `(-3, 3)`, or
`(-4, 2)`. -/
theorem subsingleton_gal_ringClassField_intAddMulOrder_iff (hK : Module.finrank ℚ K = 2) (f : ℕ)
    [NeZero f] :
    Subsingleton Gal(ringClassField (intAddMulOrder K f)/K) ↔ IsPrincipalIdealRing (𝓞 K) ∧
      (f = 1 ∨ (f = 2 ∧ NumberField.discr K % 8 = 1) ∨
        (NumberField.discr K = -3 ∧ (f = 2 ∨ f = 3)) ∨ (NumberField.discr K = -4 ∧ f = 2)) :=
  (subsingleton_gal_ringClassField_iff (intAddMulOrder K f)).trans
    (subsingleton_pic_intAddMulOrder_iff hK f)

/-- **Classification of imaginary quadratic orders with trivial ring class field**: in an imaginary
quadratic field `K`, `ringClassField (intAddMulOrder K f) = ⊥` iff `𝓞 K` is a principal ideal
domain and `(discr K, f)` is one of `(D, 1)`, `(D, 2)` with `D ≡ 1 (mod 8)`, `(-3, 2)`, `(-3, 3)`,
or `(-4, 2)`. -/
theorem ringClassField_intAddMulOrder_eq_bot_iff (hK : Module.finrank ℚ K = 2) (f : ℕ)
    [NeZero f] :
    ringClassField (intAddMulOrder K f) = ⊥ ↔ IsPrincipalIdealRing (𝓞 K) ∧
      (f = 1 ∨ (f = 2 ∧ NumberField.discr K % 8 = 1) ∨
        (NumberField.discr K = -3 ∧ (f = 2 ∨ f = 3)) ∨ (NumberField.discr K = -4 ∧ f = 2)) :=
  (ringClassField_eq_bot_iff (intAddMulOrder K f)).trans
    (subsingleton_pic_intAddMulOrder_iff hK f)

end TauCeti.ClassFieldTheory
