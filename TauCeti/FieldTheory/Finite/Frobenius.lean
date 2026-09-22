/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# The Frobenius over a finite base field

Let `K` be a finite field with `q` elements. Over any `K`-algebra `A` the `q`-power map is the
algebra endomorphism `FiniteField.frobeniusAlgHom K A`; its iterates raise every element to a
`q ^ n`-th power, and the elements they fix form a `K`-subalgebra. Both statements hold for every
`K`-algebra, with no characteristic hypothesis on `A`: `TauCeti.frobeniusFixedSubring` is the same
subset when `A` has exponential characteristic `p` and `q` is a power of `p`, but that hypothesis
fails for the zero ring, which a subgroup scheme still has to be evaluated at.

For a field extension `L` of `K` the range of the `q`-power map is a subfield over which `L` is
purely inseparable: every `x : L` has `x ^ q` in that image, and `q` is a power of the exponential
characteristic.

## Main definitions

* `TauCeti.FiniteField.frobeniusFixedSubalgebra`: the subalgebra fixed by an iterate of the
  Frobenius.

## Main results

* `TauCeti.FiniteField.frobeniusAlgHom_pow_apply`: the `n`-th iterate is the `q ^ n`-power map.
* `TauCeti.FiniteField.mem_frobeniusFixedSubalgebra`: membership in the fixed subalgebra is the
  equation `a ^ q ^ n = a`.
* `TauCeti.FiniteField.isPurelyInseparable_fieldRange_frobeniusAlgHom`: `L` is purely
  inseparable over the field range of `FiniteField.frobeniusAlgHom K L`.

## Mathematical context

This is the field-theoretic input to proving that the Frobenius isogeny `π_q` is purely inseparable
of degree `q`. Stating it before specializing to a curve keeps the argument independent of the
particular function field, just as the degree computation first identifies the field range of the
same `q`-power map.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

namespace TauCeti.FiniteField

variable (K A : Type*) [Field K] [Fintype K] [CommRing A] [Algebra K A]

/-- The `n`-th iterate of the Frobenius over a finite base field raises every element to the
`(Nat.card K) ^ n`-th power. -/
theorem frobeniusAlgHom_pow_apply (n : ℕ) (x : A) :
    ((_root_.FiniteField.frobeniusAlgHom K A) ^ n) x = x ^ (Nat.card K) ^ n := by
  rw [AlgHom.coe_pow, _root_.FiniteField.coe_frobeniusAlgHom, pow_iterate,
    Nat.card_eq_fintype_card]

/-- **The subalgebra fixed by an iterate of the Frobenius over a finite base field**, the
equalizer of that iterate with the identity, that is, the solutions of `a ^ (Nat.card K) ^ n = a`.

For `K = 𝔽_q`, `A` an algebraic closure of `K` and `0 < n` this is the subfield of `q ^ n`
elements, but nothing of the sort is asserted here. Unlike `TauCeti.frobeniusFixedSubring`, which
reads the same subset off `iterateFrobenius`, this needs no exponential characteristic on `A`. -/
def frobeniusFixedSubalgebra (n : ℕ) : Subalgebra K A :=
  AlgHom.equalizer ((_root_.FiniteField.frobeniusAlgHom K A) ^ n) (AlgHom.id K A)

/-- The Frobenius-fixed subalgebra is the equalizer of the `n`-th Frobenius iterate with the
identity. -/
theorem frobeniusFixedSubalgebra_def (n : ℕ) :
    frobeniusFixedSubalgebra K A n =
      AlgHom.equalizer ((_root_.FiniteField.frobeniusAlgHom K A) ^ n) (AlgHom.id K A) := by
  rw [frobeniusFixedSubalgebra]

variable {K A}

/-- Membership in the Frobenius-fixed subalgebra is the equation `a ^ (Nat.card K) ^ n = a`. -/
@[simp]
theorem mem_frobeniusFixedSubalgebra {n : ℕ} {a : A} :
    a ∈ frobeniusFixedSubalgebra K A n ↔ a ^ (Nat.card K) ^ n = a := by
  rw [frobeniusFixedSubalgebra, AlgHom.mem_equalizer, frobeniusAlgHom_pow_apply, AlgHom.coe_id,
    id_eq]

variable {K L : Type*} [Field K] [Finite K] [Field L] [Algebra K L]

/-- **A field is purely inseparable over the image of its finite-base-field Frobenius**
(the field-theoretic statement in Silverman II.2.11(b)). Every element has its `q`-th power in
the image, where `q = Nat.card K` is a power of the exponential characteristic. -/
theorem isPurelyInseparable_fieldRange_frobeniusAlgHom :
    letI := Fintype.ofFinite K
    IsPurelyInseparable (_root_.FiniteField.frobeniusAlgHom K L).fieldRange L := by
  let _ := Fintype.ofFinite K
  obtain ⟨p, hpK, n, hp, hcard⟩ := _root_.FiniteField.card' K
  let _ : CharP K p := hpK
  let _ : ExpChar K p := ExpChar.prime hp
  have hcard' : Nat.card K = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro x
  have hx : x ^ p ^ (n : ℕ) ∈
      (_root_.FiniteField.frobeniusAlgHom K L).fieldRange := by
    rw [AlgHom.mem_fieldRange]
    refine ⟨x, ?_⟩
    rw [_root_.FiniteField.coe_frobeniusAlgHom, ← Nat.card_eq_fintype_card, hcard']
  refine ⟨(n : ℕ), ?_⟩
  refine ⟨⟨x ^ p ^ (n : ℕ), hx⟩, ?_⟩
  exact IntermediateField.algebraMap_apply
    (S := (_root_.FiniteField.frobeniusAlgHom K L).fieldRange) _

end TauCeti.FiniteField

end
