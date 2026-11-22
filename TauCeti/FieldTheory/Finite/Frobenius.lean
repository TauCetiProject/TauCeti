/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import TauCeti.FieldTheory.Finite.FrobeniusFixed

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

On a finite field of order `p ^ 2` the Frobenius automorphism `frobeniusEquiv K p`, sending `x`
to `x ^ p`, is an involution. This is the field automorphism behind Hermitian duality of codes
over the field of four elements. More generally, on a field of order `q ^ 2` any ring endomorphism
acting as `x ↦ x ^ q` is an involution (`involutive_of_natCard_eq_sq`), specializing on a field of
order `p ^ (2 n)` to the iterated Frobenius `x ↦ x ^ p ^ n`, the conjugation of the field with `q²`
elements over the field with `q = p ^ n` elements behind the finite unitary groups.

## Main definitions

* `TauCeti.FiniteField.frobeniusFixedSubalgebra`: the subalgebra fixed by an iterate of the
  Frobenius.

## Main results

* `TauCeti.FiniteField.frobeniusAlgHom_pow_apply`: the `n`-th iterate is the `q ^ n`-power map.
* `TauCeti.FiniteField.sub_pow_natCard`: the `q`-power map is additive,
  `(x - y) ^ q = x ^ q - y ^ q`.
* `TauCeti.FiniteField.mem_frobeniusFixedSubalgebra`: membership in the fixed subalgebra is the
  equation `a ^ q ^ n = a`.
* `TauCeti.FiniteField.finite_frobeniusFixedSubalgebra`: in a domain, a positive iterate fixes
  only finitely many elements.
* `TauCeti.FiniteField.isPurelyInseparable_fieldRange_frobeniusAlgHom`: `L` is purely
  inseparable over the field range of `FiniteField.frobeniusAlgHom K L`.
* `TauCeti.FiniteField.involutive_of_natCard_eq_sq`: on a field of order `q ^ 2`, any ring
  endomorphism acting as `x ↦ x ^ q` is an involution.
* `TauCeti.FiniteField.frobeniusEquiv_involutive`: on a field of order `p ^ 2`, the Frobenius
  automorphism `x ↦ x ^ p` is an involution.
* `TauCeti.FiniteField.iterateFrobenius_involutive`: on a field of order `p ^ (2 n)`, the iterated
  Frobenius `x ↦ x ^ p ^ n` is an involution.
* `TauCeti.FiniteField.exists_iterateFrobenius_ne`: on a domain with more than `p ^ n` elements,
  finite or not, the iterated Frobenius `x ↦ x ^ p ^ n` moves some element when `1 < p ^ n`.
* `TauCeti.FiniteField.exists_iterateFrobenius_ne_of_card_eq_sq`: on a field of order
  `(p ^ n) ^ 2`, the iterated Frobenius `x ↦ x ^ p ^ n` is not the identity.

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

/-- **Raising to the order of a finite base field is additive**: in a `K`-algebra,
`(x - y) ^ q = x ^ q - y ^ q` for `q` the number of elements of `K`. -/
-- Not `@[simp]`: whenever a `Fintype K` instance is available, `Nat.card_eq_fintype_card` rewrites
-- the left-hand side to `(x - y) ^ Fintype.card K`, so the simpNF linter rejects the attribute.
theorem sub_pow_natCard (K A : Type*) [Field K] [Finite K] [CommRing A] [Algebra K A] (x y : A) :
    (x - y) ^ Nat.card K = x ^ Nat.card K - y ^ Nat.card K := by
  let _ := Fintype.ofFinite K
  simpa only [_root_.FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card] using
    map_sub (_root_.FiniteField.frobeniusAlgHom K A) x y

variable (K A : Type*) [Field K] [Fintype K] [CommRing A] [Algebra K A]

/-- The `n`-th iterate of the Frobenius over a finite base field raises every element to the
`(Nat.card K) ^ n`-th power. -/
theorem frobeniusAlgHom_pow_apply (n : ℕ) (x : A) :
    ((FiniteField.frobeniusAlgHom K A) ^ n) x = x ^ (Nat.card K) ^ n := by
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate,
    Nat.card_eq_fintype_card]

/-- **The subalgebra fixed by an iterate of the Frobenius over a finite base field**, the
equalizer of that iterate with the identity, that is, the solutions of `a ^ (Nat.card K) ^ n = a`.

For `K = 𝔽_q`, `A` an algebraic closure of `K` and `0 < n` this is the subfield of `q ^ n`
elements, but nothing of the sort is asserted here. Unlike `TauCeti.frobeniusFixedSubring`, which
reads the same subset off `iterateFrobenius`, this needs no exponential characteristic on `A`. -/
def frobeniusFixedSubalgebra (n : ℕ) : Subalgebra K A :=
  AlgHom.equalizer ((FiniteField.frobeniusAlgHom K A) ^ n) (AlgHom.id K A)

/-- The Frobenius-fixed subalgebra is the equalizer of the `n`-th Frobenius iterate with the
identity. -/
theorem frobeniusFixedSubalgebra_def (n : ℕ) :
    frobeniusFixedSubalgebra K A n =
      AlgHom.equalizer ((FiniteField.frobeniusAlgHom K A) ^ n) (AlgHom.id K A) := by
  rw [frobeniusFixedSubalgebra]

variable {K A}

/-- Membership in the Frobenius-fixed subalgebra is the equation `a ^ (Nat.card K) ^ n = a`. -/
@[simp]
theorem mem_frobeniusFixedSubalgebra {n : ℕ} {a : A} :
    a ∈ frobeniusFixedSubalgebra K A n ↔ a ^ (Nat.card K) ^ n = a := by
  rw [frobeniusFixedSubalgebra, AlgHom.mem_equalizer, frobeniusAlgHom_pow_apply, AlgHom.coe_id,
    id_eq]

/-- **In a domain, a positive iterate of the Frobenius fixes only finitely many elements**: they
are roots of the nonzero polynomial `X ^ (Nat.card K) ^ n - X`, so for `K = 𝔽_q` there are at
most `q ^ n` of them. -/
theorem finite_frobeniusFixedSubalgebra [IsDomain A] {n : ℕ} (hn : n ≠ 0) :
    Finite (frobeniusFixedSubalgebra K A n) := by
  have hq : 1 < Nat.card K ^ n := Nat.one_lt_pow hn Finite.one_lt_card
  refine Set.Finite.to_subtype ((Polynomial.finite_setOfPred_isRoot
    (Polynomial.X_pow_sub_X_ne_zero (R := A) hq)).subset fun a ha => ?_)
  rw [SetLike.mem_coe, mem_frobeniusFixedSubalgebra] at ha
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, ha, sub_self]

variable {K L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L]

/-- **A field is purely inseparable over the image of its finite-base-field Frobenius**
(the field-theoretic statement in Silverman II.2.11(b)). Every element has its `q`-th power in
the image, where `q = Nat.card K` is a power of the exponential characteristic. -/
theorem isPurelyInseparable_fieldRange_frobeniusAlgHom :
    IsPurelyInseparable (FiniteField.frobeniusAlgHom K L).fieldRange L := by
  obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' K
  have : ExpChar K p := .prime hp
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro x
  use n
  refine ⟨⟨x ^ p ^ (n : ℕ), ?_⟩, IntermediateField.algebraMap_apply _ _⟩
  rw [AlgHom.mem_fieldRange]
  use x
  rw [FiniteField.coe_frobeniusAlgHom, hcard]

/-! ### The Frobenius of a field of order `q ^ 2`, `p ^ 2`, or `p ^ (2 n)` -/

/-- In a field of order `q ^ 2`, any ring endomorphism acting as `a ↦ a ^ q` is an involution. -/
theorem involutive_of_natCard_eq_sq {K : Type*} [Field K] {σ : K →+* K} {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ a, σ a = a ^ q) :
    Function.Involutive σ := fun a ↦ by
  rw [hσ, hσ]
  exact pow_pow_eq_self_of_natCard_eq_sq hK (fun h ↦ by simpa [h] using hσ 0) a

variable {K : Type*} [Field K] {p : ℕ} [ExpChar K p]

/-- On a field of order `p ^ (2 n)`, the iterated Frobenius `x ↦ x ^ p ^ n` is an involution. For
the field with `q²` elements, `q = p ^ n`, this is the involution `x ↦ x ^ q`. -/
theorem iterateFrobenius_involutive {n : ℕ} (hK : Nat.card K = p ^ (n * 2)) :
    Function.Involutive (iterateFrobenius K p n) :=
  involutive_of_natCard_eq_sq (by rw [hK, pow_mul]) (iterateFrobenius_def p n)

/-- On a field of order `p ^ 2`, the Frobenius automorphism `x ↦ x ^ p` is an involution: the case
`n = 1` of `iterateFrobenius_involutive`. -/
theorem frobeniusEquiv_involutive [PerfectRing K p] (hK : Nat.card K = p ^ 2) :
    Function.Involutive (frobeniusEquiv K p) := by
  have h := iterateFrobenius_involutive (K := K) (p := p) (n := 1) (by rwa [one_mul])
  rwa [iterateFrobenius_one, ← coe_frobeniusEquiv] at h

/-- An iterate of Frobenius is not the identity on a domain, finite or infinite, with more than
`p ^ n` elements, provided `1 < p ^ n`. -/
theorem exists_iterateFrobenius_ne {K : Type*} [CommRing K] [IsDomain K] {p n : ℕ}
    [ExpChar K p] (hq : 1 < p ^ n) (hK : (p ^ n : ℕ) < Cardinal.mk K) :
    ∃ s : K, iterateFrobenius K p n s ≠ s := by
  -- A point where `X ^ p ^ n - X` does not vanish is one that the iterate moves.
  obtain ⟨s, hs⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _
    (Polynomial.X_pow_sub_X_ne_zero (R := K) hq) (by rwa [Polynomial.natDegree_X_pow_sub_X hq])
  refine ⟨s, fun h ↦ hs ?_⟩
  rw [iterateFrobenius_def] at h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, h, sub_self]

/-- On a field of order `(p ^ n) ^ 2`, the iterated Frobenius `x ↦ x ^ p ^ n` is not the
identity. -/
theorem exists_iterateFrobenius_ne_of_card_eq_sq {n : ℕ}
    (hK : Nat.card K = (p ^ n) ^ 2) : ∃ s : K, iterateFrobenius K p n s ≠ s := by
  have : Finite K := Nat.finite_of_card_ne_zero
    (by rw [hK]; exact (pow_pos (pow_pos (expChar_pos K p) n) 2).ne')
  have hq : 1 < p ^ n := (Nat.one_lt_pow_iff two_ne_zero).mp (hK ▸ Finite.one_lt_card)
  refine exists_iterateFrobenius_ne hq ?_
  rw [← Nat.cast_card, hK]
  exact_mod_cast lt_self_pow₀ hq one_lt_two

end TauCeti.FiniteField

end
