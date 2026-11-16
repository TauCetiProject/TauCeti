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

On a finite field of order `p ^ 2` the Frobenius automorphism `frobeniusEquiv K p`, sending `x`
to `x ^ p`, is an involution. This is the field automorphism behind Hermitian duality of codes
over the field of four elements. More generally, on a field of order `p ^ (2 n)` the iterated
Frobenius `x ↦ x ^ p ^ n` is an involution, the conjugation of the field with `q²` elements over
the field with `q = p ^ n` elements behind the finite unitary groups.

## Main definitions

* `TauCeti.FiniteField.frobeniusFixedSubalgebra`: the subalgebra fixed by an iterate of the
  Frobenius.
* `TauCeti.FiniteField.arithmeticFrobenius`, `TauCeti.FiniteField.geometricFrobenius`: the
  arithmetic Frobenius `x ↦ x ^ Nat.card K` and its inverse, the geometric Frobenius, of an
  algebraic extension `L / K` of a finite field `K`.

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
* `TauCeti.FiniteField.frobeniusEquiv_involutive`: on a field of order `p ^ 2`, the Frobenius
  automorphism `x ↦ x ^ p` is an involution.
* `TauCeti.FiniteField.iterateFrobenius_involutive`: on a field of order `p ^ (2 n)`, the iterated
  Frobenius `x ↦ x ^ p ^ n` is an involution.
* `TauCeti.FiniteField.arithmeticFrobenius_pow_apply`,
  `TauCeti.FiniteField.arithmeticFrobenius_pow_comp_eq_iff`: powers of the arithmetic Frobenius and
  its exact period on embeddings of any field extension.

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

/-! ### The Frobenius of a field of order `p ^ 2` or `p ^ (2 n)` -/

section Involutive

variable {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- On a field of order `p ^ 2`, the Frobenius automorphism `x ↦ x ^ p` is an involution. -/
theorem frobeniusEquiv_involutive (hK : Nat.card K = p ^ 2) :
    Function.Involutive (frobeniusEquiv K p) := by
  let := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ 2 := Nat.card_eq_fintype_card.symm.trans hK
  intro x
  simpa only [coe_frobeniusEquiv, pow_two, RingHom.mul_def, RingHom.comp_apply, RingHom.one_def,
    RingHom.id_apply] using DFunLike.congr_fun (FiniteField.frobenius_pow hcard) x

omit [Finite K] in
/-- On a field of order `p ^ (2 n)`, the iterated Frobenius `x ↦ x ^ p ^ n` is an involution. For
the field with `q²` elements, `q = p ^ n`, this is the involution `x ↦ x ^ q`. -/
theorem iterateFrobenius_involutive {n : ℕ} (hK : Nat.card K = p ^ (n * 2)) :
    Function.Involutive (iterateFrobenius K p n) := by
  have : Finite K := Nat.finite_of_card_ne_zero
    (by rw [hK]; exact (pow_pos (Fact.out : p.Prime).pos _).ne')
  let := Fintype.ofFinite K
  intro x
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, ← mul_two, ← hK,
    Nat.card_eq_fintype_card, FiniteField.pow_card]

end Involutive

/-! ### Arithmetic and geometric Frobenius of an algebraic extension -/

section Algebraic

variable (K L : Type*) [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- **The arithmetic Frobenius** of an algebraic extension `L / K` of a finite field `K`: the
`K`-automorphism `x ↦ x ^ Nat.card K`, packaging Mathlib's
`FiniteField.frobeniusAlgEquivOfAlgebraic` with a `[Finite K]` hypothesis. -/
noncomputable def arithmeticFrobenius : Gal(L/K) :=
  let _ := Fintype.ofFinite K
  _root_.FiniteField.frobeniusAlgEquivOfAlgebraic K L

/-- The arithmetic Frobenius raises every element to the power `Nat.card K`. -/
@[simp]
theorem arithmeticFrobenius_apply (x : L) :
    arithmeticFrobenius K L x = x ^ Nat.card K := by
  let _ := Fintype.ofFinite K
  rw [arithmeticFrobenius, _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    Nat.card_eq_fintype_card]

/-- **The geometric Frobenius** of an algebraic extension `L / K` of a finite field `K`: the
inverse of the arithmetic Frobenius `x ↦ x ^ Nat.card K`. -/
noncomputable def geometricFrobenius : Gal(L/K) :=
  (arithmeticFrobenius K L).symm

/-- The geometric Frobenius is the inverse of the arithmetic Frobenius in `Gal(L/K)`. -/
theorem geometricFrobenius_eq_inv :
    geometricFrobenius K L = (arithmeticFrobenius K L)⁻¹ :=
  (rfl)

/-- The inverse of the geometric Frobenius is the arithmetic Frobenius. -/
@[simp]
theorem geometricFrobenius_inv :
    (geometricFrobenius K L)⁻¹ = arithmeticFrobenius K L :=
  inv_inv _

/-- Applying the geometric Frobenius and then raising to the power `Nat.card K` is the identity. -/
@[simp]
theorem geometricFrobenius_apply_pow (x : L) :
    (geometricFrobenius K L x) ^ Nat.card K = x := by
  rw [← arithmeticFrobenius_apply K L, geometricFrobenius, AlgEquiv.apply_symm_apply]

/-- Raising to the power `Nat.card K` and then applying the geometric Frobenius is the identity. -/
theorem geometricFrobenius_pow_apply (x : L) :
    geometricFrobenius K L (x ^ Nat.card K) = x := by
  rw [← arithmeticFrobenius_apply K L, geometricFrobenius, AlgEquiv.symm_apply_apply]

/-- The `m`-th iterate of `arithmeticFrobenius K L` raises every element to the
`(Nat.card K) ^ m`-th power. -/
theorem arithmeticFrobenius_pow_apply (m : ℕ) (x : L) :
    ((arithmeticFrobenius K L) ^ m) x = x ^ (Nat.card K) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, arithmeticFrobenius_apply, ih, ← pow_mul, pow_succ]

/-- For any field extension `E / K` of a finite field `K` and any `K`-embedding `φ : E →ₐ[K] L`
into an algebraic extension `L / K`, postcomposing `φ` with the `m`-th power of
`arithmeticFrobenius K L` equals `φ` if and only if `[E : K] ∣ m`. -/
theorem arithmeticFrobenius_pow_comp_eq_iff {E : Type*} [Field E] [Algebra K E]
    (φ : E →ₐ[K] L) (m : ℕ) :
    ((arithmeticFrobenius K L) ^ m).toAlgHom.comp φ = φ ↔ Module.finrank K E ∣ m := by
  let _ := Fintype.ofFinite K
  by_cases hfin : Module.Finite K E
  · have : Finite E := Module.finite_of_finite K
    rw [AlgHom.ext_iff]
    have hcomp (x : E) :
        (((arithmeticFrobenius K L) ^ m).toAlgHom.comp φ) x =
          φ (((_root_.FiniteField.frobeniusAlgHom K E) ^ m) x) := by
      rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, arithmeticFrobenius_pow_apply,
        frobeniusAlgHom_pow_apply, map_pow]
    have hinj : Function.Injective φ := φ.toRingHom.injective
    simp_rw [hcomp, hinj.eq_iff]
    have heq : (∀ x : E, ((_root_.FiniteField.frobeniusAlgHom K E) ^ m) x = x) ↔
        (_root_.FiniteField.frobeniusAlgHom K E) ^ m = 1 :=
      ⟨fun h ↦ AlgHom.ext h, fun h x ↦ by rw [h, AlgHom.one_apply]⟩
    rw [heq, ← orderOf_dvd_iff_pow_eq_one, _root_.FiniteField.orderOf_frobeniusAlgHom]
  · rw [Module.finrank_of_infinite_dimensional hfin, zero_dvd_iff]
    refine ⟨fun h ↦ ?_, fun hm ↦ by subst hm; exact AlgHom.ext fun x ↦ by simp⟩
    by_contra hm
    have hmem (x : E) : x ∈ frobeniusFixedSubalgebra K E m := by
      rw [mem_frobeniusFixedSubalgebra]
      have hx := DFunLike.congr_fun h x
      rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, arithmeticFrobenius_pow_apply,
        ← map_pow] at hx
      exact φ.toRingHom.injective hx
    have hfinSub : Finite (frobeniusFixedSubalgebra K E m) := finite_frobeniusFixedSubalgebra hm
    have : Finite E :=
      Finite.of_injective (fun x : E ↦ (⟨x, hmem x⟩ : frobeniusFixedSubalgebra K E m))
        fun _ _ hxy ↦ congrArg Subtype.val hxy
    exact hfin .of_finite

end Algebraic

end TauCeti.FiniteField

end
