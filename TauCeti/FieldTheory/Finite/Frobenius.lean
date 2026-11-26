/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import TauCeti.Algebra.CharP.Frobenius.Fixed
import TauCeti.Algebra.GroupWithZero.Units.Finite
import TauCeti.SetTheory.Cardinal.Finite

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

On a finite field of exponential characteristic `p` and order `p ^ 2` the Frobenius automorphism
`frobeniusEquiv K p`, sending `x` to `x ^ p`, is an involution. This is the field automorphism
behind Hermitian duality of codes over the field of four elements. More generally, on a field of
exponential characteristic `p` and order `p ^ (2 n)` the iterated Frobenius `x ↦ x ^ p ^ n` is an
involution, the conjugation of the field with `q²` elements over the field with `q = p ^ n`
elements behind the finite unitary groups.

## Main definitions

* `TauCeti.FiniteField.frobeniusFixedSubalgebra`: the subalgebra fixed by an iterate of the
  Frobenius.
* `TauCeti.FiniteField.frobeniusAlgEquivOfFinite`: the `Nat.card K`-power `K`-algebra automorphism
  on a perfect field `L / K` without requiring `[Fintype K]`.

## Main results

* `TauCeti.FiniteField.frobeniusAlgHom_pow_apply`,
  `TauCeti.FiniteField.frobeniusAlgEquivOfFinite_pow_apply`: the `n`-th iterate is the
  `q ^ n`-power map.
* `TauCeti.FiniteField.sub_pow_natCard`: the `q`-power map is additive,
  `(x - y) ^ q = x ^ q - y ^ q`.
* `TauCeti.FiniteField.mem_frobeniusFixedSubalgebra`: membership in the fixed subalgebra is the
  equation `a ^ q ^ n = a`.
* `TauCeti.FiniteField.finite_frobeniusFixedSubalgebra`: in a domain, a positive iterate fixes
  only finitely many elements.
* `TauCeti.FiniteField.isPurelyInseparable_fieldRange_frobeniusAlgHom`: `L` is purely
  inseparable over the field range of `FiniteField.frobeniusAlgHom K L`.
* `TauCeti.FiniteField.frobeniusAlgHom_pow_comp_eq_iff`,
  `TauCeti.FiniteField.frobeniusAlgEquivOfFinite_pow_comp_eq_iff`: period of the arithmetic
  Frobenius on embeddings of a field extension (supplied in finite degree by
  `FiniteField.orderOf_frobeniusAlgHom`; when `E / K` is infinite, `Module.finrank K E = 0` so
  only `m = 0` fixes the embedding).
* `TauCeti.FiniteField.iterateFrobenius_involutive`: on a field of exponential characteristic `p`
  with `Nat.card K = p ^ (n * 2)`, the iterated Frobenius `x ↦ x ^ p ^ n` is an involution.
* `TauCeti.FiniteField.frobeniusEquiv_involutive`: on a field of exponential characteristic `p`
  with `Nat.card K = p ^ 2` and `[PerfectRing K p]` (automatic once `K` is finite), the Frobenius
  automorphism `x ↦ x ^ p` is an involution.
* `TauCeti.FiniteField.exists_iterateFrobenius_ne_of_card_eq_sq`: on a field of exponential
  characteristic `p` with `Nat.card K = (p ^ n) ^ 2`, the iterated Frobenius `x ↦ x ^ p ^ n` is not
  the identity.

None of these three assumes `[Finite K]`: the `Nat.card` equation implies it, by
`TauCeti.finite_of_natCard_eq_pow`.

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

variable {K : Type*} [Field K] {p : ℕ} [ExpChar K p]

/-- On a field of exponential characteristic `p` with `Nat.card K = p ^ (n * 2)`, the iterated
Frobenius `x ↦ x ^ p ^ n` is an involution. For the field with `q²` elements, `q = p ^ n`, this is
the involution `x ↦ x ^ q`. -/
theorem iterateFrobenius_involutive {n : ℕ} (hK : Nat.card K = p ^ (n * 2)) :
    Function.Involutive (iterateFrobenius K p n) := by
  have := finite_of_natCard_eq_pow (expChar_pos K p).ne' hK
  intro x
  -- Two passes of the `p ^ n`-power map make the `Nat.card K`-power map, which fixes `x`.
  rw [← iterateFrobenius_add_apply, ← mul_two, iterateFrobenius_def, ← hK, pow_natCard]

/-- On a field of exponential characteristic `p` with `Nat.card K = p ^ 2`, the Frobenius
automorphism `x ↦ x ^ p` is an involution: the case `n = 1` of `iterateFrobenius_involutive`.
The instance `[PerfectRing K p]` is needed to state `frobeniusEquiv K p`. Every finite field is
perfect, so a caller with only the `Nat.card` equation obtains it after deriving `Finite K` by
`TauCeti.finite_of_natCard_eq_pow`. -/
theorem frobeniusEquiv_involutive [PerfectRing K p] (hK : Nat.card K = p ^ 2) :
    Function.Involutive (frobeniusEquiv K p) := by
  have h := iterateFrobenius_involutive (K := K) (p := p) (n := 1) (by rwa [one_mul])
  rwa [iterateFrobenius_one, ← coe_frobeniusEquiv] at h

/-- On a field of exponential characteristic `p` with `Nat.card K = (p ^ n) ^ 2`, the iterated
Frobenius `x ↦ x ^ p ^ n` is not the identity. -/
theorem exists_iterateFrobenius_ne_of_card_eq_sq {n : ℕ}
    (hK : Nat.card K = (p ^ n) ^ 2) : ∃ s : K, iterateFrobenius K p n s ≠ s := by
  have := finite_of_natCard_eq_pow (expChar_pow_pos K p n).ne' hK
  have hq := one_lt_of_natCard_eq_pow (expChar_pow_pos K p n).ne' hK
  refine exists_iterateFrobenius_ne hq ?_
  rw [← Nat.cast_card, hK]
  exact_mod_cast lt_self_pow₀ hq one_lt_two

/-! ### The `Nat.card K`-power automorphism of a perfect extension -/

section Perfect

/-- If `L` is a perfect field over a finite field `K`, the `Nat.card K`-power map is a
`K`-algebra automorphism of `L`. This wraps Mathlib's `FiniteField.frobeniusAlgEquiv` with the
`[Fintype K]` and exponential characteristic choices encapsulated. -/
noncomputable def frobeniusAlgEquivOfFinite (K L : Type*) [Field K] [Finite K] [Field L]
    [Algebra K L] [PerfectField L] : L ≃ₐ[K] L :=
  let _ := Fintype.ofFinite K
  have : ExpChar L (ringExpChar K) := expChar_of_injective_algebraMap (algebraMap K L).injective _
  _root_.FiniteField.frobeniusAlgEquiv K L (ringExpChar K)

/-- `TauCeti.FiniteField.frobeniusAlgEquivOfFinite K L` raises every element to the `Nat.card K`-th
power. -/
@[simp]
theorem frobeniusAlgEquivOfFinite_apply (K L : Type*) [Field K] [Finite K] [Field L] [Algebra K L]
    [PerfectField L] (x : L) :
    frobeniusAlgEquivOfFinite K L x = x ^ Nat.card K := by
  let _ := Fintype.ofFinite K
  simp [frobeniusAlgEquivOfFinite, Nat.card_eq_fintype_card]

/-- Raising the inverse image under `TauCeti.FiniteField.frobeniusAlgEquivOfFinite K L` to the
`Nat.card K`-th power recovers the input. -/
theorem frobeniusAlgEquivOfFinite_symm_apply_pow (K L : Type*) [Field K] [Finite K] [Field L]
    [Algebra K L] [PerfectField L] (x : L) :
    ((frobeniusAlgEquivOfFinite K L).symm x) ^ Nat.card K = x := by
  rw [← frobeniusAlgEquivOfFinite_apply K L, AlgEquiv.apply_symm_apply]

/-- The `m`-th power of `TauCeti.FiniteField.frobeniusAlgEquivOfFinite K L` raises every element to
the `(Nat.card K) ^ m`-th power. -/
@[simp]
theorem frobeniusAlgEquivOfFinite_pow_apply (K L : Type*) [Field K] [Finite K] [Field L]
    [Algebra K L] [PerfectField L] (m : ℕ) (x : L) :
    (frobeniusAlgEquivOfFinite K L ^ m) x = x ^ Nat.card K ^ m := by
  rw [AlgEquiv.coe_pow, show ⇑(frobeniusAlgEquivOfFinite K L) = (· ^ Nat.card K) from
    funext (frobeniusAlgEquivOfFinite_apply K L), pow_iterate]

/-- When `K` carries a `Fintype` instance, `(frobeniusAlgEquivOfFinite K L ^ m).toAlgHom` equals
`FiniteField.frobeniusAlgHom K L ^ m`. -/
theorem frobeniusAlgEquivOfFinite_pow_toAlgHom (K L : Type*) [Field K] [Fintype K] [Field L]
    [Algebra K L] [PerfectField L] (m : ℕ) :
    (frobeniusAlgEquivOfFinite K L ^ m).toAlgHom = _root_.FiniteField.frobeniusAlgHom K L ^ m := by
  ext x
  rw [AlgEquiv.coe_toAlgHom, frobeniusAlgEquivOfFinite_pow_apply, frobeniusAlgHom_pow_apply]

end Perfect

/-! ### Exact period of the arithmetic Frobenius on embeddings -/

section Embeddings

/-- For any field extension `E / K` of a finite field `K` and any `K`-algebra homomorphism
`φ : E →ₐ[K] A` into a nontrivial commutative `K`-algebra `A`, postcomposing `φ` with the `m`-th
power of `FiniteField.frobeniusAlgHom K A` equals `φ` if and only if `Module.finrank K E ∣ m`.
When `E / K` is finite this gives exact period `[E : K]` (supplied by
`FiniteField.orderOf_frobeniusAlgHom`); when `E / K` is infinite, `Module.finrank K E = 0`, so the
condition reduces to `m = 0`. -/
theorem frobeniusAlgHom_pow_comp_eq_iff (K A : Type*) [Field K] [Fintype K] [CommRing A]
    [Nontrivial A] [Algebra K A] {E : Type*} [Field E] [Algebra K E]
    (φ : E →ₐ[K] A) (m : ℕ) :
    ((_root_.FiniteField.frobeniusAlgHom K A ^ m).comp φ) = φ ↔
      Module.finrank K E ∣ m := by
  have hpow (x : E) :
      ((_root_.FiniteField.frobeniusAlgHom K A ^ m).comp φ) x =
        φ (x ^ Nat.card K ^ m) := by
    rw [AlgHom.comp_apply, frobeniusAlgHom_pow_apply, map_pow]
  by_cases hfin : Module.Finite K E
  · have : Finite E := Module.finite_of_finite K
    rw [AlgHom.ext_iff]
    have hcomp (x : E) :
        ((_root_.FiniteField.frobeniusAlgHom K A ^ m).comp φ) x =
          φ (((_root_.FiniteField.frobeniusAlgHom K E) ^ m) x) := by
      rw [hpow, frobeniusAlgHom_pow_apply]
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
      exact φ.toRingHom.injective ((hpow x).symm.trans (DFunLike.congr_fun h x))
    have hfinSub : Finite (frobeniusFixedSubalgebra K E m) := finite_frobeniusFixedSubalgebra hm
    have : Finite E :=
      Finite.of_injective (fun x : E ↦ (⟨x, hmem x⟩ : frobeniusFixedSubalgebra K E m))
        fun _ _ hxy ↦ congrArg Subtype.val hxy
    exact hfin .of_finite

/-- For any field extension `E / K` of a finite field `K` and any `K`-embedding `φ : E →ₐ[K] L`
into a perfect field `L`, postcomposing `φ` with the `m`-th power of
`TauCeti.FiniteField.frobeniusAlgEquivOfFinite K L` equals `φ` if and only if
`Module.finrank K E ∣ m` (supplied in finite degree by `FiniteField.orderOf_frobeniusAlgHom`; in
infinite degree `Module.finrank K E = 0`, so this reduces to `m = 0`). -/
theorem frobeniusAlgEquivOfFinite_pow_comp_eq_iff (K L : Type*) [Field K] [Finite K] [Field L]
    [Algebra K L] [PerfectField L] {E : Type*} [Field E] [Algebra K E]
    (φ : E →ₐ[K] L) (m : ℕ) :
    ((frobeniusAlgEquivOfFinite K L ^ m).toAlgHom.comp φ) = φ ↔
      Module.finrank K E ∣ m := by
  let _ := Fintype.ofFinite K
  rw [frobeniusAlgEquivOfFinite_pow_toAlgHom]
  exact frobeniusAlgHom_pow_comp_eq_iff K L φ m

end Embeddings

end TauCeti.FiniteField

end
