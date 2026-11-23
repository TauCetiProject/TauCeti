/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.FieldTheory.Finite.Card
import TauCeti.FieldTheory.Finite.EulerCriterion

/-!
# Frobenius on a quadratic algebra over a finite field

Let `F` be a finite field with `Q = Nat.card F` elements and let `r ∈ F`. On
`A = QuadraticAlgebra F r 0` the `Q`-th power map is Mathlib's Frobenius `F`-algebra endomorphism
`FiniteField.frobeniusAlgHom F A`, so it is determined by its value at the generator `ω`. For odd
`Q` this value is `ω ^ Q = r ^ (Q / 2) • ω` (`QuadraticAlgebra.omega_pow_of_odd`), and Euler's
criterion (`FiniteField.isSquare_iff`, `TauCeti.FiniteField.pow_card_div_two_eq_neg_one`)
evaluates `r ^ (Q / 2)` as `-1` or `1` according as `r` is a nonsquare or a nonzero square. For even
`Q` (characteristic two), `ω ^ Q = r ^ (Q / 2)` (`QuadraticAlgebra.omega_pow_of_even`), collapsing
the algebra into `F` (`QuadraticAlgebra.pow_card_eq_algebraMap_of_even_card`). This gives the three
Frobenius identities:

* `QuadraticAlgebra.pow_card_eq_star`: if `r` is not a square, then `A` is a quadratic field
  extension of `F` and `z ^ Q = star z`; in particular `ω ^ Q = -ω`
  (`QuadraticAlgebra.omega_pow_card_eq_neg`). A nonsquare forces `Q` odd, since in
  characteristic two every element is a square.
* `QuadraticAlgebra.pow_card_eq_self_of_square`: if `Q` is odd and `r` is a nonzero square, then
  `z ^ Q = z`. Oddness is needed: over `𝔽₂` with `r = 1` the element `ω + 1` is a nonzero
  nilpotent, so the `Q`-th power map is not the identity.
* `QuadraticAlgebra.pow_card_eq_algebraMap_re`: if `r = 0`, then `z ^ Q = z.re`, for every `Q`.

Conversely, `z ^ Q = star z` holds for every `z` exactly when `r` is not a square
(`QuadraticAlgebra.forall_pow_card_eq_star_iff`), and `z ^ Q = z` holds for every `z` exactly when
`Q` is odd and `r` is a nonzero square (`QuadraticAlgebra.forall_pow_card_eq_self_iff`).

In the inert case (`¬IsSquare r`), the `Q`-th power map is an involution (`(z ^ Q) ^ Q = z`),
turns Mathlib's `algebraMap_trace_eq_add_star` and `algebraMap_norm_eq_mul_star` into
`trace z = z + z ^ Q` and `norm z = z * z ^ Q`, has fixed points exactly `F`, and is the unique
nontrivial `F`-algebra endomorphism of `F(√r)`
(`QuadraticAlgebra.algHom_eq_id_or_eq_starAlgEquiv`, in `TauCeti.Algebra.QuadraticAlgebra.Star`).
Its iterates alternate between the identity (`QuadraticAlgebra.pow_card_pow_eq_self_of_even`) and
conjugation (`QuadraticAlgebra.pow_card_pow_eq_star_of_odd`). When `r` is a square, the `Q`-th
power map is idempotent instead (`QuadraticAlgebra.pow_card_pow_card_eq_pow_card`), so every
positive iterate equals the first (`QuadraticAlgebra.pow_card_pow_eq_pow_card`).

## Scalar extension

For a finite field extension `F ⊂ F'` of degree `n = [F' : F]` with `Q' = Nat.card F' = Q ^ n`,
an element `r ∈ F` remains a nonsquare in `F'` if and only if `r` is not a square in `F` and `n` is
odd (`TauCeti.FiniteField.not_isSquare_algebraMap_iff`). Accordingly, on the scalar-extended algebra
`QuadraticAlgebra F' (algebraMap F F' r) 0`:

* `QuadraticAlgebra.forall_pow_card_eq_star_algebraMap_iff`: `w ^ Q' = star w` for all `w` if and
  only if `r` is not a square in `F` and `[F' : F]` is odd
  (`QuadraticAlgebra.pow_card_eq_star_of_odd_finrank`).
* `QuadraticAlgebra.forall_pow_card_eq_self_algebraMap_iff`: `w ^ Q' = w` for all `w` if and only
  if `Q` is odd, `r ≠ 0`, and either `r` is already a square in `F` or `[F' : F]` is even
  (`QuadraticAlgebra.pow_card_eq_self_of_even_finrank`).

Restricting along Mathlib's canonical embedding
`QuadraticAlgebra.baseChange F' r 0 : QuadraticAlgebra F r 0 →ₐ[F] ...`, these same conditions
characterize when `baseChange z ^ Q'` equals `star (baseChange z)`, `baseChange z`, or
`baseChange (z ^ Q)` for every `z ∈ QuadraticAlgebra F r 0`
(`QuadraticAlgebra.forall_baseChange_pow_card_eq_star_iff`,
`QuadraticAlgebra.forall_baseChange_pow_card_eq_self_iff`,
`QuadraticAlgebra.forall_baseChange_pow_card_eq_map_pow_card_iff`). In particular, when `r` is not
a square in `F`, the identity `z ^ Q = star z` is the restriction of `w ^ Q' = star w` only when
`[F' : F]` is odd; over an even-degree extension `r` becomes a square in `F'` and the identity
changes to `w ^ Q' = w`.

## References

* J. S. Milne, *Algebraic Number Theory*, Example 7.54: the Frobenius generates the Galois group
  of a finite extension of a finite field.
-/

public section

namespace QuadraticAlgebra

open TauCeti.FiniteField

section Finite

variable {F : Type*} [Field F] [Finite F]

/-- The `Q`-th power map fixes the coordinates, since it is an `F`-algebra endomorphism
(`FiniteField.frobeniusAlgHom`): `(x + yω) ^ Q = x + y ω ^ Q`. -/
theorem pow_card_eq_re_smul_add_im_smul {a b : F} (z : QuadraticAlgebra F a b) :
    z ^ Nat.card F = z.re • 1 + z.im • ω ^ Nat.card F := by
  have := Fintype.ofFinite F
  have hf (w : QuadraticAlgebra F a b) :
      w ^ Nat.card F = FiniteField.frobeniusAlgHom F (QuadraticAlgebra F a b) w := by
    simp [Nat.card_eq_fintype_card]
  rw [hf, hf ω]
  conv_lhs => rw [← re_smul_add_im_smul z]
  rw [map_add, map_smul, map_smul, map_one]

variable {r : F}

/-- For odd `Q = Nat.card F`, the `Q`-th power map fixes the first coordinate and multiplies the
second by `r ^ (Q / 2)`. -/
theorem pow_card_eq_mk (hodd : Odd (Nat.card F)) (z : QuadraticAlgebra F r 0) :
    z ^ Nat.card F = ⟨z.re, r ^ (Nat.card F / 2) * z.im⟩ := by
  rw [pow_card_eq_re_smul_add_im_smul, omega_pow_of_odd hodd]
  ext <;> simp [mul_comm]

/-- For even `Q = Nat.card F` (characteristic two), the `Q`-th power map collapses
`QuadraticAlgebra F r 0` into `F`: `ω ^ Q = r ^ (Q / 2)` is a scalar, so
`(x + yω) ^ Q = x + y * r ^ (Q / 2)`. -/
theorem pow_card_eq_algebraMap_of_even_card (heven : Even (Nat.card F))
    (z : QuadraticAlgebra F r 0) :
    z ^ Nat.card F = algebraMap F _ (z.re + z.im * r ^ (Nat.card F / 2)) := by
  rw [pow_card_eq_re_smul_add_im_smul, omega_pow_of_even heven]
  ext <;> simp

/-- **Frobenius at the generator in the inert case.** For a nonsquare `r`, `ω ^ Q = -ω`. -/
theorem omega_pow_card_eq_neg (hr : ¬IsSquare r) :
    (ω : QuadraticAlgebra F r 0) ^ Nat.card F = -ω := by
  rw [omega_pow_of_odd (odd_card_of_not_isSquare hr), pow_card_div_two_eq_neg_one hr,
    neg_one_smul]

/-- **Frobenius is conjugation in the inert case.** Over a finite field `F` with `Q` elements and
a nonsquare `r`, every element of the quadratic field `F(√r)` satisfies `z ^ Q = star z`. -/
theorem pow_card_eq_star (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    z ^ Nat.card F = star z := by
  rw [pow_card_eq_mk (odd_card_of_not_isSquare hr), pow_card_div_two_eq_neg_one hr]
  ext <;> simp

/-- **Frobenius is the identity in the split case.** Over a finite field of odd cardinality `Q`
and for a nonzero square `r`, the algebra `QuadraticAlgebra F r 0` is `F × F`
(`QuadraticAlgebra.algEquivProdOfSq`) and every element satisfies `z ^ Q = z`. -/
@[simp] theorem pow_card_eq_self_of_square (hodd : Odd (Nat.card F)) (hr : IsSquare r) (hr0 : r ≠ 0)
    (z : QuadraticAlgebra F r 0) : z ^ Nat.card F = z := by
  have := Fintype.ofFinite F
  have h : r ^ (Nat.card F / 2) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact (FiniteField.isSquare_iff (ringChar_ne_two_of_odd_card hodd) hr0).mp hr
  rw [pow_card_eq_mk hodd, h, one_mul]

/-- **Frobenius in the repeated-root case.** In `QuadraticAlgebra F 0 0`, where `ω ^ 2 = 0`,
every element satisfies `z ^ Q = z.re`, for every finite field `F`. -/
@[simp] theorem pow_card_eq_algebraMap_re (z : QuadraticAlgebra F 0 0) :
    z ^ Nat.card F = algebraMap F _ z.re := by
  have := Fintype.ofFinite F
  have hω : (ω : QuadraticAlgebra F 0 0) ^ Nat.card F = 0 := by
    rw [← Nat.sub_add_cancel Finite.one_lt_card, pow_add, sq, omega_mul_omega_eq_algebraMap]
    simp
  rw [pow_card_eq_re_smul_add_im_smul, hω, smul_zero, add_zero, Algebra.algebraMap_eq_smul_one]

/-- **Frobenius is not conjugation outside the inert case.** If `r` is a square in `F`, then
`ω ^ Q ≠ star ω`: the power `ω ^ Q` is the scalar `0` when `r = 0`, the scalar `r ^ (Q / 2)` when
`Q` is even, and `ω` when `Q` is odd and `r ≠ 0`, while `star ω = -ω` has second coordinate
`-1 ≠ 1`. -/
theorem omega_pow_card_ne_star (hr : IsSquare r) :
    (ω : QuadraticAlgebra F r 0) ^ Nat.card F ≠ star ω := by
  intro h
  have him := congrArg im h
  rw [im_star, im_omega] at him
  by_cases hr0 : r = 0
  · subst hr0
    rw [pow_card_eq_algebraMap_re] at him
    simp at him
  rcases Nat.even_or_odd (Nat.card F) with heven | hodd
  · rw [omega_pow_of_even heven, algebraMap_im] at him
    exact one_ne_zero (neg_eq_zero.mp him.symm)
  · rw [pow_card_eq_self_of_square hodd hr hr0, im_omega] at him
    exact Ring.two_ne_zero (ringChar_ne_two_of_odd_card hodd) (by linear_combination him)

/-- **Frobenius is conjugation exactly in the inert case.** Over a finite field `F` with `Q`
elements, every `z ∈ QuadraticAlgebra F r 0` satisfies `z ^ Q = star z` exactly when `r` is not a
square. -/
theorem forall_pow_card_eq_star_iff :
    (∀ z : QuadraticAlgebra F r 0, z ^ Nat.card F = star z) ↔ ¬IsSquare r :=
  ⟨fun h hr ↦ omega_pow_card_ne_star hr (h ω), pow_card_eq_star⟩

omit [Finite F] in
/-- In the inert case the Frobenius algebra endomorphism is conjugation. -/
theorem frobeniusAlgHom_eq_starAlgEquiv [Fintype F] (hr : ¬IsSquare r) :
    FiniteField.frobeniusAlgHom F (QuadraticAlgebra F r 0) =
      (starAlgEquiv : QuadraticAlgebra F r 0 ≃ₐ[F] _).toAlgHom := by
  ext1
  simp [← Nat.card_eq_fintype_card, pow_card_eq_star hr]

/-- In the inert case the trace is `z + z ^ Q`. -/
theorem algebraMap_trace_eq_add_pow_card (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    algebraMap F _ (trace z) = z + z ^ Nat.card F := by
  rw [pow_card_eq_star hr, algebraMap_trace_eq_add_star]

/-- In the inert case the norm is `z * z ^ Q`. -/
theorem algebraMap_norm_eq_mul_pow_card (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    algebraMap F _ (norm z) = z * z ^ Nat.card F := by
  rw [pow_card_eq_star hr, algebraMap_norm_eq_mul_star]

/-- In the inert case the `Q`-th power map is an involution. -/
@[simp] theorem pow_card_pow_card (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    (z ^ Nat.card F) ^ Nat.card F = z := by
  rw [pow_card_eq_star hr, pow_card_eq_star hr, star_star]

/-- In the inert case the fixed points of the `Q`-th power map are the elements with zero
second coordinate. -/
theorem pow_card_eq_self_iff_im_eq_zero (hr : ¬IsSquare r) {z : QuadraticAlgebra F r 0} :
    z ^ Nat.card F = z ↔ z.im = 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero
    (ringChar_ne_two_of_odd_card (odd_card_of_not_isSquare hr))
  rw [pow_card_eq_star hr, QuadraticAlgebra.ext_iff]
  simp only [re_star, zero_mul, add_zero, im_star, true_and, neg_eq_iff_add_eq_zero, ← two_mul,
    mul_eq_zero, h2, false_or]

/-- In the inert case the fixed points of the `Q`-th power map are exactly the elements of `F`. -/
theorem pow_card_eq_self_iff_mem_range (hr : ¬IsSquare r) {z : QuadraticAlgebra F r 0} :
    z ^ Nat.card F = z ↔ z ∈ Set.range (algebraMap F (QuadraticAlgebra F r 0)) := by
  rw [pow_card_eq_self_iff_im_eq_zero hr]
  refine ⟨fun h ↦ ⟨z.re, by ext <;> simp [h]⟩, ?_⟩
  rintro ⟨x, rfl⟩
  simp

/-- **Frobenius is the identity exactly in the split case.** Over a finite field `F` with `Q`
elements, every `z ∈ QuadraticAlgebra F r 0` satisfies `z ^ Q = z` exactly when `Q` is odd and
`r` is a nonzero square. -/
theorem forall_pow_card_eq_self_iff :
    (∀ z : QuadraticAlgebra F r 0, z ^ Nat.card F = z) ↔
      Odd (Nat.card F) ∧ IsSquare r ∧ r ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hodd, hr, hr0⟩ ↦ pow_card_eq_self_of_square hodd hr hr0⟩
  have hω := h ω
  have hodd : Odd (Nat.card F) := (Nat.even_or_odd _).resolve_left fun heven ↦ by
    have him := congrArg im hω
    rw [pow_card_eq_algebraMap_of_even_card heven, algebraMap_im, im_omega] at him
    exact zero_ne_one him
  have hr : IsSquare r := by
    by_contra hr
    have := (pow_card_eq_self_iff_im_eq_zero hr).mp hω
    simp at this
  have hr0 : r ≠ 0 := by
    rintro rfl
    have him := congrArg im hω
    rw [pow_card_eq_algebraMap_re, algebraMap_im, im_omega] at him
    exact zero_ne_one him
  exact ⟨hodd, hr, hr0⟩

/-! ### Iterated Frobenius -/

/-- When `r` is a square in `F`, the `Q`-th power map on `QuadraticAlgebra F r 0` is idempotent:
it is the identity when `Q` is odd and `r ≠ 0`, and lands in `F` (which it fixes) when `r = 0` or
`Q` is even. -/
@[simp] theorem pow_card_pow_card_eq_pow_card (hr : IsSquare r) (z : QuadraticAlgebra F r 0) :
    (z ^ Nat.card F) ^ Nat.card F = z ^ Nat.card F := by
  have := Fintype.ofFinite F
  have hfix (x : F) :
      (algebraMap F (QuadraticAlgebra F r 0) x) ^ Nat.card F = algebraMap F _ x := by
    rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [pow_card_eq_algebraMap_re z, hfix]
  rcases Nat.even_or_odd (Nat.card F) with heven | hodd
  · rw [pow_card_eq_algebraMap_of_even_card heven z, hfix]
  · rw [pow_card_eq_self_of_square hodd hr hr0]

/-- When `r` is a square in `F`, every positive iterate of the `Q`-th power map equals the first:
`z ^ (Q ^ n) = z ^ Q` for `n ≠ 0`. -/
theorem pow_card_pow_eq_pow_card (hr : IsSquare r) {n : ℕ} (hn : n ≠ 0)
    (z : QuadraticAlgebra F r 0) : z ^ Nat.card F ^ n = z ^ Nat.card F := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  clear hn
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, pow_card_pow_card_eq_pow_card hr]

/-- In the inert case, an even iterate of the `Q`-th power map is the identity:
`z ^ (Q ^ n) = z` for even `n`. -/
theorem pow_card_pow_eq_self_of_even (hr : ¬IsSquare r) {n : ℕ} (hn : Even n)
    (z : QuadraticAlgebra F r 0) : z ^ Nat.card F ^ n = z := by
  obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
  clear hn
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, sq, pow_mul, pow_card_pow_card hr]

/-- In the inert case, an odd iterate of the `Q`-th power map is conjugation:
`z ^ (Q ^ n) = star z` for odd `n`. -/
theorem pow_card_pow_eq_star_of_odd (hr : ¬IsSquare r) {n : ℕ} (hn : Odd n)
    (z : QuadraticAlgebra F r 0) : z ^ Nat.card F ^ n = star z := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, pow_card_pow_eq_self_of_even hr (even_two_mul k), pow_card_eq_star hr]

/-- For `n ≠ 0`, the `(Q ^ n)`-th power map on `QuadraticAlgebra F r 0` is conjugation if and only
if `r` is not a square and `n` is odd. (At `n = 0` in characteristic two `star = id`, so `n ≠ 0`
cannot be dropped.) -/
theorem forall_pow_card_pow_eq_star_iff {n : ℕ} (hn : n ≠ 0) :
    (∀ z : QuadraticAlgebra F r 0, z ^ Nat.card F ^ n = star z) ↔ ¬IsSquare r ∧ Odd n := by
  refine ⟨fun h ↦ ?_, fun ⟨hr, hodd⟩ ↦ pow_card_pow_eq_star_of_odd hr hodd⟩
  have hr : ¬IsSquare r := fun hr ↦
    omega_pow_card_ne_star hr ((pow_card_pow_eq_pow_card hr hn ω).symm.trans (h ω))
  refine ⟨hr, (Nat.even_or_odd n).resolve_left fun heven ↦ ?_⟩
  have hω : (ω : QuadraticAlgebra F r 0) ^ Nat.card F = ω := by
    rw [pow_card_eq_star hr, ← h ω, pow_card_pow_eq_self_of_even hr heven]
  simpa using (pow_card_eq_self_iff_im_eq_zero hr).mp hω

/-- For `n ≠ 0`, the `(Q ^ n)`-th power map on `QuadraticAlgebra F r 0` is the identity if and
only if `Q` is odd, `r ≠ 0`, and either `r` is a square or `n` is even. -/
theorem forall_pow_card_pow_eq_self_iff {n : ℕ} (hn : n ≠ 0) :
    (∀ z : QuadraticAlgebra F r 0, z ^ Nat.card F ^ n = z) ↔
      Odd (Nat.card F) ∧ (IsSquare r ∨ Even n) ∧ r ≠ 0 := by
  constructor
  · intro h
    by_cases hr : IsSquare r
    · have h1 : ∀ z : QuadraticAlgebra F r 0, z ^ Nat.card F = z := fun z ↦
        (pow_card_pow_eq_pow_card hr hn z).symm.trans (h z)
      obtain ⟨hodd, _, hr0⟩ := forall_pow_card_eq_self_iff.mp h1
      exact ⟨hodd, .inl hr, hr0⟩
    · refine ⟨odd_card_of_not_isSquare hr, .inr ?_, by rintro rfl; exact hr .zero⟩
      refine (Nat.even_or_odd n).resolve_right fun hodd ↦ ?_
      have hω : (ω : QuadraticAlgebra F r 0) ^ Nat.card F = ω := by
        rw [pow_card_eq_star hr, ← pow_card_pow_eq_star_of_odd hr hodd, h ω]
      simpa using (pow_card_eq_self_iff_im_eq_zero hr).mp hω
  · rintro ⟨hodd, hr | heven, hr0⟩ z
    · rw [pow_card_pow_eq_pow_card hr hn, pow_card_eq_self_of_square hodd hr hr0]
    · by_cases hr : IsSquare r
      · rw [pow_card_pow_eq_pow_card hr hn, pow_card_eq_self_of_square hodd hr hr0]
      · exact pow_card_pow_eq_self_of_even hr heven z

/-- For `n ≠ 0`, the `(Q ^ n)`-th power map on `QuadraticAlgebra F r 0` agrees with the `Q`-th
power map if and only if either `r` is a square or `n` is odd. -/
theorem forall_pow_card_pow_eq_pow_card_iff {n : ℕ} (hn : n ≠ 0) :
    (∀ z : QuadraticAlgebra F r 0, z ^ Nat.card F ^ n = z ^ Nat.card F) ↔
      IsSquare r ∨ Odd n := by
  constructor
  · intro h
    by_cases hr : IsSquare r
    · exact .inl hr
    · refine .inr ((Nat.even_or_odd n).resolve_left fun heven ↦ ?_)
      have hω : (ω : QuadraticAlgebra F r 0) ^ Nat.card F = ω :=
        (h ω).symm.trans (pow_card_pow_eq_self_of_even hr heven ω)
      simpa using (pow_card_eq_self_iff_im_eq_zero hr).mp hω
  · rintro (hr | hodd) z
    · exact pow_card_pow_eq_pow_card hr hn z
    · by_cases hr : IsSquare r
      · exact pow_card_pow_eq_pow_card hr hn z
      · rw [pow_card_pow_eq_star_of_odd hr hodd, pow_card_eq_star hr]

end Finite

/-! ### Scalar extension -/

section ScalarExtension

variable {F F' : Type*} [Field F] [Field F'] [Finite F'] [Algebra F F'] {r : F}

/-- **Frobenius is conjugation after scalar extension exactly when `r` stays a nonsquare.** Over a
finite extension `F'/F` of finite fields with `Q' = Nat.card F'`, every element of
`QuadraticAlgebra F' (algebraMap F F' r) 0` satisfies `w ^ Q' = star w` if and only if `r` is not
a square in `F` and `[F' : F]` is odd. -/
theorem forall_pow_card_eq_star_algebraMap_iff :
    (∀ w : QuadraticAlgebra F' (algebraMap F F' r) 0, w ^ Nat.card F' = star w) ↔
      ¬IsSquare r ∧ Odd (Module.finrank F F') := by
  rw [forall_pow_card_eq_star_iff, not_isSquare_algebraMap_iff]

/-- If `r ∈ F` is not a square and `[F' : F]` is odd, then `r` stays a nonsquare in `F'` and the
`Q'`-th power map on `QuadraticAlgebra F' (algebraMap F F' r) 0` is conjugation. -/
theorem pow_card_eq_star_of_odd_finrank (hr : ¬IsSquare r) (hodd : Odd (Module.finrank F F'))
    (w : QuadraticAlgebra F' (algebraMap F F' r) 0) : w ^ Nat.card F' = star w :=
  forall_pow_card_eq_star_algebraMap_iff.mpr ⟨hr, hodd⟩ w

/-- **Frobenius is the identity after scalar extension.** Over a finite extension `F'/F` of finite
fields with `Q' = Nat.card F'`, every element of `QuadraticAlgebra F' (algebraMap F F' r) 0`
satisfies `w ^ Q' = w` if and only if `Nat.card F` is odd, `r ≠ 0`, and either `r` is already a
square in `F` or `[F' : F]` is even. -/
theorem forall_pow_card_eq_self_algebraMap_iff :
    (∀ w : QuadraticAlgebra F' (algebraMap F F' r) 0, w ^ Nat.card F' = w) ↔
      Odd (Nat.card F) ∧ (IsSquare r ∨ Even (Module.finrank F F')) ∧ r ≠ 0 := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Module.Finite F F' := .of_finite
  rw [forall_pow_card_eq_self_iff, Module.natCard_eq_pow_finrank (K := F) (V := F'),
    Nat.odd_pow_iff Module.finrank_pos.ne', isSquare_algebraMap_iff,
    map_ne_zero_iff _ (algebraMap F F').injective]

/-- Over an even-degree extension `F'/F` of finite fields of odd cardinality, every nonzero
`r ∈ F` becomes a square in `F'`, so the `Q'`-th power map on
`QuadraticAlgebra F' (algebraMap F F' r) 0` is the identity. In particular this applies to every
nonsquare `r ∈ F`, replacing `z ^ Q = star z` with `w ^ Q' = w`. -/
theorem pow_card_eq_self_of_even_finrank (hodd : Odd (Nat.card F)) (hr0 : r ≠ 0)
    (heven : Even (Module.finrank F F')) (w : QuadraticAlgebra F' (algebraMap F F' r) 0) :
    w ^ Nat.card F' = w :=
  forall_pow_card_eq_self_algebraMap_iff.mpr ⟨hodd, .inr heven, hr0⟩ w

/-- **Restriction of `w ^ Q' = star w` along `baseChange`.** For a finite extension `F'/F` of finite
fields, the `Q'`-th power map agrees with `star` on the image of
`QuadraticAlgebra.baseChange F' r 0` if and only if `r` is not a square in `F` and `[F' : F]` is
odd — the exact condition under which `w ^ Q' = star w` holds on all of
`QuadraticAlgebra F' (algebraMap F F' r) 0`. -/
theorem forall_baseChange_pow_card_eq_star_iff :
    (∀ z : QuadraticAlgebra F r 0,
      baseChange F' r 0 z ^ Nat.card F' = star (baseChange F' r 0 z)) ↔
      ¬IsSquare r ∧ Odd (Module.finrank F F') := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Module.Finite F F' := .of_finite
  have hinj := baseChange_injective (R := F) F' r 0
  have hstar (z : QuadraticAlgebra F r 0) :
      star (baseChange F' r 0 z) = baseChange F' r 0 (star z) := by
    simp only [← AlgHom.coe_toRingHom, coe_baseChange, mapRingHom_star]
  simp_rw [← map_pow, hstar, hinj.eq_iff, Module.natCard_eq_pow_finrank (K := F) (V := F')]
  exact forall_pow_card_pow_eq_star_iff Module.finrank_pos.ne'

/-- **Restriction of `w ^ Q' = w` along `baseChange`.** For a finite extension `F'/F` of finite
fields, the `Q'`-th power map acts as the identity on the image of
`QuadraticAlgebra.baseChange F' r 0` if and only if `Nat.card F` is odd, `r ≠ 0`, and either `r` is
a square in `F` or `[F' : F]` is even. -/
theorem forall_baseChange_pow_card_eq_self_iff :
    (∀ z : QuadraticAlgebra F r 0,
      baseChange F' r 0 z ^ Nat.card F' = baseChange F' r 0 z) ↔
      Odd (Nat.card F) ∧ (IsSquare r ∨ Even (Module.finrank F F')) ∧ r ≠ 0 := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Module.Finite F F' := .of_finite
  have hinj := baseChange_injective (R := F) F' r 0
  simp_rw [← map_pow, hinj.eq_iff, Module.natCard_eq_pow_finrank (K := F) (V := F')]
  exact forall_pow_card_pow_eq_self_iff Module.finrank_pos.ne'

/-- **Compatibility of Frobenius with scalar extension.** The `Q'`-th power map on the image of
`QuadraticAlgebra.baseChange F' r 0` restricts to the `Q`-th power map on `QuadraticAlgebra F r 0`
if and only if either `r` is already a square in `F` or `[F' : F]` is odd. In particular, for a
nonsquare `r`, `z ^ Q = star z` is the restriction of the `Q'`-th power map on the scalar extension
exactly when `[F' : F]` is odd. -/
theorem forall_baseChange_pow_card_eq_map_pow_card_iff :
    (∀ z : QuadraticAlgebra F r 0,
      baseChange F' r 0 z ^ Nat.card F' = baseChange F' r 0 (z ^ Nat.card F)) ↔
      IsSquare r ∨ Odd (Module.finrank F F') := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Module.Finite F F' := .of_finite
  have hinj := baseChange_injective (R := F) F' r 0
  simp_rw [← map_pow, hinj.eq_iff, Module.natCard_eq_pow_finrank (K := F) (V := F')]
  exact forall_pow_card_pow_eq_pow_card_iff Module.finrank_pos.ne'

end ScalarExtension

/-! ### Checks -/

section Checks

/-- `F = ℤ/3`, `r = -1` (nonsquare): `(1 + ω) ^ 3 = 1 - ω = star (1 + ω)`. -/
example : (1 + ω : QuadraticAlgebra (ZMod 3) (-1) 0) ^ 3 = star (1 + ω) := by
  have hr : ¬IsSquare (-1 : ZMod 3) := by decide
  simpa only [Nat.card_zmod] using pow_card_eq_star hr (1 + ω)

/-- `F = ℤ/5`, `r = -1 = 2 ^ 2` (nonzero square): `(1 + ω) ^ 5 = 1 + ω`. -/
example : (1 + ω : QuadraticAlgebra (ZMod 5) (-1) 0) ^ 5 = 1 + ω := by
  have hr : IsSquare (-1 : ZMod 5) := ⟨2, by decide⟩
  have hr0 : (-1 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hodd : Odd (Nat.card (ZMod 5)) := by rw [Nat.card_zmod]; decide
  simpa only [Nat.card_zmod] using pow_card_eq_self_of_square hodd hr hr0 (1 + ω)

/-- `F = ℤ/3`, `r = 0` (repeated root): `(1 + ω) ^ 3 = 1`. -/
example : (1 + ω : QuadraticAlgebra (ZMod 3) 0 0) ^ 3 = 1 := by
  have h := pow_card_eq_algebraMap_re (1 + ω : QuadraticAlgebra (ZMod 3) 0 0)
  rw [Nat.card_zmod] at h
  simpa [re_add, re_one, re_omega] using h

/-- `F = ℤ/7`, `r = 3` (nonsquare): `ω ^ 7 = -ω`. -/
example : (ω : QuadraticAlgebra (ZMod 7) 3 0) ^ 7 = -ω := by
  have hr : ¬IsSquare (3 : ZMod 7) := by decide
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  simpa only [Nat.card_zmod] using omega_pow_card_eq_neg hr

/-- Degree-2 scalar extension `𝔽₉ = (ℤ/3)[√-1]` over `ℤ/3`: `-1` is not a square in `ℤ/3`, becomes
a square in `𝔽₉`, and Frobenius on `QuadraticAlgebra 𝔽₉ (-1) 0` changes from `star` to the identity
`w ^ 9 = w`. -/
example :
    let F' := QuadraticAlgebra (ZMod 3) (-1) 0
    (∀ w : QuadraticAlgebra F' (algebraMap (ZMod 3) F' (-1)) 0, w ^ 9 = w) ∧
      ¬(∀ w : QuadraticAlgebra F' (algebraMap (ZMod 3) F' (-1)) 0, w ^ 9 = star w) := by
  have : Fact (¬IsSquare (-1 : ZMod 3)) := ⟨by decide⟩
  let F' := QuadraticAlgebra (ZMod 3) (-1) 0
  have : Finite F' := Finite.of_equiv _ (equivProd _ _).symm
  have hdim : Module.finrank (ZMod 3) F' = 2 := by
    simpa [F'] using Module.finrank_eq_card_basis (basis (-1 : ZMod 3) 0)
  have hcard : Nat.card F' = 9 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := F'), Nat.card_zmod, hdim]
    rfl
  refine ⟨fun w ↦ ?_, fun h ↦ ?_⟩
  · rw [← hcard]
    exact pow_card_eq_self_of_even_finrank (by rw [Nat.card_zmod]; decide) (by decide)
      (by rw [hdim]; decide) w
  · have h' := (forall_pow_card_eq_star_algebraMap_iff (F := ZMod 3) (F' := F') (r := -1)).mp
      fun w ↦ by rw [hcard]; exact h w
    rw [hdim] at h'
    exact Nat.not_odd_iff_even.mpr even_two h'.2

/-- Any cubic extension `F'` of `ℤ/3` (odd degree 3): `-1` stays a nonsquare in `F'`, Frobenius on
`QuadraticAlgebra F' (-1) 0` stays `w ^ 27 = star w`, and along `baseChange` it restricts to
`z ^ 3 = star z` on `QuadraticAlgebra (ZMod 3) (-1) 0`. -/
example {F' : Type*} [Field F'] [Finite F'] [Algebra (ZMod 3) F']
    (hdim : Module.finrank (ZMod 3) F' = 3) :
    (∀ w : QuadraticAlgebra F' (algebraMap (ZMod 3) F' (-1)) 0, w ^ 27 = star w) ∧
      (∀ z : QuadraticAlgebra (ZMod 3) (-1) 0,
        baseChange F' (-1) 0 z ^ 27 = baseChange F' (-1) 0 (z ^ 3)) := by
  have : Module.Finite (ZMod 3) F' := .of_finite
  have hcard : Nat.card F' = 27 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := F'), Nat.card_zmod, hdim]
    rfl
  have hodd : Odd (Module.finrank (ZMod 3) F') := by rw [hdim]; decide
  refine ⟨fun w ↦ ?_, fun z ↦ ?_⟩
  · rw [← hcard]
    exact pow_card_eq_star_of_odd_finrank (by decide) hodd w
  · rw [← hcard]
    simpa only [Nat.card_zmod] using
      forall_baseChange_pow_card_eq_map_pow_card_iff.mpr (.inr hodd) z

/-- Negative control in characteristic two: over any finite extension `F'/𝔽₂` with `r = 1 ≠ 0`
(even when `[F' : 𝔽₂]` is even), Frobenius is never the identity (`Odd (Nat.card F)` cannot be
dropped). -/
example {F' : Type*} [Field F'] [Finite F'] [Algebra (ZMod 2) F'] :
    ¬(∀ w : QuadraticAlgebra F' (algebraMap (ZMod 2) F' 1) 0, w ^ Nat.card F' = w) := by
  intro h
  have hodd := (forall_pow_card_eq_self_algebraMap_iff.mp h).1
  rw [Nat.card_zmod] at hodd
  exact Nat.not_odd_iff_even.mpr even_two hodd

end Checks

end QuadraticAlgebra
