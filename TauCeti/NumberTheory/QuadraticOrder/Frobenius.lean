/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.FiniteField
public import TauCeti.NumberTheory.QuadraticOrder.PrimeIdeal
import Mathlib.NumberTheory.LegendreSymbol.Basic
import TauCeti.FieldTheory.Finite.EulerCriterion

/-!
# The integral Frobenius congruence in `ℤ[√r]`

Let `ℤ[√r] = QuadraticAlgebra ℤ r 0` for an integer `r`, and let `p` be a prime such that `r` is
not a square modulo `p`. Reduction modulo `p` (`QuadraticAlgebra.mapRingHom` along
`ℤ → ℤ/p`) is a ring map commuting with `star`, and over the field `ℤ/p` with `p` elements the
`p`-th power map is conjugation (`QuadraticAlgebra.pow_card_eq_star`). Since the kernel of
reduction is the ideal `(p)` (`QuadraticAlgebra.ker_mapRingHom_intCastRingHom`), every
`z = u + v√r` satisfies `z ^ p ≡ u - v√r` modulo `p`, coefficientwise.

The hypothesis forces `p` to be odd, since every residue modulo `2` is a square, and it is sharp:
when `r` is a square modulo `p`, including `r ≡ 0` and `p = 2`, the generator `ω = √r` already
violates the congruence.

## Main results

* `QuadraticAlgebra.mapRingHom_intCastRingHom_pow_eq_star`: the commuting square
  `ρ_p (z ^ p) = star (ρ_p z) = ρ_p (star z)` for reduction `ρ_p` modulo `p`.
* `QuadraticAlgebra.frobenius_congruence`: `z ^ p - star z ∈ (p)`.
* `QuadraticAlgebra.re_pow_modEq` and `QuadraticAlgebra.im_pow_modEq`: the coordinate form
  `(z ^ p).re ≡ u` and `(z ^ p).im ≡ -v` modulo `p`; the first needs only `p` odd, for every `r`.
  The integer consequence
  `p ∣ v ^ p * r ^ ((p - 1) / 2) + v` is Euler's criterion `r ^ ((p - 1) / 2) ≡ -1` multiplied by
  `v` (`Int.dvd_pow_mul_pow_div_two_add`).
* `QuadraticAlgebra.omega_pow_sub_star_notMem_span_natCast` and
  `QuadraticAlgebra.forall_pow_sub_star_mem_span_natCast_iff`: when `r` is a square modulo `p`
  the congruence fails at `ω`, so it holds for every `z` exactly when `r` is not a square
  modulo `p`.

The hypothesis is the inertness of `(p)` in `ℤ[√r]`
(`QuadraticAlgebra.isMaximal_span_natCast_iff_not_isSquare`). In a quadratic field `ℚ(θ)` with
`θ² = d`, at an odd prime `p ∤ d`, it is also the nontriviality of the arithmetic Frobenius
(`TauCeti.NumberField.arithFrobAt_ne_one_iff_isMaximal_span_natCast`).

The congruence takes place in the presented order `ℤ[√r]`, not in the maximal order: for `r = 5`
the prime `2` is inert in the maximal order of `ℚ(√5)`, while `ℤ[√5]/(2)` has the nonzero
nilpotent `ω - 1` and the congruence fails at `ω`.

## References

* B. Conrad, *Quadratic characters associated to quadratic fields*, course handout
  (https://math.stanford.edu/~conrad/676Page/handouts/quadchar.pdf), Theorem 2.4 (p. 3) and
  Corollary 3.1 (p. 4).
* J. S. Milne, *Algebraic Number Theory*, Example 3.44: the decomposition of `p` in a quadratic
  field according to whether `d` is a square modulo `p`, and the inertness of `2` in `ℚ(√5)`.
-/

public section

namespace QuadraticAlgebra

variable {r : ℤ} {p : ℕ} [Fact p.Prime]

/-- Reduction modulo `p` lands in `QuadraticAlgebra (ZMod p) r (Int.castRingHom (ZMod p) 0)`,
whose parameter is `0` only propositionally. A statement proved for every element of
`QuadraticAlgebra (ZMod p) r 0` therefore holds for every element of that algebra. -/
private theorem forall_of_intCastRingHom_zero
    {P : ∀ b : ZMod p, QuadraticAlgebra (ZMod p) (r : ZMod p) b → Prop} (h : ∀ w, P 0 w)
    (w : QuadraticAlgebra (ZMod p) (r : ZMod p) (Int.castRingHom (ZMod p) 0)) :
    P (Int.castRingHom (ZMod p) 0) w := by
  have key : ∀ b : ZMod p, b = 0 → ∀ w, P b w := by
    rintro _ rfl
    exact h
  exact key _ (map_zero _) w

/-- **The commuting square.** For a prime `p` modulo which `r` is not a square, reduction modulo
`p` sends `z ^ p` to the conjugate of the reduction of `z`, which is the reduction of `star z`. -/
theorem mapRingHom_intCastRingHom_pow_eq_star (hr : ¬IsSquare (r : ZMod p))
    (z : QuadraticAlgebra ℤ r 0) :
    mapRingHom (Int.castRingHom (ZMod p)) r 0 (z ^ p) =
      star (mapRingHom (Int.castRingHom (ZMod p)) r 0 z) := by
  rw [map_pow]
  exact forall_of_intCastRingHom_zero (P := fun _ w ↦ w ^ p = star w)
    (fun w ↦ by simpa only [Nat.card_zmod] using pow_card_eq_star hr w) _

/-- **The integral Frobenius congruence.** For an integer `r`, a prime `p` modulo which `r` is not
a square (so `p` is odd, `TauCeti.FiniteField.odd_card_of_not_isSquare`), and every
`z = u + v√r` in `ℤ[√r]`, `z ^ p ≡ u - v√r` modulo `p`: the difference `z ^ p - star z` lies in the
ideal `(p)`. -/
theorem frobenius_congruence (hr : ¬IsSquare (r : ZMod p)) (z : QuadraticAlgebra ℤ r 0) :
    z ^ p - star z ∈ Ideal.span {(p : QuadraticAlgebra ℤ r 0)} := by
  rw [← ker_mapRingHom_intCastRingHom, RingHom.mem_ker, map_sub,
    mapRingHom_intCastRingHom_pow_eq_star hr, mapRingHom_star, sub_self]

/-- The first coordinate of the Frobenius congruence: for an odd prime `p` and every integer `r`,
`(z ^ p).re ≡ z.re` modulo `p`. Over `ℤ/p` the `p`-th power map fixes the first coordinate
(`QuadraticAlgebra.pow_card_eq_mk`), whether or not `r` is a square modulo `p`. -/
theorem re_pow_modEq (hp : p ≠ 2) (z : QuadraticAlgebra ℤ r 0) :
    (z ^ p).re ≡ z.re [ZMOD p] := by
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp
  -- Over `ℤ/p` the `p`-th power map fixes the first coordinate.
  have h := forall_of_intCastRingHom_zero (P := fun _ w ↦ (w ^ p).re = w.re)
    (fun w ↦ by simpa only [Nat.card_zmod] using congrArg re (pow_card_eq_mk hodd w))
    (mapRingHom (Int.castRingHom (ZMod p)) r 0 z)
  rw [← map_pow, re_mapRingHom_intCastRingHom, re_mapRingHom_intCastRingHom] at h
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp h

/-- The second coordinate of the Frobenius congruence: `(z ^ p).im ≡ -z.im` modulo `p`. -/
theorem im_pow_modEq (hr : ¬IsSquare (r : ZMod p)) (z : QuadraticAlgebra ℤ r 0) :
    (z ^ p).im ≡ -z.im [ZMOD p] := by
  simpa using (sub_mem_span_natCast_iff.mp (frobenius_congruence hr z)).2

/-- **Sharpness of the hypothesis.** If `r` is a square modulo the prime `p`, including `r ≡ 0`
and `p = 2`, then the generator `ω = √r` violates the Frobenius congruence. Modulo an odd `p`, the
power `ω ^ p` reduces to `0` when `r ≡ 0` and to `ω` otherwise, while for `p = 2` it is the scalar
`ω ^ 2 = r`. In all cases `ω ^ p - star ω = ω ^ p + ω` has second coordinate `1` or `2` modulo `p`,
which is nonzero (`QuadraticAlgebra.omega_pow_card_ne_star` over `ℤ/p`). -/
theorem omega_pow_sub_star_notMem_span_natCast (hr : IsSquare (r : ZMod p)) :
    (ω : QuadraticAlgebra ℤ r 0) ^ p - star ω ∉ Ideal.span {(p : QuadraticAlgebra ℤ r 0)} := by
  rw [← ker_mapRingHom_intCastRingHom, RingHom.mem_ker, map_sub, map_pow, mapRingHom_star,
    mapRingHom_omega]
  exact forall_of_intCastRingHom_zero (r := r)
    (P := fun b _ ↦ (ω : QuadraticAlgebra (ZMod p) (r : ZMod p) b) ^ p - star ω ≠ 0)
    (fun _ h ↦ omega_pow_card_ne_star hr (by rwa [Nat.card_zmod, ← sub_eq_zero])) ω

/-- **The congruence characterizes the nonsquares.** For a prime `p`, every `z ∈ ℤ[√r]` satisfies
`z ^ p ≡ star z` modulo `p` exactly when `r` is not a square modulo `p`. -/
theorem forall_pow_sub_star_mem_span_natCast_iff :
    (∀ z : QuadraticAlgebra ℤ r 0, z ^ p - star z ∈ Ideal.span {(p : QuadraticAlgebra ℤ r 0)}) ↔
      ¬IsSquare (r : ZMod p) :=
  ⟨fun h hr => omega_pow_sub_star_notMem_span_natCast hr (h ω), frobenius_congruence⟩

end QuadraticAlgebra

/-! ### Checks -/

namespace QuadraticAlgebra

/-- `r = -1`, `p = 3`: `-1` is not a square modulo `3`, so `(u + v√-1) ^ 3 ≡ u - v√-1` modulo
`3` for all `u, v`. -/
example (z : QuadraticAlgebra ℤ (-1) 0) :
    z ^ 3 - star z ∈ Ideal.span {((3 : ℕ) : QuadraticAlgebra ℤ (-1) 0)} :=
  frobenius_congruence (by rw [Int.cast_neg, Int.cast_one, ZMod.exists_sq_eq_neg_one_iff]; decide) z

/-- `r = -1`, `p = 5`: `-1 = 2 ^ 2` is a square modulo `5`, and the congruence fails at `ω`. -/
example : (ω : QuadraticAlgebra ℤ (-1) 0) ^ 5 - star ω ∉
    Ideal.span {((5 : ℕ) : QuadraticAlgebra ℤ (-1) 0)} :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  omega_pow_sub_star_notMem_span_natCast ⟨2, rfl⟩

/-- `r = 5`, `p = 2`: every residue modulo `2` is a square, and the congruence fails at `ω`,
although `2` is inert in the maximal order of `ℚ(√5)`. -/
example : (ω : QuadraticAlgebra ℤ 5 0) ^ 2 - star ω ∉
    Ideal.span {((2 : ℕ) : QuadraticAlgebra ℤ 5 0)} :=
  omega_pow_sub_star_notMem_span_natCast ⟨1, rfl⟩

/-- `r = 3`, `p = 3`: the ramified prime, `3 ≡ 0` is a square, and the congruence fails at `ω`. -/
example : (ω : QuadraticAlgebra ℤ 3 0) ^ 3 - star ω ∉
    Ideal.span {((3 : ℕ) : QuadraticAlgebra ℤ 3 0)} :=
  omega_pow_sub_star_notMem_span_natCast ⟨0, rfl⟩

end QuadraticAlgebra

namespace Int

/-- **Euler's criterion times `v`.** For a prime `p` modulo which the integer `r` is not a square
and every integer `v`, `p ∣ v ^ p * r ^ ((p - 1) / 2) + v`: by Fermat `v ^ p ≡ v` and by Euler's
criterion `r ^ ((p - 1) / 2) ≡ -1`, the exponent being written `p / 2`. For `p ∤ v` this is Euler's
criterion for `r` itself. -/
theorem dvd_pow_mul_pow_div_two_add {p : ℕ} [Fact p.Prime] {r : ℤ}
    (hr : ¬IsSquare (r : ZMod p)) (v : ℤ) : (p : ℤ) ∣ v ^ p * r ^ (p / 2) + v := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h := TauCeti.FiniteField.pow_card_div_two_eq_neg_one hr
  rw [Nat.card_zmod] at h
  push_cast
  rw [ZMod.pow_card, h, mul_neg_one, neg_add_cancel]

end Int
