/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring
import TauCeti.Data.Int.Progression
import TauCeti.Data.Int.Round

/-!
# Non-negativity of a binary quadratic form and its discriminant

Mathlib's `discrim_le_zero` shows that a quadratic polynomial over a linearly ordered field which
is non-negative at every point of the field has non-positive discriminant. This file supplies two
facts about the homogeneous two-variable form `a * x ^ 2 + b * x * y + c * y ^ 2` that it does not
give: the reverse implication, and an integral version whose hypothesis is much weaker. It also
records two elementary facts about discriminants used for positive definite integral forms: a
negative discriminant together with `0 ≤ a` forces `0 < a`, and an integral discriminant is `0` or
`1` modulo `4`.

The integral version is the substantial one, and it is worth being precise about what makes it
substantial. Over a *field*, non-negativity along a single line `y = y₀ ≠ 0` already forces
`discrim a b c ≤ 0`: the restriction is a quadratic in `x`, so `discrim_le_zero` applies and the
resulting `y₀ ^ 2 * discrim a b c ≤ 0` may be divided by `y₀ ^ 2`. Over `ℤ` the same hypothesis
with `x` ranging over the *integers* is strictly weaker, and is genuinely not enough: the map
`x ↦ x ^ 2 - x` is non-negative at every integer, yet `discrim 1 (-1) 0 = 1 > 0`, which is
`forall_int_nonneg_and_discrim_pos` below. `Int.discrim_le_zero_of_nonneg_of_lt_abs` says that one
extra condition — that `|y₀|` exceed the leading coefficient — repairs this, with no further
quantification needed.

Together with the reverse implication this gives the upgrade that motivates the file: a form known
to be non-negative only on some sparse subset of `ℤ × ℤ` — the locus where a fixed prime divides
neither coordinate — is non-negative everywhere.
`Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd` pins the discriminant from that locus alone,
and `nonneg_of_discrim_le_zero` then propagates the conclusion to every `(x, y)`.

## Main results

* `nonneg_of_discrim_le_zero`: `0 < a` and `discrim a b c ≤ 0` give `0 ≤ a x² + b x y + c y²`.
* `discrim_pos_of_exists_pos_of_exists_neg`: representing both signs forces positive discriminant.
* `Int.discrim_le_zero_of_nonneg_of_lt_abs`: for `a < |y|`, and with no sign condition on `a`,
  non-negativity of `a x² + b x y + c y²` in `x` alone forces `discrim a b c ≤ 0`.
* `Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd`: the same conclusion from non-negativity
  on `{(x, y) : d ∤ x ∧ d ∤ y}`, for any non-unit `d`.
* `pos_of_nonneg_of_discrim_lt_zero`: a quadratic of negative discriminant with `0 ≤ a` has
  `0 < a`.
* `Int.discrim_emod_four`: `discrim a b c % 4 = b % 2`, so an integral discriminant is `0` or `1`
  modulo `4`.
* `TauCeti.not_dvd_two_mul_mul_add_of_not_dvd_discrim`: a root modulo `p` of a quadratic whose
  discriminant is not divisible by `p` is simple, that is `p ∤ 2 a x + b`;
  `TauCeti.not_dvd_two_mul_add_of_not_dvd_sq_add_four_mul` is the case of the monic quadratic
  `x² + b x − c`.

The two `Int.discrim_le_zero_…` results are proved from a common lemma in which `x` runs over an
arithmetic progression rather than all of `ℤ`. Only one `x` is ever used — the member of the
progression nearest the minimum of the restricted form — so thinning the line to gap `m` costs
exactly a factor `m` in the height hypothesis, which the choice of `y` absorbs; `m = 1` is the full
line.

The variant whose hypothesis constrains only `y` is not stated separately: that hypothesis is
strictly stronger than the one above, so a caller holding it applies the same theorem through
`fun x y _ hy => h x y hy`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/Discriminant.lean`, declarations `exists_int_balanced`,
`qf_nonneg_of_nonneg_on_coprime` and `qf_nonneg_of_nonneg_on_coprime_both`. The statements here
are strictly stronger: the form is arbitrary rather than `q r² − t r s + s²`, no primality is
assumed, and a single `y` replaces an infinite family of prime powers.

The source proves its two locus results independently, the `d ∤ y` one by an infinite family of
prime powers together with a balanced-remainder lemma. Neither is reproduced. The `d ∤ y`
statement is not carried at all: it follows from the `d ∤ x ∧ d ∤ y` one in a line, its hypothesis
being the stronger of the two. The balanced remainder it needed is
`Int.exists_two_mul_abs_sub_mul_le`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.2 — the Cauchy–Schwarz step that turns
  positivity of the degree form on a rank-two lattice into the Hasse inequality of V.1.1.
-/

public section

/-- A binary quadratic form with positive leading coefficient and non-positive discriminant is
non-negative. This is the implication opposite to Mathlib's `discrim_le_zero`, stated for the
homogeneous two-variable form and over a linearly ordered commutative ring rather than a field.
The hypothesis `0 < a` cannot be dropped: `discrim 0 0 (-1) = 0`, while `- y ^ 2` is negative. -/
theorem nonneg_of_discrim_le_zero {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b c : R} (ha : 0 < a) (hd : discrim a b c ≤ 0) (x y : R) :
    0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  -- The completed square `4a·Q = (2ax + by)² + (4ac − b²)y²` uses no division.
  have hb : 0 ≤ 4 * a * c - b ^ 2 := by rw [discrim] at hd; linarith
  nlinarith [sq_nonneg (2 * a * x + b * y), mul_nonneg hb (sq_nonneg y)]

/-- A homogeneous binary quadratic form which represents both a positive and a negative value
has positive discriminant. The statement needs no division or nondegeneracy hypothesis. -/
theorem discrim_pos_of_exists_pos_of_exists_neg {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b c : R}
    (hpos : ∃ x y, 0 < a * x ^ 2 + b * x * y + c * y ^ 2)
    (hneg : ∃ x y, a * x ^ 2 + b * x * y + c * y ^ 2 < 0) : 0 < discrim a b c := by
  by_contra! hd
  obtain ⟨xp, yp, hp⟩ := hpos
  obtain ⟨xn, yn, hn⟩ := hneg
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have h := nonneg_of_discrim_le_zero (neg_pos.mpr ha)
      ((discrim_neg a b c).symm ▸ hd) xp yp
    nlinarith
  · subst a
    obtain rfl : b = 0 := by simpa [discrim] using hd
    simp only [zero_mul, zero_add] at hp hn
    rcases le_or_gt c 0 with hc | hc
    · exact hp.not_ge (mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg yp))
    · exact hn.not_ge (mul_nonneg hc.le (sq_nonneg yn))
  · exact hn.not_ge (nonneg_of_discrim_le_zero ha hd xn yn)

/-- A quadratic of negative discriminant with a non-negative leading coefficient has a positive
one: at `a = 0` the discriminant is `b ^ 2`, which is not negative. -/
theorem pos_of_nonneg_of_discrim_lt_zero {R : Type*} [Ring R] [LinearOrder R]
    [IsOrderedRing R] {a b c : R} (ha : 0 ≤ a) (hd : discrim a b c < 0) : 0 < a :=
  ha.lt_of_ne' fun ha ↦ hd.not_ge <| by simp [discrim, ha, sq_nonneg]

/-- **An arithmetic progression of large enough height pins the discriminant.** If a binary
quadratic form over `ℤ` with positive leading coefficient `a` is non-negative at `(x, y)` for a
fixed `y` and every `x` in the progression `x₀ + m * ℤ`, and `a * m < |y|`, then
`discrim a b c ≤ 0`.

The height hypothesis carries a factor `m` that the single-line version does not; `m = 1` is the
full line. -/
private theorem discrim_le_zero_of_pos_of_nonneg_on_progression {a b c m x₀ y : ℤ} (ha : 0 < a)
    (hm : 0 < m) (hy : a * m < |y|)
    (h : ∀ k : ℤ, 0 ≤ a * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  -- Only one `x` is used: the member of the progression nearest the minimum of the restricted
  -- form, which satisfies `|2 a x + b y| ≤ a * m`. That is why thinning the line to gap `m` costs
  -- exactly a factor `m` in the height.
  by_contra! hcon
  rw [discrim] at hcon
  -- Shifting `x₀` by `m * k` moves `2 a x + b y` by `2 a m * k`, so the best `k` is the nearest
  -- multiple of `2 a m`.
  obtain ⟨n, hn⟩ := Int.exists_two_mul_abs_sub_mul_le (2 * a * x₀ + b * y)
    (μ := 2 * a * m) (by positivity)
  rw [abs_of_pos (by positivity : 0 < 2 * a * m)] at hn
  set x : ℤ := x₀ + m * -n with hx
  have hsq : (2 * a * x + b * y) ^ 2 ≤ (a * m) ^ 2 := by
    rw [sq_le_sq, abs_of_pos (by positivity : 0 < a * m),
      show 2 * a * x + b * y = 2 * a * x₀ + b * y - n * (2 * a * m) by rw [hx]; ring]
    linarith
  -- `a * m < |y|` makes the `(4ac − b²)y²` term outweigh it, so the form is negative at `(x, y)`.
  have ham0 : 0 < a * m := by positivity
  have hy2 : (a * m) ^ 2 < y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  have hkey : 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2)
      = (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by ring
  nlinarith [h (-n), hsq, hy2, hkey]

/-- A form with negative leading coefficient is eventually negative along any progression, so the
non-negativity hypothesis is unsatisfiable. -/
private theorem not_forall_nonneg_on_progression_of_neg {a b c m x₀ y : ℤ} (ha : a < 0)
    (hm : 0 < m) :
    ¬ ∀ k : ℤ, 0 ≤ a * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2 := fun h => by
  have hA0 : 0 ≤ |b * y| := abs_nonneg _
  have hB0 : 0 ≤ |c * y ^ 2| := abs_nonneg _
  -- The progression reaches past `M`, and there the square already dominates the rest.
  set M : ℤ := |b * y| + |c * y ^ 2| + 1
  set k : ℤ := M + |x₀|
  have hk0 : 0 ≤ k := by have := abs_nonneg x₀; omega
  set x : ℤ := x₀ + m * k
  have hxM : M ≤ x := by
    have h1 : k ≤ m * k := le_mul_of_one_le_left hk0 hm
    have h2 : -|x₀| ≤ x₀ := neg_abs_le x₀
    omega
  have h2 : b * x * y ≤ |b * y| * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self (b * y))) (by omega : (0 : ℤ) ≤ x)]
  nlinarith [h k, le_abs_self (c * y ^ 2), sq_nonneg x]

/-- A form with zero leading coefficient is linear along a progression, so non-negativity there
forces the slope `b * y * m` to vanish; with `y ≠ 0` and `0 < m` that makes `b = 0`. -/
private theorem eq_zero_of_forall_nonneg_on_progression_of_ne {b c m x₀ y : ℤ} (hy : y ≠ 0)
    (hm : 0 < m)
    (h : ∀ k : ℤ, 0 ≤ 0 * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2) : b = 0 := by
  by_contra hb
  set C : ℤ := b * y * x₀ + c * y ^ 2 with hC
  have hid : ∀ k : ℤ, 0 * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2
      = b * y * m * k + C := fun k => by rw [hC]; ring
  have hC0 : 0 ≤ |C| := abs_nonneg _
  have hCle : C ≤ |C| := le_abs_self _
  have hpos : 0 < (b * y * m) ^ 2 := by positivity
  -- At this `k` the linear term is `-(|C| + 1) * (b y m)²`, which the constant cannot offset.
  have hx := h (-((|C| + 1) * (b * y * m)))
  rw [hid] at hx
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ |C| + 1)
    (by linarith : (0 : ℤ) ≤ (b * y * m) ^ 2 - 1)]

/-- **A progression of large enough height pins the discriminant, whatever the sign of `a`.** No
sign hypothesis on `a` is needed; this is the form both public theorems specialise. -/
private theorem discrim_le_zero_of_nonneg_on_progression {a b c m x₀ y : ℤ} (hm : 0 < m)
    (hy : a * m < |y|)
    (h : ∀ k : ℤ, 0 ≤ a * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  -- A negative leading coefficient makes the hypothesis unsatisfiable; a zero one collapses the
  -- form to a linear function, forcing `b = 0`; a positive one is the case that does the work.
  rcases lt_trichotomy a 0 with ha | ha | ha
  · exact absurd h (not_forall_nonneg_on_progression_of_neg ha hm)
  · subst ha
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    rw [discrim, eq_zero_of_forall_nonneg_on_progression_of_ne hy0 hm h]
    simp
  · exact discrim_le_zero_of_pos_of_nonneg_on_progression ha hm hy h

/-- **A single line of large enough height pins the discriminant.** If a binary quadratic form
over `ℤ` is non-negative at `(x, y)` for a fixed `y` with `a < |y|` and every integer `x`, then
`discrim a b c ≤ 0`, that is `b ^ 2 ≤ 4 * a * c`.

No sign hypothesis on `a` is needed. A negative leading coefficient makes the hypothesis
unsatisfiable, and a zero one collapses the form to a linear function of `x`, forcing `b = 0`.

The height hypothesis `a < |y|` is necessary, not an artefact of the proof: without it the
integer-valued hypothesis is strictly weaker than its field counterpart, as
`forall_int_nonneg_and_discrim_pos` witnesses. -/
theorem Int.discrim_le_zero_of_nonneg_of_lt_abs {a b c y : ℤ} (hy : a < |y|)
    (h : ∀ x : ℤ, 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) : discrim a b c ≤ 0 :=
  -- The whole line is the progression of gap `1` through `0`.
  discrim_le_zero_of_nonneg_on_progression (x₀ := 0) one_pos (by simpa using hy)
    fun k => by simpa using h k

/-- The height hypothesis of `Int.discrim_le_zero_of_nonneg_of_lt_abs` cannot be dropped:
`x ↦ x ^ 2 - x` is non-negative at every integer, yet its discriminant is positive. Here the
leading coefficient and `|y|` are both `1`, so `a < |y|` fails by exactly one. -/
private theorem forall_int_nonneg_and_discrim_pos :
    (∀ x : ℤ, 0 ≤ 1 * x ^ 2 + (-1) * x * 1 + 0 * 1 ^ 2) ∧ 0 < discrim (1 : ℤ) (-1) 0 := by
  refine ⟨fun x => ?_, by norm_num [discrim]⟩
  rcases le_or_gt x 0 with hx | hx
  · nlinarith
  · nlinarith [Int.add_one_le_iff.mpr hx]

/-- **The locus where `d` divides neither coordinate pins the discriminant.** If a binary
quadratic form over `ℤ` is non-negative at every `(x, y)` with `d ∤ x` and `d ∤ y`, for a non-unit
`d`, then `discrim a b c ≤ 0`.

The one-coordinate variant, constraining only `y`, is not stated separately: its hypothesis holds
on a strictly larger set of points, so it is the stronger of the two and a caller holding it
applies this theorem through `fun x y _ hy => h x y hy`. The implication does not run the other
way, and it is this form that an elliptic curve supplies, the pencil `r π − s` being known to be
an isogeny only away from both coordinates.

`d = 0` is allowed, the hypothesis then being non-negativity at every `(x, y)` with `x ≠ 0` and
`y ≠ 0`. -/
theorem Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd {a b c d : ℤ} (hd : ¬ IsUnit d)
    (h : ∀ x y : ℤ, ¬ d ∣ x → ¬ d ∣ y → 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  -- Both coordinates run over `1 + max |d| 2 * ℤ`, every member of which avoids the multiples of
  -- `d`; the widened gap costs a factor `max |d| 2` in the height, which the choice of `y` absorbs.
  set m : ℤ := max |d| 2
  have hm : 2 ≤ m := le_max_right _ _
  have hdm : ∀ k : ℤ, ¬ d ∣ 1 + m * k := Int.not_dvd_one_add_max_abs_mul hd
  -- One second coordinate serves every case: it avoids `d` and clears the widened height bound.
  have hheight : a * m < |1 + m * (|a| * m)| := by
    have ha : 0 ≤ |a| * m := mul_nonneg (abs_nonneg a) (by omega)
    rw [abs_of_pos (by nlinarith)]
    nlinarith [le_abs_self a]
  exact discrim_le_zero_of_nonneg_on_progression (by omega) hheight fun k => h _ _ (hdm k) (hdm _)

/-- The discriminant `b² - 4 a c` of integers `a`, `b`, `c` leaves the remainder `b % 2` on
division by `4`, so it is `0` or `1` modulo `4`. -/
@[simp]
theorem Int.discrim_emod_four (a b c : ℤ) : discrim a b c % 4 = b % 2 := by
  rw [discrim, mul_assoc, Int.sub_mul_emod_self_left, Int.sq_emod_four]

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- A root modulo `p` of a quadratic whose discriminant is not divisible by `p` is simple: the
derivative `2 a x + b` is not divisible by `p`, since
`(2 a x + b)² = 4 a (a x² + b x + c) + discrim a b c`. -/
theorem not_dvd_two_mul_mul_add_of_not_dvd_discrim {p a b c x : R}
    (hd : ¬ p ∣ discrim a b c) (hx : p ∣ a * (x * x) + b * x + c) : ¬ p ∣ 2 * a * x + b :=
  fun h ↦ hd <| by
    rw [show discrim a b c = (2 * a * x + b) ^ 2 - 4 * a * (a * (x * x) + b * x + c) by
      rw [discrim]; ring]
    exact dvd_sub (dvd_pow h two_ne_zero) (hx.mul_left _)

/-- A root modulo `p` of the monic quadratic `x² + b x − c` is simple when `p ∤ b² + 4 c`: the
derivative `2 x + b` is not divisible by `p`. This is
`TauCeti.not_dvd_two_mul_mul_add_of_not_dvd_discrim` for the monic quadratic, whose discriminant
is `b² + 4 c`. -/
theorem not_dvd_two_mul_add_of_not_dvd_sq_add_four_mul {p b c x : R} (hd : ¬ p ∣ b ^ 2 + 4 * c)
    (hx : p ∣ x ^ 2 + b * x - c) : ¬ p ∣ 2 * x + b := by
  simpa using not_dvd_two_mul_mul_add_of_not_dvd_discrim (a := 1) (c := -c)
    (by rwa [discrim, mul_neg, sub_neg_eq_add, mul_one]) (by rwa [one_mul, ← sq, ← sub_eq_add_neg])

end TauCeti
