/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition

/-!
# Sign assignments for grid rectangles

Over `𝔽₂` the grid differential squares to zero because the two-step rectangle domains between two
grid states are counted in pairs. Over a ring of other characteristic the rectangles must be
counted with signs for the two terms of a pair to cancel. A *sign assignment* attaches a sign
`S(r) ∈ {±1}` to every empty rectangle `r` between two grid states of size `n`, subject to three
rules (Manolescu--Ozsváth--Szabó--Thurston):

* *square rule*: if two distinct two-step decompositions `r₁ * r₂` and `r₁' * r₂'` from `x` to `z`
  cover the same domain, then `S(r₁) S(r₂) = -S(r₁') S(r₂')`;
* *vertical annulus rule*: if `r₁` goes from `x` to `y` and `r₂` returns from `y` to `x` along the
  same initial side, so that together they cover a vertical annulus, then `S(r₁) S(r₂) = -1`;
* *horizontal annulus rule*: if `r₂` instead starts at the terminal side of `r₁`, so that together
  they cover a horizontal annulus, then `S(r₁) S(r₂) = 1`.

The domain of a two-step decomposition is recorded as the multiset sum of the squares its two
rectangles cover, so overlapping rectangles count the common squares twice. The rules mention only
grid states and rectangles, never markings, so a sign assignment depends on the grid size alone.

Two sign assignments that differ by a *gauge*, a sign `f(x)` on each grid state applied to both
endpoints of every rectangle, are interchangeable: the gauge transform `S.gauge f` is again a sign
assignment, and the signed grid complexes of `S` and `S.gauge f` are isomorphic.

## Main definitions

* `TauCeti.GridSignAssignment`: a sign assignment on the empty rectangles of size-`n` grid
  states.
* `TauCeti.GridSignAssignment.signOf`: its sign on an arbitrary rectangle, extended by `1` to the
  nonempty rectangles, which the rules do not constrain.
* `TauCeti.GridSignAssignment.gauge`: the gauge transform by a sign on grid states.

## Main results

* `TauCeti.GridSignAssignment.ext`: a sign assignment is determined by its signs on empty
  rectangles.
* `TauCeti.GridSignAssignment.signOf_mul_signOf_eq_neg`: the square rule for `signOf`.
* `TauCeti.GridSignAssignment.gauge_gauge`, `TauCeti.GridSignAssignment.gauge_one`: gauge
  transforms compose by pointwise multiplication, and the trivial gauge does nothing.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 4: sign assignments, their existence and their uniqueness up to
  gauge.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 15: grid homology with integer coefficients.
-/

public section

namespace TauCeti

/-- A sign assignment for grid states of size `n`: a sign on every empty rectangle between two
grid states, satisfying the square rule and the two annulus rules of
Manolescu--Ozsváth--Szabó--Thurston. -/
structure GridSignAssignment (n : ℕ) where
  /-- The sign of an empty rectangle. -/
  sign : ∀ {x y : GridState n} (r : GridRectangleBetween x y), r.IsEmpty → ℤˣ
  /-- The square rule: two distinct two-step decompositions of the same domain, made of empty
  rectangles, carry opposite products of signs. -/
  sign_mul_sign_eq_neg : ∀ {x z : GridState n} (D E : GridRectangleDecomposition x z)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hE₂ : E.second.IsEmpty), E ≠ D →
    E.first.toGridRectangle.coveredSquares.val + E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val →
    sign E.first hE₁ * sign E.second hE₂ = -(sign D.first hD₁ * sign D.second hD₂)
  /-- The vertical annulus rule: an empty rectangle followed by an empty rectangle back along the
  same initial side covers a vertical annulus, and the two signs multiply to `-1`. -/
  sign_mul_sign_eq_neg_one_of_left_eq_left : ∀ {x y : GridState n} (r : GridRectangleBetween x y)
    (s : GridRectangleBetween y x) (hr : r.IsEmpty) (hs : s.IsEmpty), s.left = r.left →
    sign r hr * sign s hs = -1
  /-- The horizontal annulus rule: an empty rectangle followed by an empty rectangle back from
  its terminal side covers a horizontal annulus, and the two signs multiply to `1`. -/
  sign_mul_sign_eq_one_of_left_eq_right : ∀ {x y : GridState n} (r : GridRectangleBetween x y)
    (s : GridRectangleBetween y x) (hr : r.IsEmpty) (hs : s.IsEmpty), s.left = r.right →
    sign r hr * sign s hs = 1

namespace GridSignAssignment

variable {n : ℕ} (S : GridSignAssignment n)

/-- A sign assignment is determined by its signs on the empty rectangles. -/
@[ext]
theorem ext {S T : GridSignAssignment n}
    (h : ∀ (x y : GridState n) (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      S.sign r hr = T.sign r hr) : S = T := by
  cases S
  cases T
  congr
  funext x y r hr
  exact h x y r hr

/-! ### Signs of arbitrary rectangles -/

open Classical in
/-- The sign of an arbitrary rectangle: the assigned sign of an empty rectangle, and `1` on the
nonempty rectangles, where the rules impose nothing. The grid differentials only count empty
rectangles, so the extension never contributes. -/
noncomputable def signOf {x y : GridState n} (r : GridRectangleBetween x y) : ℤˣ :=
  if hr : r.IsEmpty then S.sign r hr else 1

/-- On an empty rectangle `signOf` is the assigned sign. -/
@[simp]
theorem signOf_of_isEmpty {x y : GridState n} {r : GridRectangleBetween x y} (hr : r.IsEmpty) :
    S.signOf r = S.sign r hr := by
  simp [signOf, hr]

/-- On a nonempty rectangle `signOf` is `1`. -/
@[simp]
theorem signOf_of_not_isEmpty {x y : GridState n} {r : GridRectangleBetween x y}
    (hr : ¬ r.IsEmpty) : S.signOf r = 1 := by
  simp [signOf, hr]

/-- The square rule for `signOf`: two distinct two-step decompositions of the same domain, made of
empty rectangles, carry opposite products of signs. -/
theorem signOf_mul_signOf_eq_neg {x z : GridState n} {D E : GridRectangleDecomposition x z}
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hE₂ : E.second.IsEmpty) (hne : E ≠ D)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val) :
    S.signOf E.first * S.signOf E.second = -(S.signOf D.first * S.signOf D.second) := by
  rw [S.signOf_of_isEmpty hD₁, S.signOf_of_isEmpty hD₂, S.signOf_of_isEmpty hE₁,
    S.signOf_of_isEmpty hE₂]
  exact S.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdomain

/-! ### Gauge transforms -/

/-- In a two-step product of gauged signs the gauge sign `b` of the intermediate state appears
twice and cancels. -/
private theorem gauge_mul_gauge (a b c s t : ℤˣ) : a * b * s * (b * c * t) = a * c * (s * t) := by
  calc a * b * s * (b * c * t) = (b * b) * (a * c * (s * t)) := by ac_rfl
    _ = a * c * (s * t) := by rw [Int.units_mul_self, one_mul]

/-- The gauge transform of a sign assignment by a sign `f` on grid states: the sign of a rectangle
from `x` to `y` is multiplied by `f x * f y`. The rules survive because in every two-step product
the sign of the intermediate state appears twice. -/
def gauge (f : GridState n → ℤˣ) : GridSignAssignment n where
  sign {x y} r hr := f x * f y * S.sign r hr
  sign_mul_sign_eq_neg {x z} D E hD₁ hD₂ hE₁ hE₂ hne hdomain := by
    rw [gauge_mul_gauge, gauge_mul_gauge, S.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdomain,
      mul_neg]
  sign_mul_sign_eq_neg_one_of_left_eq_left {x y} r s hr hs hleft := by
    rw [gauge_mul_gauge, S.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft,
      Int.units_mul_self, one_mul]
  sign_mul_sign_eq_one_of_left_eq_right {x y} r s hr hs hright := by
    rw [gauge_mul_gauge, S.sign_mul_sign_eq_one_of_left_eq_right r s hr hs hright,
      Int.units_mul_self, one_mul]

/-- The sign of an empty rectangle in a gauge transform. -/
@[simp]
theorem gauge_sign (f : GridState n → ℤˣ) {x y : GridState n} (r : GridRectangleBetween x y)
    (hr : r.IsEmpty) : (S.gauge f).sign r hr = f x * f y * S.sign r hr :=
  (rfl)

/-- The sign of an empty rectangle in a gauge transform, in terms of `signOf`. -/
theorem signOf_gauge (f : GridState n → ℤˣ) {x y : GridState n} {r : GridRectangleBetween x y}
    (hr : r.IsEmpty) : (S.gauge f).signOf r = f x * f y * S.signOf r := by
  rw [signOf_of_isEmpty _ hr, signOf_of_isEmpty _ hr, gauge_sign]

/-- Gauge transforms compose by pointwise multiplication of the gauges. -/
@[simp]
theorem gauge_gauge (f g : GridState n → ℤˣ) : (S.gauge f).gauge g = S.gauge (g * f) := by
  ext x y r hr
  simp only [gauge_sign, Pi.mul_apply]
  ac_rfl

/-- The trivial gauge leaves a sign assignment unchanged. -/
@[simp]
theorem gauge_one : S.gauge 1 = S := by
  ext x y r hr
  simp

/-- A gauge transform is undone by the same gauge, since every sign squares to `1`. -/
theorem gauge_gauge_self (f : GridState n → ℤˣ) : (S.gauge f).gauge f = S := by
  have hf : f * f = 1 := funext fun x => Int.units_mul_self (f x)
  rw [gauge_gauge, hf, gauge_one]

end GridSignAssignment

end TauCeti
