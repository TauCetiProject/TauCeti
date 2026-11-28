/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.Equation
import Mathlib.Data.Set.Card
import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The three points of order two on a scaled Legendre equation

Over a field `K`, let `d ≠ 0`, `l ≠ 0` and `l ≠ 1`. The cubic of the scaled Legendre equation

  `y² = x (x - d) (x - d l)`

has the three distinct roots `0`, `d` and `d l`, in this order, and its derivative at them is
`d² l`, `d² (1 - l)` and `d² l (l - 1)`, all nonzero. So the points `(0, 0)`, `(d, 0)` and
`(d l, 0)` are nonsingular, and they make up the labelled tuple
`TauCeti.scaledLegendreRootPoint : Fin 3 → (scaledLegendre d l).toAffine.Point`. Its entries are
affine points, never the origin.

Since `a₁ = a₃ = 0`, negation is `(x, y) ↦ (x, -y)`, so each of the three points is its own
negative and is killed by `2`; the line `y = 0` through two of them meets the curve again at the
third, so their sum is `0`. These facts hold in every characteristic. When moreover `2 ≠ 0`, an
affine point killed by `2` has `y = 0` (`WeierstrassCurve.y_eq_zero_of_order_two`), so its first
coordinate is a root of the cubic: the points killed by `2` are exactly the origin and the three
labelled points, and there are four of them. The general count
`WeierstrassCurve.Affine.card_ker_nsmul_two` gives only this number; here the points themselves
are named, in the order of the roots, as the explicit `2`-descent of a curve with full rational
`2`-torsion needs them.

## Main definitions

* `TauCeti.scaledLegendreRootPoint`: the points `(0, 0)`, `(d, 0)` and `(d l, 0)` of the scaled
  Legendre equation, indexed by `Fin 3`.

## Main results

* `TauCeti.nonsingular_scaledLegendre_root`: the three root pairs are nonsingular points.
* `TauCeti.scaledLegendreRootPoint_injective`: the three points are distinct.
* `TauCeti.two_nsmul_scaledLegendreRootPoint`: each of them is killed by `2`.
* `TauCeti.sum_scaledLegendreRootPoint`: their sum is `0`.
* `TauCeti.two_nsmul_eq_zero_iff_scaledLegendre`: over a field with `2 ≠ 0`, a point is killed
  by `2` exactly when it is `0` or one of the three points;
  `TauCeti.card_ker_nsmul_two_scaledLegendre`: there are four such points.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2, for negation on a
  Weierstrass equation and the points of order two.
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, §6, the proofs of Lemmas 6.5 and 6.6, for the three
  points of order two of a scaled Legendre equation.
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] {d l : K}

/-- **The three roots give nonsingular points.** For `d ≠ 0`, `l ≠ 0` and `l ≠ 1`, the pairs
`(0, 0)`, `(d, 0)` and `(d l, 0)` are nonsingular points of `y² = x (x - d) (x - d l)`: the
derivative of the cubic there is `d² l`, `d² (1 - l)` and `d² l (l - 1)` respectively. No
hypothesis on the characteristic is needed. -/
theorem nonsingular_scaledLegendre_root (hd : d ≠ 0) (hl₀ : l ≠ 0) (hl₁ : l ≠ 1) (j : Fin 3) :
    (scaledLegendre d l).toAffine.Nonsingular (![0, d, d * l] j) 0 := by
  have hl₁' : l - 1 ≠ 0 := sub_ne_zero.mpr hl₁
  rw [nonsingular_iff, equation_scaledLegendre_iff]
  refine ⟨by fin_cases j <;> simp, Or.inl ?_⟩
  simp only [a₁_of_isCharNeTwoNF, scaledLegendre_a₂, scaledLegendre_a₄, zero_mul]
  fin_cases j
  · simpa using ⟨hd, hl₀⟩
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show 3 * d ^ 2 + 2 * -(d * (1 + l)) * d + d ^ 2 * l = -(d ^ 2 * (l - 1)) by ring]
    simpa using ⟨hd, hl₁'⟩
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [show 3 * (d * l) ^ 2 + 2 * -(d * (1 + l)) * (d * l) + d ^ 2 * l =
      d ^ 2 * l * (l - 1) by ring]
    simpa using ⟨⟨hd, hl₀⟩, hl₁'⟩

/-- **The three points of order two of a scaled Legendre equation**, `(0, 0)`, `(d, 0)` and
`(d l, 0)`, labelled by `Fin 3` in the order `0`, `d`, `d l` of the roots of the cubic
`x (x - d) (x - d l)`, for `d ≠ 0`, `l ≠ 0` and `l ≠ 1`. The origin is not among them. -/
noncomputable def scaledLegendreRootPoint (hd : d ≠ 0) (hl₀ : l ≠ 0) (hl₁ : l ≠ 1) (j : Fin 3) :
    (scaledLegendre d l).toAffine.Point :=
  .some _ _ (nonsingular_scaledLegendre_root hd hl₀ hl₁ j)

variable (hd : d ≠ 0) (hl₀ : l ≠ 0) (hl₁ : l ≠ 1)

/-- The labelled points are the affine points `(0, 0)`, `(d, 0)` and `(d l, 0)`. -/
theorem scaledLegendreRootPoint_eq_some (j : Fin 3) :
    scaledLegendreRootPoint hd hl₀ hl₁ j =
      .some (![0, d, d * l] j) 0 (nonsingular_scaledLegendre_root hd hl₀ hl₁ j) :=
  (rfl)

/-- No labelled point is the origin. -/
@[simp]
theorem scaledLegendreRootPoint_ne_zero (j : Fin 3) : scaledLegendreRootPoint hd hl₀ hl₁ j ≠ 0 :=
  by rw [scaledLegendreRootPoint_eq_some]; exact Point.some_ne_zero _

/-- **The three labelled points are distinct**, since the roots `0`, `d` and `d l` are. -/
theorem scaledLegendreRootPoint_injective :
    Function.Injective (scaledLegendreRootPoint hd hl₀ hl₁) := by
  intro i j h
  simp only [scaledLegendreRootPoint_eq_some, Point.some.injEq, and_true] at h
  have : d ≠ d * l := fun h ↦ hl₁ (mul_eq_left₀ hd |>.mp h.symm)
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm (a := (0 : K))]

variable [DecidableEq K]

/-- **Each labelled point is killed by `2`**: it is its own negative, since `y = 0` and
`a₁ = a₃ = 0`. No hypothesis on the characteristic is needed. -/
@[simp]
theorem two_nsmul_scaledLegendreRootPoint (j : Fin 3) :
    2 • scaledLegendreRootPoint hd hl₀ hl₁ j = 0 := by
  rw [two_nsmul, scaledLegendreRootPoint_eq_some]
  exact Point.add_self_of_Y_eq (by simp [negY])

/-- The sum of the first two labelled points is the third: the line `y = 0` through `(0, 0)` and
`(d, 0)` meets the curve again at `(d l, 0)`, which is its own negative. -/
theorem scaledLegendreRootPoint_zero_add_one :
    scaledLegendreRootPoint hd hl₀ hl₁ 0 + scaledLegendreRootPoint hd hl₀ hl₁ 1 =
      scaledLegendreRootPoint hd hl₀ hl₁ 2 := by
  simp only [scaledLegendreRootPoint_eq_some]
  rw [Point.add_of_X_ne (by simpa using hd.symm)]
  simp [addY, negY, slope_of_X_ne (by simpa using hd.symm : (0 : K) ≠ d)]
  ring

/-- **The three labelled points sum to `0`.** -/
theorem sum_scaledLegendreRootPoint : ∑ j, scaledLegendreRootPoint hd hl₀ hl₁ j = 0 := by
  rw [Fin.sum_univ_three, scaledLegendreRootPoint_zero_add_one, ← two_nsmul,
    two_nsmul_scaledLegendreRootPoint]

/-- **The points killed by `2`.** Over a field with `2 ≠ 0`, a point of the scaled Legendre
equation is killed by `2` exactly when it is the origin or one of the three labelled points. -/
theorem two_nsmul_eq_zero_iff_scaledLegendre (h2 : (2 : K) ≠ 0)
    (P : (scaledLegendre d l).toAffine.Point) :
    2 • P = 0 ↔ P = 0 ∨ ∃ j, scaledLegendreRootPoint hd hl₀ hl₁ j = P := by
  refine ⟨fun hP ↦ ?_, ?_⟩
  · rcases P with _ | ⟨x, y, h⟩
    · exact Or.inl rfl
    obtain rfl := y_eq_zero_of_order_two h2 h hP
    have hx := (equation_scaledLegendre_iff d l x 0).mp h.1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_eq_mul, mul_eq_zero,
      sub_eq_zero] at hx
    refine Or.inr ?_
    rcases hx with (rfl | rfl) | rfl
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · rintro (rfl | ⟨j, rfl⟩)
    · exact smul_zero 2
    · exact two_nsmul_scaledLegendreRootPoint hd hl₀ hl₁ j

/-- Over a field with `2 ≠ 0`, the points killed by `2` are the origin and the three labelled
points. -/
theorem coe_ker_nsmul_two_scaledLegendre (h2 : (2 : K) ≠ 0) :
    ((nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker : Set _) =
      insert 0 (Set.range (scaledLegendreRootPoint hd hl₀ hl₁)) := by
  ext P
  exact two_nsmul_eq_zero_iff_scaledLegendre hd hl₀ hl₁ h2 P

include hd hl₀ hl₁ in
/-- **Over a field with `2 ≠ 0`, exactly four points are killed by `2`**: the origin and the three
labelled points. -/
theorem card_ker_nsmul_two_scaledLegendre (h2 : (2 : K) ≠ 0) :
    Nat.card (nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker = 4 := by
  rw [← SetLike.coe_sort_coe, coe_ker_nsmul_two_scaledLegendre hd hl₀ hl₁ h2,
    Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_range_of_injective
      (scaledLegendreRootPoint_injective hd hl₀ hl₁), Nat.card_eq_fintype_card, Fintype.card_fin]
  rintro ⟨j, hj⟩
  exact scaledLegendreRootPoint_ne_zero hd hl₀ hl₁ j hj

end TauCeti
