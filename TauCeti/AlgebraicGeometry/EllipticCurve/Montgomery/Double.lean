/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates

/-!
# Montgomery doubling

The polynomial map `double N D` doubles a raw projective Montgomery coordinate pair using
scaled constants satisfying `4 * N = (A + 2) * D`. It is homogeneous of degree four and
commutes with ring homomorphisms, so it can be used both over fields and over composite
residue rings.

`double_coordinates` proves correctness on Mathlib's native point group, including infinity
and points of order two. Its output is nonzero even when the model is singular, since native
points are nonsingular. `double_coordinates_of_cross_eq_zero` gives the same result for any nonzero
representative of a point's coordinate pair.

The proof uses Mathlib's duplication numerator and denominator, in particular
`WeierstrassCurve.Affine.den_duplication_ne_zero_or_num_duplication_ne_zero` and
`WeierstrassCurve.Affine.addX_self_of_Y_ne`.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1, p. 261, duplication display.
* D. J. Bernstein and T. Lange, *Explicit-Formulas Database*, Montgomery XZ coordinates,
  entry `dbl-1987-m-3`. Both output coordinates are multiplied by `D` here.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Montgomery doubling with scaled `A24 = (A + 2)/4`: put `U = (X + Z)²`,
`V = (X - Z)²`, and `C = U - V`, and return `(D U V, C (D V + N C))`.
The output is a raw pair and can be zero on arbitrary inputs. -/
def double (N D : R) (P : Pair R) : Pair R :=
  let U := (P.x + P.z) ^ 2
  let V := (P.x - P.z) ^ 2
  let C := U - V
  ⟨D * U * V, C * (D * V + N * C)⟩

/-- The first field of doubling is independent of `N`. -/
theorem double_x (N D : R) (P : Pair R) :
    (double N D P).x = D * (P.x ^ 2 - P.z ^ 2) ^ 2 := by
  simp only [double]
  ring

/-- The second field in the scaled `A24` formula. -/
theorem double_z (N D : R) (P : Pair R) :
    (double N D P).z = ((P.x + P.z) ^ 2 - (P.x - P.z) ^ 2) *
      (D * (P.x - P.z) ^ 2 + N * ((P.x + P.z) ^ 2 - (P.x - P.z) ^ 2)) := by
  simp only [double]

/-- When the scaled constants satisfy their defining relation, the second field is the
homogeneous Montgomery duplication denominator. -/
theorem double_z_of_relation {A N D : R} (h : 4 * N = (A + 2) * D) (P : Pair R) :
    (double N D P).z = 4 * D * P.x * P.z *
      (P.x ^ 2 + A * P.x * P.z + P.z ^ 2) := by
  rw [double_z]
  linear_combination 4 * P.x ^ 2 * P.z ^ 2 * h

/-- Doubling is homogeneous of degree four. -/
@[simp]
theorem double_smul (N D c : R) (P : Pair R) :
    double N D (c • P) = c ^ 4 • double N D P := by
  ext <;> simp only [double, Pair.smul_x, Pair.smul_z] <;> ring

/-- Doubling commutes with any change of coefficient ring. -/
@[simp]
theorem map_double (f : R →+* S) (N D : R) (P : Pair R) :
    (double N D P).map f = double (f N) (f D) (P.map f) := by
  ext <;> simp [double]

@[simp]
theorem double_zero (N D : R) : double N D 0 = 0 := by
  ext <;> simp [double]

/-- Infinity doubles to infinity when `D` is nonzero. -/
@[simp]
theorem double_one_zero (N D : R) : double N D ⟨1, 0⟩ = ⟨D, 0⟩ := by
  ext <;> simp [double]

/-- The coordinate of the distinguished point of order two doubles to infinity when `D ≠ 0`. -/
@[simp]
theorem double_zero_one (N D : R) : double N D ⟨0, 1⟩ = ⟨D, 0⟩ := by
  ext <;> simp [double]

/-- On an affine coordinate pair the scaled formula is precisely Mathlib's duplication
numerator and denominator, with the second field additionally scaled by `B`. -/
private theorem double_some_eq {A B N D : R} (h : 4 * N = (A + 2) * D) (x : R) :
    double N D ⟨x, B⟩ =
      ⟨D * (x ^ 4 - (model A B).b₄ * x ^ 2 - 2 * (model A B).b₆ * x -
          (model A B).b₈),
        D * B * (4 * x ^ 3 + (model A B).b₂ * x ^ 2 +
          2 * (model A B).b₄ * x + (model A B).b₆)⟩ := by
  ext
  · simp only [double_x, model_b₄, model_b₆, model_b₈]
    ring
  · rw [double_z_of_relation h]
    simp only [model_b₂, model_b₄, model_b₆]
    ring

end CommRing

section Field

variable {K : Type*} [Field K] [DecidableEq K] {A B N D : K}

omit [DecidableEq K] in
/-- For `B = 0` the model is the cusp `y² = x³`, whose nonsingular affine points have `x ≠ 0`. -/
private theorem x_ne_zero_of_nonsingular_zero {A x y : K}
    (h : (model A 0).toAffine.Nonsingular x y) : x ≠ 0 := by
  rintro rfl
  rw [Affine.nonsingular_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [Affine.equation_iff] at h1
  simp only [model_a₁, mul_zero, zero_mul, add_zero, model_a₃, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, model_a₂, model_a₄, model_a₆, pow_eq_zero_iff, not_true_eq_false,
    sub_zero, false_or] at h1 h2
  exact h2 (by rw [h1, neg_zero])

omit [DecidableEq K] in
/-- The coordinate pair of a native point is nonzero. For `B ≠ 0` this is
`coordinates_ne_zero`; for `B = 0` the model is the cusp `y² = x³` and its nonsingular affine
points have `x ≠ 0`. -/
private theorem coordinates_ne_zero_of_field (P : (model A B).toAffine.Point) :
    coordinates A B P ≠ 0 := by
  by_cases hB : B = 0
  · subst hB
    rcases P with _ | ⟨x, y, hP⟩
    · simp [← Affine.Point.zero_def, Pair.eq_zero_iff]
    · simp [Pair.eq_zero_iff, x_ne_zero_of_nonsingular_zero hP]
  · exact coordinates_ne_zero hB P

/-- **Correctness of Montgomery doubling on native points.** For nonzero `D` and `4N = (A + 2)D`,
the output is nonzero and has vanishing cross difference with the coordinate pair of `P + P`. No
ellipticity assumption is needed, nor `B ≠ 0`: for `B = 0` the model is the cusp `y² = x³`. In
characteristic two, the scaled relation and `D ≠ 0` force `A = 0`, so only that degenerate model
is covered. -/
theorem double_coordinates (hD : D ≠ 0)
    (h : 4 * N = (A + 2) * D) (P : (model A B).toAffine.Point) :
    double N D (coordinates A B P) ≠ 0 ∧
      (double N D (coordinates A B P)).cross (coordinates A B (P + P)) = 0 := by
  rcases P with _ | ⟨x, y, hP⟩
  · simp [← Affine.Point.zero_def, Pair.eq_zero_iff, Pair.cross_def, hD]
  · rw [coordinates_some, double_some_eq h]
    constructor
    · by_cases hB : B = 0
      · subst hB
        have hx := x_ne_zero_of_nonsingular_zero hP
        simp [Pair.ne_zero_iff, hD, hx, model_b₄, model_b₆, model_b₈]
      · have hn := Affine.den_duplication_ne_zero_or_num_duplication_ne_zero hP
        simpa [Pair.ne_zero_iff, hD, hB, or_comm] using hn
    · by_cases hy : y = (model A B).toAffine.negY x y
      · have hd := (Affine.den_duplication_eq_zero_iff hP.1).mpr hy
        rw [Affine.Point.add_self_of_Y_eq hy, coordinates_zero, Pair.cross_def, hd]
        simp
      · have hd := (Affine.den_duplication_eq_zero_iff hP.1).not.mpr hy
        rw [Affine.Point.add_self_of_Y_ne hy, coordinates_some, Pair.cross_def,
          Affine.addX_self_of_Y_ne hP.1 hy]
        -- Remove the affine-coordinate wrapper so the denominator in hd and the goal
        -- matches the model invariants in the cancellation identity below.
        dsimp only [toAffine] at hd ⊢
        linear_combination -(D * B) *
          (div_mul_cancel₀
            (x ^ 4 - (model A B).b₄ * x ^ 2 - 2 * (model A B).b₆ * x - (model A B).b₈) hd)

/-- Doubling any nonzero representative of a native point gives a nonzero representative
of its double. This is the representative-independent form used by `x`-only scalar arithmetic. -/
theorem double_coordinates_of_cross_eq_zero (hD : D ≠ 0)
    (h : 4 * N = (A + 2) * D) {P : (model A B).toAffine.Point} {S : Pair K}
    (hS : S ≠ 0) (hSP : S.cross (coordinates A B P) = 0) :
    double N D S ≠ 0 ∧
      (double N D S).cross (coordinates A B (P + P)) = 0 := by
  obtain ⟨c, rfl⟩ := (Pair.cross_eq_zero_iff_exists_smul (coordinates_ne_zero_of_field P)).mp hSP
  have hc : c ≠ 0 := by
    intro hc
    apply hS
    ext <;> simp [hc]
  obtain ⟨hn, hx⟩ := double_coordinates hD h P
  rw [double_smul]
  constructor
  · rw [Pair.ne_zero_iff] at hn ⊢
    simpa [hc] using hn
  · simp [hx]

end Field

end TauCeti.Montgomery
