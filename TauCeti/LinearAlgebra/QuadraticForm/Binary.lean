/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Representation
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.SquareClass

/-!
# Binary quadratic forms

This file develops two standard families of binary quadratic forms on `Fin 2 → R`: diagonal forms
`⟨a, b⟩` (`QuadraticMap.weightedSumSquares R ![a, b]`) and general binary forms `[a, b]` with a
unit cross term (`TauCeti.binaryQuadraticForm R a b`).

## Diagonal binary forms `⟨a, b⟩`

For a diagonal binary form `QuadraticMap.weightedSumSquares R ![a, b]` on `Fin 2 → R`,
classically written `⟨a, b⟩`, this file proves the two normal-form theorems that pin such a form
down.

The first is the **representation normal form**: a unit `c` is represented by `⟨a, b⟩` exactly
when `c` may be taken as the first coefficient, the second being forced to `a * b * c`. Its
content is a single explicit change of variables. If `a x² + b y² = c` with `c` invertible, then
the vector `(x, y)` and its orthogonal companion `(-b y, a x)` form a basis, because the
determinant of the pair is exactly `c`, and reading `⟨a, b⟩` in that basis gives `⟨c, a b c⟩`.
Since `a * b * c` and `a * b * c⁻¹` differ by the square `c²`, the two spellings of the second
coefficient found in the sources present the same form. Only the *represented* value has to be a
unit here, so this half of the theory is developed over a commutative ring.

The second is the **binary equivalence criterion**: two binary forms with unit coefficients are
isometric exactly when they have the same discriminant modulo squares and represent a common
unit. One direction follows from the discriminant change-of-variables formula; the other applies
the representation normal form to both sides and compares the forced second coefficients.

Both statements are about the *unit* value set `QuadraticMap.unitValueSet`. Invertibility of the
represented value carries the whole content of the first theorem: every quadratic form represents
`0` through the zero vector, so a reading at `c = 0` says nothing.

## Binary quadratic forms `[a, b]`

The binary quadratic form `TauCeti.binaryQuadraticForm R a b` given by
`a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2` on `Fin 2 → R` (Elman--Karpenko--Merkurjev, §7.B)
carries a unimodular polar pairing whenever `2 * a = 0` and `2 * b = 0` (in particular whenever
`a = b = 0`, giving the characteristic-free hyperbolic plane `x 0 * x 1`, or in characteristic
two). Over any commutative ring, `binaryQuadraticForm R a 0` and `binaryQuadraticForm R 0 b` are
explicitly isometric to the hyperbolic plane `binaryQuadraticForm R 0 0` via shear isometries, and
over any field `binaryQuadraticForm K 1 c` is anisotropic if and only if the Artin--Schreier
polynomial `t ^ 2 + t + c` has no root in `K`.

## Main definitions

* `TauCeti.isometryEquivBinaryNormalForm`: the change of variables carrying `⟨c, a b c⟩` to
  `⟨a, b⟩`, built from a solution of `a x² + b y² = c`.
* `TauCeti.binaryQuadraticForm`: the binary quadratic form `a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2`
  on `Fin 2 → R` (Elman--Karpenko--Merkurjev's `[a, b]`).
* `TauCeti.isometryEquivBinaryQuadraticFormLeft`, `TauCeti.isometryEquivBinaryQuadraticFormRight`:
  explicit shear isometries from `binaryQuadraticForm R a 0` and `binaryQuadraticForm R 0 b` to the
  hyperbolic plane `binaryQuadraticForm R 0 0`.

## Main results

* `TauCeti.mem_unitValueSet_binary_iff_equivalent`: the representation normal form, Lam I.2.3 (2).
* `TauCeti.equivalent_binaryNormalForm_inv`: the two spellings `a b c` and `a b c⁻¹` of the
  forced second coefficient present the same form.
* `TauCeti.apply_mul_eq_of_equivalent_binary`: a pairing constant on isometric binary forms
  agrees on their discriminants in its first argument.
* `TauCeti.equivalent_binary_iff`: the binary equivalence criterion, Lam I.5.1.
* `TauCeti.represents_binary_one_neg_iff`: coordinate representation criterion for the norm form
  `⟨1, -d⟩`.
* `TauCeti.anisotropic_binary_iff`: `⟨a, b⟩` is anisotropic exactly when `-ab` is not a square;
  `TauCeti.anisotropic_binary_one_neg_iff` is its square-radicand form for `⟨1, -d⟩`.
* `TauCeti.nondegenerate_polarBilin_binaryQuadraticForm_zero`,
  `TauCeti.nondegenerate_polarBilin_binaryQuadraticForm_of_two_mul_eq_zero`: nondegeneracy of the
  polar bilinear form of `[a, b]` when `2 * a = 0` and `2 * b = 0`.
* `TauCeti.isTotallyIsotropic_ker_proj_one_binaryQuadraticForm`,
  `TauCeti.not_anisotropic_binaryQuadraticForm_zero`,
  `TauCeti.anisotropic_binaryQuadraticForm_one_iff`: isotropy and Artin--Schreier anisotropy
  criteria for `[a, b]`.

## References

* R. Elman, N. Karpenko, and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  American Mathematical Society Colloquium Publications 56 (2008), Chapter II, §7.B.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Proposition 2.3 and Proposition 5.1.
-/

public section

open QuadraticMap

namespace TauCeti

universe u

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- A binary diagonal form represents its first coefficient. -/
theorem represents_binary_left (a b : R) : Represents (weightedSumSquares R ![a, b]) a :=
  (represents_iff _ _).mpr <| Set.mem_range.mpr
    ⟨![1, 0], by simp [weightedSumSquares_apply, Fin.sum_univ_two]⟩

/-- The first coefficient of a binary diagonal form lies in its unit value set. -/
theorem mem_unitValueSet_binary_left (a : Rˣ) (b : R) :
    a ∈ unitValueSet (weightedSumSquares R ![(a : R), b]) :=
  mem_unitValueSet.mpr (represents_binary_left _ _)

/-- The two spellings of the second coefficient of the binary normal form present the same form:
`a * b * c` and `a * b * c⁻¹` differ by the square `c²`, so `⟨c, a b c⟩` and `⟨c, a b c⁻¹⟩` are
isometric.

Sources state the normal form both ways, the second because the square class of the second
coefficient is forced to be that of the discriminant `a * b` divided by `c`. -/
theorem equivalent_binaryNormalForm_inv (a b : R) (c : Rˣ) :
    (weightedSumSquares R ![(c : R), a * b * c]).Equivalent
      (weightedSumSquares R ![(c : R), a * b * (c⁻¹ : Rˣ)]) :=
  ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares ![1, c] (by
    intro i
    fin_cases i <;> simp [pow_two, mul_assoc])⟩

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

/-- The **binary representation normal form** as an explicit change of variables: a solution of
`a x² + b y² = c` with `c` invertible carries `⟨c, a * b * c⟩` to `⟨a, b⟩`.

The map sends the first standard basis vector to `(x, y)`, on which `⟨a, b⟩` takes the value `c`,
and the second to the orthogonal companion `(-b y, a x)`, on which `⟨a, b⟩` takes the value
`a * b * c`. Its determinant is `a x² + b y² = c`, which is why the hypothesis asks for a unit. -/
def isometryEquivBinaryNormalForm (a b x y : R) (c : Rˣ) (h : a * x ^ 2 + b * y ^ 2 = c) :
    (weightedSumSquares R ![(c : R), a * b * c]).IsometryEquiv (weightedSumSquares R ![a, b]) where
  toFun v := ![x * v 0 - b * y * v 1, y * v 0 + a * x * v 1]
  invFun v := ![(↑c⁻¹ : R) * (a * x * v 0 + b * y * v 1), (↑c⁻¹ : R) * (x * v 1 - y * v 0)]
  map_add' u v := by
    ext i
    fin_cases i <;> · simp; ring
  map_smul' r v := by
    ext i
    fin_cases i <;> · simp; ring
  left_inv v := by
    have hc : (↑c⁻¹ : R) * (a * x ^ 2 + b * y ^ 2) = 1 := by rw [h]; exact c.inv_mul
    ext i
    fin_cases i <;> simp
    · linear_combination v 0 * hc
    · linear_combination v 1 * hc
  right_inv v := by
    have hc : (↑c⁻¹ : R) * (a * x ^ 2 + b * y ^ 2) = 1 := by rw [h]; exact c.inv_mul
    ext i
    fin_cases i <;> simp
    · linear_combination v 0 * hc
    · linear_combination v 1 * hc
  map_app' v := by
    simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    linear_combination (v 0 * v 0 + a * b * (v 1 * v 1)) * h

/-- The explicit coordinates of the isometry on a vector. -/
@[simp]
theorem isometryEquivBinaryNormalForm_apply (a b x y : R) (c : Rˣ)
    (h : a * x ^ 2 + b * y ^ 2 = c) (v : Fin 2 → R) :
    isometryEquivBinaryNormalForm a b x y c h v =
      ![x * v 0 - b * y * v 1, y * v 0 + a * x * v 1] :=
  (rfl)

/-- The explicit coordinates of the inverse isometry on a vector. -/
@[simp]
theorem isometryEquivBinaryNormalForm_symm_apply (a b x y : R) (c : Rˣ)
    (h : a * x ^ 2 + b * y ^ 2 = c) (v : Fin 2 → R) :
    (isometryEquivBinaryNormalForm a b x y c h).symm v =
      ![(↑c⁻¹ : R) * (a * x * v 0 + b * y * v 1),
        (↑c⁻¹ : R) * (x * v 1 - y * v 0)] :=
  (rfl)

/-- **The binary representation normal form**, Lam I.2.3 (2): a unit represented by a binary
diagonal form may be taken as its first coefficient. -/
theorem equivalent_binaryNormalForm_of_mem_unitValueSet {a b : R} {c : Rˣ}
    (h : c ∈ unitValueSet (weightedSumSquares R ![a, b])) :
    (weightedSumSquares R ![a, b]).Equivalent
      (weightedSumSquares R ![(c : R), a * b * c]) := by
  obtain ⟨v, hv⟩ := Set.mem_range.mp
    ((represents_iff _ _).mp (mem_unitValueSet.mp h))
  rw [weightedSumSquares_apply, Fin.sum_univ_two] at hv
  refine ⟨(isometryEquivBinaryNormalForm a b (v 0) (v 1) c ?_).symm⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] at hv
  linear_combination hv

/-- **The binary representation normal form**, Lam I.2.3 (2). A binary diagonal form represents a
unit `c` exactly when it is isometric to `⟨c, a * b * c⟩`.

⚠ That `c` is a unit is essential: every quadratic form represents the scalar `0` through the
zero vector, and `⟨a, b⟩` is in general not isometric to `⟨0, 0⟩`. -/
theorem mem_unitValueSet_binary_iff_equivalent (a b : R) (c : Rˣ) :
    c ∈ unitValueSet (weightedSumSquares R ![a, b]) ↔
      (weightedSumSquares R ![a, b]).Equivalent
        (weightedSumSquares R ![(c : R), a * b * c]) := by
  refine ⟨fun h => equivalent_binaryNormalForm_of_mem_unitValueSet h, fun h => ?_⟩
  rw [h.unitValueSet_eq]
  exact mem_unitValueSet_binary_left _ _

/-- Two binary diagonal forms with unit coefficients that have the same discriminant modulo
squares and represent a common unit are isometric. This is the substantial direction of
Lam I.5.1, and it needs no assumption on the characteristic. -/
theorem equivalent_binary_of_isSquare_of_mem_unitValueSet {a b c d e : Rˣ}
    (hdisc : IsSquare (a * b * (c * d)))
    (hab : e ∈ unitValueSet (weightedSumSquares R ![(a : R), (b : R)]))
    (hcd : e ∈ unitValueSet (weightedSumSquares R ![(c : R), (d : R)])) :
    (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(c : R), (d : R)]) := by
  obtain ⟨t, ht⟩ := hdisc
  refine (equivalent_binaryNormalForm_of_mem_unitValueSet hab).trans
    (Equivalent.trans ?_
      (equivalent_binaryNormalForm_of_mem_unitValueSet hcd).symm)
  refine ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares ![1, t * (c * d)⁻¹] ?_⟩
  intro i
  fin_cases i
  · simp
  · have hu : c * (d * (e * (t * (c * d)⁻¹) ^ 2)) = a * (b * e) := by
      rw [pow_two]
      calc
        c * (d * (e * ((t * (c * d)⁻¹) * (t * (c * d)⁻¹)))) =
            (t * t) * ((c * d)⁻¹ * (c * d)⁻¹ * (c * d)) * e := by ac_rfl
        _ = (a * b * (c * d)) * ((c * d)⁻¹ * (c * d)⁻¹ * (c * d)) * e := by rw [ht]
        _ = a * (b * e) := by simp [mul_assoc]
    simpa [mul_assoc] using congrArg Units.val hu

/-- **The binary equivalence criterion**, Lam I.5.1. Two binary diagonal forms with unit
coefficients are isometric exactly when their discriminants agree modulo squares and they
represent a common unit.

The quotient-free spelling `IsSquare (a * b * (c * d))` of "equal discriminants" is the one that
`TauCeti.squareClass_eq_zero_iff` translates into the square-class group. -/
theorem equivalent_binary_iff [Invertible (2 : R)] (a b c d : Rˣ) :
    (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
        (weightedSumSquares R ![(c : R), (d : R)]) ↔
      IsSquare (a * b * (c * d)) ∧
        ∃ e : Rˣ, e ∈ unitValueSet (weightedSumSquares R ![(a : R), (b : R)]) ∧
          e ∈ unitValueSet (weightedSumSquares R ![(c : R), (d : R)]) := by
  refine ⟨fun h => ⟨?_, a,
    mem_unitValueSet_binary_left _ _, ?_⟩,
    fun ⟨hdisc, _, hab, hcd⟩ => equivalent_binary_of_isSquare_of_mem_unitValueSet hdisc hab hcd⟩
  · have hcoe (u v : Rˣ) : (fun i => ((![u, v] i : Rˣ) : R)) = ![(u : R), (v : R)] := by
      ext i
      fin_cases i <;> rfl
    have hunit : (weightedSumSquares R ![a, b]).Equivalent (weightedSumSquares R ![c, d]) := by
      simpa only [weightedSumSquares_units, hcoe] using h
    simpa [Fin.prod_univ_two] using isSquare_prod_mul_prod_of_equivalent hunit
  · rw [← h.unitValueSet_eq]
    exact mem_unitValueSet_binary_left _ _

/-- A pairing constant on the coefficients of isometric binary forms takes the same values
at their discriminants in its first argument. -/
theorem apply_mul_eq_of_equivalent_binary [Invertible (2 : R)] {M : Type*}
    {F : Rˣ → Rˣ → M}
    (hF : ∀ a b c d : Rˣ, (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(c : R), (d : R)]) → F a b = F c d)
    {a b c d : Rˣ} (h : (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(c : R), (d : R)])) (x : Rˣ) :
    F (a * b) x = F (c * d) x := by
  apply hF
  have hsq : ∀ i : Fin 2, IsSquare (![a * b, x] i / ![c * d, x] i) := by
    intro i
    fin_cases i
    · simpa [pow_two] using
        ((equivalent_binary_iff a b c d).mp h).1.div (IsSquare.sq (c * d))
    · simp
  have hcoe (u v : Rˣ) : (fun i => ((![u, v] i : Rˣ) : R)) = ![(u : R), (v : R)] := by
    ext i
    fin_cases i <;> rfl
  simpa only [weightedSumSquares_units, hcoe] using
    equivalent_weightedSumSquares_of_isSquare_div (R := R) hsq

/-- The binary form `⟨1, -d⟩` represents `a` if and only if `a = x² - d y²` is solvable. -/
theorem represents_binary_one_neg_iff (d a : R) :
    Represents (weightedSumSquares R ![1, -d]) a ↔ ∃ x y : R, a = x ^ 2 - d * y ^ 2 := by
  rw [represents_iff, Set.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v 0, v 1, by simp [weightedSumSquares_apply, Fin.sum_univ_two, pow_two]; ring⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨![x, y], by simp [weightedSumSquares_apply, Fin.sum_univ_two, pow_two]; ring⟩

end CommRing

/-- **Isotropy of a binary diagonal form.** The form `⟨a, b⟩` is anisotropic exactly when `-ab`
is not a square: a zero `(x, y) ≠ 0` of `a x² + b y²` with `y ≠ 0` gives `-ab = (a x / y)²`,
and one with `y = 0` forces `a = 0`. -/
theorem anisotropic_binary_iff {F : Type*} [Field F] (a b : F) :
    (weightedSumSquares F ![a, b]).Anisotropic ↔ ¬IsSquare (-(a * b)) := by
  simp only [QuadraticMap.Anisotropic, weightedSumSquares_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  refine ⟨fun h ⟨r, hr⟩ ↦ ?_, fun h x hx ↦ ?_⟩
  · by_cases ha : a = 0
    · simpa using congrFun (h ![1, 0] (by simp [ha])) 0
    · have := h ![r, a] (by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination -a * hr)
      simpa [ha] using congrFun this 1
  · by_cases h1 : x 1 = 0
    · by_cases ha : a = 0
      · exact absurd ⟨0, by simp [ha]⟩ h
      · have h0 : x 0 = 0 := by simpa [h1, ha] using hx
        funext i
        fin_cases i <;> simp [h0, h1]
    · exact absurd ⟨a * x 0 / x 1, by
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero h1 h1)]
        linear_combination -a * hx⟩ h

/-- The binary form `⟨1, -d⟩` over a field is anisotropic if and only if `d` is not a square. -/
theorem anisotropic_binary_one_neg_iff {F : Type*} [Field F] (d : F) :
    (weightedSumSquares F ![(1 : F), -d]).Anisotropic ↔ ¬ IsSquare d := by
  simpa using anisotropic_binary_iff (1 : F) (-d)

/-- **Worked example.** Over `ℚ` the binary forms `⟨1, 1⟩` and `⟨2, 2⟩` are isometric: their
discriminants `1` and `4` agree modulo squares, and both represent `2`, once as `1² + 1²` and once
as `2 · 1² + 2 · 0²`. Concretely `x² + y²` becomes `2 s² + 2 t²` under `(s, t) ↦ (s - t, s + t)`. -/
example : (weightedSumSquares ℚ ![(1 : ℚ), 1]).Equivalent (weightedSumSquares ℚ ![(2 : ℚ), 2]) := by
  have : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  have hu : ((Units.mk0 (2 : ℚ) two_ne_zero : ℚˣ) : ℚ) = 2 := rfl
  have key := equivalent_binary_iff (R := ℚ) 1 1 (Units.mk0 2 two_ne_zero)
    (Units.mk0 2 two_ne_zero)
  simp only [hu, Units.val_one] at key
  refine key.mpr ⟨⟨Units.mk0 2 two_ne_zero, by rw [one_mul, one_mul]⟩,
    Units.mk0 2 two_ne_zero, ?_, ?_⟩
  · refine mem_unitValueSet.mpr ((represents_iff _ _).mpr
      (Set.mem_range.mpr ⟨![1, 1], ?_⟩))
    norm_num [weightedSumSquares_apply, Fin.sum_univ_two]
  · simpa [hu] using mem_unitValueSet_binary_left (R := ℚ) (Units.mk0 2 two_ne_zero) 2

/-! ### Binary quadratic forms `[a, b]` -/

section BinaryQuadraticForm

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- The binary quadratic form `[a, b]` given by `a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2` on
`Fin 2 → R` (Elman--Karpenko--Merkurjev, §7.B).

In characteristic two its polarization is the standard alternating pairing
`x 0 * y 1 + x 1 * y 0` independently of `a` and `b`; `binaryQuadraticForm R 0 0` is the
`xy`-hyperbolic plane, and over `ZMod 2` the form `binaryQuadraticForm (ZMod 2) 1 1` is the unique
anisotropic nonsingular binary form. -/
def binaryQuadraticForm (R : Type u) [CommSemiring R] (a b : R) :
    QuadraticForm R (Fin 2 → R) :=
  weightedSumSquares R ![a, b] + proj 0 1

/-- Evaluation of `TauCeti.binaryQuadraticForm` in coordinates. -/
@[simp]
theorem binaryQuadraticForm_apply (a b : R) (x : Fin 2 → R) :
    binaryQuadraticForm R a b x = a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2 := by
  simp only [binaryQuadraticForm, add_apply, weightedSumSquares_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, proj_apply, smul_eq_mul, pow_two]
  ring

/-- The first coordinate axis `{x | x 1 = 0}` is totally isotropic for
`binaryQuadraticForm R 0 b`. -/
theorem isTotallyIsotropic_ker_proj_one_binaryQuadraticForm (b : R) :
    (binaryQuadraticForm R 0 b).IsTotallyIsotropic
      (LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) 1)) := by
  rw [isTotallyIsotropic_iff]
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.proj_apply] at hx
  simp [hx]

/-- Over a nontrivial commutative semiring, the hyperbolic plane `binaryQuadraticForm R 0 0` is not
anisotropic, since `![1, 0]` is a nonzero isotropic vector. -/
theorem not_anisotropic_binaryQuadraticForm_zero [Nontrivial R] :
    ¬(binaryQuadraticForm R 0 0).Anisotropic := by
  intro h
  have h10 := h ![1, 0] (by simp)
  exact one_ne_zero (α := R) (by simpa using congrFun h10 0)

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

/-- Polarization of `TauCeti.binaryQuadraticForm` over a commutative ring. -/
theorem polar_binaryQuadraticForm (a b : R) (x y : Fin 2 → R) :
    polar (binaryQuadraticForm R a b) x y =
      2 * (a * (x 0 * y 0) + b * (x 1 * y 1)) + (x 0 * y 1 + x 1 * y 0) := by
  simp only [polar, binaryQuadraticForm_apply, Pi.add_apply]
  ring

/-- Polarization of the hyperbolic plane `binaryQuadraticForm R 0 0` in coordinates. -/
@[simp]
theorem polar_binaryQuadraticForm_zero (x y : Fin 2 → R) :
    polar (binaryQuadraticForm R 0 0) x y = x 0 * y 1 + x 1 * y 0 := by
  rw [polar_binaryQuadraticForm]
  ring

/-- The polar bilinear form of the hyperbolic plane `binaryQuadraticForm R 0 0` is nondegenerate
over every commutative ring. -/
theorem nondegenerate_polarBilin_binaryQuadraticForm_zero :
    (binaryQuadraticForm R 0 0).polarBilin.Nondegenerate := by
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (binaryQuadraticForm R 0 0).isRefl_polarBilin]
  intro x hx
  have h0 : x 0 = 0 := by simpa [polarBilin_apply_apply] using hx ![0, 1]
  have h1 : x 1 = 0 := by simpa [polarBilin_apply_apply] using hx ![1, 0]
  ext i
  fin_cases i <;> simp [h0, h1]

/-- Whenever `2 * a = 0` and `2 * b = 0`, the polar bilinear form of `binaryQuadraticForm R a b`
coincides with that of the hyperbolic plane `binaryQuadraticForm R 0 0`. -/
theorem polarBilin_binaryQuadraticForm_of_two_mul_eq_zero {a b : R}
    (ha : 2 * a = 0) (hb : 2 * b = 0) :
    (binaryQuadraticForm R a b).polarBilin = (binaryQuadraticForm R 0 0).polarBilin :=
  LinearMap.ext₂ fun x y ↦ by
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_binaryQuadraticForm,
      polar_binaryQuadraticForm_zero, mul_add 2, ← mul_assoc 2 a, ← mul_assoc 2 b, ha, hb,
      zero_mul, zero_mul, add_zero, zero_add]

/-- Whenever `2 * a = 0` and `2 * b = 0`, `binaryQuadraticForm R a b` has nondegenerate polar
bilinear form. -/
theorem nondegenerate_polarBilin_binaryQuadraticForm_of_two_mul_eq_zero {a b : R}
    (ha : 2 * a = 0) (hb : 2 * b = 0) :
    (binaryQuadraticForm R a b).polarBilin.Nondegenerate := by
  rw [polarBilin_binaryQuadraticForm_of_two_mul_eq_zero ha hb]
  exact nondegenerate_polarBilin_binaryQuadraticForm_zero

/-- Explicit shear isometry `(x 0, x 1) ↦ (x 0, a * x 0 + x 1)` from `binaryQuadraticForm R a 0`
to the hyperbolic plane `binaryQuadraticForm R 0 0`, valid over every commutative ring. -/
def isometryEquivBinaryQuadraticFormLeft (a : R) :
    (binaryQuadraticForm R a 0).IsometryEquiv (binaryQuadraticForm R 0 0) where
  toFun x := ![x 0, a * x 0 + x 1]
  invFun u := ![u 0, u 1 - a * u 0]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add, add_assoc, add_left_comm]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [mul_add, mul_left_comm]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv u := by
    ext i
    fin_cases i <;> simp
  map_app' x := by
    simp only [binaryQuadraticForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- Coordinates of `TauCeti.isometryEquivBinaryQuadraticFormLeft`. -/
@[simp]
theorem isometryEquivBinaryQuadraticFormLeft_apply (a : R) (x : Fin 2 → R) :
    isometryEquivBinaryQuadraticFormLeft a x = ![x 0, a * x 0 + x 1] :=
  (rfl)

/-- Coordinates of the inverse of `TauCeti.isometryEquivBinaryQuadraticFormLeft`. -/
@[simp]
theorem isometryEquivBinaryQuadraticFormLeft_symm_apply (a : R) (u : Fin 2 → R) :
    (isometryEquivBinaryQuadraticFormLeft a).symm u = ![u 0, u 1 - a * u 0] :=
  (rfl)

/-- Explicit shear isometry `(x 0, x 1) ↦ (x 0 + b * x 1, x 1)` from `binaryQuadraticForm R 0 b`
to the hyperbolic plane `binaryQuadraticForm R 0 0`, valid over every commutative ring. -/
def isometryEquivBinaryQuadraticFormRight (b : R) :
    (binaryQuadraticForm R 0 b).IsometryEquiv (binaryQuadraticForm R 0 0) where
  toFun x := ![x 0 + b * x 1, x 1]
  invFun u := ![u 0 - b * u 1, u 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add, add_assoc, add_left_comm]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [mul_add, mul_left_comm]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv u := by
    ext i
    fin_cases i <;> simp
  map_app' x := by
    simp only [binaryQuadraticForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- Coordinates of `TauCeti.isometryEquivBinaryQuadraticFormRight`. -/
@[simp]
theorem isometryEquivBinaryQuadraticFormRight_apply (b : R) (x : Fin 2 → R) :
    isometryEquivBinaryQuadraticFormRight b x = ![x 0 + b * x 1, x 1] :=
  (rfl)

/-- Coordinates of the inverse of `TauCeti.isometryEquivBinaryQuadraticFormRight`. -/
@[simp]
theorem isometryEquivBinaryQuadraticFormRight_symm_apply (b : R) (u : Fin 2 → R) :
    (isometryEquivBinaryQuadraticFormRight b).symm u = ![u 0 - b * u 1, u 1] :=
  (rfl)

end CommRing

section Field

/-- Over a field, `binaryQuadraticForm K 1 c` is anisotropic if and only if the Artin--Schreier
polynomial `t ^ 2 + t + c` has no root in `K`. -/
theorem anisotropic_binaryQuadraticForm_one_iff {K : Type u} [Field K] (c : K) :
    (binaryQuadraticForm K 1 c).Anisotropic ↔ ∀ t : K, t ^ 2 + t + c ≠ 0 := by
  refine ⟨fun h t ht ↦ ?_, fun h x hx ↦ ?_⟩
  · have h0 := h ![t, 1] (by simpa [binaryQuadraticForm_apply] using ht)
    exact one_ne_zero (α := K) (by simpa using congrFun h0 1)
  · by_cases hx1 : x 1 = 0
    · have hx0 : x 0 = 0 := by simpa [binaryQuadraticForm_apply, hx1] using hx
      ext i
      fin_cases i <;> simp [hx0, hx1]
    · refine False.elim (h (x 0 / x 1) ?_)
      have hdiv : (x 0 / x 1) ^ 2 + x 0 / x 1 + c =
          (x 0 ^ 2 + x 0 * x 1 + c * x 1 ^ 2) / x 1 ^ 2 := by
        field_simp
      rw [hdiv]
      have hx' : x 0 ^ 2 + x 0 * x 1 + c * x 1 ^ 2 = 0 := by
        simpa [binaryQuadraticForm_apply] using hx
      rw [hx', zero_div]

end Field

end BinaryQuadraticForm

end TauCeti
