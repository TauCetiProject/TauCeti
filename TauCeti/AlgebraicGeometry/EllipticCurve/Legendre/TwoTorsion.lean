/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.Fin.VecNotation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.Equation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The labelled two-torsion of the scaled Legendre equation

The three roots of `y² = x (x - d) (x - d l)` give the three nonzero points killed by two,
labelled `(0, 0)`, `(d, 0)` and `(d l, 0)`. They are native affine points, so their group law is
Mathlib's group law on `WeierstrassCurve.Affine.Point`. Together with the origin they exhaust
the kernel of multiplication by two, which consequently has cardinality four. Their sum is zero.

The constructor is available over any nontrivial commutative ring where the curve is elliptic.
The group and kernel statements are over a field. The ellipticity assumption already forces
`2 ≠ 0` and the three roots to be distinct.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, §6, Lemma 6.5.

## API reuse

Nonsingularity uses Mathlib's `WeierstrassCurve.Affine.equation_iff_nonsingular`. Doubling uses
`WeierstrassCurve.Affine.Point.add_self_of_Y_eq`, and the kernel calculation uses
`WeierstrassCurve.y_eq_zero_of_order_two` with `TauCeti.equation_scaledLegendre_iff`.
-/

public section

namespace TauCeti

open WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] [Nontrivial R] (d l : R)
  [(scaledLegendre d l).IsElliptic]

/-- The labelled roots give nonsingular affine points of an elliptic scaled Legendre equation. -/
theorem scaledLegendreTwoTorsionPoint_nonsingular (i : Fin 3) :
    (scaledLegendre d l).toAffine.Nonsingular (![0, d, d * l] i) 0 := by
  apply Affine.equation_iff_nonsingular.mp
  rw [equation_scaledLegendre_iff]
  fin_cases i <;> simp

/-- The three labelled affine points `(0, 0)`, `(d, 0)` and `(d l, 0)` on an elliptic scaled
Legendre equation. Over a field these are precisely the nonzero points killed by two. -/
def scaledLegendreTwoTorsionPoint (i : Fin 3) : (scaledLegendre d l).toAffine.Point :=
  .some (![0, d, d * l] i) 0 (scaledLegendreTwoTorsionPoint_nonsingular d l i)

/-- The characteristic constructor equation, with any proof of nonsingularity of the labelled
coordinates. Proof irrelevance keeps this usable with the caller's own proof. -/
theorem scaledLegendreTwoTorsionPoint_eq_some (i : Fin 3)
    (h : (scaledLegendre d l).toAffine.Nonsingular (![0, d, d * l] i) 0) :
    scaledLegendreTwoTorsionPoint d l i = .some (![0, d, d * l] i) 0 h :=
  (rfl)

/-- The homogeneous `x`-coordinates of the three labelled points. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_xRep (i : Fin 3) :
    (scaledLegendreTwoTorsionPoint d l i).xRep = ![![0, d, d * l] i, 1] :=
  Affine.Point.xRep_some (scaledLegendreTwoTorsionPoint_nonsingular d l i)

/-- None of the three labelled points is the origin. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_ne_zero (i : Fin 3) :
    scaledLegendreTwoTorsionPoint d l i ≠ 0 :=
  Affine.Point.some_ne_zero _

/-- The labels of the three nonzero points killed by two are distinct. -/
theorem scaledLegendreTwoTorsionPoint_injective :
    Function.Injective (scaledLegendreTwoTorsionPoint d l) := by
  have hunit := (isElliptic_scaledLegendre_iff d l).mp ‹_›
  simp only [IsUnit.mul_iff] at hunit
  obtain ⟨⟨⟨_, hdu⟩, hlu⟩, hl₁u⟩ := hunit
  have hd : d ≠ 0 := hdu.ne_zero
  have hdl : d * l ≠ 0 := (hdu.mul hlu).ne_zero
  have hdld : d * l ≠ d := by
    intro h
    exact hl₁u.ne_zero (sub_eq_zero.mpr (hdu.mul_left_cancel (by simpa using h)))
  intro i j hij
  have hx := congrFun (congrArg Affine.Point.xRep hij) 0
  simp only [scaledLegendreTwoTorsionPoint_xRep, Matrix.cons_val_zero] at hx
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

end CommRing

section Field

variable {K : Type*} [Field K] (d l : K) [(scaledLegendre d l).IsElliptic]

variable [DecidableEq K]

/-- Each labelled point is killed by two in the native point group. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_two_nsmul (i : Fin 3) :
    (2 : ℕ) • scaledLegendreTwoTorsionPoint d l i = 0 := by
  rw [two_nsmul, scaledLegendreTwoTorsionPoint]
  exact Affine.Point.add_self_of_Y_eq (by simp [Affine.negY])

/-- The origin and the three labelled points exhaust the points killed by two. -/
theorem scaledLegendreTwoTorsionPoint_two_nsmul_eq_zero_iff
    (P : (scaledLegendre d l).toAffine.Point) :
    (2 : ℕ) • P = 0 ↔ P = 0 ∨ ∃ i, P = scaledLegendreTwoTorsionPoint d l i := by
  constructor
  · intro hP
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      have hunit := (isElliptic_scaledLegendre_iff d l).mp ‹_›
      simp only [IsUnit.mul_iff] at hunit
      have h2 : (2 : K) ≠ 0 := hunit.1.1.1.ne_zero
      obtain rfl := y_eq_zero_of_order_two h2 h hP
      have hx := (equation_scaledLegendre_iff d l x 0).mp h.1
      simp only [zero_pow (by decide : 2 ≠ 0), eq_comm (a := (0 : K)), mul_eq_zero,
        sub_eq_zero] at hx
      rcases hx with (hx | hx) | hx
      · exact Or.inr ⟨0, by subst x; rfl⟩
      · exact Or.inr ⟨1, by subst x; rfl⟩
      · exact Or.inr ⟨2, by subst x; rfl⟩
  · rintro (rfl | ⟨i, rfl⟩) <;> simp

/-- The kernel of multiplication by two as a subset of the native point group. -/
theorem scaledLegendreTwoTorsionPoint_ker_nsmul_two :
    ((nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker :
        Set (scaledLegendre d l).toAffine.Point) =
      insert 0 (Set.range (scaledLegendreTwoTorsionPoint d l)) := by
  ext P
  simp [scaledLegendreTwoTorsionPoint_two_nsmul_eq_zero_iff, Set.mem_range, eq_comm]

/-- The scaled Legendre equation has four rational points killed by two. -/
theorem scaledLegendreTwoTorsionPoint_card_ker_nsmul_two :
    Nat.card (nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker = 4 := by
  calc
    Nat.card (nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker =
        ((nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker :
          Set (scaledLegendre d l).toAffine.Point).ncard := Nat.card_coe_set_eq _
    _ = 4 := by
      rw [scaledLegendreTwoTorsionPoint_ker_nsmul_two,
        Set.ncard_insert_of_notMem (by
          rintro ⟨i, hi⟩
          exact scaledLegendreTwoTorsionPoint_ne_zero d l i hi),
        Set.ncard_range_of_injective (scaledLegendreTwoTorsionPoint_injective d l)]
      simp

/-- The sum of the three labelled nonzero points killed by two is zero. -/
theorem scaledLegendreTwoTorsionPoint_sum :
    ∑ i : Fin 3, scaledLegendreTwoTorsionPoint d l i = 0 := by
  let T := scaledLegendreTwoTorsionPoint d l
  have hinj := scaledLegendreTwoTorsionPoint_injective d l
  have hn (i : Fin 3) : T i ≠ 0 := scaledLegendreTwoTorsionPoint_ne_zero d l i
  have htwo (i : Fin 3) : T i + T i = 0 := by
    simpa only [two_nsmul] using scaledLegendreTwoTorsionPoint_two_nsmul d l i
  have h01 : T 0 + T 1 = T 2 := by
    have h : (2 : ℕ) • (T 0 + T 1) = 0 := by simp [T]
    rcases (scaledLegendreTwoTorsionPoint_two_nsmul_eq_zero_iff d l _).mp h with h | ⟨i, hi⟩
    · have he : T 0 = T 1 := by
        apply add_right_cancel (b := T 1)
        rw [h, htwo]
      exact ((by decide : (0 : Fin 3) ≠ 1) (hinj he)).elim
    · fin_cases i
      · exact False.elim (hn 1 (add_left_cancel (hi.trans (add_zero (T 0)).symm)))
      · exact False.elim (hn 0 (add_right_cancel (hi.trans (zero_add (T 1)).symm)))
      · exact hi
  rw [Fin.sum_univ_three]
  exact (congrArg (· + T 2) h01).trans (htwo 2)

end Field

end TauCeti
