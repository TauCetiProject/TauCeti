/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.Equation
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Line
import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The labelled two-torsion of the scaled Legendre equation

The three roots of `y² = x (x - d) (x - d l)` give distinct affine points
`(0, 0)`, `(d, 0)` and `(d l, 0)` over a commutative ring with nonzero discriminant.
Over a field they are the three nonzero points killed by two in Mathlib's group law on
`WeierstrassCurve.Affine.Point`. Together with the origin they give a doubling kernel of
cardinality four, and their sum is zero.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, §6, Lemma 6.5.

## API reuse

Nonsingularity uses Mathlib's `WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero`.
Doubling uses `WeierstrassCurve.Affine.Point.add_self_of_Y_eq`, and the kernel calculation uses
`WeierstrassCurve.y_eq_zero_of_order_two` with `TauCeti.equation_scaledLegendre_iff`. The zero-sum
relation uses `WeierstrassCurve.Affine.Point.some_add_some_add_some_eq_zero` on the line `y = 0`.
-/

public section

namespace TauCeti

open WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (d l : R)

private theorem scaledLegendre_root_inequalities (hΔ : (scaledLegendre d l).Δ ≠ 0) :
    (2 : R) ≠ 0 ∧ d ≠ 0 ∧ d * l ≠ 0 ∧ d ≠ d * l := by
  have hfactor : (scaledLegendre d l).Δ = 2 ^ 4 * d ^ 2 * (d * l) ^ 2 * (d - d * l) ^ 2 := by
    rw [scaledLegendre_Δ]
    ring
  rw [hfactor] at hΔ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact hΔ (by simp [h])
  · intro h
    exact hΔ (by simp [h])
  · intro h
    exact hΔ (by simp [h])
  · intro h
    exact hΔ (by simp [sub_eq_zero.mpr h])

/-- The labelled roots of a scaled Legendre equation with nonzero discriminant
give nonsingular affine points. -/
theorem nonsingular_scaledLegendre_labelledRoot (hΔ : (scaledLegendre d l).Δ ≠ 0) (i : Fin 3) :
    (scaledLegendre d l).toAffine.Nonsingular (![0, d, d * l] i) 0 := by
  apply (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
  rw [equation_scaledLegendre_iff]
  fin_cases i <;> simp

variable (hΔ : (scaledLegendre d l).Δ ≠ 0)

/-- The three labelled affine points `(0, 0)`, `(d, 0)` and `(d l, 0)` on a scaled Legendre
equation with nonzero discriminant. Over a field these are precisely the nonzero points killed by
two. -/
def scaledLegendreTwoTorsionPoint (i : Fin 3) : (scaledLegendre d l).toAffine.Point :=
  .some (![0, d, d * l] i) 0 (nonsingular_scaledLegendre_labelledRoot d l hΔ i)

/-- The characteristic constructor equation, with any proof of nonsingularity of the labelled
coordinates. Proof irrelevance keeps this usable with the caller's own proof. -/
theorem scaledLegendreTwoTorsionPoint_eq_some (i : Fin 3)
    (h : (scaledLegendre d l).toAffine.Nonsingular (![0, d, d * l] i) 0) :
    scaledLegendreTwoTorsionPoint d l hΔ i = .some (![0, d, d * l] i) 0 h :=
  (rfl)

/-- The homogeneous `x`-coordinates of the three labelled points. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_xRep (i : Fin 3) :
    (scaledLegendreTwoTorsionPoint d l hΔ i).xRep = ![![0, d, d * l] i, 1] :=
  Affine.Point.xRep_some (nonsingular_scaledLegendre_labelledRoot d l hΔ i)

/-- None of the three labelled points is the origin. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_ne_zero (i : Fin 3) :
    scaledLegendreTwoTorsionPoint d l hΔ i ≠ 0 :=
  Affine.Point.some_ne_zero _

/-- Distinct labels give distinct affine points. -/
theorem scaledLegendreTwoTorsionPoint_injective :
    Function.Injective (scaledLegendreTwoTorsionPoint d l hΔ) := by
  obtain ⟨_, hd, hdl, hdd⟩ := scaledLegendre_root_inequalities d l hΔ
  intro i j hij
  have hx := congrFun (congrArg Affine.Point.xRep hij) 0
  simp only [scaledLegendreTwoTorsionPoint_xRep, Matrix.cons_val_zero] at hx
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- Two labelled points are equal exactly when their labels are equal. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_inj {i j : Fin 3} :
    scaledLegendreTwoTorsionPoint d l hΔ i = scaledLegendreTwoTorsionPoint d l hΔ j ↔ i = j :=
  (scaledLegendreTwoTorsionPoint_injective d l hΔ).eq_iff

end CommRing

section Field

variable {K : Type*} [Field K] (d l : K) [(scaledLegendre d l).IsElliptic]

variable [DecidableEq K]

/-- Each labelled point is killed by two in the native point group. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_two_nsmul (i : Fin 3) :
    (2 : ℕ) • scaledLegendreTwoTorsionPoint d l (scaledLegendre d l).isUnit_Δ.ne_zero i =
      0 := by
  rw [two_nsmul, scaledLegendreTwoTorsionPoint]
  exact Affine.Point.add_self_of_Y_eq (by simp [Affine.negY])

/-- The origin and the three labelled points exhaust the points killed by two. -/
theorem two_nsmul_eq_zero_iff_scaledLegendre
    (P : (scaledLegendre d l).toAffine.Point) :
    (2 : ℕ) • P = 0 ↔ P = 0 ∨
      ∃ i, P = scaledLegendreTwoTorsionPoint d l (scaledLegendre d l).isUnit_Δ.ne_zero i := by
  constructor
  · intro hP
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      obtain ⟨h2, _, _, _⟩ :=
        scaledLegendre_root_inequalities d l (scaledLegendre d l).isUnit_Δ.ne_zero
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
theorem ker_nsmul_two_scaledLegendre :
    ((nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker :
        Set (scaledLegendre d l).toAffine.Point) =
      insert 0 (Set.range (scaledLegendreTwoTorsionPoint d l
        (scaledLegendre d l).isUnit_Δ.ne_zero)) := by
  ext P
  simp [two_nsmul_eq_zero_iff_scaledLegendre, Set.mem_range, eq_comm]

/-- The scaled Legendre equation has four rational points killed by two. -/
@[simp]
theorem card_ker_nsmul_two_scaledLegendre :
    Nat.card {P : (scaledLegendre d l).toAffine.Point // (2 : ℕ) • P = 0} = 4 := by
  have hΔ := (scaledLegendre d l).isUnit_Δ.ne_zero
  calc
    Nat.card (nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker =
        ((nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker :
          Set (scaledLegendre d l).toAffine.Point).ncard := Nat.card_coe_set_eq _
    _ = 4 := by
      rw [ker_nsmul_two_scaledLegendre,
        Set.ncard_insert_of_notMem (by
          rintro ⟨i, hi⟩
          exact scaledLegendreTwoTorsionPoint_ne_zero d l hΔ i hi),
        Set.ncard_range_of_injective (scaledLegendreTwoTorsionPoint_injective d l hΔ)]
      simp

/-- The sum of the three labelled nonzero points killed by two is zero. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_sum :
    ∑ i : Fin 3, scaledLegendreTwoTorsionPoint d l (scaledLegendre d l).isUnit_Δ.ne_zero i =
      0 := by
  have hΔ := (scaledLegendre d l).isUnit_Δ.ne_zero
  obtain ⟨_, hd, hdl, hdd⟩ := scaledLegendre_root_inequalities d l hΔ
  rw [Fin.sum_univ_three]
  exact Affine.Point.some_add_some_add_some_eq_zero (μ := 0) (ν := 0)
    (nonsingular_scaledLegendre_labelledRoot d l hΔ 0)
    (nonsingular_scaledLegendre_labelledRoot d l hΔ 1)
    (nonsingular_scaledLegendre_labelledRoot d l hΔ 2)
    hd.symm hdl.symm hdd (by simp) (by simp) (by simp)

end Field

end TauCeti
