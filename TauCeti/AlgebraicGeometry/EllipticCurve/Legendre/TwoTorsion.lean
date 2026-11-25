/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.Equation
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Line
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.TwoTorsion

/-!
# The labelled two-torsion of the scaled Legendre equation

The ordered roots of the cubic `x (x - d) (x - d l)` at `y = 0` give distinct affine points
`(0, 0)`, `(d, 0)` and `(d l, 0)` over a commutative ring with nonzero discriminant.
Over a field they are the three nonzero points killed by two in Mathlib's group law on
`WeierstrassCurve.Affine.Point`. Together with the origin they give a doubling kernel of
cardinality four, and their sum is zero. The fixed order lets halving criteria refer to the
three differences of a point's `x`-coordinate from these roots by label.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, §6, Lemma 6.5.
* The kernel enumeration specializes `WeierstrassCurve.Affine.ker_nsmul_two_eq_insert_range`.
  The zero-sum relation is the horizontal-line case of
  `WeierstrassCurve.Affine.Point.some_add_some_add_some_eq_zero`.
-/

public section

namespace TauCeti

open WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (d l : R)

private theorem eval_f_scaledLegendre (x : R) :
    (scaledLegendre d l).toAffine.f.eval x = x * (x - d) * (x - d * l) := by
  rw [Affine.eval_f, scaledLegendre_a₂, scaledLegendre_a₄, scaledLegendre_a₆]
  ring

/-- Every labelled coordinate is a root of the native Weierstrass cubic. The simp rule fires
before simplification expands the cubic or evaluates a literal label. -/
@[simp↓]
theorem eval_f_scaledLegendreRoots (i : Fin 3) :
    (scaledLegendre d l).toAffine.f.eval (scaledLegendreRoots d l i) = 0 := by
  rw [eval_f_scaledLegendre]
  fin_cases i <;> simp

/-- The labelled roots of a scaled Legendre equation with nonzero discriminant
give nonsingular affine points. -/
theorem nonsingular_scaledLegendreRoots (hΔ : (scaledLegendre d l).Δ ≠ 0) (i : Fin 3) :
    (scaledLegendre d l).toAffine.Nonsingular (scaledLegendreRoots d l i) 0 := by
  apply (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
  rw [Affine.equation_iff_eval_f_eq_sq, eval_f_scaledLegendreRoots, zero_pow two_ne_zero]

variable (hΔ : (scaledLegendre d l).Δ ≠ 0)

/-- The three labelled affine points `(0, 0)`, `(d, 0)` and `(d l, 0)` on a scaled Legendre
equation with nonzero discriminant. Over a field these are precisely the nonzero points killed by
two. -/
def scaledLegendreTwoTorsionPoint (i : Fin 3) : (scaledLegendre d l).toAffine.Point :=
  .some (scaledLegendreRoots d l i) 0 (nonsingular_scaledLegendreRoots d l hΔ i)

/-- The point with label `i` has x-coordinate `scaledLegendreRoots d l i` and y-coordinate zero,
for any nonsingularity witness. -/
theorem scaledLegendreTwoTorsionPoint_eq_some (i : Fin 3)
    (h : (scaledLegendre d l).toAffine.Nonsingular (scaledLegendreRoots d l i) 0) :
    scaledLegendreTwoTorsionPoint d l hΔ i = .some (scaledLegendreRoots d l i) 0 h :=
  (rfl)

/-- The homogeneous `x`-coordinates of the three labelled points. -/
@[simp]
theorem xRep_scaledLegendreTwoTorsionPoint (i : Fin 3) :
    (scaledLegendreTwoTorsionPoint d l hΔ i).xRep = ![scaledLegendreRoots d l i, 1] := by
  rw [scaledLegendreTwoTorsionPoint_eq_some d l hΔ i
    (nonsingular_scaledLegendreRoots d l hΔ i), Affine.Point.xRep_some]

/-- None of the three labelled points is the origin. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_ne_zero (i : Fin 3) :
    scaledLegendreTwoTorsionPoint d l hΔ i ≠ 0 := by
  rw [scaledLegendreTwoTorsionPoint_eq_some d l hΔ i
    (nonsingular_scaledLegendreRoots d l hΔ i)]
  exact Affine.Point.some_ne_zero _

/-- Each labelled point is its own negative. -/
@[simp]
theorem neg_scaledLegendreTwoTorsionPoint (i : Fin 3) :
    -scaledLegendreTwoTorsionPoint d l hΔ i = scaledLegendreTwoTorsionPoint d l hΔ i := by
  rw [scaledLegendreTwoTorsionPoint_eq_some d l hΔ i
    (nonsingular_scaledLegendreRoots d l hΔ i)]
  simp [Affine.negY]

/-- Distinct labels give distinct affine points. -/
theorem scaledLegendreTwoTorsionPoint_injective :
    Function.Injective (scaledLegendreTwoTorsionPoint d l hΔ) := by
  intro i j hij
  rw [scaledLegendreTwoTorsionPoint_eq_some d l hΔ i (nonsingular_scaledLegendreRoots d l hΔ i),
    scaledLegendreTwoTorsionPoint_eq_some d l hΔ j (nonsingular_scaledLegendreRoots d l hΔ j),
    Affine.Point.some.injEq] at hij
  exact scaledLegendreRoots_injective d l hΔ hij.1

/-- Two labelled points are equal exactly when their labels are equal. -/
@[simp]
theorem scaledLegendreTwoTorsionPoint_inj {i j : Fin 3} :
    scaledLegendreTwoTorsionPoint d l hΔ i = scaledLegendreTwoTorsionPoint d l hΔ j ↔ i = j :=
  (scaledLegendreTwoTorsionPoint_injective d l hΔ).eq_iff

end CommRing

section NoZeroDivisors

variable {R : Type*} [CommRing R] [NoZeroDivisors R] (d l : R)

/-- Over a ring without zero divisors, the native Weierstrass cubic vanishes exactly at the
labelled roots. -/
theorem eval_f_scaledLegendre_eq_zero_iff (x : R) :
    (scaledLegendre d l).toAffine.f.eval x = 0 ↔ x ∈ Set.range (scaledLegendreRoots d l) := by
  rw [eval_f_scaledLegendre, scaledLegendreRoots_def, Matrix.range_cons,
    Matrix.range_cons_cons_empty]
  simp only [mul_eq_zero, sub_eq_zero, or_assoc, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_insert_iff]

end NoZeroDivisors

section Field

variable {K : Type*} [Field K] (d l : K)

private noncomputable def scaledLegendreRootEquiv (hΔ : (scaledLegendre d l).Δ ≠ 0) :
    Fin 3 ≃ {x : K // (scaledLegendre d l).toAffine.f.eval x = 0} :=
  (Equiv.ofInjective _ (scaledLegendreRoots_injective d l hΔ)).trans
    (Equiv.subtypeEquivRight fun x ↦ (eval_f_scaledLegendre_eq_zero_iff d l x).symm)

@[simp]
private theorem scaledLegendreRootEquiv_apply_coe (hΔ : (scaledLegendre d l).Δ ≠ 0) (i : Fin 3) :
    (scaledLegendreRootEquiv d l hΔ i : K) = scaledLegendreRoots d l i := by
  simp [scaledLegendreRootEquiv, Equiv.subtypeEquivRight_apply]

variable [DecidableEq K] (hΔ : (scaledLegendre d l).Δ ≠ 0)

/-- Each labelled point is killed by two in the native point group. -/
@[simp]
theorem two_nsmul_scaledLegendreTwoTorsionPoint_eq_zero (i : Fin 3) :
    (2 : ℕ) • scaledLegendreTwoTorsionPoint d l hΔ i = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, neg_scaledLegendreTwoTorsionPoint]

/-- The doubling kernel, as a set, consists of the origin and the range of the labelled tuple. -/
theorem ker_nsmul_two_scaledLegendre :
    ((nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker :
        Set (scaledLegendre d l).toAffine.Point) =
      insert 0 (Set.range (scaledLegendreTwoTorsionPoint d l hΔ)) := by
  have : (scaledLegendre d l).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  rw [Affine.ker_nsmul_two_eq_insert_range]
  have hcomp : (scaledLegendre d l).toAffine.pointOfRoot ∘ scaledLegendreRootEquiv d l hΔ =
      scaledLegendreTwoTorsionPoint d l hΔ := by
    funext i
    rw [Function.comp_apply, Affine.pointOfRoot_eq_some,
      scaledLegendreTwoTorsionPoint_eq_some d l hΔ i (nonsingular_scaledLegendreRoots d l hΔ i),
      Affine.Point.some.injEq]
    exact ⟨scaledLegendreRootEquiv_apply_coe d l hΔ i, rfl⟩
  rw [← hcomp, EquivLike.range_comp]

/-- The origin and the three labelled points exhaust the points killed by two. -/
theorem two_nsmul_eq_zero_iff_scaledLegendre
    (P : (scaledLegendre d l).toAffine.Point) :
    (2 : ℕ) • P = 0 ↔ P = 0 ∨ ∃ i, P = scaledLegendreTwoTorsionPoint d l hΔ i := by
  simpa [Set.mem_range, eq_comm] using Set.ext_iff.mp (ker_nsmul_two_scaledLegendre d l hΔ) P

/-- The scaled Legendre equation has four rational points killed by two. -/
theorem card_ker_nsmul_two_scaledLegendre (hΔ : (scaledLegendre d l).Δ ≠ 0) :
    Nat.card {P : (scaledLegendre d l).toAffine.Point // (2 : ℕ) • P = 0} = 4 := by
  have : (scaledLegendre d l).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  let e : {P : (scaledLegendre d l).toAffine.Point // (2 : ℕ) • P = 0} ≃
      (nsmulAddMonoidHom (α := (scaledLegendre d l).toAffine.Point) 2).ker :=
    Equiv.subtypeEquivRight fun _ ↦ by simp
  rw [Nat.card_congr e, Affine.card_ker_nsmul_two,
    Nat.card_congr (scaledLegendreRootEquiv d l hΔ).symm]
  simp

/-- The sum of the three labelled nonzero points killed by two is zero. -/
@[simp]
theorem sum_scaledLegendreTwoTorsionPoint_eq_zero :
    ∑ i : Fin 3, scaledLegendreTwoTorsionPoint d l hΔ i = 0 := by
  have hinj := scaledLegendreRoots_injective d l hΔ
  rw [Fin.sum_univ_three,
    scaledLegendreTwoTorsionPoint_eq_some d l hΔ 0
      (nonsingular_scaledLegendreRoots d l hΔ 0),
    scaledLegendreTwoTorsionPoint_eq_some d l hΔ 1
      (nonsingular_scaledLegendreRoots d l hΔ 1),
    scaledLegendreTwoTorsionPoint_eq_some d l hΔ 2
      (nonsingular_scaledLegendreRoots d l hΔ 2)]
  exact Affine.Point.some_add_some_add_some_eq_zero (μ := 0) (ν := 0)
    (nonsingular_scaledLegendreRoots d l hΔ 0)
    (nonsingular_scaledLegendreRoots d l hΔ 1)
    (nonsingular_scaledLegendreRoots d l hΔ 2)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    (by simp) (by simp) (by simp)

end Field

end TauCeti
