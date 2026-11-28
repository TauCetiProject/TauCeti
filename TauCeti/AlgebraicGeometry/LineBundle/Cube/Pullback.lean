/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Cube.Basic
import TauCeti.Data.Int.MulPred
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Integer multiplication and the cube identity

When a line-bundle class on a group scheme has trivial cube class, its pullback along the
integer powers of a test point is determined by its pullbacks along the point, its inverse,
and the unit. The unit contributes the factor with exponent `1 - n²`. With a trivial pullback
at the unit, inversion-invariant and inversion-anti-invariant classes give exponents `n²`
and `n`, respectively. The same identity gives the parallelogram law for inversion-invariant
classes.

## References

* J. S. Milne, *Abelian Varieties* (2022), Corollaries 6.4–6.6.
* B. Conrad, *Abelian Varieties*, notes by T. Feng (2015), Theorems 3.1.6 and 4.1.4.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} {G T : Over S}

section Monoid

variable [MonObj G]

private lemma div_pullback_one_mul (c : LineBundleClass G.left) (x y : T ⟶ G) :
    pullback (x * y).left c / pullback (1 : T ⟶ G).left c =
      (pullback x.left c / pullback (1 : T ⟶ G).left c) *
      (pullback y.left c / pullback (1 : T ⟶ G).left c) * pairing c x y := by
  apply Additive.ofMul.injective
  simp only [pairing_def, ofMul_mul, ofMul_div, ofMul_inv]
  abel

end Monoid

variable [GrpObj G] {c : LineBundleClass G.left}

private lemma pairing_self_eq (hc : cubeClass c = 1) (x : T ⟶ G) :
    pairing c x x =
      (pullback x.left c / pullback (1 : T ⟶ G).left c) *
      (pullback (x⁻¹).left c / pullback (1 : T ⟶ G).left c) := by
  have h := div_pullback_one_mul c x x⁻¹
  have hinv : pairing c x x⁻¹ = (pairing c x x)⁻¹ := by
    simpa only [pairingHom_apply] using map_inv (pairingHom hc T x) x
  rw [mul_inv_cancel, div_self', hinv, ← div_eq_mul_inv] at h
  exact (div_eq_one.mp h.symm).symm

private lemma zpow_div_pullback_one (hc : cubeClass c = 1) (x : T ⟶ G) (n : ℤ) :
    pullback (x ^ n).left c / pullback (1 : T ⟶ G).left c =
      (pullback x.left c / pullback (1 : T ⟶ G).left c) ^ n *
        pairing c x x ^ (n * (n - 1) / 2) := by
  let q (k : ℤ) := pullback (x ^ k).left c / pullback (1 : T ⟶ G).left c
  let b := pairing c x x
  let r (k : ℤ) := q 1 ^ k * b ^ (k * (k - 1) / 2)
  have hq (k : ℤ) : q (k + 1) = q k * (q 1 * b ^ k) := by
    have hz : pairing c (x ^ k) x = b ^ k := by
      simpa only [pairingHom_apply, MonoidHom.zpow_apply] using
        congrArg (fun f : (T ⟶ G) →* LineBundleClass T.left ↦ f x)
          (map_zpow (pairingHom hc T) x k)
    simpa only [q, zpow_add_one, zpow_one, hz, _root_.mul_assoc] using
      div_pullback_one_mul c (x ^ k) x
  have hr (k : ℤ) : r (k + 1) = r k * (q 1 * b ^ k) := by
    have hk : (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := by
      simpa using Int.add_mul_add_sub_one_ediv_two k 1
    simp only [r, hk, zpow_add, zpow_one]
    ac_rfl
  -- Both sequences start at one and their common successor relation is reversible.
  suffices h : q n = r n by simpa only [q, r, zpow_one] using h
  induction n using Int.induction_on with
  | zero => simp [q, r]
  | succ k ih => rw [hq, hr, ih]
  | pred k ih =>
    apply mul_right_cancel (b := q 1 * b ^ (-(k : ℤ) - 1))
    rw [← hq, ← hr, sub_add_cancel, ih]

/-- For a class with trivial cube, its pullback at `xⁿ` is determined by its pullbacks at
`x`, `x⁻¹` and the unit. This formula works for every integer and for an arbitrary test scheme
over the base of the group scheme. -/
lemma pullback_zpow_of_cubeClass_eq_one (hc : cubeClass c = 1) (x : T ⟶ G) (n : ℤ) :
    pullback (x ^ n).left c =
      pullback x.left c ^ (n * (n + 1) / 2) *
        pullback (x⁻¹).left c ^ (n * (n - 1) / 2) *
        pullback (1 : T ⟶ G).left c ^ (1 - n ^ 2) := by
  have hnext : n * (n + 1) / 2 = n * (n - 1) / 2 + n := by
    simpa [mul_comm] using Int.add_mul_add_sub_one_ediv_two n 1
  have hsum : (n * (n - 1) / 2 + n) + n * (n - 1) / 2 = n ^ 2 := by
    calc
      _ = n + 2 * (n * (n - 1) / 2) := by ring
      _ = _ := by rw [Int.two_mul_mul_sub_one_ediv_two]; ring
  have h := zpow_div_pullback_one hc x n
  rw [pairing_self_eq hc x] at h
  refine (div_eq_iff_eq_mul.mp h).trans ?_
  simp only [mul_zpow, div_zpow, ← hsum, hnext, zpow_add, zpow_sub, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

private lemma pullback_one_point (hunit : pullback η[G].left c = 1) :
    pullback (1 : T ⟶ G).left c = 1 := by
  rw [Hom.one_def, Over.comp_left, ← pullback_comp, hunit, pullback_one]

/-- The integer pullback formula for a class trivial along the unit section, as for a
zero-rigidified line bundle on an abelian scheme. -/
lemma pullback_zpow_of_cubeClass_eq_one_of_unit_eq_one (hc : cubeClass c = 1)
    (hunit : pullback η[G].left c = 1) (x : T ⟶ G) (n : ℤ) :
    pullback (x ^ n).left c =
      pullback x.left c ^ (n * (n + 1) / 2) * pullback (x⁻¹).left c ^ (n * (n - 1) / 2) := by
  simpa only [pullback_one_point hunit, one_zpow, _root_.mul_one] using
    pullback_zpow_of_cubeClass_eq_one hc x n

/-- For a symmetric class trivial along the unit, the cube identity makes pullback along
`xⁿ` the `n²`-th power of pullback along `x`. -/
lemma pullback_zpow_of_cubeClass_eq_one_of_symmetric (hc : cubeClass c = 1)
    (hunit : pullback η[G].left c = 1) (hsym : pullback ι[G].left c = c)
    (x : T ⟶ G) (n : ℤ) :
    pullback (x ^ n).left c = pullback x.left c ^ (n ^ 2) := by
  have h := Int.add_mul_add_sub_one_ediv_two n (-n)
  have hneg : -n - 1 = -(n + 1) := by omega
  rw [add_neg_cancel, zero_mul, Int.zero_ediv, hneg, neg_mul_neg, mul_neg, ← pow_two] at h
  have hexp : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by omega
  rw [pullback_zpow_of_cubeClass_eq_one_of_unit_eq_one hc hunit, Hom.inv_def, Over.comp_left,
    ← pullback_comp, hsym, ← zpow_add, hexp]

/-- For an antisymmetric class trivial along the unit, the cube identity makes pullback
along `xⁿ` the `n`-th power of pullback along `x`. -/
lemma pullback_zpow_of_cubeClass_eq_one_of_antisymmetric (hc : cubeClass c = 1)
    (hunit : pullback η[G].left c = 1) (hanti : pullback ι[G].left c = c⁻¹)
    (x : T ⟶ G) (n : ℤ) :
    pullback (x ^ n).left c = pullback x.left c ^ n := by
  have hnext : n * (n + 1) / 2 = n * (n - 1) / 2 + n := by
    simpa [mul_comm] using Int.add_mul_add_sub_one_ediv_two n 1
  simp only [pullback_zpow_of_cubeClass_eq_one_of_unit_eq_one hc hunit, Hom.inv_def, Over.comp_left,
    ← pullback_comp, hanti, pullback_inv, inv_zpow, ← zpow_sub, hnext, add_sub_cancel_left]

/-- A symmetric class with trivial cube satisfies the parallelogram law. In particular,
the sum–difference map pulls the exterior product of a normalized symmetric class with
itself back to the exterior product of its squares. -/
lemma parallelogramLaw_of_cubeClass_eq_one (hc : cubeClass c = 1)
    (hsym : pullback ι[G].left c = c) : ParallelogramLaw c := by
  rw [parallelogramLaw_iff]
  intro T x y
  have hinv : pairing c x y⁻¹ = (pairing c x y)⁻¹ := by
    simpa only [pairingHom_apply] using map_inv (pairingHom hc T x) y
  have h := congrArg₂ (· * ·) (div_pullback_one_mul c x y) (div_pullback_one_mul c x y⁻¹)
  have hy : pullback (y⁻¹).left c = pullback y.left c := by
    rw [Hom.inv_def, Over.comp_left, ← pullback_comp, hsym]
  rw [hinv, hy] at h
  have hprod : pullback (x * y).left c / pullback (1 : T ⟶ G).left c *
      (pullback (x / y).left c / pullback (1 : T ⟶ G).left c) =
      ((pullback x.left c / pullback (1 : T ⟶ G).left c) *
        (pullback y.left c / pullback (1 : T ⟶ G).left c)) ^ 2 := by
    rw [div_eq_mul_inv x y, h]
    apply Additive.ofMul.injective
    simp only [pow_two, ofMul_mul, ofMul_inv]
    abel
  rw [div_mul_div_comm, div_mul_div_comm, div_pow, ← pow_two] at hprod
  have hcross := div_eq_div_iff_mul_eq_mul.mp hprod
  rw [pow_two (pullback (1 : T ⟶ G).left c ^ 2), ← _root_.mul_assoc] at hcross
  exact mul_right_cancel hcross

end TauCeti.AlgebraicGeometry.LineBundleClass
