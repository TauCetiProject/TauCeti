/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector

/-!
# Reversal on Clifford subalgebras

This file restricts Clifford reversal to the even subalgebra, records its action on bivectors,
and develops general reverse-norm identities and comparisons with Clifford conjugation.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- Reversal restricted to the even Clifford subalgebra. -/
def reverseEven (Q : QuadraticForm R M) : ↥(even Q) →ₗ[R] ↥(even Q) :=
  (reverse (Q := Q)).restrict (p := (even Q).toSubmodule) (q := (even Q).toSubmodule)
    (fun _x hx => (reverse_mem_evenOdd_iff Q).2 hx)

/-- Coercing the restricted reversal agrees with Clifford reversal. -/
@[simp] theorem coe_reverseEven_apply (x : ↥(even Q)) :
    (reverseEven Q x : CliffordAlgebra Q) = reverse x := by
  exact LinearMap.coe_restrict_apply (f := reverse (Q := Q))
    (fun _x hx => (reverse_mem_evenOdd_iff Q).2 hx) x

/-- On the even Clifford subalgebra, Clifford reversal agrees with Clifford `star`. -/
@[simp] theorem reverse_eq_star_of_mem_even (x : ↥(even Q)) :
    reverse (x : CliffordAlgebra Q) = star (x : CliffordAlgebra Q) := by
  rw [star_def,
    involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact x.2)]

/-- Reversal restricted to the even subalgebra fixes its unit. -/
@[simp] theorem reverseEven_map_one : reverseEven Q 1 = 1 := by
  apply Subtype.ext
  simp

/-- Reversal restricted to the even subalgebra fixes scalars. -/
@[simp] theorem reverseEven_algebraMap (r : R) :
    reverseEven Q (algebraMap R (even Q) r) = algebraMap R (even Q) r := by
  apply Subtype.ext
  simp

/-- Reversal restricted to the even subalgebra reverses products. -/
@[simp] theorem reverseEven_mul (x y : ↥(even Q)) :
    reverseEven Q (x * y) = reverseEven Q y * reverseEven Q x := by
  apply Subtype.ext
  simp only [coe_reverseEven_apply, Subalgebra.coe_mul, reverse.map_mul]

/-- Reversal restricted to the even subalgebra is an involution. -/
@[simp] theorem reverseEven_reverseEven (x : ↥(even Q)) :
    reverseEven Q (reverseEven Q x) = x := by
  apply Subtype.ext
  simpa only [coe_reverseEven_apply] using (reverse_reverse (Q := Q) (x : CliffordAlgebra Q))

/-! ### Reverse norms and comparison with Clifford conjugation -/

/-- The reverse norm of a product of vectors is the product of their quadratic norms. -/
theorem reverse_prod_map_ι_mul_prod_map_ι (l : List M) :
    reverse (l.map (ι Q)).prod * (l.map (ι Q)).prod =
      algebraMap R (CliffordAlgebra Q) (l.map Q).prod := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [List.map_cons, List.prod_cons, reverse.map_mul, reverse_ι, mul_assoc,
      ← mul_assoc (ι Q m), ι_sq_scalar, ← mul_assoc, ← Algebra.commutes, mul_assoc, ih,
      ← map_mul, List.map_cons, List.prod_cons]

/-- On an even element, the `star` norm and the `reverse` norm agree. -/
theorem star_mul_self_eq_reverse_mul_self_of_mem_even {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) : star x * x = reverse x * x := by
  rw [star_def, involute_eq_of_mem_even hx]

/-- On an odd element, the `star` norm is the negative of the `reverse` norm. -/
theorem star_mul_self_eq_neg_reverse_mul_self_of_mem_odd {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 1) : star x * x = -(reverse x * x) := by
  rw [star_def, involute_eq_of_mem_odd hx, map_neg, neg_mul]

/-- On a product of `r` vectors, the `star` norm is `(-1) ^ r` times the `reverse` norm. -/
theorem star_mul_self_eq_neg_one_pow_smul_reverse_mul_self (l : List M) :
    star (l.map (ι Q)).prod * (l.map (ι Q)).prod =
      (-1 : R) ^ l.length • (reverse (l.map (ι Q)).prod * (l.map (ι Q)).prod) := by
  rw [star_def, involute_prod_map_ι, map_smul, smul_mul_assoc]

/-- When the reverse norm of `x` is the scalar `r`, the reverse norm of `x * y` is `r` times
the reverse norm of `y`. -/
theorem reverse_mul_mul_self_mul {x y : CliffordAlgebra Q} {r : R}
    (hx : reverse x * x = algebraMap R (CliffordAlgebra Q) r) :
    reverse (x * y) * (x * y) = algebraMap R (CliffordAlgebra Q) r * (reverse y * y) := by
  rw [reverse.map_mul, mul_assoc, ← mul_assoc (reverse x), hx, ← mul_assoc, ← Algebra.commutes,
    mul_assoc]

/-- If the reverse norm of a unit is a scalar, then so is the reverse norm on the other side. -/
theorem self_mul_reverse_of_reverse_mul_self {x : (CliffordAlgebra Q)ˣ} {r : R}
    (hx : reverse (x : CliffordAlgebra Q) * x = algebraMap R (CliffordAlgebra Q) r) :
    (x : CliffordAlgebra Q) * reverse (x : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) r := by
  have hrev : reverse (x : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r * ↑x⁻¹ := by
    rw [← hx, mul_assoc, Units.mul_inv, mul_one]
  rw [hrev, ← mul_assoc, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

/-- If the reverse norm of a unit is the scalar unit `r`, that of its inverse is `r⁻¹`. -/
theorem reverse_inv_mul_inv {x : (CliffordAlgebra Q)ˣ} {r : Rˣ}
    (hx : reverse (x : CliffordAlgebra Q) * x = algebraMap R (CliffordAlgebra Q) r) :
    reverse ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ↑x⁻¹ =
      algebraMap R (CliffordAlgebra Q) ↑r⁻¹ := by
  have hinv : ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) ↑r⁻¹ * reverse (x : CliffordAlgebra Q) := by
    calc ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
        = algebraMap R (CliffordAlgebra Q) (↑r⁻¹ * ↑r) * ↑x⁻¹ := by simp
      _ = algebraMap R (CliffordAlgebra Q) ↑r⁻¹ * (reverse (x : CliffordAlgebra Q) * x) *
          ↑x⁻¹ := by rw [hx, map_mul]
      _ = algebraMap R (CliffordAlgebra Q) ↑r⁻¹ * reverse (x : CliffordAlgebra Q) := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  conv_lhs => rhs; rw [hinv]
  rw [← mul_assoc, ← Algebra.commutes, mul_assoc, ← reverse.map_mul, Units.mul_inv,
    reverse.map_one, mul_one]

section Bivector

variable [Invertible (2 : R)]

/-- Clifford reversal negates every bivector. -/
@[simp] theorem reverse_bivector (q : QuadraticForm R M) (a b : M) :
    reverse (bivector q a b) = -bivector q a b := by
  rw [bivector_def, map_smul, map_sub, reverse.map_mul, reverse.map_mul, reverse_ι, reverse_ι]
  module

/-- Clifford reversal negates the image of the exterior-square bivector map. -/
@[simp] theorem reverse_bivectorExterior (q : QuadraticForm R M) (x : ⋀[R]^2 M) :
    reverse (bivectorExterior q x) = -bivectorExterior q x := by
  let P := LinearMap.eqLocus (reverse (Q := q)) (-LinearMap.id)
  have hle : LinearMap.range (bivectorExterior q) ≤ P :=
    bivectorExterior_range_le_of_bivector_mem q P fun a b =>
      LinearMap.mem_eqLocus.2 (reverse_bivector q a b)
  exact LinearMap.mem_eqLocus.mp (hle ⟨x, rfl⟩)

end Bivector

end CliffordAlgebra
