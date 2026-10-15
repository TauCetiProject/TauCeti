/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Even-Clifford transport along a negative vector

Multiplying a Clifford generator on the right by a fixed generator produces a linear map into the
even Clifford algebra. When the fixed vector has quadratic value `-1`, conjugation by its negated
generator preserves the even subalgebra. These constructions provide the algebraic transport used
by low-rank Spin action comparisons without depending on Spin groups.

## Main definitions

* `CliffordAlgebra.rightIotaEven Q e` is the linear map `m ↦ ι(m)ι(e)` into the even
  Clifford algebra.
* `CliffordAlgebra.conjugateNegativeIotaEven Q e he` restricts conjugation by `-ι(e)` to the
  even algebra when `Q(e) = -1`.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- The linear map into the even Clifford algebra obtained by multiplying a generating vector on
the right by another generating vector. -/
def rightIotaEven (e : M) : M →ₗ[R] even Q :=
  (even.ι Q).bilin.flip e

omit [Invertible (2 : R)] in
/-- Evaluating `rightIotaEven` gives the canonical bilinear generator of the even algebra. -/
@[simp]
theorem rightIotaEven_apply (e m : M) :
    rightIotaEven Q e m = (even.ι Q).bilin m e :=
  by simp only [rightIotaEven, LinearMap.flip_apply]

omit [Invertible (2 : R)] in
/-- The ambient Clifford value of `rightIotaEven`. -/
theorem coe_rightIotaEven (e m : M) :
    (rightIotaEven Q e m : CliffordAlgebra Q) = ι Q m * ι Q e :=
  by rfl

omit [Invertible (2 : R)] in
/-- Coercing a canonical bilinear generator of the even algebra gives the product of its two
Clifford generators. -/
@[simp]
theorem coe_even_ι_bilin (m e : M) :
    (((even.ι Q).bilin m e : even Q) : CliffordAlgebra Q) = ι Q m * ι Q e := by
  rw [← rightIotaEven_apply Q e m]
  exact coe_rightIotaEven Q e m

omit [Invertible (2 : R)] in
private theorem iota_sq_neg_one (e : M) (he : Q e = -1) :
    ι Q e * ι Q e = -1 := by
  rw [ι_sq_scalar, he, map_neg, map_one]

private def negativeIotaUnit (e : M) (he : Q e = -1) : (CliffordAlgebra Q)ˣ where
  val := -ι Q e
  inv := ι Q e
  val_inv := by rw [neg_mul, iota_sq_neg_one Q e he, neg_neg]
  inv_val := by rw [mul_neg, iota_sq_neg_one Q e he, neg_neg]

private noncomputable def conjugateNegativeIota
    (e : M) (he : Q e = -1) : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q :=
  MulSemiringAction.toAlgEquiv R _ (ConjAct.toConjAct (negativeIotaUnit Q e he))

omit [Invertible (2 : R)] in
private theorem conjugateNegativeIota_apply (e : M) (he : Q e = -1)
    (x : CliffordAlgebra Q) :
    conjugateNegativeIota Q e he x = (-ι Q e * x) * ι Q e := by
  simp [conjugateNegativeIota, negativeIotaUnit, ConjAct.units_smul_def]

/-- If `Q(e) = -1`, conjugation by the unit `-ι(e)` preserves the even Clifford algebra. -/
noncomputable def conjugateNegativeIotaEven (e : M) (he : Q e = -1) :
    even Q →ₐ[R] even Q where
  toFun x := ⟨conjugateNegativeIota Q e he (x : CliffordAlgebra Q), by
    rw [conjugateNegativeIota_apply]
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    have hleft : -ι Q e ∈ evenOdd Q 1 :=
      Submodule.neg_mem _ (ι_mem_evenOdd_one _ _)
    have h := SetLike.mul_mem_graded (SetLike.mul_mem_graded hleft x.2)
      (ι_mem_evenOdd_one Q e)
    exact (show (1 + 1 : ZMod 2) = 0 by decide) ▸ (by simpa only [add_zero] using h)⟩
  map_one' := Subtype.ext (map_one (conjugateNegativeIota Q e he))
  map_mul' x y := Subtype.ext (map_mul (conjugateNegativeIota Q e he)
    (x : CliffordAlgebra Q) y)
  map_zero' := Subtype.ext (map_zero (conjugateNegativeIota Q e he))
  map_add' x y := Subtype.ext (map_add (conjugateNegativeIota Q e he)
    (x : CliffordAlgebra Q) y)
  commutes' r := Subtype.ext (AlgEquiv.commutes (conjugateNegativeIota Q e he) r)

omit [Invertible (2 : R)] in
/-- The ambient Clifford value of conjugation by `-ι(e)` on the even subalgebra. -/
@[simp]
theorem coe_conjugateNegativeIotaEven (e : M) (he : Q e = -1) (x : even Q) :
    (conjugateNegativeIotaEven Q e he x : CliffordAlgebra Q) =
      (-ι Q e * (x : CliffordAlgebra Q)) * ι Q e :=
  conjugateNegativeIota_apply Q e he x

end CliffordAlgebra
