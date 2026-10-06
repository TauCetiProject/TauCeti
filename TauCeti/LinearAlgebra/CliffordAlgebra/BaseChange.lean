/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Clifford involutions, the even part, and extension of scalars

This file records the structural properties of Mathlib's `CliffordAlgebra.ofBaseChangeAux`, the
canonical map from a Clifford algebra into the Clifford algebra after extension of scalars: it
commutes with the grade involution and with Clifford conjugation, and it preserves the even
subalgebra. These are the compatibilities needed to transport twisted-conjugation actions and the
Lipschitz, Pin, and Spin subgroups along scalar extensions.

## Main results

* `CliffordAlgebra.ofBaseChangeAux_involute` proves naturality of the grade involution.
* `CliffordAlgebra.ofBaseChangeAux_reverse` proves naturality of Clifford reversal.
* `CliffordAlgebra.ofBaseChangeAux_star` proves naturality of Clifford conjugation.
* `CliffordAlgebra.ofBaseChangeAux_mem_even` proves preservation of the even subalgebra.
* `CliffordAlgebra.ofBaseChangeAux_baseChange` identifies direct and successive scalar extension.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- The canonical map to the Clifford algebra after extension of scalars commutes with the grade
involution. -/
@[simp]
theorem ofBaseChangeAux_involute (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    ofBaseChangeAux A Q (involute x) =
      involute (Q := Q.baseChange A) (ofBaseChangeAux A Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- The canonical map to the Clifford algebra after extension of scalars commutes with Clifford
reversal. -/
@[simp]
theorem ofBaseChangeAux_reverse (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    ofBaseChangeAux A Q (reverse x) =
      reverse (Q := Q.baseChange A) (ofBaseChangeAux A Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [reverse.commutes, (ofBaseChangeAux A Q).commutes]
      rw [IsScalarTower.algebraMap_apply R A (CliffordAlgebra (Q.baseChange A)),
        reverse.commutes]
  | ι m => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [reverse.map_mul, map_mul, hx, hy]

/-- The canonical map to the Clifford algebra after extension of scalars commutes with Clifford
conjugation. -/
@[simp]
theorem ofBaseChangeAux_star (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    ofBaseChangeAux A Q (star x) = star (ofBaseChangeAux A Q x) := by
  simp only [star_def, ofBaseChangeAux_reverse, ofBaseChangeAux_involute]

/-- The canonical map to the Clifford algebra after extension of scalars sends even elements to
even elements. -/
theorem ofBaseChangeAux_mem_even (Q : QuadraticForm R M) {x : CliffordAlgebra Q}
    (hx : x ∈ even Q) : ofBaseChangeAux A Q x ∈ even (Q.baseChange A) := by
  -- `even` is the subalgebra wrapper around degree zero of `evenOdd`, and `even_induction` is
  -- stated for the underlying graded submodule.
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hx
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      simpa using one_le_evenOdd_zero (Q.baseChange A)
        (Submodule.mem_one.mpr ⟨algebraMap R A r,
          (IsScalarTower.algebraMap_apply R A (CliffordAlgebra (Q.baseChange A)) r).symm⟩)
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | ι_mul_ι_mul m n x _ hx =>
      simpa only [map_mul, ofBaseChangeAux_ι, zero_add] using
        SetLike.mul_mem_graded
          (ι_mul_ι_mem_evenOdd_zero (Q.baseChange A) (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] n)) hx

section ScalarTower

variable {B : Type x} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Transporting a direct scalar extension of a Clifford element along the canonical scalar-tower
isometry agrees with extending the element successively. -/
@[simp]
theorem ofBaseChangeAux_baseChange (Q : QuadraticForm R M) (z : CliffordAlgebra Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    CliffordAlgebra.map
        (QuadraticForm.baseChangeBaseChange (A := A) (B := B) Q).toIsometry
        (ofBaseChangeAux B Q z) =
      ofBaseChangeAux B (Q.baseChange A) (ofBaseChangeAux A Q z) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  induction z using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | mul z w hz hw => simp only [map_mul, hz, hw]

end ScalarTower

end CliffordAlgebra
