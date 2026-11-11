/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The integral special linear action on the plane

`TauCeti.slTwoAction` packages column multiplication by `SL₂(ℤ)` as automorphisms of the
multiplicative copy of `ℤ²`, so that it can be used in `SemidirectProduct`. Its application
lemma identifies it with Mathlib's existing action on column vectors.

The upper and lower unipotent subgroups act by shears. We compute their action and their
fixed vectors, and show that their only common fixed vector is zero. In particular, the
upper shear sends `(0, 1)` to `(1, 1)` and fixes `(1, 0)`, distinguishing column multiplication
from the row-vector convention.
-/

public section

namespace TauCeti

open Matrix Multiplicative

/-- The column-vector action of `SL₂(ℤ)` on the multiplicative copy of `ℤ²`.
This is the homomorphism used to form the semidirect product `ℤ² ⋊ SL₂(ℤ)`. -/
def slTwoAction : SpecialLinearGroup (Fin 2) ℤ →* MulAut (Multiplicative (Fin 2 → ℤ)) where
  toFun g := AddEquiv.toMultiplicative (SpecialLinearGroup.toLin' g).toAddEquiv
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

/-- Forgetting the multiplicative type tag recovers the usual action on column vectors. -/
@[simp]
theorem slTwoAction_apply (g : SpecialLinearGroup (Fin 2) ℤ)
    (v : Multiplicative (Fin 2 → ℤ)) :
    toAdd (slTwoAction g v) = g • toAdd v := (rfl)

/-- The matrix formula for the integral special linear action. -/
theorem slTwoAction_apply_eq_mulVec (g : SpecialLinearGroup (Fin 2) ℤ)
    (v : Multiplicative (Fin 2 → ℤ)) :
    toAdd (slTwoAction g v) = (g : Matrix (Fin 2) (Fin 2) ℤ).mulVec (toAdd v) := by
  rw [slTwoAction_apply, SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]

/-- The upper unipotent matrix with parameter `n` adds `n` times the second coordinate to
the first coordinate. -/
@[simp]
theorem slTwoAction_upper (n x y : ℤ) :
    slTwoAction (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) n)
      (ofAdd ![x, y]) = ofAdd ![x + n * y, y] := by
  apply toAdd.injective
  ext i
  fin_cases i <;> simp

/-- The lower unipotent matrix with parameter `n` adds `n` times the first coordinate to
the second coordinate. -/
@[simp]
theorem slTwoAction_lower (n x y : ℤ) :
    slTwoAction (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) n)
      (ofAdd ![x, y]) = ofAdd ![x, y + n * x] := by
  apply toAdd.injective
  ext i
  fin_cases i <;> simp

/-- A nontrivial upper shear fixes exactly the horizontal axis. -/
@[simp]
theorem slTwoAction_upper_eq_self_iff {n : ℤ} (hn : n ≠ 0)
    (v : Multiplicative (Fin 2 → ℤ)) :
    slTwoAction (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) n) v = v ↔
      toAdd v 1 = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun w : Multiplicative (Fin 2 → ℤ) ↦ toAdd w 0) h
    simpa [hn] using h0
  · intro hv
    apply toAdd.injective
    ext i
    fin_cases i <;> simp [hv]

/-- A nontrivial lower shear fixes exactly the vertical axis. -/
@[simp]
theorem slTwoAction_lower_eq_self_iff {n : ℤ} (hn : n ≠ 0)
    (v : Multiplicative (Fin 2 → ℤ)) :
    slTwoAction (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) n) v = v ↔
      toAdd v 0 = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun w : Multiplicative (Fin 2 → ℤ) ↦ toAdd w 1) h
    simpa [hn] using h1
  · intro hv
    apply toAdd.injective
    ext i
    fin_cases i <;> simp [hv]

/-- The only vector fixed by all of `SL₂(ℤ)` is zero, or `1` in the multiplicative copy. -/
@[simp]
theorem slTwoAction_fixed_iff (v : Multiplicative (Fin 2 → ℤ)) :
    (∀ g : SpecialLinearGroup (Fin 2) ℤ, slTwoAction g v = v) ↔ v = 1 := by
  constructor
  · intro h
    have h0 := (slTwoAction_lower_eq_self_iff (n := 1) (by decide) v).mp
      (h (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) 1))
    have h1 := (slTwoAction_upper_eq_self_iff (n := 1) (by decide) v).mp
      (h (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) 1))
    apply toAdd.injective
    ext i
    fin_cases i <;> simp [h0, h1]
  · rintro rfl g
    exact map_one (slTwoAction g)

end TauCeti
