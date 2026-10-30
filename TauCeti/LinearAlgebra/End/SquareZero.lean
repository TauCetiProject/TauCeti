/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.Abel

/-!
# Finite-order endomorphisms with square-zero displacement

A linear endomorphism which is the identity on a submodule and on the quotient can still
be a nontrivial shear. If its order is invertible in the coefficient division ring, however, it
is the identity. This is the linear rigidity argument for finite actions preserving
normal coordinates: an element fixing the tangent space of a face cannot shear the
normal directions into that tangent space.
-/

public section

namespace Module.End

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A finite-order endomorphism whose displacement from the identity has square zero is
the identity, provided the order is nonzero in the coefficient division ring.
No finite-dimensionality hypothesis is needed. -/
theorem eq_one_of_pow_eq_one_of_sub_one_sq_eq_zero (f : Module.End K V) {n : ℕ}
    (hn : (n : K) ≠ 0) (hpow : f ^ n = 1) (hsq : (f - 1) ^ 2 = 0) : f = 1 := by
  have hfix (v : V) : f (f v - v) = f v - v := by
    have h := LinearMap.congr_fun hsq v
    simpa [pow_two, Module.End.mul_apply, sub_eq_zero] using h
  have hiter (m : ℕ) (v : V) : (f ^ m) v = v + (m : K) • (f v - v) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, hfix, Nat.cast_succ,
        add_smul, one_smul]
      abel
  ext v
  have h : (n : K) • (f v - v) = 0 := by
    simpa [hpow] using (hiter n v).symm
  exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left hn)

/-- A finite-order endomorphism acting trivially on both a submodule and the quotient is
the identity, when its order is nonzero in the coefficient division ring. The quotient condition
is expressed without choosing a quotient carrier, as containment of the displacement range. -/
theorem eq_one_of_pow_eq_one_of_range_sub_one_le (f : Module.End K V) (W : Submodule K V)
    {n : ℕ} (hn : (n : K) ≠ 0) (hpow : f ^ n = 1)
    (hfixed : W ≤ LinearMap.ker (f - 1)) (hrange : LinearMap.range (f - 1) ≤ W) : f = 1 := by
  apply f.eq_one_of_pow_eq_one_of_sub_one_sq_eq_zero hn hpow
  rw [pow_two, Module.End.mul_eq_comp, ← LinearMap.range_le_ker_iff]
  exact hrange.trans hfixed

end Module.End
