/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.ZMod.Basic

/-!
# Power traces of a trace-one quadratic generator

The trace of a power of the universal quadratic generator computes the sum of two
conjugate powers in any commutative ring. Modulo a divisor of the norm, the generator
becomes idempotent, so the trace of every positive power is one.
-/

public section

namespace QuadraticAlgebra

/-- If `x + y = 1` and `xy = N`, the universal quadratic trace computes `x^j + y^j`. -/
theorem intCast_trace_omega_pow {R : Type*} [CommRing R] {N : ℤ} {x y : R}
    (hadd : x + y = 1) (hmul : x * y = (N : R)) (j : ℕ) :
    ((trace ((ω : QuadraticAlgebra ℤ (-N) 1) ^ j) : ℤ) : R) = x ^ j + y ^ j := by
  let f : QuadraticAlgebra ℤ (-N) 1 →ₐ[ℤ] R := lift ⟨x, by
    simp only [neg_smul, Int.smul_one_eq_cast, one_smul]
    calc
      x * x = x * (x + y) - x * y := by ring
      _ = -(N : R) + x := by rw [hadd, hmul, mul_one]; abel⟩
  have hf : f ω = x := by simp [f]
  have hfs : f (star ω) = y := by
    apply add_left_cancel (a := x)
    calc
      x + f (star ω) = f (ω + star ω) := by rw [map_add, hf]
      _ = (1 : R) := by rw [← algebraMap_trace_eq_add_star, trace_omega, map_one, map_one]
      _ = x + y := hadd.symm
  simpa only [AlgHom.commutes, map_add, star_pow, map_pow, hf, hfs,
    algebraMap_int_eq, Int.coe_castRingHom, map_intCast] using
    congrArg f (algebraMap_trace_eq_add_star ((ω : QuadraticAlgebra ℤ (-N) 1) ^ j))

/-- The trace of any positive power of a trace-one quadratic generator is congruent to
one modulo any divisor of its norm. -/
theorem trace_omega_pow_modEq_one {N : ℤ} {m j : ℕ} (hm : (m : ℤ) ∣ N) (hj : 0 < j) :
    trace ((ω : QuadraticAlgebra ℤ (-N) 1) ^ j) ≡ 1 [ZMOD m] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ m).mp
  let f : ℤ →+* ZMod m := Int.castRingHom _
  have hN : f (-N) = 0 := by
    have h : f N = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd N m).mpr hm
    simp only [map_neg, h, neg_zero]
  have hω : IsIdempotentElem (ω : QuadraticAlgebra (ZMod m) (f (-N)) (f 1)) := by
    rw [IsIdempotentElem, omega_mul_omega_eq_algebraMap, hN]
    simp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  calc
    ((trace ((ω : QuadraticAlgebra ℤ (-N) 1) ^ k.succ) : ℤ) : ZMod m) =
      trace (mapRingHom f (-N) 1 (ω ^ k.succ)) := (trace_mapRingHom f (-N) 1 _).symm
    _ = (1 : ℤ) := by
      rw [map_pow, mapRingHom_omega, hω.pow_succ_eq, trace_omega, map_one, Int.cast_one]

end QuadraticAlgebra
