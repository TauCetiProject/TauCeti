/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Ray
import Mathlib.Order.Preorder.Finite

/-!
# Sums of vectors in the same ray

Two nonzero vectors in the same ray cannot cancel: their sum is again nonzero. This is the
non-degeneracy needed to merge adjacent segments of a piecewise-linear path that point in the same
direction. A vector lies in the same ray as such a sum exactly when it lies in the same ray as the
summands, since `SameRay` is transitive through a nonzero vector.

Two distinct points of a finite orbit of a linear group action never lie in the same ray. This is
what makes the velocity of each segment of a path with velocities in a Weyl orbit recoverable from
the segment alone.
-/

public section

open Module

section Semiring

variable {R M : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommMonoid M] [Module R M] {x y z : M}

/-- `SameRay` is transitive through a nonzero vector. -/
theorem SameRay.trans_of_ne_zero (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y ≠ 0) :
    SameRay R x z :=
  hxy.trans hyz fun h ↦ absurd h hy

end Semiring

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [IsTorsionFree R M] {x y z : M}

/-- The sum of two vectors in the same ray, the first of them nonzero, is nonzero. -/
theorem SameRay.add_ne_zero (h : SameRay R x y) (hx : x ≠ 0) : x + y ≠ 0 := by
  intro hxy
  rw [add_eq_zero_iff_eq_neg'] at hxy
  exact hx (eq_zero_of_sameRay_self_neg (hxy ▸ h))

/-- If `x` and `y` lie in the same ray and `y` is nonzero, then a vector lies in the same ray as
`x + y` exactly when it lies in the same ray as `y`. -/
theorem SameRay.sameRay_add_left_iff (h : SameRay R x y) (hy : y ≠ 0) :
    SameRay R (x + y) z ↔ SameRay R y z := by
  have hxy : SameRay R (x + y) y := h.add_left SameRay.rfl
  exact ⟨fun h' ↦ hxy.symm.trans_of_ne_zero h' (add_comm x y ▸ h.symm.add_ne_zero hy),
    fun h' ↦ hxy.trans_of_ne_zero h' hy⟩

section Orbit

variable {R M G : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] [Group G] [MulAction G M] [SMulCommClass G R M] {x y z : M}

/-- Two points of a finite orbit of a group acting by maps commuting with scalar multiplication
are equal as soon as they lie in the same ray. If `g` moved a nonzero point `y` of the orbit to
`r • y` with `0 < r`, the powers of `g` would move `y` to the points `r ^ n • y` of the orbit, which
are pairwise distinct unless `r = 1`. -/
theorem SameRay.eq_of_mem_orbit (h : SameRay R y z) (hy : y ∈ MulAction.orbit G x)
    (hz : z ∈ MulAction.orbit G x) (hfin : (MulAction.orbit G x).Finite) : y = z := by
  obtain ⟨g, rfl⟩ := hy
  obtain ⟨g', rfl⟩ := hz
  dsimp only at h ⊢
  -- The point `0` is fixed, since the action commutes with multiplication by `0 : R`.
  have hzero (k : G) : k • (0 : M) = 0 := by simpa using smul_comm k (0 : R) (0 : M)
  have hx (k : G) (hk : k • x = 0) : x = 0 := by
    rw [← inv_smul_smul k x, hk, hzero]
  by_cases hy0 : g • x = 0
  · rw [hy0, hx g hy0, hzero]
  by_cases hz0 : g' • x = 0
  · rw [hz0, hx g' hz0, hzero]
  obtain ⟨r, hr, hrz⟩ := h.exists_pos_left hy0 hz0
  -- The element `g' * g⁻¹` moves `g • x` to `r • g • x`, so its powers move it to `r ^ n • g • x`.
  have hpow (n : ℕ) : (g' * g⁻¹) ^ n • g • x = r ^ n • g • x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_smul, mul_smul, inv_smul_smul, ← hrz, smul_comm, ih, pow_succ', mul_smul]
  obtain ⟨m, n, hmn, hrmn⟩ := hfin.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ ↦ r ^ n • g • x) fun n ↦
      MulAction.mem_orbit_iff.2 ⟨(g' * g⁻¹) ^ n * g, by rw [mul_smul, hpow]⟩
  have hr1 : r = 1 := by
    by_contra hr1
    exact hmn.ne (pow_right_injective₀ hr hr1 (smul_left_injective R hy0 hrmn))
  rw [← hrz, hr1, one_smul]

end Orbit
