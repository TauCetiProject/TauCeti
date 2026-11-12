/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sphere.Basic

/-!
# Divisor cohomology of point twists on the Riemann sphere

For a point `x` of the Riemann sphere `ℙ¹ = OnePoint ℂ` and an integer `n`, write `𝒪(n)` for the
divisor sheaf of `n • [x]`. Stepping through the six-term point-twist sequence from
`h⁰(𝒪) = 1` and `h¹(𝒪) = 0`, we compute

`h⁰(𝒪(n)) = max(n + 1, 0)` and `h¹(𝒪(n)) = max(-n - 1, 0)`,

so `h⁰ - h¹ = n + 1` for every `n`. In particular `𝒪(-1)` has `(h⁰, h¹) = (0, 0)` and `𝒪(-2)`
has `(h⁰, h¹) = (0, 1)`. Only point twists of a single point are treated; no general
Riemann–Roch theorem is asserted.

## Main results

* `TauCeti.RiemannSurface.finiteDimensional_divisorCechCohomology_one_zsmul_ofPoint_sphere`:
  `H¹(𝒪(n))` is finite-dimensional.
* `TauCeti.RiemannSurface.finrank_zsmul_ofPoint_euler_characteristic_sphere`:
  `h⁰(𝒪(n)) - h¹(𝒪(n)) = n + 1`.
* `TauCeti.RiemannSurface.finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere_of_neg_one_le`:
  `h¹(𝒪(n)) = 0` for `n ≥ -1`.
* `TauCeti.RiemannSurface.finrank_divisorSheaf_zsmul_ofPoint_globalSections_sphere` and
  `TauCeti.RiemannSurface.finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere`: the closed
  dimension formulas.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16-17.
-/

public noncomputable section

open CategoryTheory Limits Opposite
open TauCeti.AlgebraicGeometry

namespace TauCeti.RiemannSurface

variable (x : OnePoint ℂ)

/-- The first cohomology of `𝒪(n • [x])` on `ℙ¹` is finite-dimensional. -/
instance finiteDimensional_divisorCechCohomology_one_zsmul_ofPoint_sphere (n : ℤ) :
    FiniteDimensional ℂ (divisorCechCohomology (n • WeilDivisor.ofPoint x) 1) := by
  induction n using Int.induction_on with
  | zero =>
    rw [zero_zsmul]
    have := ModuleCat.isZero_iff_subsingleton.1 isZero_divisorCechCohomology_zero_one_sphere
    infer_instance
  | succ i ih =>
    rw [add_one_zsmul]
    exact (finiteDimensional_divisorCechCohomology_one_add_point_iff _ x).2 ih
  | pred i ih =>
    refine (finiteDimensional_divisorCechCohomology_one_add_point_iff _ x).1 ?_
    rwa [← add_one_zsmul, sub_add_cancel]

/-- **Riemann–Roch for point twists on `ℙ¹`.** `h⁰(𝒪(n • [x])) - h¹(𝒪(n • [x])) = n + 1`. -/
theorem finrank_zsmul_ofPoint_euler_characteristic_sphere (n : ℤ) :
    (Module.finrank ℂ ((divisorSheaf (n • WeilDivisor.ofPoint x)).obj.obj (op ⊤)) : ℤ) -
      Module.finrank ℂ (divisorCechCohomology (n • WeilDivisor.ofPoint x) 1) = n + 1 := by
  induction n using Int.induction_on with
  | zero =>
    rw [zero_zsmul, finrank_divisorSheaf_zero_globalSections,
      finrank_divisorCechCohomology_zero_one_sphere]
    norm_num
  | succ i ih =>
    rw [add_one_zsmul, finrank_pointTwist_euler_characteristic, ih]
  | pred i ih =>
    have h := finrank_pointTwist_euler_characteristic ((-i - 1 : ℤ) • WeilDivisor.ofPoint x) x
    rw [← add_one_zsmul, sub_add_cancel, ih] at h
    omega

/-- `h¹(𝒪(n • [x])) = 0` on `ℙ¹` for `n ≥ -1`. -/
theorem finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere_of_neg_one_le {n : ℤ}
    (hn : -1 ≤ n) :
    Module.finrank ℂ (divisorCechCohomology (n • WeilDivisor.ofPoint x) 1) = 0 := by
  obtain rfl | hn := hn.eq_or_lt
  · have h := finrank_zsmul_ofPoint_euler_characteristic_sphere x (-1)
    rw [finrank_divisorSheaf_zsmul_ofPoint_globalSections_of_neg x (by norm_num)] at h
    omega
  have key (m : ℕ) :
      Module.finrank ℂ (divisorCechCohomology ((m : ℤ) • WeilDivisor.ofPoint x) 1) = 0 := by
    induction m with
    | zero =>
      rw [Nat.cast_zero, zero_zsmul]
      exact finrank_divisorCechCohomology_zero_one_sphere
    | succ m ih =>
      rw [Nat.cast_succ, add_one_zsmul]
      have h := LinearMap.finrank_le_finrank_of_surjective
        (pointTwistCohomologyMap_one_surjective ((m : ℤ) • WeilDivisor.ofPoint x) x)
      rw [ih] at h
      omega
  lift n to ℕ using (by omega)
  exact key n

/-- **The dimension of `H⁰` of a point twist on `ℙ¹`.** `h⁰(𝒪(n • [x])) = max(n + 1, 0)`. -/
theorem finrank_divisorSheaf_zsmul_ofPoint_globalSections_sphere (n : ℤ) :
    Module.finrank ℂ ((divisorSheaf (n • WeilDivisor.ofPoint x)).obj.obj (op ⊤)) =
      (n + 1).toNat := by
  have h := finrank_zsmul_ofPoint_euler_characteristic_sphere x n
  rcases le_or_gt 0 n with hn | hn
  · rw [finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere_of_neg_one_le x (by omega)] at h
    omega
  · rw [finrank_divisorSheaf_zsmul_ofPoint_globalSections_of_neg x hn]
    omega

/-- **The dimension of `H¹` of a point twist on `ℙ¹`.** `h¹(𝒪(n • [x])) = max(-n - 1, 0)`. -/
theorem finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere (n : ℤ) :
    Module.finrank ℂ (divisorCechCohomology (n • WeilDivisor.ofPoint x) 1) = (-n - 1).toNat := by
  have h := finrank_zsmul_ofPoint_euler_characteristic_sphere x n
  rw [finrank_divisorSheaf_zsmul_ofPoint_globalSections_sphere] at h
  omega

end TauCeti.RiemannSurface
