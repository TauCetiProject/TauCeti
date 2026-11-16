/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Basic
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic

/-!
# Riemann–Roch for divisor sheaves

Let `X` be a compact connected Riemann surface. Its *analytic genus* is
`g_an = dim H¹(X, 𝒪)`, the dimension of the first Čech cohomology of the holomorphic structure
sheaf. For a divisor `D`, write `h⁰(D)` and `h¹(D)` for the dimensions of the global sections and of
the first Čech cohomology of the divisor sheaf `𝒪(D)`.

The finiteness of `H¹(X, 𝒪)` is an analytic theorem which is not proved here; every statement that
needs it takes it as an explicit instance argument. Under that hypothesis `H¹(X, 𝒪(D))` is
finite-dimensional for every divisor `D`, because finiteness is unchanged by a point twist
(`TauCeti.RiemannSurface.finiteDimensional_divisorCechCohomology_one`), and this file proves:

* **Riemann–Roch for divisor sheaves**: `h⁰(D) - h¹(D) = deg D + 1 - g_an`
  (`finrank_divisorSheaf_euler_characteristic`). The proof is induction over the point twists
  `𝒪(D) → 𝒪(D + x)`, each of which raises `h⁰ - h¹` by one, starting from `h⁰(0) = 1`
  (holomorphic functions on `X` are constant) and `h¹(0) = g_an`;
* the lower bound `deg D + 1 - g_an ≤ h⁰(D)`.

Combined with the vanishing `h⁰(D) = 0` for `deg D < 0`
(`finrank_divisorSheaf_eq_zero_of_degree_neg`, which needs no finiteness hypothesis), Riemann–Roch
computes `h¹(D) = g_an - 1 - deg D` for divisors of negative degree.

## Main declarations

* `TauCeti.RiemannSurface.analyticGenus`: the analytic genus `dim H¹(X, 𝒪)`;
* `TauCeti.RiemannSurface.analyticGenus_eq_finrank_divisorCechCohomology`: it is also the
  dimension of `H¹(X, 𝒪(0))`;
* `TauCeti.RiemannSurface.finrank_divisorSheaf_euler_characteristic`: Riemann–Roch for divisor
  sheaves;
* `TauCeti.RiemannSurface.finrank_divisorCechCohomology_one_of_degree_neg`:
  `h¹(D) = g_an - 1 - deg D` if `deg D < 0`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §16 (Theorem 16.9 and its proof).
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.Topology TauCeti.AlgebraicGeometry
open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X : Type}

variable [TopologicalSpace X] [ChartedSpace ℂ X]

variable (X) in
/-- The **analytic genus** `g_an = dim H¹(X, 𝒪)` of a Riemann surface: the dimension of the first
Čech cohomology of its holomorphic structure sheaf. This is a `Module.finrank`, so it is `0` when
the cohomology is infinite-dimensional; statements about it carry the finiteness of `H¹(X, 𝒪)` as
a hypothesis. -/
def analyticGenus : ℕ :=
  Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
    (holomorphicStructureSheafModules 𝓘(ℂ) X).obj)

/-- The analytic genus is the dimension of the first Čech cohomology of the holomorphic structure
sheaf. -/
theorem analyticGenus_def :
    analyticGenus X = Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) :=
  (rfl)

variable [IsManifold 𝓘(ℂ) 1 X]

/-- The analytic genus is the dimension of the first cohomology of the divisor sheaf `𝒪(0)`. -/
theorem analyticGenus_eq_finrank_divisorCechCohomology :
    analyticGenus X = Module.finrank ℂ (divisorCechCohomology (0 : WeilDivisor X) 1) :=
  (divisorCechCohomologyZeroIso X 1).toLinearEquiv.finrank_eq.symm

variable [CompactSpace X] [T2Space X] [ConnectedSpace X]
  [FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
  (holomorphicStructureSheafModules 𝓘(ℂ) X).obj)]

/-- **Riemann–Roch for divisor sheaves.** On a compact connected Riemann surface with
finite-dimensional `H¹(X, 𝒪)`, every divisor `D` satisfies
`h⁰(D) - h¹(D) = deg D + 1 - g_an`. -/
theorem finrank_divisorSheaf_euler_characteristic (D : WeilDivisor X) :
    (Module.finrank ℂ ((divisorSheaf D).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ (divisorCechCohomology D 1) =
      WeilDivisor.degree D + 1 - analyticGenus X := by
  refine WeilDivisor.induction_add_ofPoint (P := fun D : WeilDivisor X ↦
    (Module.finrank ℂ ((divisorSheaf D).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ (divisorCechCohomology D 1) =
      WeilDivisor.degree D + 1 - analyticGenus X) ?_ (fun D x ↦ ?_) D
  · rw [finrank_divisorSheaf_zero, analyticGenus_eq_finrank_divisorCechCohomology]
    simp
  · rw [finrank_pointTwist_euler_characteristic, map_add, WeilDivisor.degree_ofPoint]
    constructor <;> intro h <;> linarith

/-- Riemann–Roch gives a lower bound for the dimension of the global sections of `𝒪(D)`:
`deg D + 1 - g_an ≤ h⁰(D)`. -/
theorem degree_add_one_sub_analyticGenus_le_finrank_divisorSheaf (D : WeilDivisor X) :
    WeilDivisor.degree D + 1 - analyticGenus X ≤
      (Module.finrank ℂ ((divisorSheaf D).obj.obj (op ⊤)) : ℤ) := by
  rw [← finrank_divisorSheaf_euler_characteristic]
  omega

/-- For a divisor of negative degree, Riemann–Roch computes the first cohomology alone:
`h¹(D) = g_an - 1 - deg D`. -/
theorem finrank_divisorCechCohomology_one_of_degree_neg {D : WeilDivisor X}
    (hD : WeilDivisor.degree D < 0) :
    (Module.finrank ℂ (divisorCechCohomology D 1) : ℤ) =
      analyticGenus X - 1 - WeilDivisor.degree D := by
  have h := finrank_divisorSheaf_euler_characteristic D
  rw [finrank_divisorSheaf_eq_zero_of_degree_neg hD] at h
  omega

end TauCeti.RiemannSurface
