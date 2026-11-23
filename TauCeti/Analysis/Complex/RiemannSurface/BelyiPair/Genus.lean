/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Analysis.Complex.RiemannSurface.BelyiPair.Basic
public import TauCeti.Geometry.Manifold.Complex.FiniteCWType

/-!
# Euler characteristic and genus of analytic Belyi pairs

Invariance, degree-one/sphere evaluations, and `isoSetoid` descent for `eulerChar` and `genus`.
-/

public noncomputable section

open scoped OnePoint

namespace TauCeti.AnalyticBelyiPair

open RiemannSurface

universe u

/-- Isomorphic analytic Belyi pairs have the same Euler characteristic. -/
theorem Iso.eulerChar_eq {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q) :
    eulerChar P.X = eulerChar Q.X := e.toHomeomorph.eulerChar_eq

/-- Isomorphic analytic Belyi pairs have the same topological genus. -/
theorem Iso.genus_eq {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q) : genus P.X = genus Q.X :=
  e.toHomeomorph.toHomotopyEquiv.genus_eq

/-- **An analytic Belyi pair of degree one has Euler characteristic `2`.** -/
theorem eulerChar_X_eq_two_of_degree_eq_one {P : AnalyticBelyiPair.{u}} (hP : degree P.β = 1) :
    eulerChar P.X = 2 := by
  have h : Fintype.card (ULift.{u} (Fin 3)) = 2 + 1 := by simp
  let _ := sphereCWComplex h; have := finite_sphereCWComplex h
  rw [eulerChar_eq_cwEulerChar ((biholomorphOfDegreeEqOne P.β hP).toHomeomorph.trans
    (onePointEquivSphereOfFinrankEq (ι := ULift.{u} (Fin 3))
      (by simp [Complex.finrank_real_complex]))).toHomotopyEquiv, cwEulerChar_sphereCWComplex h]
  norm_num

/-- **An analytic Belyi pair of degree one has genus `0`.** -/
theorem genus_X_eq_zero_of_degree_eq_one {P : AnalyticBelyiPair.{u}} (hP : degree P.β = 1) :
    genus P.X = 0 := genus_eq_of_eulerChar_eq (eulerChar_X_eq_two_of_degree_eq_one hP)

/-- The power Belyi pair `z ↦ z ^ n` on the Riemann sphere has Euler characteristic `2`. -/
@[simp] theorem eulerChar_X_pow {n : ℕ} (hn : n ≠ 0) : eulerChar (pow hn).X = 2 := by
  rw [pow, eulerChar_onePoint, Complex.finrank_real_complex]; norm_num

/-- The power Belyi pair `z ↦ z ^ n` on the Riemann sphere has genus `0`. -/
@[simp] theorem genus_X_pow {n : ℕ} (hn : n ≠ 0) : genus (pow hn).X = 0 := genus_onePoint_complex

/-- The Chebyshev Belyi pair `z ↦ 4z(1 - z)` on the Riemann sphere has Euler characteristic `2`. -/
@[simp] theorem eulerChar_X_chebyshev : eulerChar chebyshev.X = 2 := by
  rw [chebyshev, eulerChar_onePoint, Complex.finrank_real_complex]; norm_num

/-- The Chebyshev Belyi pair `z ↦ 4z(1 - z)` on the Riemann sphere has genus `0`. -/
@[simp] theorem genus_X_chebyshev : genus chebyshev.X = 0 := genus_onePoint_complex

/-- The Euler characteristic of an isomorphism class of degree-`n` analytic Belyi pairs. -/
def isoClassEulerChar (n : ℕ) : Quotient (isoSetoid.{u} n) → ℤ :=
  Quotient.lift (fun P ↦ eulerChar P.val.X) fun _ _ h ↦ (isoSetoid_r.1 h).elim Iso.eulerChar_eq

/-- On the class of a pair, `isoClassEulerChar` evaluates to `eulerChar P.val.X`. -/
@[simp] theorem isoClassEulerChar_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    isoClassEulerChar n ⟦P⟧ = eulerChar P.val.X := (rfl)

/-- The topological genus of an isomorphism class of degree-`n` analytic Belyi pairs. -/
def isoClassGenus (n : ℕ) : Quotient (isoSetoid.{u} n) → ℕ :=
  Quotient.lift (fun P ↦ genus P.val.X) fun _ _ h ↦ (isoSetoid_r.1 h).elim Iso.genus_eq

/-- On the class of a pair, `isoClassGenus` evaluates to `genus P.val.X`. -/
@[simp] theorem isoClassGenus_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    isoClassGenus n ⟦P⟧ = genus P.val.X := (rfl)

end TauCeti.AnalyticBelyiPair
