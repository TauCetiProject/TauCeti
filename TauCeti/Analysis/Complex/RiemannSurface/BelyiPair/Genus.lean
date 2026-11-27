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

Invariance, degree-one evaluations, and `isoSetoid` descent for `eulerChar` and `genus`.
-/

public noncomputable section

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
  rw [((biholomorphOfDegreeEqOne P.β hP).toHomeomorph.trans
    (onePointEquivSphereOfFinrankEq (ι := ULift.{u} (Fin 3))
      (by simp [Complex.finrank_real_complex]))).eulerChar_eq,
    eulerChar_sphere (n := 2) (by simp)]
  norm_num

/-- **An analytic Belyi pair of degree one has genus `0`.** -/
theorem genus_X_eq_zero_of_degree_eq_one {P : AnalyticBelyiPair.{u}} (hP : degree P.β = 1) :
    genus P.X = 0 := genus_eq_of_eulerChar_eq (eulerChar_X_eq_two_of_degree_eq_one hP)

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

/-- The total space of `P.toTopBranchedCover h` has finite CW type. -/
instance instFiniteCWTypeToTopBranchedCover (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (h : degree P.β = n) : FiniteCWType (P.toTopBranchedCover h).Z :=
  inferInstanceAs (FiniteCWType P.X)

/-- Forgetting the complex structure preserves the Euler characteristic. -/
@[simp] theorem eulerChar_toTopBranchedCover (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (h : degree P.β = n) [FiniteCWType (P.toTopBranchedCover h).Z] :
    eulerChar (P.toTopBranchedCover h).Z = eulerChar P.X :=
  (Homeomorph.refl P.X : (P.toTopBranchedCover h).Z ≃ₜ P.X).eulerChar_eq

/-- Forgetting the complex structure preserves the topological genus. -/
@[simp] theorem genus_toTopBranchedCover (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (h : degree P.β = n) [FiniteCWType (P.toTopBranchedCover h).Z] :
    genus (P.toTopBranchedCover h).Z = genus P.X :=
  (Homeomorph.refl P.X : (P.toTopBranchedCover h).Z ≃ₜ P.X).toHomotopyEquiv.genus_eq

end TauCeti.AnalyticBelyiPair
