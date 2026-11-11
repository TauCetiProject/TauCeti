/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Singular Betti numbers

`TauCeti.bettiNumber k X j` is the natural-number dimension of singular homology in degree `j`
with coefficients in the division ring `k`. It is invariant under homotopy equivalence.
As with `Module.finrank`, its value is zero for infinite-dimensional homology; interpreting it
as a dimension therefore requires a separate finiteness result.
-/

public section

noncomputable section

universe u

namespace TauCeti

/-- The `j`-th singular Betti number of `X` with coefficients in `k`. This is zero when the
singular homology is infinite-dimensional, following the convention of `Module.finrank`. -/
def bettiNumber (k : Type u) [DivisionRing k] (X : Type u) [TopologicalSpace X] (j : ℕ) : ℕ :=
  Module.finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj
    (ModuleCat.of k k)).obj (TopCat.of X))

/-- The Betti number is the finrank of native singular homology with coefficients in `k`. -/
theorem bettiNumber_def (k : Type u) [DivisionRing k] (X : Type u) [TopologicalSpace X] (j : ℕ) :
    bettiNumber k X j =
      Module.finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj
        (ModuleCat.of k k)).obj (TopCat.of X)) := (rfl)

/-- The Betti number is zero when the singular homology is not finite-dimensional. -/
@[simp]
theorem bettiNumber_eq_zero_of_not_finite (k : Type u) [DivisionRing k]
    (X : Type u) [TopologicalSpace X] (j : ℕ)
    (h : ¬Module.Finite k
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj
        (ModuleCat.of k k)).obj (TopCat.of X))) :
    bettiNumber k X j = 0 := by
  rw [bettiNumber_def]
  exact Module.finrank_of_not_finite h

/-- For finite-dimensional singular homology, the Betti number casts to its cardinal rank. -/
@[simp]
theorem bettiNumber_eq_rank (k : Type u) [DivisionRing k]
    (X : Type u) [TopologicalSpace X] (j : ℕ)
    [Module.Finite k
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj
        (ModuleCat.of k k)).obj (TopCat.of X))] :
    (bettiNumber k X j : Cardinal) =
      Module.rank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj
        (ModuleCat.of k k)).obj (TopCat.of X)) := by
  rw [bettiNumber_def]
  exact Module.finrank_eq_rank ..

end TauCeti

/-- Homotopy equivalent spaces have the same singular Betti numbers. -/
theorem ContinuousMap.HomotopyEquiv.bettiNumber_eq {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y)
    (k : Type u) [DivisionRing k] (j : ℕ) :
    TauCeti.bettiNumber k X j = TauCeti.bettiNumber k Y j := by
  rw [TauCeti.bettiNumber_def, TauCeti.bettiNumber_def]
  exact (e.singularHomologyIso (ModuleCat.of k k) j).toLinearEquiv.finrank_eq
