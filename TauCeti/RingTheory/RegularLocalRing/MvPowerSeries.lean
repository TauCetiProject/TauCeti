/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# Multivariate power series over a regular local ring

Power series in finitely many variables over a regular local ring form a regular local ring:
`R⟦X₀, …, Xₙ⟧` is power series in one variable over `R⟦X₀, …, Xₙ₋₁⟧`
(`MvPowerSeries.finSuccEquiv`), so this follows by induction from the one-variable case
`TauCeti.PowerSeries.isRegularLocalRing`. Any finite type of variables is then reached by
renaming the variables. Over a discrete valuation ring `O`, for instance, `O⟦X₀, …, Xₙ₋₁⟧` is a
regular local ring of dimension `n + 1`; quotients of it by a single element of the maximal ideal
outside its square are again regular, hence domains.

## Main results

* `TauCeti.MvPowerSeries.isRegularLocalRing`: `MvPowerSeries σ R` is a regular local ring for
  every finite type `σ` whenever `R` is.

## References

* H. Matsumura, *Commutative Ring Theory*, §14 and §15.
-/

public section

namespace TauCeti.MvPowerSeries

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- Power series in the variables `Fin n`, by induction on `n`. -/
private theorem isRegularLocalRing_fin (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact .of_ringEquiv (_root_.MvPowerSeries.isEmptyEquiv (Fin 0) R).symm.toRingEquiv
  | succ n ih =>
    exact .of_ringEquiv (_root_.MvPowerSeries.finSuccEquiv R n).symm.toRingEquiv

/-- **Power series in finitely many variables over a regular local ring form a regular local
ring.** -/
instance isRegularLocalRing (σ : Type*) [Finite σ] :
    IsRegularLocalRing (MvPowerSeries σ R) :=
  have := isRegularLocalRing_fin (R := R) (Nat.card σ)
  .of_ringEquiv (_root_.MvPowerSeries.renameEquiv R (Finite.equivFin σ).symm).toRingEquiv

end TauCeti.MvPowerSeries
