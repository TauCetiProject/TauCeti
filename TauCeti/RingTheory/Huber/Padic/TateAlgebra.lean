/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Padic.Field
public import TauCeti.RingTheory.Huber.Restricted.Noetherian

/-!
# The p-adic Tate algebra `ℚ_p⟨T₁, …, Tₙ⟩`

The Tate algebra `ℚ_p⟨T₁, …, Tₙ⟩` is the ring of power series over `ℚ_[p]` whose coefficients
tend to zero, with the Gauss norm, the supremum of the coefficient norms. In Mathlib this is the
subring `MvPowerSeries.IsRestricted.subring` of unit-radius restricted series. It is the
coordinate ring of the closed `p`-adic polydisc and the basic example of a complete strongly
noetherian Tate ring, the class of rings to which Tate acyclicity (Wedhorn, Theorem 8.28)
applies.

Every property is an instance of a general result over a complete nontrivially normed field
with an ultrametric norm, so the statements below are `example`s recording the instances that
apply to `ℚ_[p]`:

* `ℚ_p⟨T₁, …, Tₙ⟩` is complete and Hausdorff, because the Gauss norm of restricted series over a
  complete ring is complete;
* it is a Tate ring (`TauCeti.Huber.IsTateRing.isRestricted_subring`), with the constant `p` as a
  pseudouniformiser;
* it is noetherian (`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`, BGR §5.2.6);
* it is strongly noetherian (`TauCeti.Huber.IsStronglyNoetherian.isRestricted_subring`): every
  restricted power-series algebra over it is noetherian.

The same holds for the completed Huber algebra `TauCeti.Huber.restrictedMvPowerSeriesCompletion`
over `ℚ_[p]`, which is identified with `ℚ_p⟨T₁, …, Tₙ⟩` by
`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §5.6 for restricted power series, §6 for Tate rings
  and strongly noetherian Tate rings, and Theorem 8.28.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, for noetherianity of Tate
  algebras.
-/

public section

namespace TauCeti.Huber.Padic

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- `ℚ_p⟨T₁, …, Tₙ⟩` is complete for its Gauss norm. -/
example : CompleteSpace (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ)) :=
  inferInstance

/-- `ℚ_p⟨T₁, …, Tₙ⟩` is Hausdorff. -/
example : T2Space (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ)) :=
  inferInstance

/-- `ℚ_p⟨T₁, …, Tₙ⟩` is a Tate ring. -/
example : IsTateRing (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ)) :=
  inferInstance

/-- `ℚ_p⟨T₁, …, Tₙ⟩` is noetherian. -/
example :
    IsNoetherianRing (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ)) :=
  MvPowerSeries.isNoetherianRing_isRestricted_subring

/-- **`ℚ_p⟨T₁, …, Tₙ⟩` is strongly noetherian.** -/
example :
    IsStronglyNoetherian
      (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ)) :=
  inferInstance

/-- The completed Huber Tate algebra over `ℚ_[p]` is complete. -/
example : CompleteSpace (restrictedMvPowerSeriesCompletion n ℚ_[p]) := inferInstance

/-- The completed Huber Tate algebra over `ℚ_[p]` is strongly noetherian. -/
example : IsStronglyNoetherian (restrictedMvPowerSeriesCompletion n ℚ_[p]) := inferInstance

end TauCeti.Huber.Padic
