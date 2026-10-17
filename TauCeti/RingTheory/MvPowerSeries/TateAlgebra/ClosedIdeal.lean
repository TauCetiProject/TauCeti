/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import TauCeti.Analysis.Normed.Group.Quotient

import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.RingTheory.Huber.Normed

/-!
# Closed ideals of Tate algebras

Every ideal of a restricted power-series algebra `K⟨X₁/c₁, …, Xₙ/cₙ⟩` in finitely many
variables over a complete ultrametric field is closed for the Gauss norm. The algebra is
noetherian, and in a noetherian Banach algebra over a nontrivially normed ultrametric field every
ideal is closed.

The instance makes Mathlib's `Ideal.Quotient.normedCommRing` apply to every quotient of a Tate
algebra. Together with `Ideal.Quotient.normedAlgebra`, `Submodule.Quotient.completeSpace` and
`Submodule.Quotient.instIsUltrametricDist`, the residue Gauss norm on such a quotient is a
complete ultrametric algebra norm.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§5.2.6–5.2.7.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)]

/-- Every ideal of a finite-variable restricted power-series algebra over a complete ultrametric
field is closed for the Gauss norm. -/
instance isClosed_ideal_isRestrictedSubring (I : Ideal (IsRestricted.subring (R := K) c)) :
    IsClosed (I : Set (IsRestricted.subring (R := K) c)) := by
  have := isNoetherianRing_isRestricted_subring (K := K) (c := c)
  let : TauCeti.Huber.IsTateRing (IsRestricted.subring (R := K) c) :=
    TauCeti.Huber.IsTateRing.of_normedAlgebra K _
  exact TauCeti.Huber.isClosed_of_isNoetherian I

end TauCeti.MvPowerSeries
