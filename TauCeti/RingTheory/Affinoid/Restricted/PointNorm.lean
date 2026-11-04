/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.PowerBounded
public import TauCeti.RingTheory.Affinoid.Restricted

/-!
# Classical points of quotients of restricted series

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, carrying a complete
ultrametric algebra norm, and let `I` be an ideal of the restricted series algebra
`A⟨X₁, …, Xₖ⟩`. This file shows that each variable `Xᵢ` has absolute value at most one at every
classical point of `A⟨X₁, …, Xₖ⟩ ⧸ I`: the variable is power-bounded in `A⟨X₁, …, Xₖ⟩`, hence has
supremum seminorm at most one, and the classical points of the quotient are among those of
`A⟨X₁, …, Xₖ⟩`. Rational and Laurent fraction algebras are quotients of this form.

## Main results

* `TauCeti.IsAffinoidAlgebra.pointNorm_quotientMk_X_le_one`: each variable has absolute value at
  most one at every classical point of a quotient of `A⟨X₁, …, Xₖ⟩`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§6.1.4 and
  7.2.2.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IsAffinoidAlgebra

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormedAlgebra K A] [CompleteSpace A]

/-- **The variables have absolute value at most one.** For an affinoid algebra `A` with a complete
ultrametric algebra norm and an ideal `I` of `A⟨X₁, …, Xₖ⟩`, each variable `Xᵢ` has absolute value
at most one at every classical point of `A⟨X₁, …, Xₖ⟩ ⧸ I`. -/
theorem pointNorm_quotientMk_X_le_one {k : ℕ} (hA : IsAffinoidAlgebra K A)
    {I : Ideal (IsRestricted.subring (R := A) (fun _ : Fin k ↦ 1))}
    (x : MaximalSpectrum (IsRestricted.subring (R := A) (fun _ : Fin k ↦ 1) ⧸ I)) (i : Fin k) :
    pointNorm K x (Ideal.Quotient.mk I ⟨X i, isRestricted_X _ i⟩) ≤ 1 := by
  -- The variable is power-bounded in `A⟨X⟩`, whose points include the points of the quotient.
  have hT := hA.isRestricted_subring (τ := Fin k)
  rw [← Ideal.Quotient.mkₐ_eq_mk K, ← (hT.quotient I).pointNorm_maximalSpectrumComap]
  exact (hT.pointNorm_le_supSeminorm _ _).trans
    (hT.isPowerBounded_iff_supSeminorm_le_one.mp (isPowerBounded_X i))

end IsAffinoidAlgebra

end TauCeti
