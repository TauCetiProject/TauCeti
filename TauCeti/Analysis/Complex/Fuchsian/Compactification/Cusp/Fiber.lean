/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Map

/-!
# Fibres over cusps in compactified Fuchsian quotient maps

The fibre of the map of compactified Fuchsian quotients over an adjoined cusp consists exactly
of the cusp orbits above it. Together with the boundary-orbit fibre equivalence for finite-index
subgroups, this lets orbit and stabilizer calculations on the boundary count these points.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)} (h : Δ ≤ Γ)

/-- The fibre over an adjoined cusp in a compactified quotient map is the fibre of the
cusp-orbit map. -/
def cuspOrbitFiberEquivCompactifiedFiber (C : Γ.CuspOrbit) :
    {D : Δ.CuspOrbit // cuspOrbitMap h D = C} ≃
      {y : Δ.CompactifiedQuotient //
        compactifiedQuotientMap h y = .ofCusp C} where
  toFun D := ⟨.ofCusp D.1, by
    simpa only [compactifiedQuotientMap_ofCusp] using
      (congrArg (CompactifiedQuotient.ofCusp (Γ := Γ)) D.2)⟩
  invFun y := by
    obtain ⟨y, hy⟩ := y
    cases y with
    | ofQuotient p =>
        simp only [compactifiedQuotientMap_ofQuotient] at hy
        cases hy
    | ofCusp D =>
        simp only [compactifiedQuotientMap_ofCusp] at hy
        exact ⟨D, CompactifiedQuotient.ofCusp.inj hy⟩
  left_inv D := by cases D; rfl
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    cases y with
    | ofQuotient p =>
        simp only [compactifiedQuotientMap_ofQuotient] at hy
        cases hy
    | ofCusp D => rfl

/-- The cusp-fibre equivalence inserts a cusp orbit as an adjoined point. -/
@[simp]
theorem cuspOrbitFiberEquivCompactifiedFiber_apply (C : Γ.CuspOrbit)
    (D : {D : Δ.CuspOrbit // cuspOrbitMap h D = C}) :
    (cuspOrbitFiberEquivCompactifiedFiber h C D).1 = .ofCusp D.1 :=
  (rfl)

end Subgroup
