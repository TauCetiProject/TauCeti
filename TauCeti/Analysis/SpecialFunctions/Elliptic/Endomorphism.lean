/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Quadratic
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Lattice

/-!
# Complex scalar multiplier orders of period lattices and elliptic curves

For a complex period lattice `Λ`, its left order `Λ.leftOrder` (`Submodule.leftOrder`) is the
`ℤ`-subalgebra `{α ∈ ℂ | α Λ ⊆ Λ}` of complex scalar endomorphisms preserving `Λ`. Because
rescaling a period pair preserves `Submodule.leftOrder`, `leftOrder` descends to homothety classes
(`PeriodPair.HomothetyClass.leftOrder`) and is invariant under Weierstrass coordinate changes and
`j`-equivalence on complex elliptic curves. Only complex scalar lattice multipliers
(`Submodule.leftOrder`) are formalized here; no comparison with algebraic elliptic-curve
endomorphisms (`TauCeti.Isogeny.Hom`) is proved in this file.

## Main definitions

* `PeriodPair.HomothetyClass.leftOrder`: the complex scalar multiplier order of a homothety class
  of period lattices.

## Main results

* `PeriodPair.Homothetic.leftOrder_lattice_eq`,
  `PeriodPair.leftOrder_lattice_eq_of_weierstrassCurve_j_eq`: homothety and `j`-invariance of the
  complex scalar multiplier order of a period lattice.
* `WeierstrassCurve.leftOrder_variableChange_periodLattice`,
  `WeierstrassCurve.leftOrder_periodLattice_eq_of_j_eq`: coordinate-change and `j`-invariance of
  the period-lattice scalar multiplier order of a complex elliptic curve.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer, 2009, Theorems VI.4.1(b)
  and VI.6.1.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Springer, 1994,
  Proposition II.1.1.
* D. A. Cox, *Primes of the Form x² + ny²*, §10B and §11A.
-/

public noncomputable section

open Complex UpperHalfPlane WeierstrassCurve
open scoped Pointwise

namespace PeriodPair

/-- Homothetic period pairs have the same complex multiplier order. -/
theorem Homothetic.leftOrder_lattice_eq {L L' : PeriodPair} (h : L.Homothetic L') :
    L.lattice.leftOrder = L'.lattice.leftOrder := by
  obtain ⟨c, hc⟩ := homothetic_def.mp h; rw [hc, leftOrder_lattice_smul]

/-- Period pairs with the same Weierstrass `j`-invariant have the same complex multiplier order. -/
theorem leftOrder_lattice_eq_of_weierstrassCurve_j_eq {L L' : PeriodPair}
    (h : L.weierstrassCurve.j = L'.weierstrassCurve.j) :
    L.lattice.leftOrder = L'.lattice.leftOrder :=
  (homothetic_iff_weierstrassCurve_j_eq.mpr h).leftOrder_lattice_eq

namespace HomothetyClass

/-- The complex multiplier order (`Submodule.leftOrder`) of a homothety class of period lattices. -/
def leftOrder : HomothetyClass → Subalgebra ℤ ℂ :=
  lift (fun L ↦ L.lattice.leftOrder) fun _ _ h ↦ h.leftOrder_lattice_eq

/-- On the homothety class of `L`, `leftOrder` is the left order of `L.lattice`. -/
@[simp] theorem leftOrder_mk (L : PeriodPair) : (mk L).leftOrder = L.lattice.leftOrder :=
  lift_mk _ _ L

end HomothetyClass

end PeriodPair

namespace WeierstrassCurve

/-- Isomorphic complex elliptic curves have the same period-lattice multiplier order. -/
@[simp] theorem leftOrder_variableChange_periodLattice (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (C : VariableChange ℂ) : (C • E).periodLattice.leftOrder = E.periodLattice.leftOrder := by
  rw [variableChange_periodLattice]
  exact E.periodLattice.leftOrder_smul C.u.isUnit.isRegular.left (by simp)

/-- Complex elliptic curves with the same `j`-invariant have the same period-lattice multiplier
order. -/
theorem leftOrder_periodLattice_eq_of_j_eq {E E' : WeierstrassCurve ℂ} [E.IsElliptic]
    [E'.IsElliptic] (h : E.j = E'.j) : E.periodLattice.leftOrder = E'.periodLattice.leftOrder := by
  obtain ⟨L, C, hu, rfl⟩ := E.exists_periodPair_variableChange_smul_eq
  obtain ⟨L', C', hu', rfl⟩ := E'.exists_periodPair_variableChange_smul_eq
  rw [periodLattice_eq_iff.mpr ⟨C, hu, rfl⟩, periodLattice_eq_iff.mpr ⟨C', hu', rfl⟩]
  rw [variableChange_j, variableChange_j] at h
  exact PeriodPair.leftOrder_lattice_eq_of_weierstrassCurve_j_eq h

end WeierstrassCurve
