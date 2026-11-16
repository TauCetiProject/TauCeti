/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber

/-!
# Orders of geometric isogeny kernels

The geometric kernel of a separable isogeny has order equal to the degree. This identification
expresses local cohomology order formulas in terms of isogeny degrees.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10.
-/

public noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve ContCohomology Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- The geometric kernel coefficient module of a separable isogeny has order equal to its degree. -/
theorem natCard_kerCoeff_eq_degree
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    Nat.card (ofIsogeny φ).KerCoeff = φ.degree := by
  classical
  let ψ := φ.baseChange (SeparableClosure K)
  have hmem (P : W₁.PointCoeff) :
      P ∈ ((ofIsogeny φ).pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker ↔
        W₁.pointCoeffEquiv.symm P ∈ ψ.toPointHom.ker := by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, AddMonoidHom.mem_ker,
      ← Hom.pointMap_mapSeparableClosure_ofIsogeny_eq_toPointHom,
      ← Hom.pointCoeffEquiv_symm_pointCoeffMap]
    exact W₂.pointCoeffEquiv.symm.map_eq_zero_iff.symm
  rw [Nat.card_congr (Equiv.subtypeEquiv W₁.pointCoeffEquiv.symm.toEquiv hmem),
    ψ.card_ker_toPointHom_eq_degree]
  exact degree_map φ _

end TauCeti.Isogeny
