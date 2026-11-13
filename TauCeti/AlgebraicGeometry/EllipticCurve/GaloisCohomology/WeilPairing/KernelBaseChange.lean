/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Restriction

import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability

/-!
# Base change of the isogeny Weil pairing

The pairing of the kernels of an isogeny and its dual commutes with field extension.
We compare values in the ambient separable closure: the two roots-of-unity subgroups are
indexed by degrees that agree propositionally, and the base change of the dual agrees
propositionally with the dual of the base change. Specifying the images of the two points
avoids casts across either equality.

This compatibility supplies the coefficient-level localization identity for cup products
along the isogeny Weil pairing. It follows from the characteristic identity
`e_φ(P, φ R) = e_n(P, R)` and base-change compatibility of `e_n`, without a choice of torsion
basis or roots of unity in the base field.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §§2 and 4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology
open Hom (ofIsogeny)

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- The isogeny Weil pairing commutes with every field extension. The hypotheses specify
only the underlying images of the two kernel points; the values are compared in the ambient
separable closure, so no casts between degree-indexed roots of unity are needed. -/
theorem coe_kerCoeffWeilPairing_baseChange
    (hnL : IsUnit ((φ.baseChange L).degree : L))
    (P : (ofIsogeny φ).KerCoeff) (Q : (ofIsogeny φ.dual).KerCoeff)
    (P' : (ofIsogeny (φ.baseChange L)).KerCoeff)
    (Q' : (ofIsogeny (φ.baseChange L).dual).KerCoeff)
    (hP : (P' : (W₁⁄L).PointCoeff) = W₁.pointCoeffBaseChange τ P)
    (hQ : (Q' : (W₂⁄L).PointCoeff) = W₂.pointCoeffBaseChange τ Q) :
    ((φ.baseChange L).kerCoeffWeilPairing hnL P' Q').toMul.val.val =
      τ ((φ.kerCoeffWeilPairing hn P Q).toMul.val.val) := by
  classical
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  obtain ⟨R, rfl⟩ := φ.torsionCoeffToDualKerCoeff_surjective Q
  have hd : (φ.baseChange L).degree = φ.degree := φ.degree_map (algebraMap K L)
  -- Reindex only the torsion level, retaining the ordinary coordinate base-change map.
  let R' : (W₁⁄L).TorsionCoeff (φ.baseChange L).degree :=
    ⟨W₁.pointCoeffBaseChange τ R, by
      simpa only [hd, coe_torsionCoeffBaseChange] using
        (W₁.torsionCoeffBaseChange τ φ.degree R).2⟩
  have hR' : (R' : (W₁⁄L).PointCoeff) = W₁.pointCoeffBaseChange τ R := rfl
  have hQ' : (φ.baseChange L).torsionCoeffToDualKerCoeff R' = Q' := by
    apply Subtype.ext
    rw [coe_torsionCoeffToDualKerCoeff, hR', pointCoeffMap_baseChange_pointCoeffBaseChange,
      hQ, coe_torsionCoeffToDualKerCoeff]
  rw [← hQ', kerCoeffWeilPairing_torsionCoeffToDualKerCoeff,
    kerCoeffWeilPairing_torsionCoeffToDualKerCoeff]
  exact W₁.coe_torsionCoeffWeilPairing_baseChange hn τ _ hnL hd
    (φ.kerCoeffToTorsionCoeff P) R
    ((φ.baseChange L).kerCoeffToTorsionCoeff P') R'
    (by simpa only [coe_kerCoeffToTorsionCoeff] using hP) hR'

end TauCeti.Isogeny
