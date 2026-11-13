/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny
import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Cardinality

/-!
# The order of second local isogeny cohomology

For an isogeny `φ` of degree invertible in a nonarchimedean local field `K`, local Tate
duality identifies the order of `H²(K, E₁[φ])` with the order of the rational dual kernel
`E₂(K)[φ̂]`.

This is a cohomology order needed when comparing the local Kummer images of
an isogeny and its dual with their annihilators. No rationality assumption is imposed on
the geometric kernels or on the roots of unity.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, Theorem 2.1.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve ContCohomology ClassFieldTheory Hom

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

include hn in
/-- For an isogeny `φ` of degree invertible in a nonarchimedean local field `K`,
`#H²(K, E₁[φ]) = #E₂(K)[φ̂]`. -/
theorem natCard_H2_kerCoeff [DecidableEq K] :
    Nat.card (H2 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ.dual).pointMapHom.ker := by
  have := hn.neZero_natCast
  rw [Nat.card_congr (ofIsogeny φ.dual).kerPointMapEquivInvariants.toEquiv]
  rw [natCard_H2_eq_natCard_H0_internalHom hn (ofIsogeny φ).KerCoeff
    φ.degree_nsmul_kerCoeff_eq_zero]
  exact Nat.card_congr (Equiv.ofBijective _
    (explicitCoeff0_bijective _ _ (φ.kerCoeffWeilDual_bijective hn))).symm

end TauCeti.Isogeny
