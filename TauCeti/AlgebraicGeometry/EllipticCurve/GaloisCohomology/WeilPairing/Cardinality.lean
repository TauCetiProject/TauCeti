/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Cardinality
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Explicit
import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability

/-!
# Orders of local isogeny cohomology groups

For an isogeny `φ` of degree invertible in a nonarchimedean local field `K`, local Tate
duality identifies the order of `H²(K, E₁[φ])` with the order of `H⁰(K, E₂[φ̂])`.
Over a finite extension of `ℚ_p`, the local Euler characteristic then computes
`#H¹(K, E₁[φ])` as `#E₁(K)[φ] · #E₂(K)[φ̂] · p ^ ([K : ℚ_p] v_p(deg φ))`.

These are the ambient cohomology orders needed when comparing the local Kummer images of
an isogeny and its dual with their annihilators. No rationality assumption is imposed on
the geometric kernels or on the roots of unity.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, Theorems 2.1 and 2.8.
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
/-- Local duality computes second cohomology from the rational invariants of the dual kernel. -/
theorem natCard_H2_kerCoeff [DecidableEq K] :
    Nat.card (H2 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ.dual).pointMapHom.ker := by
  have := hn.neZero_natCast
  rw [Nat.card_congr (ofIsogeny φ.dual).kerPointMapEquivInvariants.toEquiv]
  rw [natCard_H2_eq_natCard_H0_internalHom hn (ofIsogeny φ).KerCoeff
    φ.degree_nsmul_kerCoeff_eq_zero]
  exact Nat.card_congr (Equiv.ofBijective _
    (explicitCoeff0_bijective _ _ (φ.kerCoeffWeilDual_bijective hn))).symm

section MixedCharacteristic

variable (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]

/-- The order of first cohomology of an isogeny kernel over a finite extension of `ℚ_p`,
including when the residue characteristic divides the kernel order. -/
theorem natCard_H1_kerCoeff [DecidableEq K] :
    Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ).pointMapHom.ker *
        Nat.card (ofIsogeny φ.dual).pointMapHom.ker *
        p ^ (Module.finrank ℚ_[p] K * padicValNat p φ.degree) := by
  have := FinitePadicExtension.charZero K p
  have : NeZero φ.degree := ⟨φ.degree_pos.ne'⟩
  have hn : IsUnit (φ.degree : K) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (NeZero.ne _))
  have := (φ.isSeparable_dual_and_self_iff.2 hn.ne_zero).2
  rw [natCard_H1_eq_mul p K _,
    φ.natCard_H2_kerCoeff hn, φ.natCard_kerCoeff_eq_degree,
    Nat.card_congr (ofIsogeny φ).kerPointMapEquivInvariants.toEquiv]

end MixedCharacteristic

end TauCeti.Isogeny
