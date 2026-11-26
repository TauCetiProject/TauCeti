/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem
import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability

/-!
# Orders of local torsion and isogeny cohomology groups

For an elliptic curve `E` over a nonarchimedean local field `K` and an integer `m` invertible in
`K`, local Tate duality identifies the order of `H²(K, E[m])` with the order of the rational
`m`-torsion `E(K)[m]`. Over a finite compatible extension of `ℚ_p`, the local Euler characteristic
then computes `#H¹(K, E[m]) = (#E(K)[m] · p ^ ([K : ℚ_p] v_p(m)))²` for every nonzero `m`,
including when `p` divides `m`.

Likewise, for an isogeny `φ` of degree invertible in `K`, local Tate duality identifies the order
of `H²(K, E₁[φ])` with the order of the rational dual kernel `E₂(K)[φ̂]`. Over a finite compatible
extension of `ℚ_p`, the local Euler characteristic computes the order of `H¹(K, E₁[φ])` from the
two rational kernel orders and the degree, including when `p` divides the degree.

These cohomology orders are needed when comparing the local Kummer images of `[m]`, and of an
isogeny and its dual, with their annihilators. No rationality assumption is imposed on the
geometric kernels or on the roots of unity.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, Theorems 2.1 and 2.8.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- For an elliptic curve over a nonarchimedean local field `K` and `m` invertible in `K`,
`#H²(K, E[m]) = #E(K)[m]`. -/
theorem natCard_H2_torsionCoeff [DecidableEq K] (m : ℕ) (hm : IsUnit (m : K)) :
    Nat.card (H2 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) := by
  have := hm.neZero_natCast
  rw [Nat.card_congr (W.baseTorsionEquivInvariants m).toEquiv,
    natCard_H2_eq_natCard_H0_internalHom hm (W.TorsionCoeff m)
      fun P ↦ AddSubgroup.torsionBy.nsmul P]
  exact Nat.card_congr (Equiv.ofBijective _
    (explicitCoeff0_bijective _ _ (W.torsionCoeffWeilDual_bijective m hm))).symm

/-- Over a finite compatible extension of `ℚ_p`, the order of `H¹(K, E[m])` for `m ≠ 0` is the
square of `#E(K)[m] · p ^ ([K : ℚ_p] v_p(m))`, including when `p` divides `m`. -/
theorem natCard_H1_torsionCoeff [DecidableEq K] {m : ℕ} (hm0 : m ≠ 0) (p : ℕ) [Fact p.Prime]
    [FinitePadicExtension K p] :
    Nat.card (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) =
      (Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) *
        p ^ (Module.finrank ℚ_[p] K * padicValNat p m)) ^ 2 := by
  have := FinitePadicExtension.charZero K p
  have : NeZero m := ⟨hm0⟩
  have hm : IsUnit (m : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hm0)
  -- `padicValNat.pow` is deprecated in favor of `Nat.multiplicity_pow`, so pass between
  -- `padicValNat` and `multiplicity` via `Nat.padicValNat_def`.
  rw [natCard_H1_eq_mul p K (W.TorsionCoeff m),
    ← Nat.card_congr (W.baseTorsionEquivInvariants m).toEquiv,
    W.natCard_H2_torsionCoeff m hm, W.natCard_torsionCoeff hm, Nat.padicValNat_def,
    Nat.multiplicity_pow m 2, ← Nat.padicValNat_def]
  ring

end WeierstrassCurve

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

/-- Over a finite extension of `ℚ_p`, the order of first isogeny cohomology is the product of
the two rational kernel orders and the inverse normalized absolute value of the degree.
The prime `p` is allowed to divide the isogeny degree. -/
theorem natCard_H1_kerCoeff [DecidableEq K] (p : ℕ) [Fact p.Prime]
    [FinitePadicExtension K p] :
    Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker *
        p ^ (Module.finrank ℚ_[p] K * padicValNat p φ.degree) := by
  classical
  have := FinitePadicExtension.charZero K p
  have hn : IsUnit (φ.degree : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr φ.degree_pos.ne')
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  rw [natCard_H1_eq_mul p K (ofIsogeny φ).KerCoeff,
    ← Nat.card_congr (ofIsogeny φ).kerPointMapEquivInvariants.toEquiv,
    φ.natCard_H2_kerCoeff hn, φ.natCard_kerCoeff_eq_degree]

end TauCeti.Isogeny
