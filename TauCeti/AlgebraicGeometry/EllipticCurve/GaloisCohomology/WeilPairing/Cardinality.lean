/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Cardinality
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem
import TauCeti.RepresentationTheory.Homological.ContCohomology.NatCardComparison
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability

/-!
# Orders of local isogeny cohomology groups

For an isogeny `φ : E₁ → E₂` of degree invertible in a nonarchimedean local field `K`,
local Tate duality gives `#H²(K, E₁[φ]) = #E₂(K)[φ̂]`. Over a finite compatible extension
of `ℚ_p`, the local Euler characteristic therefore computes `#H¹(K, E₁[φ])` from the
rational kernels of `φ` and `φ̂` and the isogeny degree. These are the
ambient cohomology orders needed to upgrade orthogonality of local Kummer images to
exact annihilator statements. No rationality assumption on the geometric kernel is imposed.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, Theorems 2.1 and 2.8.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory
open Hom (ofIsogeny)

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

include hn in
/-- The second cohomology of an isogeny kernel has the order of the rational dual kernel. -/
theorem natCard_H2_kerCoeff :
    Nat.card (H2 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ.dual).pointMapHom.ker := by
  classical
  have := hn.neZero_natCast
  let e := (muNRepH2Equiv φ.degree K).trans (h2MuEquivZMod K hn)
  have hd := explicitCoeff0_bijective (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff
    (φ.kerCoeffWeilDual_bijective hn)
  have he : Nat.card (H0 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
        (KummerCoeff K φ.degree))) =
      Nat.card (H0 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :=
    (Nat.card_congr (Equiv.ofBijective _ hd)).symm
  rw [Nat.card_congr (Equiv.ofBijective _
    (dualityMap2_kummerCoeff_bijective hn (ofIsogeny φ).KerCoeff
      φ.degree_nsmul_kerCoeff_eq_zero)), e.natCard_addMonoidHom_zmod]
  · rw [he, Hom.natCard_H0_kerCoeff]
  · intro x
    apply Subtype.ext
    apply InternalHom.ext
    apply AddMonoidHom.ext
    intro P
    simp only [AddSubgroup.coe_nsmul, InternalHom.toAddMonoidHom_nsmul,
      AddMonoidHom.nsmul_apply, ZeroMemClass.coe_zero,
      InternalHom.toAddMonoidHom_zero, AddMonoidHom.zero_apply]
    rw [← map_nsmul, φ.degree_nsmul_kerCoeff_eq_zero, map_zero]

/-- Over a finite extension of `ℚ_p`, the order of first isogeny cohomology is the product of
the two rational kernel orders and the inverse normalized absolute value of the degree.
The prime `p` is allowed to divide the isogeny degree. -/
theorem natCard_H1_kerCoeff (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p] :
    Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker *
        p ^ (Module.finrank ℚ_[p] K * padicValNat p φ.degree) := by
  classical
  have := FinitePadicExtension.charZero K p
  have hn : IsUnit (φ.degree : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr φ.degree_pos.ne')
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  let := AddCommGroup.zmodModule φ.degree_nsmul_kerCoeff_eq_zero
  -- Tate's formula uses the algebraic-closure Galois group, whereas point coefficients use
  -- the separable-closure group. Restrict the discrete representation along their equivalence.
  let A := ofDiscreteModule (ZMod φ.degree) (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
  let X : GalRep φ.degree K := TopRep.res (absoluteGaloisGroupRestrictEquiv K).toMonoidHom A
  have hX : IsSmoothDiscrete (ZMod φ.degree) X :=
    (ofDiscreteModule_isSmoothDiscrete _ _ _).res
      (absoluteGaloisGroupRestrictEquiv K).continuous
  have : Fact (IsSmoothDiscrete (ZMod φ.degree) X) := ⟨hX⟩
  have : DiscreteTopology X.V := hX.discreteTopology
  let := TopRep.distribMulAction X
  have := hX.continuousSMul
  let e : (ofIsogeny φ).KerCoeff ≃+ X.V := AddEquiv.refl _
  have hecont : Continuous e := continuous_of_discreteTopology
  have hecont' : Continuous e.symm :=
    @continuous_of_discreteTopology X.V _ hX.discreteTopology _ _ _
  have he (g : Field.absoluteGaloisGroup K) (x : (ofIsogeny φ).KerCoeff) :
      e (absoluteGaloisGroupRestrictEquiv K g • x) = g • e x := by
    rw [TopRep.distribMulAction_smul, ContRepresentation.restrict_apply_apply]
    exact (ofDiscreteModule_ρ_apply_apply (R := ZMod φ.degree)
      (absoluteGaloisGroupRestrictEquiv K g) x).symm
  -- Transport all three explicit cohomology orders through the same compatible pair.
  have h₀ := Nat.card_congr (Equiv.ofBijective _ (explicitMap0_bijective
    (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
    (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
    (absoluteGaloisGroupRestrictEquiv K).surjective e.toAddMonoidHom e.bijective he))
  have h₁ := Nat.card_congr (explicitMap1Equiv
    (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (Field.absoluteGaloisGroup K) X.V
    (absoluteGaloisGroupRestrictEquiv K) e hecont hecont' he).toEquiv
  have h₂ := Nat.card_congr (explicitMap2Equiv
    (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (Field.absoluteGaloisGroup K) X.V
    (absoluteGaloisGroupRestrictEquiv K) e hecont hecont' he).toEquiv
  have : Finite X.V := Finite.of_equiv _ e.toEquiv
  -- Apply the Euler characteristic, then identify H⁰ and H² with the rational kernels.
  have h := eulerCharacteristic_mixed p K φ.degree φ.degree_pos.ne' X inferInstance
  -- Supply the topology-dependent instances explicitly for the restricted representation.
  have hc₀ := @TopRep.natCard_H0_eq_natCard_continuousCohomology
    _ _ _ _ _ _ _ X hX.discreteTopology
  have hc₁ := @TopRep.natCard_H1_eq_natCard_continuousCohomology
    _ _ _ _ _ _ _ X hX.discreteTopology hX.continuousSMul
  have hc₂ := @TopRep.natCard_H2_eq_natCard_continuousCohomology
    _ _ _ _ _ _ _ X hX.discreteTopology hX.continuousSMul inferInstance
  rw [← hc₀, ← hc₁, ← hc₂, ← h₀, ← h₁, ← h₂,
    Hom.natCard_H0_kerCoeff, φ.natCard_H2_kerCoeff hn,
    ← Nat.card_congr e.toEquiv, φ.natCard_kerCoeff] at h
  exact h

end TauCeti.Isogeny
