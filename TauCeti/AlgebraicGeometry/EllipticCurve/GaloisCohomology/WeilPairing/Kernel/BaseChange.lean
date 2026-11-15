/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Restriction
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality

/-!
# Localization of the isogeny Weil cup product

The Weil cup product on the kernels of an isogeny and its dual commutes with arbitrary
field extension. The dual-kernel restriction lands in the kernel of the dual of the
base-changed isogeny. The roots-of-unity map similarly accounts for preservation of degree.
Thus the localization formula uses the native pairing over the extension, without asking
callers to transport cohomology classes across equalities of isogenies or torsion exponents.

This compatibility identifies the local cup products with restrictions of a single global
class, as needed when applying Brauer reciprocity to isogeny Selmer groups.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §§2 and 4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve ContCohomology
open Hom (ofIsogeny coe_smul_kerCoeff)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  {L : Type*} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- Coordinate base change on the dual kernel, with target the kernel of the dual of the
base-changed isogeny. -/
def dualKerCoeffBaseChange :
    (ofIsogeny φ.dual).KerCoeff →+ (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  ((W₂.pointCoeffBaseChange τ).comp
    ((ofIsogeny φ.dual).pointCoeffMap : W₂.PointCoeff →+ W₁.PointCoeff).ker.subtype).codRestrict _
    fun P ↦ by
      have hd : φ.dual.baseChange L = (φ.baseChange L).dual := φ.dual_map (algebraMap K L)
      rw [← hd]
      exact φ.dual.pointCoeffBaseChange_mem_kerCoeff τ P.2

/-- Dual-kernel base change applies the ordinary coordinate map. -/
@[simp]
theorem coe_dualKerCoeffBaseChange (Q : (ofIsogeny φ.dual).KerCoeff) :
    (φ.dualKerCoeffBaseChange τ Q : (W₂⁄L).PointCoeff) = W₂.pointCoeffBaseChange τ Q :=
  (rfl)

/-- Dual-kernel base change is equivariant for restriction of Galois automorphisms. -/
@[simp]
theorem dualKerCoeffBaseChange_smul (g : AbsoluteGaloisGroup L)
    (Q : (ofIsogeny φ.dual).KerCoeff) :
    φ.dualKerCoeffBaseChange τ (absoluteGaloisGroupMap τ g • Q) =
      g • φ.dualKerCoeffBaseChange τ Q := by
  apply Subtype.ext
  simp only [coe_dualKerCoeffBaseChange, coe_smul_kerCoeff,
    pointCoeffBaseChange_smul]

/-- Restriction of first cohomology of the dual kernel, landing in the kernel of the dual
of the base-changed isogeny. -/
def dualKerRes :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+
      H1 (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff :=
  explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (φ.dualKerCoeffBaseChange τ)
    continuous_of_discreteTopology (φ.dualKerCoeffBaseChange_smul τ)

/-- Dual-kernel restriction is pullback along the coordinate base-change map. -/
theorem dualKerRes_eq_explicitMap1 :
    φ.dualKerRes τ = explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ)
      (φ.dualKerCoeffBaseChange τ) continuous_of_discreteTopology
      (φ.dualKerCoeffBaseChange_smul τ) :=
  (rfl)

omit [W₁.IsElliptic] [W₂.IsElliptic] in
/-- The coefficient map on roots of unity, indexed by the degrees of the original and
base-changed isogenies. -/
def weilCoeffBaseChange : KummerCoeff K φ.degree →+ KummerCoeff L (φ.baseChange L).degree :=
  ((Subgroup.inclusion
    (H := rootsOfUnity φ.degree (SeparableClosure L))
    (K := rootsOfUnity (φ.baseChange L).degree (SeparableClosure L))
    (by
      have hd : (φ.baseChange L).degree = φ.degree := φ.degree_map (algebraMap K L)
      rw [hd])).comp (restrictRootsOfUnity τ φ.degree)).toAdditive

omit [W₁.IsElliptic] [W₂.IsElliptic] in
/-- The degree-indexed coefficient map applies the embedding to the underlying unit. -/
@[simp]
theorem toMul_weilCoeffBaseChange (x : KummerCoeff K φ.degree) :
    ((φ.weilCoeffBaseChange τ x).toMul : (SeparableClosure L)ˣ) =
      Units.map (τ : SeparableClosure K →* SeparableClosure L) x.toMul := by
  apply Units.ext
  simp only [weilCoeffBaseChange, MonoidHom.coe_toAdditive, Function.comp_apply,
    toMul_ofMul, MonoidHom.comp_apply, Subgroup.coe_inclusion,
    restrictRootsOfUnity_coe_apply, Units.coe_map]
  rfl

omit [W₁.IsElliptic] [W₂.IsElliptic] in
/-- The degree-indexed roots-of-unity map is Galois-equivariant. -/
theorem weilCoeffBaseChange_smul (g : AbsoluteGaloisGroup L) (x : KummerCoeff K φ.degree) :
    φ.weilCoeffBaseChange τ (absoluteGaloisGroupMap τ g • x) =
      g • φ.weilCoeffBaseChange τ x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simpa only [Additive.toMul_smul, rootsOfUnity.coe_smul, AlgEquiv.smul_units_def,
    Units.coe_map, toMul_weilCoeffBaseChange, toMul_kummerCoeffBaseChange] using
    congrArg (fun y : KummerCoeff L φ.degree ↦ y.toMul.val.val)
      (kummerCoeffBaseChange_smul φ.degree τ g x)

variable (hn : IsUnit (φ.degree : K))

/-- The kernel Weil pairing commutes with the native coefficient restriction maps,
including their degree and dual identifications. -/
theorem weilCoeffBaseChange_kerCoeffWeilPairing
    (P : (ofIsogeny φ).KerCoeff) (Q : (ofIsogeny φ.dual).KerCoeff) :
    φ.weilCoeffBaseChange τ (φ.kerCoeffWeilPairing hn P Q) =
      (φ.baseChange L).kerCoeffWeilPairing
        (by
          have hd : (φ.baseChange L).degree = φ.degree := φ.degree_map (algebraMap K L)
          simpa only [hd, map_natCast] using hn.map (algebraMap K L))
        (φ.kerCoeffBaseChange τ P) (φ.dualKerCoeffBaseChange τ Q) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rw [toMul_weilCoeffBaseChange, Units.coe_map]
  exact (φ.coe_kerCoeffWeilPairing_baseChange hn τ _ P Q _ _
    (φ.coe_kerCoeffBaseChange τ P) (φ.coe_dualKerCoeffBaseChange τ Q)).symm

/-- Restricting the isogeny Weil cup product to any field extension is the native Weil
cup product of the restricted kernel classes over that extension. -/
theorem kerH1WeilPairing_kerRes
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    (φ.baseChange L).kerH1WeilPairing
        (by
          have hd : (φ.baseChange L).degree = φ.degree := φ.degree_map (algebraMap K L)
          simpa only [hd, map_natCast] using hn.map (algebraMap K L))
        (φ.kerRes τ a) (φ.dualKerRes τ b) =
      explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K φ.degree)
        (AbsoluteGaloisGroup L) (KummerCoeff L (φ.baseChange L).degree)
        (absoluteGaloisGroupMap τ) (φ.weilCoeffBaseChange τ)
        continuous_of_discreteTopology (φ.weilCoeffBaseChange_smul τ)
        (φ.kerH1WeilPairing hn a b) := by
  simp only [kerH1WeilPairing_eq_explicitCup11, kerRes_eq_explicitMap1,
    dualKerRes_eq_explicitMap1]
  exact (explicitMap2_explicitCup11
    (G := AbsoluteGaloisGroup K) (M := (ofIsogeny φ).KerCoeff)
    (N := (ofIsogeny φ.dual).KerCoeff) (P := KummerCoeff K φ.degree)
    (H := AbsoluteGaloisGroup L) (M' := (ofIsogeny (φ.baseChange L)).KerCoeff)
    (N' := (ofIsogeny (φ.baseChange L).dual).KerCoeff)
    (P' := KummerCoeff L (φ.baseChange L).degree)
    (μ := φ.kerCoeffWeilPairing hn) (hμ := continuous_of_discreteTopology)
    (hequiv := φ.kerCoeffWeilPairing_smul hn)
    (μ' := (φ.baseChange L).kerCoeffWeilPairing
      (by
        have hd : (φ.baseChange L).degree = φ.degree := φ.degree_map (algebraMap K L)
        simpa only [hd, map_natCast] using hn.map (algebraMap K L)))
    (hμ' := continuous_of_discreteTopology)
    (hequiv' := (φ.baseChange L).kerCoeffWeilPairing_smul _)
    (φ := absoluteGaloisGroupMap τ)
    (fM := φ.kerCoeffBaseChange τ) (fN := φ.dualKerCoeffBaseChange τ)
    (fP := φ.weilCoeffBaseChange τ)
    (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
    (hcP := continuous_of_discreteTopology) (hfM := φ.kerCoeffBaseChange_smul τ)
    (hfN := φ.dualKerCoeffBaseChange_smul τ) (hfP := φ.weilCoeffBaseChange_smul τ)
    (hpair := φ.weilCoeffBaseChange_kerCoeffWeilPairing τ hn) a b).symm

end TauCeti.Isogeny
