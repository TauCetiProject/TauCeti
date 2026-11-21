/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Brauer
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Kummer.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree

/-!
# Localization of the Weil cup product

The cup product on `H¹(K, E[m])` along the Weil pairing commutes with extension of fields.
Composing with `H²(K, μ_m) → Br K` gives a bilinear Brauer-valued pairing, whose base change
is the same pairing on the restricted classes. In particular, its local invariants can be
computed using the torsion and Weil pairing of the curve over each completion, without choosing
a rational torsion basis or roots of unity in the ground field.

The same holds for the Brauer-valued cup product along the Weil pairing of an isogeny `φ` and its
dual, when the degree of `φ` is invertible in `K`, hence also in `L`
(`TauCeti.Isogeny.brBaseChange_kerWeilBrauerPairing`): its base change is the pairing for the
base change of `φ`, applied to the restricted classes `TauCeti.Isogeny.kerRes` and
`TauCeti.Isogeny.dualKerRes`. Its proof follows the torsion versions
`WeierstrassCurve.torsionH1WeilPairing_torsionRes` and
`WeierstrassCurve.brBaseChange_torsionWeilBrauerPairing` above.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §§2 and 4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : K))

variable {L : Type*} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- Restriction to a field extension commutes with the Weil cup product.
The embedding of separable closures is arbitrary. -/
theorem torsionH1WeilPairing_torsionRes
    (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    (W⁄L).torsionH1WeilPairing m (by simpa using hm.map (algebraMap K L))
        (W.torsionRes τ m a) (W.torsionRes τ m b) =
      explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K m) (AbsoluteGaloisGroup L)
        (KummerCoeff L m) (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange m τ)
        continuous_of_discreteTopology (kummerCoeffBaseChange_smul m τ)
        (W.torsionH1WeilPairing m hm a b) := by
  simp only [torsionH1WeilPairing_eq_explicitCup11, torsionRes_eq_explicitMap1]
  exact (explicitMap2_explicitCup11
    (G := AbsoluteGaloisGroup K) (M := W.TorsionCoeff m) (N := W.TorsionCoeff m)
    (P := KummerCoeff K m) (μ := W.torsionCoeffWeilPairing m hm)
    (hμ := continuous_of_discreteTopology) (hequiv := W.torsionCoeffWeilPairing_smul m hm)
    (H := AbsoluteGaloisGroup L) (M' := (W⁄L).TorsionCoeff m)
    (N' := (W⁄L).TorsionCoeff m) (P' := KummerCoeff L m)
    (μ' := (W⁄L).torsionCoeffWeilPairing m (by simpa using hm.map (algebraMap K L)))
    (hμ' := continuous_of_discreteTopology)
    (hequiv' := (W⁄L).torsionCoeffWeilPairing_smul m _)
    (φ := absoluteGaloisGroupMap τ) (fM := W.torsionCoeffBaseChange τ m)
    (fN := W.torsionCoeffBaseChange τ m) (fP := kummerCoeffBaseChange m τ)
    (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
    (hcP := continuous_of_discreteTopology) (hfM := W.torsionCoeffBaseChange_smul τ m)
    (hfN := W.torsionCoeffBaseChange_smul τ m) (hfP := kummerCoeffBaseChange_smul m τ)
    (hpair := fun P Q ↦ (W.torsionCoeffWeilPairing_torsionCoeffBaseChange hm τ P Q).symm)
    a b).symm

/-- The Brauer class of a Weil cup product localizes to the Weil cup product of the restricted
classes. This applies to every extension, including archimedean and nonarchimedean completions. -/
theorem brBaseChange_torsionWeilBrauerPairing
    (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    brBaseChange K L (W.torsionWeilBrauerPairing m hm a b) =
      (W⁄L).torsionWeilBrauerPairing m (by simpa using hm.map (algebraMap K L))
        (W.torsionRes τ m a) (W.torsionRes τ m b) := by
  rw [torsionWeilBrauerPairing_apply, torsionWeilBrauerPairing_apply,
    brBaseChange_h2MuToBr_muNRepH2Equiv m τ, torsionH1WeilPairing_torsionRes]

end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

variable {L : Type*} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- Restriction to a field extension commutes with the isogeny Weil cup product, at the common
level `deg φ`: against any pairing of the restricted kernels whose values are the images under `τ`
of those of the isogeny Weil pairing. -/
private theorem explicitCup11_kerRes_dualKerRes
    (μ' : (ofIsogeny (φ.baseChange L)).KerCoeff →+
      (ofIsogeny (φ.baseChange L).dual).KerCoeff →+ KummerCoeff L φ.degree)
    (hequiv' : ∀ (g : AbsoluteGaloisGroup L) P Q, μ' (g • P) (g • Q) = g • μ' P Q)
    (hpair : ∀ P Q, (μ' (φ.kerCoeffBaseChange τ P) (φ.dualKerCoeffBaseChange τ Q)).toMul.val.val =
      τ ((φ.kerCoeffWeilPairing hn P Q).toMul.val.val))
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    explicitCup11 (AbsoluteGaloisGroup L) _ _ (KummerCoeff L φ.degree) μ'
        continuous_of_discreteTopology hequiv' (φ.kerRes τ a) (φ.dualKerRes τ b) =
      explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K φ.degree) (AbsoluteGaloisGroup L)
        (KummerCoeff L φ.degree) (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange φ.degree τ)
        continuous_of_discreteTopology (kummerCoeffBaseChange_smul φ.degree τ)
        (φ.kerH1WeilPairing hn a b) := by
  rw [kerH1WeilPairing_eq_explicitCup11, kerRes_eq_explicitMap1, dualKerRes_eq_explicitMap1]
  exact (explicitMap2_explicitCup11
    (G := AbsoluteGaloisGroup K) (M := (ofIsogeny φ).KerCoeff) (N := (ofIsogeny φ.dual).KerCoeff)
    (P := KummerCoeff K φ.degree) (μ := φ.kerCoeffWeilPairing hn)
    (hμ := continuous_of_discreteTopology) (hequiv := φ.kerCoeffWeilPairing_smul hn)
    (H := AbsoluteGaloisGroup L) (M' := (ofIsogeny (φ.baseChange L)).KerCoeff)
    (N' := (ofIsogeny (φ.baseChange L).dual).KerCoeff) (P' := KummerCoeff L φ.degree)
    (μ' := μ') (hμ' := continuous_of_discreteTopology) (hequiv' := hequiv')
    (φ := absoluteGaloisGroupMap τ) (fM := φ.kerCoeffBaseChange τ)
    (fN := φ.dualKerCoeffBaseChange τ) (fP := kummerCoeffBaseChange φ.degree τ)
    (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
    (hcP := continuous_of_discreteTopology) (hfM := φ.kerCoeffBaseChange_smul τ)
    (hfN := φ.dualKerCoeffBaseChange_smul τ) (hfP := kummerCoeffBaseChange_smul φ.degree τ)
    (hpair := fun P Q ↦ Additive.toMul.injective <| Subtype.ext <| Units.ext <| by
      simp only [toMul_kummerCoeffBaseChange, Units.coe_map, MonoidHom.coe_ofClass]
      exact (hpair P Q).symm)
    a b).symm

/-- Base change of the Brauer class of an isogeny Weil cup, against any pairing of the restricted
kernels at a level `n'` equal to the degree whose values are the images under `τ` of those of
the isogeny Weil pairing. The level is a variable, so it can be identified with `deg φ`. -/
private theorem brBaseChange_kerWeilBrauerPairing_of_eq (n' : ℕ) (hd : n' = φ.degree)
    (μ' : (ofIsogeny (φ.baseChange L)).KerCoeff →+
      (ofIsogeny (φ.baseChange L).dual).KerCoeff →+ KummerCoeff L n')
    (hequiv' : ∀ (g : AbsoluteGaloisGroup L) P Q, μ' (g • P) (g • Q) = g • μ' P Q)
    (hpair : ∀ P Q, (μ' (φ.kerCoeffBaseChange τ P) (φ.dualKerCoeffBaseChange τ Q)).toMul.val.val =
      τ ((φ.kerCoeffWeilPairing hn P Q).toMul.val.val))
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    brBaseChange K L (φ.kerWeilBrauerPairing hn a b) =
      h2MuToBr n' L (muNRepH2Equiv n' L
        (explicitCup11 (AbsoluteGaloisGroup L) _ _ (KummerCoeff L n') μ'
          continuous_of_discreteTopology hequiv' (φ.kerRes τ a) (φ.dualKerRes τ b))) := by
  subst hd
  rw [kerWeilBrauerPairing_apply, brBaseChange_h2MuToBr_muNRepH2Equiv φ.degree τ,
    φ.explicitCup11_kerRes_dualKerRes hn τ μ' hequiv' hpair]

/-- The Brauer class of an isogeny Weil cup localizes to the isogeny Weil cup of the restricted
classes, for the base change of `φ` and its dual. The degree of `φ` is invertible in `K`, hence
in `L`. This applies to every extension, including archimedean and nonarchimedean completions. -/
theorem brBaseChange_kerWeilBrauerPairing
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    brBaseChange K L (φ.kerWeilBrauerPairing hn a b) =
      (φ.baseChange L).kerWeilBrauerPairing
        (by rw [degree_baseChange]; simpa using hn.map (algebraMap K L))
        (φ.kerRes τ a) (φ.dualKerRes τ b) := by
  rw [(φ.baseChange L).kerWeilBrauerPairing_apply,
    (φ.baseChange L).kerH1WeilPairing_eq_explicitCup11]
  exact φ.brBaseChange_kerWeilBrauerPairing_of_eq hn τ _ φ.degree_baseChange _ _
    (fun P Q ↦ φ.coe_kerCoeffWeilPairing_baseChange hn τ _ P Q _ _
      (coe_kerCoeffBaseChange τ φ P) (coe_dualKerCoeffBaseChange τ φ Q)) a b

end TauCeti.Isogeny
