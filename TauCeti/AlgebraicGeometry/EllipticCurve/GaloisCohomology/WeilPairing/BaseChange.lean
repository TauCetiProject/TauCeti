/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Brauer
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Kummer.BaseChange

/-!
# Localization of the Weil cup product

The cup product on `H¹(K, E[m])` along the Weil pairing commutes with extension of fields.
Composing with `H²(K, μ_m) → Br K` gives a bilinear Brauer-valued pairing, whose base change
is the same pairing on the restricted classes. In particular, its local invariants can be
computed using the torsion and Weil pairing of the curve over each completion, without choosing
a rational torsion basis or roots of unity in the ground field.

The same holds for an isogeny `φ : E₁ → E₂` of degree `n` invertible in `K` and the cup product
`H¹(K, E₁[φ]) × H¹(K, E₂[φ̂]) → H²(K, μ_n)` along the isogeny Weil pairing. Here the second
factor is restricted into the kernel of the dual of the base change `φ_L` of `φ`
(`TauCeti.Isogeny.dualKerRes`): the dual of `φ_L` is the base change of `φ̂`, but only
propositionally, and the local Tate pairing of `φ_L` is stated on the kernel of the dual of
`φ_L`. At the level of `H²` the restriction uses the coefficient map from `μ_n` to the roots of
unity indexed by the degree of `φ_L`. In the induced Brauer-valued pairing the level of the roots
of unity no longer appears.

## Main results

* `WeierstrassCurve.brBaseChange_torsionWeilBrauerPairing`: the Brauer class of the Weil cup
  product on `H¹(K, E[m])` localizes to the Weil cup product of the restricted classes.
* `TauCeti.Isogeny.kerH1WeilPairing_kerRes`: the isogeny Weil cup product itself commutes with
  restriction, before passing to the Brauer group.
* `TauCeti.Isogeny.brBaseChange_kerWeilBrauerPairing`: the Brauer class of the isogeny Weil cup
  product localizes to the isogeny Weil cup product of `φ_L` on the restricted classes.

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
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  {L : Type*} [Field L] [Algebra K L] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-! ### Localization of the isogeny Weil cup product -/

variable (hn : IsUnit (φ.degree : K))

/-- The kernel Weil pairing commutes with restriction on roots of unity, with the exponent
reindexed by degree preservation under base change. -/
theorem kummerCoeffBaseChangeOfDvd_kerCoeffWeilPairing
    (hnL : IsUnit ((φ.baseChange L).degree : L))
    (P : (ofIsogeny φ).KerCoeff) (Q : (ofIsogeny φ.dual).KerCoeff) :
    kummerCoeffBaseChangeOfDvd τ (φ.degree_map (algebraMap K L)).symm.dvd
        (φ.kerCoeffWeilPairing hn P Q) =
      (φ.baseChange L).kerCoeffWeilPairing hnL
        (φ.kerCoeffBaseChange τ P) (φ.dualKerCoeffBaseChange τ Q) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rw [toMul_kummerCoeffBaseChangeOfDvd, Units.coe_map]
  exact (φ.coe_kerCoeffWeilPairing_baseChange hn τ hnL P Q _ _
    (coe_kerCoeffBaseChange τ φ P) (coe_dualKerCoeffBaseChange τ φ Q)).symm

/-- Restricting the isogeny Weil cup product to any field extension gives the native Weil
cup product of the restricted kernel classes over that extension. -/
theorem kerH1WeilPairing_kerRes
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    let hnL : IsUnit ((φ.baseChange L).degree : L) := by
      have hd : (φ.baseChange L).degree = φ.degree := φ.degree_map (algebraMap K L)
      simpa only [hd, map_natCast] using hn.map (algebraMap K L)
    (φ.baseChange L).kerH1WeilPairing hnL (φ.kerRes τ a) (φ.dualKerRes τ b) =
      explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K φ.degree)
        (AbsoluteGaloisGroup L) (KummerCoeff L (φ.baseChange L).degree)
        (absoluteGaloisGroupMap τ)
        (kummerCoeffBaseChangeOfDvd τ (φ.degree_map (algebraMap K L)).symm.dvd)
        continuous_of_discreteTopology (kummerCoeffBaseChangeOfDvd_smul τ _)
        (φ.kerH1WeilPairing hn a b) := by
  intro hnL
  simp only [kerH1WeilPairing_eq_explicitCup11, kerRes_eq_explicitMap1, dualKerRes_eq_explicitMap1]
  exact (explicitMap2_explicitCup11 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
    (ofIsogeny φ.dual).KerCoeff (KummerCoeff K φ.degree) (φ.kerCoeffWeilPairing hn)
    continuous_of_discreteTopology (φ.kerCoeffWeilPairing_smul hn) (AbsoluteGaloisGroup L)
    (ofIsogeny (φ.baseChange L)).KerCoeff (ofIsogeny (φ.baseChange L).dual).KerCoeff
    (KummerCoeff L (φ.baseChange L).degree) ((φ.baseChange L).kerCoeffWeilPairing hnL)
    continuous_of_discreteTopology ((φ.baseChange L).kerCoeffWeilPairing_smul hnL)
    (absoluteGaloisGroupMap τ) (φ.kerCoeffBaseChange τ) (φ.dualKerCoeffBaseChange τ)
    (kummerCoeffBaseChangeOfDvd τ (φ.degree_map (algebraMap K L)).symm.dvd)
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    (kerCoeffBaseChange_smul τ φ) (dualKerCoeffBaseChange_smul τ φ)
    (kummerCoeffBaseChangeOfDvd_smul τ _)
    (φ.kummerCoeffBaseChangeOfDvd_kerCoeffWeilPairing τ hn hnL) a b).symm

/-- **The Brauer class of the isogeny Weil cup product localizes to the isogeny Weil cup product
of the base change**: for classes `a ∈ H¹(K, E₁[φ])` and `b ∈ H¹(K, E₂[φ̂])`, the base change to
`L` of the Brauer class of their cup product is the Brauer class of the cup product of their
restrictions, along the base change `φ_L` of `φ`. This applies to every extension, including
archimedean and nonarchimedean completions. -/
theorem brBaseChange_kerWeilBrauerPairing (hnL : IsUnit ((φ.baseChange L).degree : L))
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    brBaseChange K L (φ.kerWeilBrauerPairing hn a b) =
      (φ.baseChange L).kerWeilBrauerPairing hnL (φ.kerRes τ a) (φ.dualKerRes τ b) := by
  rw [kerWeilBrauerPairing_apply, kerWeilBrauerPairing_apply, φ.kerH1WeilPairing_kerRes τ hn,
    brBaseChange_h2MuToBr_muNRepH2Equiv_of_dvd φ.degree τ
      (m := (φ.baseChange L).degree) (φ.degree_map (algebraMap K L)).symm.dvd]

end TauCeti.Isogeny
