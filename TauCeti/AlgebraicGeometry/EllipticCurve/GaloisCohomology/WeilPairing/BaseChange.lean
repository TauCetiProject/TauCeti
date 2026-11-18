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

The same holds for an isogeny `φ : E₁ → E₂` of degree invertible in `K`: the Brauer class of the
cup product of `a ∈ H¹(K, E₁[φ])` and `b ∈ H¹(K, E₂[φ̂])` along the isogeny Weil pairing
localizes to the cup product, for the base change `φ_L`, of the restriction of `a` to
`H¹(L, E₁[φ_L])` and of `b` to `H¹(L, E₂[(φ_L)^])`. The degree of `φ_L` equals that of `φ` only
propositionally, so the comparison of roots of unity goes through
`TauCeti.ClassFieldTheory.brBaseChange_h2MuToBr_muNRepH2Equiv_of_toMul_eq`.

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

open WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory

open Hom (ofIsogeny)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

variable {L : Type*} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- **The Brauer class of an isogeny Weil cup product localizes to the isogeny Weil cup product of
the restricted classes**, for the base change of the isogeny. This applies to every extension,
including archimedean and nonarchimedean completions, and to every embedding of separable
closures. -/
theorem brBaseChange_kerWeilBrauerPairing
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    brBaseChange K L (φ.kerWeilBrauerPairing hn a b) =
      (φ.baseChange L).kerWeilBrauerPairing (φ.isUnit_degree_baseChange hn)
        (φ.kerRes τ a) (φ.dualKerRes τ b) := by
  have hnL := φ.isUnit_degree_baseChange (K := L) hn
  have hd : (φ.baseChange L).degree = φ.degree := φ.degree_map (algebraMap K L)
  let f : KummerCoeff K φ.degree →+ KummerCoeff L (φ.baseChange L).degree :=
    (kummerCoeffPow L hd.dvd : KummerCoeff L φ.degree →+ _).comp
      (kummerCoeffBaseChange φ.degree τ)
  have hfτ (y : KummerCoeff K φ.degree) : ((f y).toMul : (SeparableClosure L)ˣ) =
      Units.map (τ : SeparableClosure K →* SeparableClosure L) y.toMul := by
    simp [f, hd, Nat.div_self φ.degree_pos]
  have hf (g : AbsoluteGaloisGroup L) (y : KummerCoeff K φ.degree) :
      f (absoluteGaloisGroupMap τ g • y) = g • f y := by
    simp [f, kummerCoeffBaseChange_smul]
  have hpair (P : (ofIsogeny φ).KerCoeff) (Q : (ofIsogeny φ.dual).KerCoeff) :
      f (φ.kerCoeffWeilPairing hn P Q) = (φ.baseChange L).kerCoeffWeilPairing hnL
        (φ.kerCoeffBaseChange τ P) (φ.dualKerCoeffBaseChange τ Q) := by
    refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
    rw [φ.coe_kerCoeffWeilPairing_baseChange hn τ hnL P Q _ _ (φ.coe_kerCoeffBaseChange τ P)
      (φ.coe_dualKerCoeffBaseChange τ Q), hfτ, Units.coe_map, MonoidHom.coe_ofClass]
  rw [kerWeilBrauerPairing_apply, kerWeilBrauerPairing_apply,
    brBaseChange_h2MuToBr_muNRepH2Equiv_of_toMul_eq φ.degree τ f hf hfτ,
    φ.kerH1WeilPairing_eq_explicitCup11 hn, (φ.baseChange L).kerH1WeilPairing_eq_explicitCup11 hnL,
    explicitMap2_explicitCup11
    (G := AbsoluteGaloisGroup K) (M := (ofIsogeny φ).KerCoeff)
    (N := (ofIsogeny φ.dual).KerCoeff) (P := KummerCoeff K φ.degree)
    (μ := φ.kerCoeffWeilPairing hn) (hμ := continuous_of_discreteTopology)
    (hequiv := φ.kerCoeffWeilPairing_smul hn) (H := AbsoluteGaloisGroup L)
    (M' := (ofIsogeny (φ.baseChange L)).KerCoeff)
    (N' := (ofIsogeny (φ.baseChange L).dual).KerCoeff)
    (P' := KummerCoeff L (φ.baseChange L).degree)
    (μ' := (φ.baseChange L).kerCoeffWeilPairing hnL) (hμ' := continuous_of_discreteTopology)
    (hequiv' := (φ.baseChange L).kerCoeffWeilPairing_smul hnL)
    (φ := absoluteGaloisGroupMap τ) (fM := φ.kerCoeffBaseChange τ)
    (fN := φ.dualKerCoeffBaseChange τ) (fP := f)
    (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
    (hcP := continuous_of_discreteTopology) (hfM := φ.kerCoeffBaseChange_smul τ)
    (hfN := φ.dualKerCoeffBaseChange_smul τ) (hfP := hf) (hpair := hpair)]
  simp only [kerRes_eq_explicitMap1, dualKerRes_eq_explicitMap1]

end TauCeti.Isogeny
