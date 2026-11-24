/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Brauer
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
`φ_L`. Since the degrees of `φ` and `φ_L` also agree only propositionally, the comparison is
stated for the Brauer-valued pairings, in which the level of the roots of unity does not appear.

## Main results

* `WeierstrassCurve.brBaseChange_torsionWeilBrauerPairing`: the Brauer class of the Weil cup
  product on `H¹(K, E[m])` localizes to the Weil cup product of the restricted classes.
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

/-- The isogeny Weil pairing with values in the units of the separable closure. -/
private def kerCoeffUnitsPairing :
    (ofIsogeny φ).KerCoeff →+ (ofIsogeny φ.dual).KerCoeff →+ UnitsCoeff K :=
  (AddMonoidHom.compHom (kummerCoeffInclHom K φ.degree).toAddMonoidHom).comp
    (φ.kerCoeffWeilPairing hn)

private theorem kerCoeffUnitsPairing_apply (P : (ofIsogeny φ).KerCoeff)
    (Q : (ofIsogeny φ.dual).KerCoeff) :
    φ.kerCoeffUnitsPairing hn P Q = kummerCoeffInclHom K φ.degree (φ.kerCoeffWeilPairing hn P Q) :=
  (rfl)

private theorem kerCoeffUnitsPairing_smul (g : AbsoluteGaloisGroup K)
    (P : (ofIsogeny φ).KerCoeff) (Q : (ofIsogeny φ.dual).KerCoeff) :
    φ.kerCoeffUnitsPairing hn (g • P) (g • Q) = g • φ.kerCoeffUnitsPairing hn P Q := by
  rw [kerCoeffUnitsPairing_apply, kerCoeffUnitsPairing_apply, kerCoeffWeilPairing_smul,
    map_smul]

/-- The Brauer-valued isogeny pairing is the cup product along the unit-valued Weil pairing,
read in the Brauer group through unit coefficients. -/
private theorem kerWeilBrauerPairing_eq_explicitCup11
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    φ.kerWeilBrauerPairing hn a b =
      unitsRepH2Equiv K (explicitCup11 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
        (ofIsogeny φ.dual).KerCoeff (UnitsCoeff K) (φ.kerCoeffUnitsPairing hn)
        continuous_of_discreteTopology (φ.kerCoeffUnitsPairing_smul hn) a b) := by
  rw [kerWeilBrauerPairing_apply, h2MuToBr_muNRepH2Equiv_eq_explicitCoeff2,
    kerH1WeilPairing_eq_explicitCup11]
  congr 1
  simpa only [explicitCoeff1_id, AddMonoidHom.id_apply] using
    explicitCoeff2_explicitCup11 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
      (ofIsogeny φ.dual).KerCoeff (KummerCoeff K φ.degree) (ofIsogeny φ).KerCoeff
      (ofIsogeny φ.dual).KerCoeff (UnitsCoeff K) (φ.kerCoeffWeilPairing hn)
      continuous_of_discreteTopology (φ.kerCoeffWeilPairing_smul hn)
      (φ.kerCoeffUnitsPairing hn) continuous_of_discreteTopology
      (φ.kerCoeffUnitsPairing_smul hn) (DistribMulActionHom.id _) (DistribMulActionHom.id _)
      (kummerCoeffInclHom K φ.degree) continuous_id continuous_id
      continuous_of_discreteTopology (fun _ _ ↦ (rfl)) a b

/-- The unit-valued isogeny Weil pairing commutes with extension of fields. -/
private theorem unitsCoeffBaseChange_kerCoeffUnitsPairing
    (hnL : IsUnit ((φ.baseChange L).degree : L)) (P : (ofIsogeny φ).KerCoeff)
    (Q : (ofIsogeny φ.dual).KerCoeff) :
    unitsCoeffBaseChange τ (φ.kerCoeffUnitsPairing hn P Q) =
      (φ.baseChange L).kerCoeffUnitsPairing hnL (φ.kerCoeffBaseChange τ P)
        (φ.dualKerCoeffBaseChange τ Q) := by
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_unitsCoeffBaseChange, kerCoeffUnitsPairing_apply, kerCoeffUnitsPairing_apply,
    kummerCoeffInclHom_apply, kummerCoeffInclHom_apply, toMul_kummerCoeffIncl,
    toMul_kummerCoeffIncl, Units.coe_map, MonoidHom.coe_ofClass]
  exact (φ.coe_kerCoeffWeilPairing_baseChange hn τ hnL P Q _ _ (coe_kerCoeffBaseChange τ φ P)
    (coe_dualKerCoeffBaseChange τ φ Q)).symm

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
  rw [kerWeilBrauerPairing_eq_explicitCup11, kerWeilBrauerPairing_eq_explicitCup11,
    brBaseChange_apply K L τ, AddEquiv.symm_apply_apply, kerRes_eq_explicitMap1,
    dualKerRes_eq_explicitMap1]
  congr 1
  exact explicitMap2_explicitCup11 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
    (ofIsogeny φ.dual).KerCoeff (UnitsCoeff K) (φ.kerCoeffUnitsPairing hn)
    continuous_of_discreteTopology (φ.kerCoeffUnitsPairing_smul hn) (AbsoluteGaloisGroup L)
    (ofIsogeny (φ.baseChange L)).KerCoeff (ofIsogeny (φ.baseChange L).dual).KerCoeff
    (UnitsCoeff L) ((φ.baseChange L).kerCoeffUnitsPairing hnL) continuous_of_discreteTopology
    ((φ.baseChange L).kerCoeffUnitsPairing_smul hnL) (absoluteGaloisGroupMap τ)
    (φ.kerCoeffBaseChange τ) (φ.dualKerCoeffBaseChange τ) (unitsCoeffBaseChange τ)
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    (φ.kerCoeffBaseChange_smul τ) (φ.dualKerCoeffBaseChange_smul τ)
    (unitsCoeffBaseChange_smul τ) (φ.unitsCoeffBaseChange_kerCoeffUnitsPairing τ hn hnL) a b

end TauCeti.Isogeny
