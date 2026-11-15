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

The cup product on `H¹(K, E[m])` along the Weil pairing, as well as the cup product on
`H¹(K, E₁[φ]) × H¹(K, E₂[φ̂])` along the isogeny Weil pairing, commutes with extension of fields.
Composing with `H²(K, μ_m) → Br K` (respectively `H²(K, μ_{deg φ}) → Br K`) gives bilinear
Brauer-valued pairings whose base change is the same pairing on the restricted classes. In
particular, their local invariants can be computed using the kernels and Weil pairing over each
completion, without choosing a rational torsion basis or roots of unity in the ground field, and
without casts across the base-change equalities for the degree and dual isogeny.

## Main results

* `WeierstrassCurve.torsionH1WeilPairing_torsionRes` and
  `WeierstrassCurve.brBaseChange_torsionWeilBrauerPairing`: localization of the torsion Weil cup
  product and its Brauer class.
* `TauCeti.Isogeny.kerH1WeilPairing_kerRes` and
  `TauCeti.Isogeny.brBaseChange_kerWeilBrauerPairing`: localization of the isogeny Weil cup
  product and its Brauer class along `kerRes` and `dualKerRes`.

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

open WeierstrassCurve TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open Hom (ofIsogeny)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

variable {L : Type*} [Field L] [Algebra K L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- Base change of kernel points commutes with the coefficient-level isogeny Weil pairing after
transporting roots of unity along `(φ.baseChange L).degree = φ.degree`. -/
theorem kerCoeffWeilPairing_kerCoeffBaseChange
    (hnL : IsUnit ((φ.baseChange L).degree : L))
    (P : (ofIsogeny φ).KerCoeff) (Q : (ofIsogeny φ.dual).KerCoeff) :
    kummerCoeffPow L (φ.degree_baseChange L).dvd
        (kummerCoeffBaseChange φ.degree τ (φ.kerCoeffWeilPairing hn P Q)) =
      (φ.baseChange L).kerCoeffWeilPairing hnL
        (φ.kerCoeffBaseChange τ P) (φ.dualKerCoeffBaseChange τ Q) := by
  have hdiv : φ.degree / (φ.baseChange L).degree = 1 := by
    rw [φ.degree_baseChange L]
    exact Nat.div_self φ.degree_pos
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  have hbase := φ.coe_kerCoeffWeilPairing_baseChange hn τ hnL P Q
    (φ.kerCoeffBaseChange τ P) (φ.dualKerCoeffBaseChange τ Q)
    (φ.coe_kerCoeffBaseChange τ P) (φ.coe_dualKerCoeffBaseChange τ Q)
  simpa only [coe_toMul_kummerCoeffPow, hdiv, pow_one, toMul_kummerCoeffBaseChange, Units.coe_map,
    MonoidHom.coe_ofClass] using hbase.symm

omit [W₁.IsElliptic] [W₂.IsElliptic] in
private def kummerCoeffPowBaseChange {n m : ℕ} (h : m ∣ n) :
    KummerCoeff K n →+ KummerCoeff L m :=
  (kummerCoeffPow L h).toAddMonoidHom.comp (kummerCoeffBaseChange n τ)

omit [W₁.IsElliptic] [W₂.IsElliptic] in
private theorem kummerCoeffPowBaseChange_smul {n m : ℕ} (h : m ∣ n)
    (g : AbsoluteGaloisGroup L) (y : KummerCoeff K n) :
    kummerCoeffPowBaseChange τ h (absoluteGaloisGroupMap τ g • y) =
      g • kummerCoeffPowBaseChange τ h y := by
  rw [kummerCoeffPowBaseChange, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    kummerCoeffBaseChange_smul]
  exact (kummerCoeffPow L h).map_smul g (kummerCoeffBaseChange n τ y)

omit [W₁.IsElliptic] [W₂.IsElliptic] in
private theorem explicitCoeff2_kummerCoeffPow_explicitMap2
    {n m : ℕ} (h : m ∣ n) (x : H2 (AbsoluteGaloisGroup K) (KummerCoeff K n)) :
    explicitCoeff2 _ _ (kummerCoeffPow L h) continuous_of_discreteTopology
        (explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K n)
          (AbsoluteGaloisGroup L) (KummerCoeff L n)
          (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange n τ)
          continuous_of_discreteTopology (kummerCoeffBaseChange_smul n τ) x) =
      explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K n)
        (AbsoluteGaloisGroup L) (KummerCoeff L m)
        (absoluteGaloisGroupMap τ) (kummerCoeffPowBaseChange τ h)
        continuous_of_discreteTopology (kummerCoeffPowBaseChange_smul τ h) x := by
  have hcomp := explicitMap2_comp (AbsoluteGaloisGroup K) (KummerCoeff K n)
    (AbsoluteGaloisGroup L) (KummerCoeff L n)
    (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange n τ)
    continuous_of_discreteTopology (kummerCoeffBaseChange_smul n τ)
    (AbsoluteGaloisGroup L) (KummerCoeff L m)
    (ContinuousMonoidHom.id _) (kummerCoeffPow L h : KummerCoeff L n →+ KummerCoeff L m)
    continuous_of_discreteTopology (fun g y ↦ (kummerCoeffPow L h).map_smul g y)
  rw [explicitCoeff2_eq_explicitMap2, ← AddMonoidHom.comp_apply]
  refine DFunLike.congr_fun
    (hcomp.symm.trans (explicitMap2_congr_of_eq (AbsoluteGaloisGroup K) (KummerCoeff K n)
      (AbsoluteGaloisGroup L) (KummerCoeff L m) _ _ _ _ ?_ (AddMonoidHom.ext fun _ ↦ rfl))) x
  ext g
  simp only [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_id, id_eq]

/-- **Restriction to a field extension commutes with the isogeny Weil cup product.** The level
identity `(φ.baseChange L).degree = φ.degree` is transported on `KummerCoeff` via `kummerCoeffPow`,
which acts as the identity on underlying roots of unity. -/
theorem kerH1WeilPairing_kerRes
    (hnL : IsUnit ((φ.baseChange L).degree : L))
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    (φ.baseChange L).kerH1WeilPairing hnL (φ.kerRes τ a) (φ.dualKerRes τ b) =
      explicitCoeff2 _ _ (kummerCoeffPow L (φ.degree_baseChange L).dvd)
        continuous_of_discreteTopology
        (explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K φ.degree)
          (AbsoluteGaloisGroup L) (KummerCoeff L φ.degree)
          (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange φ.degree τ)
          continuous_of_discreteTopology (kummerCoeffBaseChange_smul φ.degree τ)
          (φ.kerH1WeilPairing hn a b)) := by
  refine Eq.trans ?_
    (explicitCoeff2_kummerCoeffPow_explicitMap2 τ (φ.degree_baseChange L).dvd
      (φ.kerH1WeilPairing hn a b)).symm
  rw [(φ.baseChange L).kerH1WeilPairing_eq_explicitCup11 hnL,
    φ.kerRes_eq_explicitMap1 τ, φ.dualKerRes_eq_explicitMap1 τ,
    φ.kerH1WeilPairing_eq_explicitCup11 hn]
  exact (explicitMap2_explicitCup11
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
    (fN := φ.dualKerCoeffBaseChange τ)
    (fP := kummerCoeffPowBaseChange τ (φ.degree_baseChange L).dvd)
    (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
    (hcP := continuous_of_discreteTopology) (hfM := φ.kerCoeffBaseChange_smul τ)
    (hfN := φ.dualKerCoeffBaseChange_smul τ)
    (hfP := kummerCoeffPowBaseChange_smul τ (φ.degree_baseChange L).dvd)
    (hpair := fun P Q ↦ φ.kerCoeffWeilPairing_kerCoeffBaseChange hn τ hnL P Q)
    a b).symm

/-- **The Brauer class of an isogeny Weil cup product localizes to the isogeny Weil cup product of
the restricted classes.** This applies to every extension, including archimedean and nonarchimedean
completions. -/
theorem brBaseChange_kerWeilBrauerPairing
    (hnL : IsUnit ((φ.baseChange L).degree : L))
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    brBaseChange K L (φ.kerWeilBrauerPairing hn a b) =
      (φ.baseChange L).kerWeilBrauerPairing hnL (φ.kerRes τ a) (φ.dualKerRes τ b) := by
  have hdeg := φ.degree_baseChange L
  have hdiv : φ.degree / (φ.baseChange L).degree = 1 := by
    rw [hdeg]
    exact Nat.div_self φ.degree_pos
  rw [kerWeilBrauerPairing_apply, kerWeilBrauerPairing_apply,
    brBaseChange_h2MuToBr_muNRepH2Equiv φ.degree τ, φ.kerH1WeilPairing_kerRes hn τ hnL a b,
    h2MuToBr_muNRepH2Equiv_eq_explicitCoeff2, h2MuToBr_muNRepH2Equiv_eq_explicitCoeff2]
  refine congrArg (unitsRepH2Equiv L) ?_
  conv_rhs => rw [← AddMonoidHom.comp_apply, ← explicitCoeff2_comp]
  refine congrArg (fun f ↦ explicitCoeff2 _ _ f continuous_of_discreteTopology _) ?_
  ext x
  apply Additive.toMul.injective
  simp only [DistribMulActionHom.comp_apply, kummerCoeffInclHom_apply, toMul_kummerCoeffIncl,
    coe_toMul_kummerCoeffPow, hdiv, pow_one]

end TauCeti.Isogeny
