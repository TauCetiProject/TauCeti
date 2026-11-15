/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Congr
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Brauer
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Kummer.BaseChange

/-!
# Localization of the Weil cup product

The cup products on `H¹(K, E[m])` and on `H¹(K, E₁[φ]) × H¹(K, E₂[φ̂])` along the Weil pairing
commute with extension of fields. Composing with `H²(K, μ_n) → Br K` gives bilinear Brauer-valued
pairings whose base change along any extension `L/K` agrees with the native pairing over `L` on
the restricted classes. In particular, their local invariants can be computed using the torsion,
isogeny kernels, and Weil pairings over each completion, without choosing rational torsion bases
or roots of unity in the ground field.

## Main results

* `WeierstrassCurve.torsionH1WeilPairing_torsionRes` and
  `WeierstrassCurve.brBaseChange_torsionWeilBrauerPairing`: localization of the `[m]`-torsion Weil
  cup product and its Brauer class.
* `TauCeti.Isogeny.kerH1WeilPairing_kerRes` and
  `TauCeti.Isogeny.brBaseChange_kerWeilBrauerPairing`: localization of the isogeny Weil cup
  product and its Brauer class.

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
open Hom (ofIsogeny kerCoeffCongrHom kerH1Congr)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

omit [W₁.IsElliptic] [W₂.IsElliptic] in
/-- Base change preserves the degree of an isogeny. -/
@[simp]
theorem degree_baseChange (L : Type*) [Field L] [Algebra K L] :
    (φ.baseChange L).degree = φ.degree :=
  φ.degree_map (algebraMap K L)

/-- Base change commutes with the dual isogeny on `Hom` carriers. -/
theorem ofIsogeny_dual_baseChange (L : Type*) [Field L] [Algebra K L] :
    ofIsogeny (φ.dual.baseChange L) = ofIsogeny (φ.baseChange L).dual :=
  congrArg ofIsogeny (φ.dual_map (algebraMap K L))

omit [W₁.IsElliptic] [W₂.IsElliptic] in
/-- If `deg φ` is invertible in `K`, then `deg (φ.baseChange L)` is invertible in any extension `L`
of `K`. -/
theorem isUnit_degree_baseChange_of_isUnit (hn : IsUnit (φ.degree : K))
    (L : Type*) [Field L] [Algebra K L] :
    IsUnit ((φ.baseChange L).degree : L) := by
  rw [φ.degree_baseChange L]
  simpa using hn.map (algebraMap K L)

omit [W₁.IsElliptic] [W₂.IsElliptic] in
/-- Over a field of characteristic zero, the degree of an isogeny is invertible. -/
theorem isUnit_degree [CharZero K] : IsUnit (φ.degree : K) :=
  (Nat.cast_ne_zero.mpr φ.degree_pos.ne').isUnit

omit [W₁.IsElliptic] [W₂.IsElliptic] in
/-- Over a base field of characteristic zero, the degree of `φ.baseChange L` is invertible in
every field extension `L` of `K`. -/
theorem isUnit_degree_baseChange [CharZero K] (L : Type*) [Field L] [Algebra K L] :
    IsUnit ((φ.baseChange L).degree : L) :=
  φ.isUnit_degree_baseChange_of_isUnit φ.isUnit_degree L

variable (hn : IsUnit (φ.degree : K))
  {L : Type*} [Field L] [Algebra K L] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- **The isogeny Weil pairing commutes with field extension on `KummerCoeff`**: transporting
points along `τ` and `φ.ofIsogeny_dual_baseChange L` matches transporting roots of unity along `τ`
and `φ.degree_baseChange L`. -/
theorem kerCoeffWeilPairing_kerCoeffBaseChange
    (P : (ofIsogeny φ).KerCoeff) (Q : (ofIsogeny φ.dual).KerCoeff) :
    (φ.baseChange L).kerCoeffWeilPairing
        (φ.isUnit_degree_baseChange_of_isUnit hn L)
        (φ.kerCoeffBaseChange τ P)
        (kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L) (φ.dual.kerCoeffBaseChange τ Q)) =
      kummerCoeffInclusion L (dvd_of_eq (φ.degree_baseChange L).symm)
        (kummerCoeffBaseChange φ.degree τ (φ.kerCoeffWeilPairing hn P Q)) := by
  have hnL : IsUnit ((φ.baseChange L).degree : L) := φ.isUnit_degree_baseChange_of_isUnit hn L
  have hQ : (kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L)
      (φ.dual.kerCoeffBaseChange τ Q) : (W₂⁄L).PointCoeff) = W₂.pointCoeffBaseChange τ Q := by
    rw [Hom.kerCoeffCongrHom_apply, Hom.coe_kerCoeffCongr, φ.dual.coe_kerCoeffBaseChange τ Q]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rw [coe_toMul_kummerCoeffInclusion, toMul_kummerCoeffBaseChange, Units.coe_map,
    MonoidHom.coe_ofClass]
  exact φ.coe_kerCoeffWeilPairing_baseChange hn τ hnL P Q _ _
    (φ.coe_kerCoeffBaseChange τ P) hQ

omit hn in
/-- Transporting a restricted dual-kernel class across `φ.ofIsogeny_dual_baseChange L` is pullback
along the composite compatible pair. -/
private theorem kerH1Congr_ofIsogeny_dual_baseChange_kerRes
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    kerH1Congr (φ.ofIsogeny_dual_baseChange L) (φ.dual.kerRes τ b) =
      explicitMap1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff
        (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff
        (absoluteGaloisGroupMap τ)
        ((kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L)).toAddMonoidHom.comp
          (φ.dual.kerCoeffBaseChange τ))
        continuous_of_discreteTopology
        (fun g Q ↦ by
          change kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L)
              (φ.dual.kerCoeffBaseChange τ (absoluteGaloisGroupMap τ g • Q)) =
            g • kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L)
              (φ.dual.kerCoeffBaseChange τ Q)
          rw [φ.dual.kerCoeffBaseChange_smul, map_smul])
        b := by
  have hcompN := explicitMap1_comp (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff
    (AbsoluteGaloisGroup L) (ofIsogeny (φ.dual.baseChange L)).KerCoeff
    (absoluteGaloisGroupMap τ) (φ.dual.kerCoeffBaseChange τ) continuous_of_discreteTopology
    (φ.dual.kerCoeffBaseChange_smul τ)
    (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff
    (ContinuousMonoidHom.id _)
    (kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L)).toAddMonoidHom
    continuous_of_discreteTopology
    (fun g x ↦ (kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L)).map_smul g x)
  rw [Hom.kerH1Congr_apply, explicitCoeff1_eq_explicitMap1, kerRes_eq_explicitMap1]
  exact DFunLike.congr_fun (hcompN.symm.trans (explicitMap1_congr_of_eq
    (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff
    (AbsoluteGaloisGroup L) (ofIsogeny (φ.baseChange L).dual).KerCoeff
    _ _ _ _ (by ext; rfl) rfl)) b

omit [W₁.IsElliptic] [W₂.IsElliptic] φ hn in
/-- Composing `explicitMap2` along `kummerCoeffBaseChange` with `explicitCoeff2` along
`kummerCoeffInclusion` is `explicitMap2` along the composite `KummerCoeff` homomorphism. -/
private theorem explicitCoeff2_kummerCoeffInclusion_explicitMap2 {m m' : ℕ} (hd : m ∣ m')
    (x : H2 (AbsoluteGaloisGroup K) (KummerCoeff K m)) :
    explicitCoeff2 _ _ (kummerCoeffInclusion L hd) continuous_of_discreteTopology
        (explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K m)
          (AbsoluteGaloisGroup L) (KummerCoeff L m) (absoluteGaloisGroupMap τ)
          (kummerCoeffBaseChange m τ) continuous_of_discreteTopology
          (kummerCoeffBaseChange_smul m τ) x) =
      explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K m)
        (AbsoluteGaloisGroup L) (KummerCoeff L m') (absoluteGaloisGroupMap τ)
        ((kummerCoeffInclusion L hd).toAddMonoidHom.comp (kummerCoeffBaseChange m τ))
        continuous_of_discreteTopology
        (fun g y ↦ by
          change kummerCoeffInclusion L hd
              (kummerCoeffBaseChange m τ (absoluteGaloisGroupMap τ g • y)) =
            g • kummerCoeffInclusion L hd (kummerCoeffBaseChange m τ y)
          rw [kummerCoeffBaseChange_smul, map_smul])
        x := by
  have hcompP := explicitMap2_comp (AbsoluteGaloisGroup K) (KummerCoeff K m)
    (AbsoluteGaloisGroup L) (KummerCoeff L m) (absoluteGaloisGroupMap τ)
    (kummerCoeffBaseChange m τ) continuous_of_discreteTopology (kummerCoeffBaseChange_smul m τ)
    (AbsoluteGaloisGroup L) (KummerCoeff L m') (ContinuousMonoidHom.id _)
    (kummerCoeffInclusion L hd).toAddMonoidHom continuous_of_discreteTopology
    (fun g y ↦ (kummerCoeffInclusion L hd).map_smul g y)
  rw [explicitCoeff2_eq_explicitMap2]
  exact DFunLike.congr_fun (hcompP.symm.trans (explicitMap2_congr_of_eq
    (AbsoluteGaloisGroup K) (KummerCoeff K m)
    (AbsoluteGaloisGroup L) (KummerCoeff L m') _ _ _ _ (by ext; rfl) rfl)) x

/-- Restriction to a field extension commutes with the isogeny Weil cup product, up to
transporting the restricted dual-kernel class across `φ.ofIsogeny_dual_baseChange L`
and the roots-of-unity level across `deg φ = deg (φ.baseChange L)`. -/
theorem kerH1WeilPairing_kerRes
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    (φ.baseChange L).kerH1WeilPairing
        (φ.isUnit_degree_baseChange_of_isUnit hn L)
        (φ.kerRes τ a)
        (kerH1Congr (φ.ofIsogeny_dual_baseChange L) (φ.dual.kerRes τ b)) =
      explicitCoeff2 _ _
        (kummerCoeffInclusion L (dvd_of_eq (φ.degree_baseChange L).symm))
        continuous_of_discreteTopology
        (explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K φ.degree)
          (AbsoluteGaloisGroup L) (KummerCoeff L φ.degree) (absoluteGaloisGroupMap τ)
          (kummerCoeffBaseChange φ.degree τ) continuous_of_discreteTopology
          (kummerCoeffBaseChange_smul φ.degree τ) (φ.kerH1WeilPairing hn a b)) := by
  have hnL : IsUnit ((φ.baseChange L).degree : L) := φ.isUnit_degree_baseChange_of_isUnit hn L
  have hd : φ.degree ∣ (φ.baseChange L).degree := dvd_of_eq (φ.degree_baseChange L).symm
  have h1 := (((φ.baseChange L).kerH1WeilPairing_eq_explicitCup11 hnL _ _).trans
    (congrArg₂ (fun x y ↦ explicitCup11 (AbsoluteGaloisGroup L)
      (ofIsogeny (φ.baseChange L)).KerCoeff (ofIsogeny (φ.baseChange L).dual).KerCoeff
      (KummerCoeff L (φ.baseChange L).degree) ((φ.baseChange L).kerCoeffWeilPairing hnL)
      continuous_of_discreteTopology ((φ.baseChange L).kerCoeffWeilPairing_smul hnL) x y)
      (DFunLike.congr_fun (φ.kerRes_eq_explicitMap1 τ) a)
      (kerH1Congr_ofIsogeny_dual_baseChange_kerRes φ τ b)))
  have h2 := (explicitCoeff2_kummerCoeffInclusion_explicitMap2 τ hd _).trans
    (congrArg _ (φ.kerH1WeilPairing_eq_explicitCup11 hn a b))
  exact h1.trans ((explicitMap2_explicitCup11
    (G := AbsoluteGaloisGroup K) (M := (ofIsogeny φ).KerCoeff) (N := (ofIsogeny φ.dual).KerCoeff)
    (P := KummerCoeff K φ.degree) (μ := φ.kerCoeffWeilPairing hn)
    (hμ := continuous_of_discreteTopology) (hequiv := φ.kerCoeffWeilPairing_smul hn)
    (H := AbsoluteGaloisGroup L) (M' := (ofIsogeny (φ.baseChange L)).KerCoeff)
    (N' := (ofIsogeny (φ.baseChange L).dual).KerCoeff)
    (P' := KummerCoeff L (φ.baseChange L).degree)
    (μ' := (φ.baseChange L).kerCoeffWeilPairing hnL) (hμ' := continuous_of_discreteTopology)
    (hequiv' := (φ.baseChange L).kerCoeffWeilPairing_smul hnL)
    (φ := absoluteGaloisGroupMap τ) (fM := φ.kerCoeffBaseChange τ)
    (fN := (kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L)).toAddMonoidHom.comp
      (φ.dual.kerCoeffBaseChange τ))
    (fP := (kummerCoeffInclusion L hd).toAddMonoidHom.comp (kummerCoeffBaseChange φ.degree τ))
    (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
    (hcP := continuous_of_discreteTopology) (hfM := φ.kerCoeffBaseChange_smul τ)
    (hfN := _) (hfP := _)
    (hpair := fun P Q ↦ (φ.kerCoeffWeilPairing_kerCoeffBaseChange hn τ P Q).symm)
    a b).symm.trans h2.symm)

/-- The Brauer class of an isogeny Weil cup product localizes to the isogeny Weil cup product of
the restricted classes over `L`. This holds for every field extension `L/K`, including archimedean
and nonarchimedean completions. -/
theorem brBaseChange_kerWeilBrauerPairing
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    brBaseChange K L (φ.kerWeilBrauerPairing hn a b) =
      (φ.baseChange L).kerWeilBrauerPairing
        (φ.isUnit_degree_baseChange_of_isUnit hn L)
        (φ.kerRes τ a)
        (kerH1Congr (φ.ofIsogeny_dual_baseChange L) (φ.dual.kerRes τ b)) := by
  rw [kerWeilBrauerPairing_apply, kerWeilBrauerPairing_apply, φ.kerH1WeilPairing_kerRes hn τ a b,
    h2MuToBr_muNRepH2Equiv_explicitCoeff2_kummerCoeffInclusion,
    brBaseChange_h2MuToBr_muNRepH2Equiv φ.degree τ]

end TauCeti.Isogeny

end
