/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.BaseChange

import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality

/-!
# Base change of the Weil pairing and cup product on Galois cohomology

The Weil pairings and cup products on `H¹(K, E[m])` and on `H¹(K, E₁[φ]) × H¹(K, E₂[φ̂])`
commute with arbitrary extensions of fields (`WeierstrassCurve.torsionH1WeilPairing_torsionRes`
and `TauCeti.Isogeny.kerH1WeilPairing_kerRes`). Localization of the induced Brauer-valued pairings
is in `TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/BaseChange/Brauer.lean`.

## Main results

* `WeierstrassCurve.torsionH1WeilPairing_torsionRes`: localization of the `[m]`-torsion Weil
  cup product along field extensions.
* `TauCeti.Isogeny.coe_kerCoeffWeilPairing_baseChange` and
  `TauCeti.Isogeny.kerCoeffWeilPairing_kerCoeffBaseChange`: the isogeny Weil pairing commutes with
  field extension.
* `TauCeti.Isogeny.kerH1WeilPairing_kerRes`: localization of the isogeny Weil cup product along
  field extensions.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §§2 and 4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

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

end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-! ### Localization of the isogeny Weil cup product -/

section

variable (hn : IsUnit (φ.degree : K))
  {L : Type*} [Field L] [Algebra K L] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- The isogeny Weil pairing commutes with every field extension. The hypotheses specify
only the underlying images of the two kernel points; the values are compared in the ambient
separable closure, so no casts between degree-indexed roots of unity are needed. -/
theorem coe_kerCoeffWeilPairing_baseChange
    (hnL : IsUnit ((φ.baseChange L).degree : L))
    (P : (ofIsogeny φ).KerCoeff) (Q : (ofIsogeny φ.dual).KerCoeff)
    (P' : (ofIsogeny (φ.baseChange L)).KerCoeff)
    (Q' : (ofIsogeny (φ.baseChange L).dual).KerCoeff)
    (hP : (P' : (W₁⁄L).PointCoeff) = W₁.pointCoeffBaseChange τ P)
    (hQ : (Q' : (W₂⁄L).PointCoeff) = W₂.pointCoeffBaseChange τ Q) :
    ((φ.baseChange L).kerCoeffWeilPairing hnL P' Q').toMul.val.val =
      τ ((φ.kerCoeffWeilPairing hn P Q).toMul.val.val) := by
  classical
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  obtain ⟨R, rfl⟩ := φ.torsionCoeffToDualKerCoeff_surjective Q
  have hd : (φ.baseChange L).degree = φ.degree := φ.degree_map (algebraMap K L)
  -- Reindex only the torsion level, retaining the ordinary coordinate base-change map.
  let R' : (W₁⁄L).TorsionCoeff (φ.baseChange L).degree :=
    ⟨W₁.pointCoeffBaseChange τ R, by
      simpa only [hd, coe_torsionCoeffBaseChange] using
        (W₁.torsionCoeffBaseChange τ φ.degree R).property⟩
  have hR' : (R' : (W₁⁄L).PointCoeff) = W₁.pointCoeffBaseChange τ R := rfl
  have hQ' : (φ.baseChange L).torsionCoeffToDualKerCoeff R' = Q' := by
    apply Subtype.ext
    rw [coe_torsionCoeffToDualKerCoeff, hR', pointCoeffMap_baseChange_pointCoeffBaseChange,
      hQ, coe_torsionCoeffToDualKerCoeff]
  rw [← hQ', kerCoeffWeilPairing_torsionCoeffToDualKerCoeff,
    kerCoeffWeilPairing_torsionCoeffToDualKerCoeff]
  exact W₁.coe_torsionCoeffWeilPairing_baseChange hn τ _ hnL hd
    (φ.kerCoeffToTorsionCoeff P) R
    ((φ.baseChange L).kerCoeffToTorsionCoeff P') R'
    (by simpa only [coe_kerCoeffToTorsionCoeff] using hP) hR'

/-- **The isogeny Weil pairing commutes with field extension on `KummerCoeff`**: transporting
points along `τ` and `φ.ofIsogeny_dual_baseChange L` matches transporting roots of unity
along `τ` and `φ.degree_baseChange`. -/
theorem kerCoeffWeilPairing_kerCoeffBaseChange
    (P : (ofIsogeny φ).KerCoeff) (Q : (ofIsogeny φ.dual).KerCoeff) :
    (φ.baseChange L).kerCoeffWeilPairing
        (φ.isUnit_degree_baseChange_of_isUnit hn L)
        (φ.kerCoeffBaseChange τ P)
        (kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L)
          (φ.dual.kerCoeffBaseChange τ Q)) =
      kummerCoeffInclusion L (dvd_of_eq (φ.degree_baseChange (K := L)).symm)
        (kummerCoeffBaseChange φ.degree τ (φ.kerCoeffWeilPairing hn P Q)) := by
  have hnL : IsUnit ((φ.baseChange L).degree : L) :=
    φ.isUnit_degree_baseChange_of_isUnit hn L
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
        (kummerCoeffInclusion L (dvd_of_eq (φ.degree_baseChange (K := L)).symm))
        continuous_of_discreteTopology
        (explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K φ.degree)
          (AbsoluteGaloisGroup L) (KummerCoeff L φ.degree) (absoluteGaloisGroupMap τ)
          (kummerCoeffBaseChange φ.degree τ) continuous_of_discreteTopology
          (kummerCoeffBaseChange_smul φ.degree τ) (φ.kerH1WeilPairing hn a b)) := by
  have hnL : IsUnit ((φ.baseChange L).degree : L) :=
    φ.isUnit_degree_baseChange_of_isUnit hn L
  have hd : φ.degree ∣ (φ.baseChange L).degree := dvd_of_eq (φ.degree_baseChange (K := L)).symm
  have h1 := (((φ.baseChange L).kerH1WeilPairing_eq_explicitCup11 hnL _ _).trans
    (congrArg₂ (fun x y ↦ explicitCup11 (AbsoluteGaloisGroup L)
      (ofIsogeny (φ.baseChange L)).KerCoeff (ofIsogeny (φ.baseChange L).dual).KerCoeff
      (KummerCoeff L (φ.baseChange L).degree) ((φ.baseChange L).kerCoeffWeilPairing hnL)
      continuous_of_discreteTopology ((φ.baseChange L).kerCoeffWeilPairing_smul hnL) x y)
      (DFunLike.congr_fun (φ.kerRes_eq_explicitMap1 τ) a)
      ((Hom.kerH1Congr_apply (φ.ofIsogeny_dual_baseChange L) (φ.dual.kerRes τ b)).trans
        ((congrArg (explicitCoeff1 (AbsoluteGaloisGroup L)
            (ofIsogeny (φ.dual.baseChange L)).KerCoeff
            (kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L)) continuous_of_discreteTopology)
            (DFunLike.congr_fun (φ.dual.kerRes_eq_explicitMap1 τ) b)).trans
          (explicitCoeff1_explicitMap1 _ _ _ _ _ _ _ _ b)))))
  have h2 := (explicitCoeff2_explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K φ.degree)
      (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange φ.degree τ) continuous_of_discreteTopology
      (kummerCoeffBaseChange_smul φ.degree τ) (kummerCoeffInclusion L hd)
      continuous_of_discreteTopology (φ.kerH1WeilPairing hn a b)).trans
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
    (fN := (kerCoeffCongrHom (φ.ofIsogeny_dual_baseChange L) : _ →+ _).comp
      (φ.dual.kerCoeffBaseChange τ))
    (fP := (kummerCoeffInclusion L hd : _ →+ _).comp (kummerCoeffBaseChange φ.degree τ))
    (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
    (hcP := continuous_of_discreteTopology) (hfM := φ.kerCoeffBaseChange_smul τ)
    (hfN := _) (hfP := _)
    (hpair := fun P Q ↦ by
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.coe_ofClass] using
        (φ.kerCoeffWeilPairing_kerCoeffBaseChange hn τ P Q).symm)
    a b).symm.trans h2.symm)

end

end TauCeti.Isogeny
