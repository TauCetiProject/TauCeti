/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny

import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality

/-!
# Base change of the Weil pairing and cup product on Galois cohomology

The Weil pairing and cup product on `H¹(K, E[m])` and the isogeny Weil pairing on
`E₁(Kˢ)[φ] × E₂(Kˢ)[φ̂]` commute with arbitrary extensions of fields
(`WeierstrassCurve.torsionH1WeilPairing_torsionRes` and
`TauCeti.Isogeny.coe_kerCoeffWeilPairing_baseChange`). Localization of the induced Brauer-valued
pairings is in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/BaseChange/Brauer.lean`.

## Main results

* `WeierstrassCurve.torsionH1WeilPairing_torsionRes`: localization of the `[m]`-torsion Weil
  cup product along field extensions.
* `TauCeti.Isogeny.coe_kerCoeffWeilPairing_baseChange`: the isogeny Weil pairing commutes with
  field extension.

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

end

end TauCeti.Isogeny
