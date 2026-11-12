/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Brauer
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny

/-!
# The Brauer-valued isogeny Weil cup product

For an isogeny `φ : E₁ → E₂` of degree `n` invertible in a field `K`, compose the cup product
along the isogeny Weil pairing with the Kummer inclusion `H²(K, μ_n) → Br K`. The resulting
bilinear pairing on `H¹(K, E₁[φ]) × H¹(K, E₂[φ̂])` has values killed by `n`. The Kummer
inclusion is injective, so passage to the Brauer group neither loses nor introduces vanishing.

This is the global Brauer class whose local invariants enter reciprocity and the comparison
of the Selmer groups of dual isogenies. Compatibility with inclusion into degree-torsion and
projection onto the dual kernel identifies it with the multiplication Weil cup product when
the second class lifts to degree-torsion. No local-field or rationality hypothesis is needed.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §§2 and 4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

/-- The cup product along the isogeny Weil pairing, followed by the Kummer inclusion into the
Brauer group. Its arguments have coefficients in the kernels of `φ` and its dual. -/
def kerWeilBrauerPairing : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+ Br K :=
  (AddMonoidHom.compHom ((h2MuToBr φ.degree K).comp
    (muNRepH2Equiv φ.degree K).toAddMonoidHom)).comp (φ.kerH1WeilPairing hn)

/-- The Brauer-valued isogeny pairing is the image of the isogeny Weil cup product. -/
@[simp]
theorem kerWeilBrauerPairing_apply
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    φ.kerWeilBrauerPairing hn a b =
      h2MuToBr φ.degree K (muNRepH2Equiv φ.degree K (φ.kerH1WeilPairing hn a b)) :=
  (rfl)

/-- Passage to the Brauer group preserves and reflects vanishing of the isogeny Weil cup. -/
-- Apply before the simplifier expands the Brauer-valued pairing.
@[simp↓]
theorem kerWeilBrauerPairing_eq_zero_iff
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    φ.kerWeilBrauerPairing hn a b = 0 ↔ φ.kerH1WeilPairing hn a b = 0 := by
  rw [kerWeilBrauerPairing_apply, map_eq_zero_iff _ (h2MuToBr_injective _ _ hn),
    AddEquiv.map_eq_zero_iff]

/-- The degree of the isogeny kills every value of its Brauer-valued pairing. -/
-- Apply before the simplifier expands the Brauer-valued pairing.
@[simp↓]
theorem degree_nsmul_kerWeilBrauerPairing
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    φ.degree • φ.kerWeilBrauerPairing hn a b = 0 :=
  (h2MuToBr_range φ.degree K hn _).mp ⟨_, (φ.kerWeilBrauerPairing_apply hn a b).symm⟩

/-- Projecting a degree-torsion class to the dual kernel turns the Brauer-valued isogeny
pairing into the multiplication Weil pairing with the first class included in degree-torsion. -/
theorem kerWeilBrauerPairing_explicitCoeff1_torsionCoeffToDualKerCoeff
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)) :
    φ.kerWeilBrauerPairing hn a
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      W₁.torsionWeilBrauerPairing φ.degree hn
        (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology a) b := by
  simp only [kerWeilBrauerPairing_apply, torsionWeilBrauerPairing_apply,
    kerH1WeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff]

end TauCeti.Isogeny

end
