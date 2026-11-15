/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cohomology
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Torsion

/-!
# The Brauer-valued Weil cup product

Composing the Weil cup product with `H²(K, μ_m) → Br K` gives a bilinear pairing on
`H¹(K, E[m])` over any field in which `m` is invertible. Likewise, for an isogeny `φ : E₁ → E₂`
of degree `n` invertible in `K`, composing the isogeny Weil cup product with `H²(K, μ_n) → Br K`
gives a bilinear pairing `H¹(K, E₁[φ]) × H¹(K, E₂[φ̂]) → Br K`.

Their comparisons with the local Tate pairings are proved in `WeilPairing.Local`; this module
does not require local-field hypotheses, so it applies equally over global fields and over
archimedean completions.

## Main definitions

* `WeierstrassCurve.torsionWeilBrauerPairing`: the Brauer-valued Weil cup product on `H¹(K, E[m])`.
* `TauCeti.Isogeny.kerWeilBrauerPairing`: the Brauer-valued isogeny Weil cup product on
  `H¹(K, E₁[φ]) × H¹(K, E₂[φ̂])`.

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

/-- The Weil cup product, followed by the inclusion `H²(K, μ_m) → Br K`.
It is bilinear on the first cohomology of elliptic torsion. -/
def torsionWeilBrauerPairing : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+
    H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+ Br K :=
  (AddMonoidHom.compHom ((h2MuToBr m K).comp
    (muNRepH2Equiv m K).toAddMonoidHom)).comp (W.torsionH1WeilPairing m hm)

/-- The Brauer-valued pairing is the image of the Weil cup product. -/
@[simp]
theorem torsionWeilBrauerPairing_apply
    (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    W.torsionWeilBrauerPairing m hm a b =
      h2MuToBr m K (muNRepH2Equiv m K (W.torsionH1WeilPairing m hm a b)) :=
  (rfl)

/-- The Brauer-valued Weil pairing is annihilated by `m`. -/
@[simp]
theorem nsmul_torsionWeilBrauerPairing_eq_zero
    (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    m • W.torsionWeilBrauerPairing m hm a b = 0 :=
  (h2MuToBr_range m K hm _).1 ⟨_, rfl⟩

end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory
open Hom (ofIsogeny)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

/-- **The Brauer-valued isogeny Weil pairing**: the cup product `kerH1WeilPairing` along
`e_φ : E₁[φ] × E₂[φ̂] → μ_n`, followed by `H²(K, μ_n) → Br K` (`n = deg φ`). -/
def kerWeilBrauerPairing : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+ Br K :=
  (AddMonoidHom.compHom ((h2MuToBr φ.degree K).comp
    (muNRepH2Equiv φ.degree K).toAddMonoidHom)).comp (φ.kerH1WeilPairing hn)

/-- The Brauer-valued isogeny Weil pairing is the image of `kerH1WeilPairing` in `Br K`. -/
@[simp]
theorem kerWeilBrauerPairing_apply
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    φ.kerWeilBrauerPairing hn a b =
      h2MuToBr φ.degree K (muNRepH2Equiv φ.degree K (φ.kerH1WeilPairing hn a b)) :=
  (rfl)

/-- The Brauer-valued isogeny Weil pairing is annihilated by `deg φ`. -/
@[simp]
theorem degree_nsmul_kerWeilBrauerPairing_eq_zero
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    φ.degree • φ.kerWeilBrauerPairing hn a b = 0 :=
  (h2MuToBr_range φ.degree K hn _).1 ⟨_, rfl⟩

/-- Compatibility of the Brauer-valued Weil pairings with inclusion into degree-torsion and
projection onto the dual kernel. -/
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
