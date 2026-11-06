/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cohomology
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Isogeny
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.FiniteModule

/-!
# Local Tate duality for elliptic torsion and isogeny kernels

For an elliptic curve over a nonarchimedean local field `K`, with `m` invertible in `K`, cup
product along the Weil pairing followed by the local invariant gives a perfect pairing

`H¹(K, E[m]) × H¹(K, E[m]) → ℤ/m`.

Likewise, for an isogeny `φ : E₁ → E₂` over `K` of degree `n` invertible in `K`, cup product along
the isogeny Weil pairing `e_φ : E₁[φ] × E₂[φ̂] → μ_n` (`TauCeti.Isogeny.kerCoeffWeilPairing`)
followed by the local invariant gives a perfect pairing

`H¹(K, E₁[φ]) × H¹(K, E₂[φ̂]) → ℤ/n`.

Here perfection is stated as bijectivity of the curried map: every additive character of
`H¹(K, E[m])`, respectively of `H¹(K, E₂[φ̂])`, is pairing with a unique class. This is the
finite-coefficient duality used to study annihilators of local Kummer images; for an isogeny it is
the local duality between the local conditions of `Sel_φ` and `Sel_φ̂` in Cassels' comparison of
these Selmer groups. Orthogonality of the Kummer images is a further result, not part of the
perfection statement.

No assumption that `K` contains the torsion or the roots of unity is required. In mixed
characteristic, `m` and `n` may be divisible by the residue characteristic.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorem 2.1.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : K))

/-- Cup product along the Weil pairing followed by the local invariant, valued in `ℤ/m`. -/
def localTateWeilPairing : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+
    H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+ ZMod m :=
  (AddMonoidHom.compHom
    ((muNRepH2Equiv m K).trans (h2MuEquivZMod K hm)).toAddMonoidHom).comp
    (W.torsionH1WeilPairing m hm)

/-- The local pairing is the local invariant of the Weil cup product. -/
@[simp]
theorem localTateWeilPairing_apply (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    W.localTateWeilPairing m hm a b =
      h2MuEquivZMod K hm (muNRepH2Equiv m K (W.torsionH1WeilPairing m hm a b)) :=
  (rfl)

/-- **Perfect local Tate duality for `E[m]`.** Pairing with a class gives a bijection from
`H¹(K, E[m])` to its additive characters with values in `ℤ/m`. -/
theorem localTateWeilPairing_bijective : Function.Bijective (W.localTateWeilPairing m hm) := by
  have := hm.neZero_natCast
  apply AddMonoidHom.bijective_of_bijective_pairing
    (dualityMap1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) (KummerCoeff K m))
    (W.localTateWeilPairing m hm) (AddMonoidHom.id _)
    (explicitCoeff1 _ _ (W.torsionCoeffWeilDual m hm) continuous_of_discreteTopology)
    ((muNRepH2Equiv m K).trans (h2MuEquivZMod K hm)).toAddMonoidHom Function.bijective_id
    (explicitCoeff1_bijective _ _ (W.torsionCoeffWeilDual_bijective m hm))
    ((muNRepH2Equiv m K).trans (h2MuEquivZMod K hm)).bijective
    (dualityMap1_kummerCoeff_bijective hm (W.TorsionCoeff m)
      fun P ↦ AddSubgroup.torsionBy.nsmul P)
  intro a b
  simp only [localTateWeilPairing_apply, torsionH1WeilPairing_eq_dualityMap1,
    AddMonoidHom.id_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply]

end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory Hom

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

/-- Cup product along the isogeny Weil pairing followed by the local invariant, valued in
`ℤ/n` for `n = deg φ`. -/
def localTateKerWeilPairing : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+ ZMod φ.degree :=
  (AddMonoidHom.compHom
    ((muNRepH2Equiv φ.degree K).trans (h2MuEquivZMod K hn)).toAddMonoidHom).comp
    (φ.kerH1WeilPairing hn)

/-- The local pairing is the local invariant of the isogeny Weil cup product. -/
@[simp]
theorem localTateKerWeilPairing_apply (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    φ.localTateKerWeilPairing hn a b =
      h2MuEquivZMod K hn (muNRepH2Equiv φ.degree K (φ.kerH1WeilPairing hn a b)) :=
  (rfl)

/-- **Perfect local Tate duality for the kernels of an isogeny and of its dual.** Pairing with a
class gives a bijection from `H¹(K, E₁[φ])` to the additive characters of `H¹(K, E₂[φ̂])` with
values in `ℤ/n`, `n = deg φ`. -/
theorem localTateKerWeilPairing_bijective :
    Function.Bijective (φ.localTateKerWeilPairing hn) := by
  have := hn.neZero_natCast
  apply AddMonoidHom.bijective_of_bijective_pairing
    (dualityMap1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff (KummerCoeff K φ.degree))
    (φ.localTateKerWeilPairing hn) (AddMonoidHom.id _)
    (explicitCoeff1 _ _ (φ.kerCoeffWeilDual hn) continuous_of_discreteTopology)
    ((muNRepH2Equiv φ.degree K).trans (h2MuEquivZMod K hn)).toAddMonoidHom Function.bijective_id
    (explicitCoeff1_bijective _ _ (φ.kerCoeffWeilDual_bijective hn))
    ((muNRepH2Equiv φ.degree K).trans (h2MuEquivZMod K hn)).bijective
    (dualityMap1_kummerCoeff_bijective hn (ofIsogeny φ).KerCoeff φ.degree_nsmul_kerCoeff_eq_zero)
  intro a b
  simp only [localTateKerWeilPairing_apply, kerH1WeilPairing_eq_dualityMap1,
    AddMonoidHom.id_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply]

end TauCeti.Isogeny

end
