/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Brauer
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Kummer
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.FiniteModule
import TauCeti.Algebra.Module.ZMod.Dual
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.Basic

/-!
# Local Tate duality for elliptic torsion and isogeny kernels

For an elliptic curve over a nonarchimedean local field `K`, with `m` invertible in `K`, cup
product along the Weil pairing followed by the local invariant gives a perfect pairing

`H¹(K, E[m]) × H¹(K, E[m]) → ℤ/m`.

Likewise, for an isogeny `φ : E₁ → E₂` over `K` of degree `n` invertible in `K`, cup product along
the isogeny Weil pairing `e_φ : E₁[φ] × E₂[φ̂] → μ_n` (`TauCeti.Isogeny.kerCoeffWeilPairing`)
followed by the local invariant gives a perfect pairing

`H¹(K, E₁[φ]) × H¹(K, E₂[φ̂]) → ℤ/n`.

Because `H¹(K, E[m])` and `H¹(K, E₁[φ])` are finite (`WeierstrassCurve.finite_H1_torsionCoeff`,
`TauCeti.Isogeny.finite_H1_kerCoeff`), perfection holds on both sides: both the left adjoints
(`WeierstrassCurve.localTateWeilPairing_bijective`,
`TauCeti.Isogeny.localTateKerWeilPairing_bijective`) and the transposed right adjoints
(`WeierstrassCurve.localTateWeilPairing_flip_bijective`,
`TauCeti.Isogeny.localTateKerWeilPairing_flip_bijective`) are bijective, and `H¹(K, E₁[φ])` and
`H¹(K, E₂[φ̂])` have the same finite order (`TauCeti.Isogeny.natCard_H1_kerCoeff_eq_dual`). This is
the finite-coefficient duality used to study annihilators of local Kummer images; for an isogeny it
is the local duality between the local conditions of `Sel_φ` and `Sel_φ̂` in Cassels' comparison of
these Selmer groups. The image of the Kummer map `E(K) → H¹(K, E[m])` is isotropic for the first
pairing (`WeierstrassCurve.localTateWeilPairing_kummerMap_kummerMap_eq_zero`); orthogonality of
the Kummer images of an isogeny and of its dual is a further result.

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

/-- The local Tate pairing, embedded in `ℚ/ℤ` by `k ↦ k/m`, is the Brauer invariant of the
Weil cup product. The exponent need only be invertible in the field, not in its residue field. -/
theorem toRatAddCircle_localTateWeilPairing
    (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    ZMod.toRatAddCircle m (W.localTateWeilPairing m hm a b) =
      invMap K (W.torsionWeilBrauerPairing m hm a b) := by
  rw [W.localTateWeilPairing_apply m hm, W.torsionWeilBrauerPairing_apply m hm]
  exact toRatAddCircle_h2MuEquivZMod K hm _

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

include hm in
/-- `H¹(K, E[m])` is finite when `m` is invertible in the nonarchimedean local field `K`. -/
theorem finite_H1_torsionCoeff :
    Finite (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) := by
  have := hm.neZero_natCast
  exact finite_H1_of_nsmul_eq_zero hm.ne_zero (W.TorsionCoeff m)
    fun P ↦ AddSubgroup.torsionBy.nsmul P

/-- **Two-sided perfection of local Tate duality for `E[m]`.** Pairing in the second variable gives
a bijection from `H¹(K, E[m])` to its additive characters with values in `ℤ/m`. -/
theorem localTateWeilPairing_flip_bijective :
    Function.Bijective (W.localTateWeilPairing m hm).flip := by
  have := hm.neZero_natCast
  have := W.finite_H1_torsionCoeff m hm
  exact (W.localTateWeilPairing m hm).bijective_flip_of_bijective_zmod
    (W.localTateWeilPairing_bijective m hm)
    (nsmul_H1_eq_zero fun P ↦ AddSubgroup.torsionBy.nsmul P)

/-- **The local Kummer image is isotropic for local Tate duality**: the local Tate pairing of the
Kummer classes of two points of `E(K)` vanishes. -/
theorem localTateWeilPairing_kummerMap_kummerMap_eq_zero [DecidableEq K]
    (P Q : W.toAffine.Point) :
    W.localTateWeilPairing m hm (W.kummerMap m hm P) (W.kummerMap m hm Q) = 0 := by
  rw [localTateWeilPairing_apply, torsionH1WeilPairing_kummerMap_kummerMap_eq_zero, map_zero,
    map_zero]

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

/-- The local isogeny Tate pairing, embedded in `ℚ/ℤ` by `k ↦ k/n`, is the local invariant
of the Brauer-valued isogeny Weil cup product. The residue characteristic may divide `n`. -/
theorem toRatAddCircle_localTateKerWeilPairing
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    ZMod.toRatAddCircle φ.degree (φ.localTateKerWeilPairing hn a b) =
      invMap K (φ.kerWeilBrauerPairing hn a b) := by
  rw [localTateKerWeilPairing_apply, kerWeilBrauerPairing_apply]
  exact toRatAddCircle_h2MuEquivZMod K hn _

/-- The local Tate pairings are compatible with inclusion into degree-torsion and
projection onto the dual kernel. No restriction on the residue characteristic is needed. -/
theorem localTateKerWeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)) :
    φ.localTateKerWeilPairing hn a
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      W₁.localTateWeilPairing φ.degree hn
        (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology a) b := by
  simp only [localTateKerWeilPairing_apply, localTateWeilPairing_apply,
    kerH1WeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff]

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

include hn in
/-- `H¹(K, E₁[φ])` is finite when `deg φ` is invertible in the nonarchimedean local field `K`. -/
theorem finite_H1_kerCoeff :
    Finite (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have : Finite (ofIsogeny φ).KerCoeff :=
    Nat.finite_of_card_ne_zero (φ.natCard_kerCoeff_eq_degree ▸ φ.degree_pos.ne')
  exact finite_H1_of_nsmul_eq_zero hn.ne_zero (ofIsogeny φ).KerCoeff
    φ.degree_nsmul_kerCoeff_eq_zero

/-- **Dual perfect local Tate duality for an isogeny.** Pairing in the second variable gives a
bijection from `H¹(K, E₂[φ̂])` to the additive characters of `H¹(K, E₁[φ])` with values in
`ℤ/deg φ`. -/
theorem localTateKerWeilPairing_flip_bijective :
    Function.Bijective (φ.localTateKerWeilPairing hn).flip := by
  have := hn.neZero_natCast
  have : Finite (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :=
    φ.dual.finite_H1_kerCoeff (φ.degree_dual.symm ▸ hn)
  exact (φ.localTateKerWeilPairing hn).bijective_flip_of_bijective_zmod
    (φ.localTateKerWeilPairing_bijective hn)
    (φ.degree_dual ▸ nsmul_H1_eq_zero φ.dual.degree_nsmul_kerCoeff_eq_zero)

include hn in
/-- Over any nonarchimedean local field in which `deg φ` is invertible, `H¹(K, E₁[φ])` and
`H¹(K, E₂[φ̂])` have the same finite order by local Tate duality. -/
theorem natCard_H1_kerCoeff_eq_dual :
    Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) =
      Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) := by
  have := hn.neZero_natCast
  rw [Nat.card_congr (Equiv.ofBijective _ (φ.localTateKerWeilPairing_bijective hn)),
    TauCeti.natCard_addMonoidHom_zmod
      (φ.degree_dual ▸ nsmul_H1_eq_zero φ.dual.degree_nsmul_kerCoeff_eq_zero)]

end TauCeti.Isogeny

end
