/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cohomology
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.FiniteModule

/-!
# Local Tate duality for elliptic torsion

For an elliptic curve over a nonarchimedean local field `K`, with `m` invertible in `K`, cup
product along the Weil pairing followed by the local invariant gives a perfect pairing

`H¹(K, E[m]) × H¹(K, E[m]) → ℤ/m`.

Here perfection is stated as bijectivity of the curried map: every additive character of
`H¹(K, E[m])` is pairing with a unique class. This is the finite-coefficient duality used to
study annihilators of local Kummer images; orthogonality of those images is a further result,
not part of the perfection statement.

No assumption that `K` contains the torsion or the roots of unity is required. In mixed
characteristic, `m` may be divisible by the residue characteristic.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorem 2.1.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.
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

end
