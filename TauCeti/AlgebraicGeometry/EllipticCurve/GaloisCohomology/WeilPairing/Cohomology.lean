/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic

import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
-- Proof-only: identify `dualityMap1` with the evaluation cup in the naturality theorem.
import all TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic

/-!
# The Weil pairing on first Galois cohomology

For an elliptic curve `W` over a field `K` and `m` invertible in `K`, the Weil pairing identifies
`E[m]` with its internal dual `Hom(E[m], μ_m)` as discrete Galois modules. The convention is
`Q ↦ (P ↦ e_m(P, Q))`; no rationality assumption on the torsion or roots of unity is needed.

The resulting cup product pairs two classes of `H¹(K, E[m])` into `H²(K, μ_m)`. On cocycles it
is `(g, h) ↦ e_m(a(g), g • b(h))`. This is the pairing used in local duality and in comparing
Kummer images with their annihilators.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 and X.1.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §2.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : K))

/-- The Weil pairing identifies a torsion point with the character `P ↦ e_m(P, Q)`.
The internal hom carries the conjugation action, so this is an equivariant map even when `Q`
is not rational. -/
def torsionCoeffWeilDual : W.TorsionCoeff m →+[AbsoluteGaloisGroup K]
    InternalHom (AbsoluteGaloisGroup K) (W.TorsionCoeff m) (KummerCoeff K m) where
  toFun Q := InternalHom.of _ ((W.torsionCoeffWeilPairing m hm).flip Q)
  map_zero' := by simp
  map_add' Q Q' := by simp
  map_smul' g Q := by
    apply InternalHom.ext
    apply AddMonoidHom.ext
    intro P
    simp only [InternalHom.toAddMonoidHom_smul, homAction_apply, AddMonoidHom.flip_apply]
    simpa only [smul_inv_smul, MonoidHom.id_apply] using
      W.torsionCoeffWeilPairing_smul m hm g (g⁻¹ • P) Q

/-- Evaluation of the Weil-dual character recovers the Weil pairing. -/
@[simp]
theorem toAddMonoidHom_torsionCoeffWeilDual (Q : W.TorsionCoeff m) :
    (W.torsionCoeffWeilDual m hm Q).toAddMonoidHom =
      (W.torsionCoeffWeilPairing m hm).flip Q := (rfl)

/-- **Self-duality of elliptic torsion as a Galois module.** Every character `E[m] → μ_m` is
pairing with a unique point. -/
theorem torsionCoeffWeilDual_bijective : Function.Bijective (W.torsionCoeffWeilDual m hm) := by
  have := hm.neZero_natCast
  have hinj : Function.Injective (W.torsionCoeffWeilDual m hm) := by
    refine (injective_iff_map_eq_zero _).2 fun Q hQ ↦ ?_
    apply W.torsionCoeffWeilPairing_nondegenerate m hm
    intro P
    have h := congrArg (fun f ↦ InternalHom.evalPairing (AbsoluteGaloisGroup K) f P) hQ
    simpa [← W.neg_torsionCoeffWeilPairing m hm Q P] using h
  apply hinj.bijective_of_nat_card_le
  rw [InternalHom.natCard_of_addEquiv_zmod (kummerCoeffAddEquivZMod hm)
    (fun P : W.TorsionCoeff m ↦ AddSubgroup.torsionBy.nsmul P)]

/-- The cup product along the Weil pairing, with values in `H²(K, μ_m)`.
It is obtained from the evaluation duality map by the Weil self-duality of `E[m]`. -/
def torsionH1WeilPairing : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+
    H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+
      H2 (AbsoluteGaloisGroup K) (KummerCoeff K m) :=
  haveI := hm.neZero_natCast
  (dualityMap1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) (KummerCoeff K m)).compl₂
    (explicitCoeff1 _ _ (W.torsionCoeffWeilDual m hm) continuous_of_discreteTopology)

/-- The Weil cup is the evaluation duality map after applying the Weil-dual coefficient map. -/
theorem torsionH1WeilPairing_eq_dualityMap1
    (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    haveI := hm.neZero_natCast
    W.torsionH1WeilPairing m hm a b =
      dualityMap1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) (KummerCoeff K m) a
        (explicitCoeff1 _ _ (W.torsionCoeffWeilDual m hm) continuous_of_discreteTopology b) := by
  have := hm.neZero_natCast
  rfl

/-- The pairing is the usual cup product along `e_m`, in the order `e_m(a(g), g • b(h))`. -/
theorem torsionH1WeilPairing_eq_explicitCup11
    (a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    W.torsionH1WeilPairing m hm a b =
      explicitCup11 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) (W.TorsionCoeff m)
        (KummerCoeff K m) (W.torsionCoeffWeilPairing m hm) continuous_of_discreteTopology
        (W.torsionCoeffWeilPairing_smul m hm) a b := by
  have := hm.neZero_natCast
  have h := explicitCoeff2_explicitCup11 (AbsoluteGaloisGroup K)
    (W.TorsionCoeff m) (W.TorsionCoeff m) (KummerCoeff K m)
    (W.TorsionCoeff m) (InternalHom (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
      (KummerCoeff K m)) (KummerCoeff K m)
    (W.torsionCoeffWeilPairing m hm) continuous_of_discreteTopology
    (W.torsionCoeffWeilPairing_smul m hm)
    (InternalHom.evalPairing (AbsoluteGaloisGroup K)).flip continuous_of_discreteTopology
    (InternalHom.evalPairing_flip_equivariant (G := AbsoluteGaloisGroup K))
    (DistribMulActionHom.id _) (W.torsionCoeffWeilDual m hm) (DistribMulActionHom.id _)
    continuous_id continuous_of_discreteTopology continuous_id
    (fun _ _ ↦ by simp only [DistribMulActionHom.id_apply, AddMonoidHom.flip_apply,
      InternalHom.evalPairing_apply, toAddMonoidHom_torsionCoeffWeilDual]) a b
  simpa only [explicitCoeff2_id, explicitCoeff1_id, AddMonoidHom.id_apply,
    torsionH1WeilPairing_eq_dualityMap1, dualityMap1] using h.symm

end WeierstrassCurve

end
