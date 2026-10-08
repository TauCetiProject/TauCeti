/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Determinant
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Galois

/-!
# The Frobenius on torsion

Let `W` be an elliptic curve over a finite field `F` with `q` elements, and `K` an extension of
`F`. The base-changed `q`-power Frobenius `π` of `W⁄K` (`TauCeti.Isogeny.baseChangeFrobenius`)
acts on the points of `W` over `K` as the `q`-power map on coordinates. When `K` is algebraic over
`F`, that map is the Frobenius automorphism `σ` of `K` over `F`, so on `N`-torsion `π` acts as the
Galois automorphism `σ`.

When moreover `K` is separably closed and `N` is invertible in `K`, the Weil pairing is
Galois-equivariant, and `σ` raises roots of unity to the `q`-th power, so `π` scales the Weil
pairing by `q`. Hence the determinant of the action of `π` on `E[N]` is `q = deg π` modulo `N`,
although `π` is inseparable (the Frobenius case of Silverman III.8.6). This is the determinant of
the Frobenius matrix in the Weil-pairing proof of the Hasse bound. The isogeny `1 - π`, and
`r π - s` when the characteristic does not divide `s`, are separable, so they are covered by
`TauCeti.Isogeny.Hom.det_torsionLinearMap_ofIsogeny`.

## Main results

* `TauCeti.Isogeny.Hom.pointMap_ofIsogeny_baseChangeFrobenius`: `π` acts on points as the
  `q`-power map on coordinates.
* `TauCeti.Isogeny.Hom.torsionLinearMap_ofIsogeny_baseChangeFrobenius_apply`: over an algebraic
  extension, `π` acts on `N`-torsion as the Frobenius automorphism.
* `TauCeti.Isogeny.Hom.det_torsionLinearMap_ofIsogeny_baseChangeFrobenius`: the determinant of
  the action of `π` on `E[N]` is `q`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1 and III.8.6.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

section Fintype

variable [Fintype F]

/-- **The Frobenius acts on points as the `q`-power map on coordinates**:
`π (x, y) = (x ^ q, y ^ q)`. -/
@[simp]
theorem pointMap_ofIsogeny_baseChangeFrobenius (P : (W⁄K).toAffine.Point) :
    (ofIsogeny (baseChangeFrobenius K W)).pointMap P =
      Point.map (FiniteField.frobeniusAlgHom F K) P := by
  rw [pointMap_eq_iff, tautologicalPoint_ofIsogeny,
    ← reductionOfDegreeEqOne_eq_iff _ (pointEquivDegreeOnePlace _ P).2,
    reductionOfDegreeEqOne_tautologicalPoint_baseChangeFrobenius]

variable [Algebra.IsAlgebraic F K]

/-- **Over an algebraic extension, the Frobenius acts on `N`-torsion as the Frobenius
automorphism** `FiniteField.frobeniusAlgEquivOfAlgebraic F K`. -/
@[simp]
theorem torsionLinearMap_ofIsogeny_baseChangeFrobenius_apply (N : ℕ)
    (P : AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ)) :
    (ofIsogeny (baseChangeFrobenius K W)).torsionLinearMap N P =
      Multiplicative.toAdd
        (torsionGaloisAction W N (FiniteField.frobeniusAlgEquivOfAlgebraic F K)) P :=
  Subtype.ext <| by
    rw [torsionLinearMap_apply, torsionGaloisAction_apply_coe, pointGaloisAction_apply,
      pointMap_ofIsogeny_baseChangeFrobenius]
    exact congrArg (Point.map · _) (AlgHom.ext fun x ↦ by simp)

end Fintype

variable [Finite F] [Algebra.IsAlgebraic F K] [IsSepClosed K] {N : ℕ} [NeZero N]

/-- **The determinant of the action of the Frobenius on `E[N]` is `q = #F`**, over a separably
closed algebraic extension `K` of the finite base `F` in which `N` is invertible. -/
theorem det_torsionLinearMap_ofIsogeny_baseChangeFrobenius (hN : (N : K) ≠ 0) :
    LinearMap.det ((ofIsogeny (baseChangeFrobenius K W)).torsionLinearMap N) = Nat.card F := by
  cases nonempty_fintype F
  rw [Nat.card_eq_fintype_card]
  refine det_eq_of_weilPairing_eq_smul hN fun S T ↦ ?_
  rw [torsionLinearMap_ofIsogeny_baseChangeFrobenius_apply,
    torsionLinearMap_ofIsogeny_baseChangeFrobenius_apply, weilPairing_torsionGaloisAction]
  refine Additive.toMul.injective <| Subtype.ext <| Units.ext ?_
  simp [restrictRootsOfUnity_coe_apply, Nat.cast_smul_eq_nsmul]

end TauCeti.Isogeny.Hom

end
