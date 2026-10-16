/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Determinant
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree

/-!
# The Frobenius on torsion

Let `W` be an elliptic curve over a finite field `F` with `q` elements, and `K` an extension of
`F`. The base-changed `q`-power Frobenius `π` of `W⁄K` (`TauCeti.Isogeny.baseChangeFrobenius`)
acts on the points of `W` over `K` as the `q`-power map on coordinates. When `K` is algebraic over
`F`, that map is the Frobenius automorphism `σ` of `K` over `F`, so on `N`-torsion `π` acts as the
Galois automorphism `σ`.

When `K` is separably closed and `N` is invertible in `K`, the determinant of the action of `π` on
`E[N]` is `q = deg π` modulo `N` (Silverman III.8.6): base change preserves the degree, so this is a
case of `TauCeti.Isogeny.Hom.det_torsionLinearMap_ofIsogeny`. It is the determinant of the
Frobenius matrix in the Weil-pairing proof of the Hasse bound.

## Main results

* `TauCeti.Isogeny.Hom.pointMap_ofIsogeny_baseChangeFrobenius`: `π` acts on points as the
  `q`-power map on coordinates.
* `TauCeti.Isogeny.Hom.torsionLinearMap_ofIsogeny_baseChangeFrobenius_apply`: over an algebraic
  extension, `π` acts on `N`-torsion as the Frobenius automorphism.
* `TauCeti.Isogeny.Hom.det_torsionLinearMap_ofIsogeny_baseChangeFrobenius`: the determinant of
  the action of `π` on `E[N]` is `q` modulo `N`.

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

variable [Finite F] [IsSepClosed K] {N : ℕ} [NeZero N]

/-- **The determinant of the action of the Frobenius on `E[N]` is `q = #F` modulo `N`**, over a
separably closed extension `K` of the finite base `F` in which `N` is invertible. -/
theorem det_torsionLinearMap_ofIsogeny_baseChangeFrobenius (hN : (N : K) ≠ 0) :
    LinearMap.det ((ofIsogeny (baseChangeFrobenius K W)).torsionLinearMap N) = Nat.card F := by
  rw [det_torsionLinearMap_ofIsogeny hN, baseChangeFrobenius_def]
  exact congrArg Nat.cast ((Isogeny.degree_map _ _).trans (degree_frobeniusIsogeny W))

end TauCeti.Isogeny.Hom

end
