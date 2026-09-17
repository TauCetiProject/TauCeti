/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount

/-!
# Point counts at a singular Weierstrass model

The projective equation points of a Weierstrass model split into its nonsingular affine points,
its singular affine points, and the point at infinity. Mathlib's `WeierstrassCurve.Affine.Point`
contains the first and third parts. Consequently, `pointCount` is the cardinality of that point
type plus the number of rational singular points.

Over a field a Weierstrass model has at most one singular point. Thus a rational singular point
contributes exactly one to `pointCount`; the final theorem characterises this case. These results
let any geometric criterion producing a rational singular point, such as one based on vanishing
discriminant over a finite field, feed directly into the point-count formula.

## Main results

* `WeierstrassCurve.pointCount_eq_card_point_add_card_singular`: the projective equation count is
  the nonsingular point count plus the number of singular affine points.
* `WeierstrassCurve.pointCount_eq_card_point_add_one_of_isSingular`: a given rational singular
  point contributes exactly one.
* `WeierstrassCurve.pointCount_eq_card_point_add_one_iff`: adding one is equivalent to the
  existence of a rational singular point.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, V.1.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private noncomputable def equationPointEquiv :
    {p : F × F // W.toAffine.Equation p.1 p.2} ≃
      {p : F × F // W.toAffine.Nonsingular p.1 p.2} ⊕
        {p : F × F // W.toAffine.IsSingular p.1 p.2} := by
  classical
  let nonsingularEquiv :
      {p : {q : F × F // W.toAffine.Equation q.1 q.2} //
          W.toAffine.Nonsingular p.1.1 p.1.2} ≃
        {p : F × F // W.toAffine.Nonsingular p.1 p.2} :=
    Equiv.subtypeSubtypeEquivSubtype fun {p : F × F}
      (h : W.toAffine.Nonsingular p.1 p.2) ↦ h.1
  let singularEquiv :
      {p : {q : F × F // W.toAffine.Equation q.1 q.2} //
          ¬ W.toAffine.Nonsingular p.1.1 p.1.2} ≃
        {p : F × F // W.toAffine.IsSingular p.1 p.2} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun p : F × F ↦ W.toAffine.Equation p.1 p.2)
      (fun p : F × F ↦ ¬ W.toAffine.Nonsingular p.1 p.2)).trans
        (Equiv.subtypeEquivProp <| funext fun p ↦ propext
          (WeierstrassCurve.Affine.isSingular_iff_equation_and_not_nonsingular
            (W := W.toAffine) (x := p.1) (y := p.2)).symm)
  exact (Equiv.sumCompl fun p : {q : F × F // W.toAffine.Equation q.1 q.2} ↦
    W.toAffine.Nonsingular p.1.1 p.1.2).symm.trans (Equiv.sumCongr nonsingularEquiv singularEquiv)

/-- **The projective equation count is the nonsingular point count plus the number of rational
singular affine points.** The point at infinity occurs in both `pointCount` and Mathlib's point
type, while the affine equation points split into their nonsingular and singular parts. -/
theorem _root_.WeierstrassCurve.pointCount_eq_card_point_add_card_singular [Finite F] :
    W.pointCount = Nat.card W.toAffine.Point +
      Nat.card {p : F × F // W.toAffine.IsSingular p.1 p.2} := by
  have hN : Nat.card (WithZero {p : F × F // W.toAffine.Nonsingular p.1 p.2}) =
      Nat.card {p : F × F // W.toAffine.Nonsingular p.1 p.2} + 1 :=
    Finite.card_option
  rw [WeierstrassCurve.pointCount_def, Nat.card_congr (equationPointEquiv W), Nat.card_sum,
    Nat.card_congr W.toAffine.nonsingularPointEquiv, hN]
  omega

/-- **A rational singular point contributes exactly one to the projective equation count.**
There cannot be another one because a Weierstrass model over a field has at most one singular
point. -/
theorem _root_.WeierstrassCurve.pointCount_eq_card_point_add_one_of_isSingular [Finite F]
    {x y : F} (h : W.toAffine.IsSingular x y) :
    W.pointCount = Nat.card W.toAffine.Point + 1 := by
  rw [W.pointCount_eq_card_point_add_card_singular]
  congr 1
  apply Nat.card_eq_one_iff_exists.2
  refine ⟨⟨(x, y), h⟩, ?_⟩
  rintro ⟨⟨x', y'⟩, h'⟩
  obtain ⟨hx, hy⟩ :=
    WeierstrassCurve.Affine.eq_of_isSingular_of_isSingular h' h
  exact Subtype.ext (Prod.ext hx hy)

/-- **The projective equation count exceeds the nonsingular point count by one exactly when the
model has a rational singular affine point.** -/
theorem _root_.WeierstrassCurve.pointCount_eq_card_point_add_one_iff [Finite F] :
    W.pointCount = Nat.card W.toAffine.Point + 1 ↔
      ∃ x y : F, W.toAffine.IsSingular x y := by
  constructor
  · intro h
    have hs : Nat.card {p : F × F // W.toAffine.IsSingular p.1 p.2} = 1 :=
      Nat.add_left_cancel (W.pointCount_eq_card_point_add_card_singular.symm.trans h)
    obtain ⟨p⟩ := (Nat.card_eq_one_iff_unique.1 hs).2
    exact ⟨p.1.1, p.1.2, p.2⟩
  · rintro ⟨x, y, h⟩
    exact W.pointCount_eq_card_point_add_one_of_isSingular h

end TauCeti

end
