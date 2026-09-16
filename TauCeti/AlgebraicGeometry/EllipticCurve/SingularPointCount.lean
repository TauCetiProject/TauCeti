/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.AlgebraicGeometry.EllipticCurve.NodePolynomial

/-!
# Point counts at a singular Weierstrass model

The projective equation points of a Weierstrass model split into its nonsingular affine points,
its singular affine points, and the point at infinity. Mathlib's `WeierstrassCurve.Affine.Point`
contains the first and third parts. Consequently, `pointCount` is the cardinality of that point
type plus the number of rational singular points.

Over a field a Weierstrass model has at most one singular point. Thus a rational singular point
contributes exactly one to `pointCount`; the theorem `pointCount_eq_card_point_add_one_iff`
characterises this case.

Over a finite field of `q` elements the singular point is rational and the count is explicit. Move
the singular point to the origin, where the equation reads `y² + a₁ x y = x³ + a₂ x²`. Away from
the origin a solution has `x ≠ 0`, and its slope `t = y / x` determines it: `x = t² + a₁ t − a₂`,
and `t` is not a root of the tangent quadratic `T² + a₁ T − a₂`. So the model has `q + 2 − r`
points, where `r` counts the rational tangent slopes, and its Frobenius trace `q + 1 − pointCount`
is `r − 1`. The node polynomial is `c₄` times the tangent quadratic, and the discriminant of that
quadratic squares to `c₄`. The three shapes of singularity therefore give the three classical
local invariants: `1` at a split node, `−1` at a nonsplit node and `0` at a cusp.

## Main results

* `WeierstrassCurve.pointCount_eq_card_point_add_card_singular`: the projective equation count is
  the nonsingular point count plus the number of singular affine points.
* `WeierstrassCurve.pointCount_eq_card_point_add_one_of_isSingular`: a given rational singular
  point contributes exactly one.
* `WeierstrassCurve.pointCount_eq_card_point_add_one_iff`: adding one is equivalent to the
  existence of a rational singular point.
* `WeierstrassCurve.frobeniusTrace_eq_one_of_splits`,
  `WeierstrassCurve.frobeniusTrace_eq_neg_one_of_not_splits` and
  `WeierstrassCurve.frobeniusTrace_eq_zero_of_c₄_eq_zero`: over a finite field, the trace of a
  singular model is `1` at a split node, `−1` at a nonsplit node and `0` at a cusp.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, III.2.5, V.1.
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

section Trace

open Polynomial

/-- The tangent quadratic `T² + a₁ T - a₂` of a model singular at the origin, whose roots are the
slopes of the tangent lines there. -/
private noncomputable abbrev tangentQuadratic : F[X] :=
  C 1 * X ^ 2 + C W.a₁ * X + C (-W.a₂)

/-- At a model singular at the origin the equation reads `y² + a₁ x y = x³ + a₂ x²`. -/
private theorem equation_iff_of_isSingular_zero (h : W.toAffine.IsSingular 0 0) (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 + W.a₁ * x * y = x ^ 3 + W.a₂ * x ^ 2 := by
  obtain ⟨h₆, h₄, h₃⟩ := (WeierstrassCurve.Affine.isSingular_zero _).1 h
  rw [WeierstrassCurve.Affine.equation_iff, h₆, h₄, h₃]
  ring_nf

/-- **The solutions at a model singular at the origin are parametrised by the tangent slope.**
Away from the origin a solution `(x, y)` has `x ≠ 0`, and its slope `t = y / x` satisfies
`x = t² + a₁ t - a₂`; conversely every `t` off the roots of the tangent quadratic gives the solution
`(t² + a₁ t - a₂, t (t² + a₁ t - a₂))`. So the solutions and the roots together number `q + 1`. -/
private theorem card_equation_add_card_rootSet_of_isSingular_zero [Finite F]
    (h : W.toAffine.IsSingular 0 0) :
    Nat.card {p : F × F // W.toAffine.Equation p.1 p.2} +
      Nat.card ((tangentQuadratic W).rootSet F) = Nat.card F + 1 := by
  classical
  have hE := equation_iff_of_isSingular_zero W h
  set S := {p : F × F // W.toAffine.Equation p.1 p.2}
  -- the only solution with `x = 0` is the origin
  have hx : ∀ p : S, p.1.1 = 0 → p.1 = 0 := by
    rintro ⟨⟨x, y⟩, hp⟩ (rfl : x = 0)
    have : y ^ 2 = 0 := by simpa using (hE 0 y).1 hp
    simp [pow_eq_zero_iff two_ne_zero |>.1 this]
  have hslope : ∀ {x y : F}, x ≠ 0 → W.toAffine.Equation x y →
      (y / x) ^ 2 + W.a₁ * (y / x) - W.a₂ = x := fun hx0 hp ↦ by
    field_simp
    linear_combination (hE _ _).1 hp
  let e : {p : S // p.1.1 ≠ 0} ≃ {t : F // ¬ t ^ 2 + W.a₁ * t - W.a₂ = 0} :=
    { toFun p := ⟨p.1.1.2 / p.1.1.1, by rw [hslope p.2 p.1.2]; exact p.2⟩
      invFun t := ⟨⟨(t.1 ^ 2 + W.a₁ * t.1 - W.a₂, t.1 * (t.1 ^ 2 + W.a₁ * t.1 - W.a₂)),
        (hE _ _).2 (by ring)⟩, t.2⟩
      left_inv := by
        rintro ⟨⟨⟨x, y⟩, hp⟩, hx0⟩
        ext <;> simp only [hslope hx0 hp]
        field_simp
      right_inv := by
        rintro ⟨t, ht⟩
        exact Subtype.ext (mul_div_cancel_right₀ t ht) }
  have hroot : Nat.card ((tangentQuadratic W).rootSet F) =
      Nat.card {t : F // t ^ 2 + W.a₁ * t - W.a₂ = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun t ↦ ?_)
    have h0 : tangentQuadratic W ≠ 0 := fun h0 ↦ by simpa using congrArg (coeff · 2) h0
    rw [mem_rootSet, and_iff_right h0]
    simp [sub_eq_add_neg]
  have h1 : Nat.card {p : S // p.1.1 = 0} = 1 :=
    Nat.card_eq_one_iff_exists.2 ⟨⟨⟨0, (hE 0 0).2 (by ring)⟩, rfl⟩,
      fun p ↦ Subtype.ext (Subtype.ext (hx p.1 p.2))⟩
  rw [hroot, ← Nat.card_congr (Equiv.sumCompl fun p : S ↦ p.1.1 = 0), Nat.card_sum, h1,
    Nat.card_congr e, ← Nat.card_congr (Equiv.sumCompl fun t : F ↦ t ^ 2 + W.a₁ * t - W.a₂ = 0),
    Nat.card_sum]
  omega

/-- The invariants of a model singular at the origin: the tangent quadratic has discriminant `b₂`,
`c₄ = b₂²`, and the node polynomial is `c₄` times the tangent quadratic. -/
private theorem invariants_of_isSingular_zero (h : W.toAffine.IsSingular 0 0) :
    discrim 1 W.a₁ (-W.a₂) = W.b₂ ∧ W.c₄ = W.b₂ ^ 2 ∧
      W.nodePolynomial = C W.c₄ * tangentQuadratic W := by
  obtain ⟨h₆, h₄, h₃⟩ := (WeierstrassCurve.Affine.isSingular_zero _).1 h
  have hb₄ : W.b₄ = 0 := by rw [WeierstrassCurve.b₄, h₄, h₃]; ring
  have hb₆ : W.b₆ = 0 := by rw [WeierstrassCurve.b₆, h₆, h₃]; ring
  refine ⟨by rw [discrim, WeierstrassCurve.b₂]; ring, by rw [WeierstrassCurve.c₄, hb₄]; ring, ?_⟩
  rw [WeierstrassCurve.nodePolynomial_def, hb₄, hb₆, tangentQuadratic]
  simp only [C_mul, C_neg, C_1, mul_zero, sub_zero, zero_add]
  ring

/-- **Moving the singular point to the origin.** Over a finite field a model with `Δ = 0` has a
rational singular point, and translating it to the origin changes neither the trace, nor `c₄`, nor
whether the node polynomial splits. -/
private theorem exists_isSingular_zero_frobeniusTrace_eq [Finite F] (hΔ : W.Δ = 0) :
    ∃ V : WeierstrassCurve F, V.toAffine.IsSingular 0 0 ∧
      W.frobeniusTrace = Nat.card ((tangentQuadratic V).rootSet F) - 1 ∧
      V.c₄ = W.c₄ ∧ (V.nodePolynomial.Splits ↔ W.nodePolynomial.Splits) := by
  obtain ⟨x, y, h⟩ := WeierstrassCurve.Affine.exists_isSingular_of_Δ_eq_zero W.toAffine hΔ
  set C : WeierstrassCurve.VariableChange F := ⟨1, x, 0, y⟩
  have h₀ : (C • W).toAffine.IsSingular 0 0 :=
    (WeierstrassCurve.Affine.isSingular_iff_variableChange _ x y).1 h
  refine ⟨C • W, h₀, ?_, ?_, ?_⟩
  · have := congrArg (Nat.cast : ℕ → ℤ)
      (card_equation_add_card_rootSet_of_isSingular_zero (C • W) h₀)
    push_cast at this
    rw [← WeierstrassCurve.frobeniusTrace_variableChange W C, WeierstrassCurve.frobeniusTrace_def,
      WeierstrassCurve.pointCount_def]
    push_cast
    linarith
  · rw [WeierstrassCurve.variableChange_c₄, inv_one, Units.val_one, one_pow, one_mul]
  · simpa using WeierstrassCurve.splits_variableChange_nodePolynomial_map_iff (RingHom.id F) W C

/-- **The Frobenius trace at a cusp is `0`.** A singular model over a finite field with `c₄ = 0`
has one tangent slope at its singular point, and `q` nonsingular points, the point at infinity
included. -/
theorem _root_.WeierstrassCurve.frobeniusTrace_eq_zero_of_c₄_eq_zero [Finite F] (hΔ : W.Δ = 0)
    (hc₄ : W.c₄ = 0) : W.frobeniusTrace = 0 := by
  obtain ⟨V, h, htr, hc, -⟩ := exists_isSingular_zero_frobeniusTrace_eq W hΔ
  obtain ⟨hd, hb, -⟩ := invariants_of_isSingular_zero V h
  have hd0 : discrim 1 V.a₁ (-V.a₂) = 0 := by
    rw [hd]
    exact (pow_eq_zero_iff two_ne_zero).1 (hb ▸ hc.trans hc₄)
  rw [htr, Nat.card_eq_fintype_card, card_rootSet_quadratic_of_discrim_eq_zero one_ne_zero
    (splits_quadratic_of_discrim_eq_zero one_ne_zero hd0) hd0]
  norm_num

/-- **The Frobenius trace at a split node is `1`.** A singular model over a finite field with
`c₄ ≠ 0` whose node polynomial splits has two rational tangent slopes at its node, and `q - 1`
nonsingular points, the point at infinity included. -/
theorem _root_.WeierstrassCurve.frobeniusTrace_eq_one_of_splits [Finite F] (hΔ : W.Δ = 0)
    (hc₄ : W.c₄ ≠ 0) (hs : W.nodePolynomial.Splits) : W.frobeniusTrace = 1 := by
  obtain ⟨V, h, htr, hc, hsV⟩ := exists_isSingular_zero_frobeniusTrace_eq W hΔ
  obtain ⟨hd, hb, hn⟩ := invariants_of_isSingular_zero V h
  rw [← hsV, hn, splits_mul_iff_right (C_ne_zero.2 (hc ▸ hc₄)) (Splits.C _)] at hs
  have hsep : (tangentQuadratic V).Separable := by
    rw [separable_quadratic_iff_discrim_ne_zero one_ne_zero, hd]
    rintro h0
    exact hc₄ (by rw [← hc, hb, h0]; ring)
  rw [htr, Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree hsep (by rwa [Algebra.algebraMap_self, map_id]),
    natDegree_quadratic one_ne_zero]
  norm_num

/-- **The Frobenius trace at a nonsplit node is `-1`.** A singular model over a finite field with
`c₄ ≠ 0` whose node polynomial does not split has no rational tangent slope at its node, and `q + 1`
nonsingular points, the point at infinity included. -/
theorem _root_.WeierstrassCurve.frobeniusTrace_eq_neg_one_of_not_splits [Finite F]
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) (hs : ¬ W.nodePolynomial.Splits) :
    W.frobeniusTrace = -1 := by
  obtain ⟨V, h, htr, hc, hsV⟩ := exists_isSingular_zero_frobeniusTrace_eq W hΔ
  obtain ⟨-, -, hn⟩ := invariants_of_isSingular_zero V h
  rw [← hsV, hn, splits_mul_iff_right (C_ne_zero.2 (hc ▸ hc₄)) (Splits.C _),
    splits_quadratic_iff_exists_root one_ne_zero] at hs
  have : IsEmpty ((tangentQuadratic V).rootSet F) :=
    ⟨fun t ↦ hs ⟨t.1, by simpa [aeval_def] using (mem_rootSet.1 t.2).2⟩⟩
  rw [htr, Nat.card_of_isEmpty]
  norm_num

end Trace

end TauCeti

end
