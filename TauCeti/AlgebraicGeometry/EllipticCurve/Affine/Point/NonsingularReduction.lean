/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Henselian
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
-- Proof-only: one Bosma–Lenstra law computes a sum over a local ring and all its residue fields.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.LocalRing

/-!
# Points with nonsingular reduction

Let `v` be a valuation on a field `F`, with valuation ring `O` and residue field `k`, and let `W`
be a Weierstrass curve over `F` with an integral model `W_O` over `O`. Every point of `W(F)` reduces
to a `k`-point of the reduced curve `W_k = W_O ⊗ k` (`WeierstrassCurve.Affine.Point.reduction`).
When `W_k` is singular, the reduction of a point may be its singular point. This file defines the
subgroup

`E₀(F) = {P ∈ W(F) | the reduction of P is a nonsingular point of W_k}`

and shows that reduction is a group homomorphism `E₀(F) →+ W_k,ns(k)` to the group of nonsingular
points of `W_k`, whose kernel is the kernel of reduction `E₁(F)`: the point at infinity together
with the points whose `x`-coordinate has a pole. This is the left-exact part of Silverman's exact
sequence `0 → E₁(F) → E₀(F) → W_k,ns(k) → 0` (AEC VII.2.1), for an arbitrary valuation and an
arbitrary integral model. The hypotheses are those of the statement: neither ellipticity of `W`,
minimality of `W_O`, discreteness of `v` nor completeness of `F` is assumed.

The subgroup `E₀(F)` depends on the integral model, but only up to changes of variables over `O`:
such a change `C` carries the integral model of `C • W` to `C` applied to that of `W`, and the
isomorphism `(C • W)(F) ≃+ W(F)` it induces carries `E₀` onto `E₀`, since it preserves the points
with a pole in `x` and acts on the reductions of the others by the reduction of `C`. In particular
the index `[W(F) : E₀(F)]` is unchanged, which is what lets it be computed on whichever integral
model of `W` is most convenient, such as the one at which Tate's algorithm stops.

The sequence is also right-exact when `O` is Henselian, for instance complete: the reduction
homomorphism is then surjective. This is Hensel's lemma applied to the Weierstrass equation in
whichever variable has a nonvanishing partial derivative at the point of `W_k`
(`WeierstrassCurve.Affine.exists_nonsingular_residue_eq`).

## Main definitions

* `WeierstrassCurve.Affine.nonsingularReduction`: the subgroup `E₀(F)` of points whose
  reduction is a nonsingular point of the reduced curve.
* `WeierstrassCurve.Affine.nonsingularReductionHom`: the reduction homomorphism
  `E₀(F) →+ W_k,ns(k)`.

## Main results

* `WeierstrassCurve.Affine.Point.reduction_add_of_nonsingularLift`: if `P` and `Q` reduce to
  nonsingular points, then the reduction of `P + Q` is the sum of their reductions.
* `WeierstrassCurve.Affine.some_mem_nonsingularReduction_iff`: an affine point with integral
  coordinates lies in `E₀(F)` exactly when the residues of its coordinates form a nonsingular point
  of the reduced curve.
* `WeierstrassCurve.Affine.mem_nonsingularReduction_of_one_lt`: the kernel of reduction is
  contained in `E₀(F)`.
* `WeierstrassCurve.Affine.equivVariableChange_mem_nonsingularReduction_iff` and
  `WeierstrassCurve.Affine.nonsingularReduction_baseChange_smul`: a change of variables over `O`
  identifies `E₀` of the two integral models.
* `WeierstrassCurve.Affine.index_nonsingularReduction_baseChange_smul`: so the index of `E₀(F)` is
  invariant under changes of variables over `O`.
* `WeierstrassCurve.Affine.nonsingularReductionHom_eq_zero_iff`: the kernel of the reduction
  homomorphism is the kernel of reduction `E₁(F)`.
* `WeierstrassCurve.Affine.mem_ker_nonsingularReductionHom_iff`: the same statement for the kernel
  subgroup `E₁(F)` of `E₀(F)`.
* `WeierstrassCurve.Affine.nonsingularReductionHom_surjective`: if the valuation ring is
  Henselian, the reduction homomorphism is surjective.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.1.
* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

open IsLocalRing Polynomial

namespace WeierstrassCurve.Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W] [DecidableEq F]

namespace Point

/-- **Reduction commutes with addition on points with nonsingular reduction.** If `P` and `Q`
reduce to nonsingular points of the reduced curve, then the reduction of `P + Q` is the sum of the
reductions of `P` and `Q` on the reduced curve. -/
theorem reduction_add_of_nonsingularLift {P Q : W.Point}
    (hP : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v P))
    (hQ : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v Q)) :
    reduction v (P + Q) =
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toProjective.addMap
        (reduction v P) (reduction v Q) := by
  -- Write `P` and `Q` as classes of primitive integral vectors `X` and `Y`. Their residues are
  -- nonsingular points of the reduced curve, where the two Bosma–Lenstra laws do not vanish
  -- simultaneously, so some coordinate of one of the laws at `(X, Y)` is a unit. That law is then
  -- a primitive integral vector `S` whose class is `P + Q` over `F` and whose reduction is the sum
  -- of the reductions of `X` and `Y` over the residue field.
  obtain ⟨X, hX, hX₁, hPX⟩ := exists_isUnimodular_toProjective_point_eq v P
  obtain ⟨Y, hY, hY₁, hQY⟩ := exists_isUnimodular_toProjective_point_eq v Q
  rw [reduction_eq_mk v hX₁ hPX, Projective.nonsingularLift_iff] at hP
  rw [reduction_eq_mk v hY₁ hQY, Projective.nonsingularLift_iff] at hQ
  obtain ⟨S, -, hS₁, hS⟩ := Projective.exists_isUnimodular_map_equiv_add hX hY hP hQ
  -- `baseChange` is `map` along `algebraMap`
  have hW : (integralModel v.valuationSubring W).toProjective.map
      (algebraMap v.valuationSubring F) = W.toProjective :=
    baseChange_integralModel_eq v.valuationSubring W
  have hPQ : (P + Q).toProjective.point = ⟦algebraMap v.valuationSubring F ∘ S⟧ := by
    have hadd : (P + Q).toProjective = P.toProjective + Q.toProjective := by
      simpa only [Projective.Point.toAffineAddEquiv_symm_apply] using
        _root_.map_add (Projective.Point.toAffineAddEquiv W.toProjective).symm P Q
    have hSF := hS (algebraMap v.valuationSubring F)
    rw [hW] at hSF
    rw [hadd, Projective.Point.add_point, hPX, hQY, Projective.addMap_eq]
    exact (Quotient.sound hSF).symm
  rw [reduction_eq_mk v hS₁ hPQ, reduction_eq_mk v hX₁ hPX, reduction_eq_mk v hY₁ hQY,
    Projective.addMap_eq]
  exact Quotient.sound (hS (residue v.valuationSubring))

end Point

variable (W) in
/-- **The subgroup `E₀(F)` of points with nonsingular reduction**: the points of `W(F)` whose
reduction is a nonsingular point of the reduced curve. -/
noncomputable def nonsingularReduction : AddSubgroup W.Point where
  carrier := {P | ((integralModel v.valuationSubring W).map
    (residue v.valuationSubring)).toProjective.NonsingularLift (Point.reduction v P)}
  zero_mem' := by
    rw [Set.mem_ofPred_eq, Point.reduction_zero, Projective.nonsingularLift_iff]
    exact Projective.nonsingular_zero
  add_mem' {P Q} hP hQ := by
    rw [Set.mem_ofPred_eq, Point.reduction_add_of_nonsingularLift v hP hQ]
    exact Projective.nonsingularLift_addMap hP hQ
  neg_mem' {P} hP := by
    rw [Set.mem_ofPred_eq, Point.reduction_neg]
    exact Projective.nonsingularLift_negMap hP

/-- A point lies in `E₀(F)` exactly when its reduction is a nonsingular point of the reduced curve.
-/
@[simp]
theorem mem_nonsingularReduction_iff {P : W.Point} :
    P ∈ W.nonsingularReduction v ↔ ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (Point.reduction v P) :=
  Iff.rfl

-- `high`: tried before `mem_nonsingularReduction_iff`, whose `NonsingularLift` form `simp` cannot
-- reduce to coordinates.
/-- An affine point with integral `x`-coordinate has nonsingular reduction exactly when the
residues of its coordinates form a nonsingular point of the reduced curve. -/
@[simp high]
theorem some_mem_nonsingularReduction_iff {x y : F} (h : W.Nonsingular x y) (hx : v x ≤ 1) :
    Point.some x y h ∈ W.nonsingularReduction v ↔
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toAffine.Nonsingular
        (residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
        (residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩) := by
  rw [mem_nonsingularReduction_iff, Point.reduction_some_of_valuation_le_one v h hx,
    Projective.nonsingularLift_some]

/-- **The kernel of reduction is contained in `E₀(F)`**: a point whose `x`-coordinate has a pole
reduces to the point at infinity, which is nonsingular. -/
theorem mem_nonsingularReduction_of_one_lt {P : W.Point} (hP : 1 < v P.xCoord) :
    P ∈ W.nonsingularReduction v := by
  rw [mem_nonsingularReduction_iff, (Point.reduction_eq_zero_iff v P).mpr (.inr hP),
    Projective.nonsingularLift_iff]
  exact Projective.nonsingular_zero

/-! ### Changes of variables over the valuation ring -/

section VariableChange

variable (C : VariableChange v.valuationSubring)

/-- **A change of variables over the valuation ring preserves nonsingular reduction.** For a change
of variables `C` defined over `O`, the isomorphism `(C • W)(F) ≃ W(F)` it induces sends a point to
a point with nonsingular reduction exactly when the point has nonsingular reduction, for the
integral models `C • W_O` and `W_O`. -/
theorem equivVariableChange_mem_nonsingularReduction_iff {P : (C.baseChange F • W).toAffine.Point} :
    Point.equivVariableChange W (C.baseChange F) P ∈ W.nonsingularReduction v ↔
      P ∈ (C.baseChange F • W).toAffine.nonsingularReduction v := by
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← Point.zero_def, Point.equivVariableChange_zero, zero_mem]
  rw [Point.equivVariableChange_some]
  -- the coefficients of `C`, read in `F`
  have hu : ((C.baseChange F).u : F) = (C.u : v.valuationSubring) := by
    simp [VariableChange.baseChange]
  have hr : (C.baseChange F).r = C.r := by simp [VariableChange.baseChange]
  have hs : (C.baseChange F).s = C.s := by simp [VariableChange.baseChange]
  have ht : (C.baseChange F).t = C.t := by simp [VariableChange.baseChange]
  have hv : v ((C.u : v.valuationSubring) : F) = 1 :=
    (Valuation.valuationSubring.integers v).one_of_isUnit C.u.isUnit
  by_cases hx : v x ≤ 1
  · -- both points have integral coordinates, and their reductions correspond under the reduction
    -- of `C`
    have hx' : v (((C.baseChange F).u : F) ^ 2 * x + (C.baseChange F).r) ≤ 1 := by
      rw [hu, hr]
      exact v.map_add_le (by rw [map_mul, map_pow, hv, one_pow, one_mul]; exact hx) C.r.2
    rw [some_mem_nonsingularReduction_iff v _ hx', some_mem_nonsingularReduction_iff v _ hx,
      integralModel_baseChange_smul, ← map_variableChange]
    convert variableChange_nonsingular ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)) (C.map (residue v.valuationSubring))
      (residue _ ⟨x, (v.mem_valuationSubring_iff x).2 hx⟩) (residue _ ⟨y,
        (v.mem_valuationSubring_iff y).2 (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩)
      using 2
    · simp only [VariableChange.map_u, Units.coe_map, MonoidHom.coe_ofClass, VariableChange.map_r,
        ← map_pow, ← map_mul, ← map_add]
      exact congrArg _ (Subtype.ext (by simp [hu, hr]))
    · simp only [VariableChange.map_u, Units.coe_map, MonoidHom.coe_ofClass, VariableChange.map_s,
        VariableChange.map_t, ← map_pow, ← map_mul, ← map_add]
      exact congrArg _ (Subtype.ext (by simp [hu, hs, ht]))
  · -- both points have a pole in `x`, so both lie in the kernel of reduction
    rw [not_le] at hx
    have hx' : 1 < v (((C.baseChange F).u : F) ^ 2 * x + (C.baseChange F).r) := by
      have hux : v (((C.baseChange F).u : F) ^ 2 * x) = v x := by
        rw [map_mul, map_pow, hu, hv, one_pow, one_mul]
      rwa [Valuation.map_add_eq_of_lt_left _ (by rw [hux, hr]; exact C.r.2.trans_lt hx), hux]
    exact iff_of_true (mem_nonsingularReduction_of_one_lt v (by rwa [Point.xCoord_some]))
      (mem_nonsingularReduction_of_one_lt v (by rwa [Point.xCoord_some]))

/-- **`E₀` of `C • W` is the preimage of `E₀` of `W`** under the isomorphism of point groups induced
by a change of variables `C` over the valuation ring. -/
theorem nonsingularReduction_baseChange_smul :
    (C.baseChange F • W).toAffine.nonsingularReduction v = (W.nonsingularReduction v).comap
      (Point.addEquivVariableChange W (C.baseChange F)).toAddMonoidHom :=
  AddSubgroup.ext fun _ ↦ by
    simp only [AddSubgroup.mem_comap, AddEquiv.coe_toAddMonoidHom,
      Point.coe_addEquivVariableChange, equivVariableChange_mem_nonsingularReduction_iff]

/-- **The index of `E₀` is invariant under changes of variables over the valuation ring**:
`[(C • W)(F) : E₀] = [W(F) : E₀]` for a change of variables `C` defined over `O`. -/
theorem index_nonsingularReduction_baseChange_smul :
    ((C.baseChange F • W).toAffine.nonsingularReduction v).index =
      (W.nonsingularReduction v).index := by
  rw [nonsingularReduction_baseChange_smul,
    AddSubgroup.index_comap_of_surjective _ (AddEquiv.surjective _)]

end VariableChange

variable [DecidableEq (ResidueField v.valuationSubring)]

variable (W) in
/-- **The reduction homomorphism** `E₀(F) →+ W_k,ns(k)`, from the points with nonsingular
reduction to the group of nonsingular points of the reduced curve. A point with integral
`x`-coordinate goes to the residues of its coordinates
(`nonsingularReductionHom_some_of_valuation_le_one`), and the other points go to the point at
infinity. -/
noncomputable def nonsingularReductionHom :
    W.nonsingularReduction v →+
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toAffine.Point where
  toFun P := (⟨P.2⟩ : Projective.Point _).toAffineLift
  map_zero' := by
    have h0 : (⟨(W.nonsingularReduction v).zero_mem⟩ : Projective.Point _) = 0 :=
      Projective.Point.ext ((Point.reduction_zero (W := W) v).trans
        Projective.Point.zero_point.symm)
    exact h0 ▸ Projective.Point.toAffineLift_zero
  map_add' P Q := by
    have hadd : (⟨(P + Q).2⟩ : Projective.Point _) = ⟨P.2⟩ + ⟨Q.2⟩ :=
      Projective.Point.ext ((Point.reduction_add_of_nonsingularLift v P.2 Q.2).trans
        (Projective.Point.add_point ⟨P.2⟩ ⟨Q.2⟩).symm)
    exact hadd ▸ Projective.Point.toAffineLift_add _ _

/-- The reduction homomorphism, read in projective coordinates, is the reduction of points. -/
@[simp]
theorem nonsingularReductionHom_toProjective_point (P : W.nonsingularReduction v) :
    (W.nonsingularReductionHom v P).toProjective.point = Point.reduction v (P : W.Point) :=
  -- `nonsingularReductionHom v P` is `toAffineLift` of the nonsingular projective point `⟨P.2⟩`
  congrArg Projective.Point.point ((Projective.Point.toAffineAddEquiv _).symm_apply_apply ⟨P.2⟩)

/-- A point with nonsingular reduction and integral `x`-coordinate reduces to the residues of its
coordinates. -/
theorem nonsingularReductionHom_some_of_valuation_le_one {x y : F} (h : W.Nonsingular x y)
    (hx : v x ≤ 1)
    (h' : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toAffine.Nonsingular
        (residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
        (residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩)) :
    W.nonsingularReductionHom v
        ⟨Point.some x y h, (some_mem_nonsingularReduction_iff v h hx).mpr h'⟩ =
      Point.some _ _ h' := by
  apply (Projective.Point.toAffineAddEquiv _).symm.injective
  rw [Projective.Point.toAffineAddEquiv_symm_apply, Projective.Point.toAffineAddEquiv_symm_apply,
    Projective.Point.fromAffine_some]
  exact Projective.Point.ext ((nonsingularReductionHom_toProjective_point v _).trans
    (Point.reduction_some_of_valuation_le_one v h hx))

/-- **The kernel of the reduction homomorphism is the kernel of reduction** `E₁(F)`: a point with
nonsingular reduction reduces to the point at infinity exactly when it is the point at infinity or
its `x`-coordinate has a pole. -/
@[simp]
theorem nonsingularReductionHom_eq_zero_iff (P : W.nonsingularReduction v) :
    W.nonsingularReductionHom v P = 0 ↔ (P : W.Point) = 0 ∨ 1 < v (P : W.Point).xCoord := by
  rw [← Point.reduction_eq_zero_iff, ← nonsingularReductionHom_toProjective_point,
    ← (Projective.Point.toAffineAddEquiv _).symm.injective.eq_iff, _root_.map_zero,
    Projective.Point.toAffineAddEquiv_symm_apply, Projective.Point.ext_iff,
    Projective.Point.zero_point]

/-- **The kernel of reduction `E₁(F)` as a subgroup of `E₀(F)`**: a point with nonsingular reduction
lies in the kernel of the reduction homomorphism exactly when it is the point at infinity or its
`x`-coordinate has a pole. -/
theorem mem_ker_nonsingularReductionHom_iff (P : W.nonsingularReduction v) :
    P ∈ (W.nonsingularReductionHom v).ker ↔ (P : W.Point) = 0 ∨ 1 < v (P : W.Point).xCoord := by
  rw [AddMonoidHom.mem_ker, nonsingularReductionHom_eq_zero_iff]

/-- **Reduction onto the nonsingular points.** If the valuation ring is Henselian, for instance
complete, every nonsingular point of the reduced curve is the reduction of a point of `W(F)` with
nonsingular reduction. -/
theorem nonsingularReductionHom_surjective [HenselianLocalRing v.valuationSubring] :
    Function.Surjective (W.nonsingularReductionHom v) := by
  rintro (_ | ⟨a, b, hab⟩)
  · exact ⟨0, _root_.map_zero _⟩
  obtain ⟨x₀, rfl⟩ := residue_surjective a
  obtain ⟨y₀, rfl⟩ := residue_surjective b
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_nonsingular_residue_eq hab
  -- the lifted point is a point of `W(F)` with integral coordinates
  have hF : W.Nonsingular (x : F) (y : F) := by
    have := ((integralModel v.valuationSubring W).toAffine.map_nonsingular
      (IsFractionRing.injective v.valuationSubring F) x y).mpr hxy
    rwa [← baseChange_integralModel_eq v.valuationSubring W]
  have hxv : v (x : F) ≤ 1 := (v.mem_valuationSubring_iff _).mp x.2
  refine ⟨⟨Point.some _ _ hF, (some_mem_nonsingularReduction_iff v hF hxv).mpr
    (hx ▸ hy ▸ hab)⟩, ?_⟩
  rw [nonsingularReductionHom_some_of_valuation_le_one v hF hxv (hx ▸ hy ▸ hab)]
  simp only [hx, hy]

end WeierstrassCurve.Affine

end
