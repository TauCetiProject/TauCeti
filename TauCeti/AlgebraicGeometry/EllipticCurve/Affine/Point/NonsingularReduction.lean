/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Reduction
-- Proof-only: one Bosma–Lenstra law computes a sum over a local ring and its residue field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.LocalRing

/-!
# The points with nonsingular reduction

Let `v` be a valuation on a field `F`, with valuation ring `O` and residue field `k`, and let `W` be
a Weierstrass curve over `F` with an integral model `W_O` over `O`, reducing to the Weierstrass
curve `W_k = W_O ⊗ k`. No hypothesis is made on the discriminant: `W_k` may be singular. This file
constructs the subgroup `E₀(F)` of the points of `W(F)` whose reduction is a nonsingular point of
`W_k`, and the reduction homomorphism `E₀(F) →+ W_k(k)` to the group of nonsingular points of
`W_k`, which is Mathlib's `WeierstrassCurve.Affine.Point` of the reduced curve. Its kernel is the
kernel of reduction `E₁(F)`, the points whose `x`-coordinate has a pole, and it is surjective when
`O` is Henselian. Together these are the exact sequence `0 → E₁(F) → E₀(F) → W_k(k) → 0` of
Silverman VII.2.1, there stated over a complete discrete valuation ring.

Additivity rests on the two Bosma–Lenstra addition laws. They never vanish together at two
nonsingular points of a Weierstrass curve over a field, singular or not, so at primitive integral
representatives `X` and `Y` of two points of `E₀(F)` one coordinate of one of the laws is a unit of
`O` (`WeierstrassCurve.Projective.exists_isUnimodular_map_equiv_add_of_nonsingular`). That law is
a primitive integral vector representing both the sum over `F` and the sum of the reductions over
`k`. Surjectivity is Hensel's lemma applied to the Weierstrass equation in whichever variable has a
nonvanishing partial derivative at the point of `W_k`
(`WeierstrassCurve.Affine.exists_nonsingular_residue_eq`).

## Main definitions

* `WeierstrassCurve.Affine.Point.nonsingularReduction`: the subgroup `E₀(F)` of points with
  nonsingular reduction.
* `WeierstrassCurve.Affine.Point.nonsingularReductionHom`: the reduction homomorphism
  `E₀(F) →+ W_k(k)`.

## Main results

* `WeierstrassCurve.Affine.Point.reduction_add_of_nonsingularLift`: reduction commutes with
  addition of two points with nonsingular reduction.
* `WeierstrassCurve.Affine.Point.nonsingularReductionHom_eq_zero_iff`: the kernel of the reduction
  homomorphism consists of the point at infinity and the points whose `x`-coordinate has a pole.
* `WeierstrassCurve.Affine.exists_nonsingular_residue_eq`: over a Henselian local ring, every
  nonsingular point of the reduced curve lifts to a nonsingular point.
* `WeierstrassCurve.Affine.Point.nonsingularReductionHom_surjective`: if the valuation ring is
  Henselian, the reduction homomorphism is surjective.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.1.
* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

open IsLocalRing Polynomial

namespace WeierstrassCurve.Affine

/-! ### Hensel's lemma for Weierstrass equations -/

section Hensel

variable {R : Type*} [CommRing R] [HenselianLocalRing R] {W : Affine R}

/-- **Nonsingular points lift along a Henselian local ring.** Over a Henselian local ring `R`, every
nonsingular point of the reduction of a Weierstrass curve `W` to the residue field is the residue
of a nonsingular point of `W`. If `2y + a₁x + a₃` is nonzero at the point, Hensel's lemma lifts the
`y`-coordinate as a simple root of the equation with `x` fixed; otherwise
`a₁y − (3x² + 2a₂x + a₄)` is nonzero and the `x`-coordinate lifts with `y` fixed. -/
theorem exists_nonsingular_residue_eq {x₀ y₀ : R}
    (h : (W.map (residue R)).Nonsingular (residue R x₀) (residue R y₀)) :
    ∃ x y : R, W.Nonsingular x y ∧ residue R x = residue R x₀ ∧ residue R y = residue R y₀ := by
  -- a solution over `R` whose residues are `(res x₀, res y₀)` is nonsingular over `R`, since one
  -- of its partial derivatives has nonzero residue
  have hns {x y : R} (he : W.Equation x y) (hx : residue R x = residue R x₀)
      (hy : residue R y = residue R y₀) : W.Nonsingular x y := by
    rw [← hx, ← hy] at h
    simp only [Nonsingular, map_polynomialX, map_polynomialY, map_mapRingHom_evalEval] at h
    exact ⟨he, h.2.imp (fun hr h0 ↦ hr (by rw [h0, map_zero]))
      (fun hr h0 ↦ hr (by rw [h0, map_zero]))⟩
  rw [nonsingular_iff'] at h
  obtain ⟨he, hX | hY⟩ := h
  · -- lift the `x`-coordinate as a simple root of the monic cubic `W(X, y₀)`, up to sign
    rw [equation_iff'] at he
    set g : R[X] := X ^ 3 + C W.a₂ * X ^ 2 + C (W.a₄ - W.a₁ * y₀) * X +
      C (W.a₆ - y₀ ^ 2 - W.a₃ * y₀) with hg
    have hgm : g.Monic := by rw [hg]; monicity!
    obtain ⟨x, hx, hxx₀⟩ := HenselianLocalRing.is_henselian g hgm x₀
      (by
        rw [← residue_eq_zero_iff, ← neg_eq_zero, ← he]
        simp [hg]
        ring)
      (by
        rw [← residue_ne_zero_iff_isUnit, ← neg_ne_zero]
        convert hX using 1
        simp [hg, derivative_pow, map_ofNat]
        ring)
    have hres : residue R x = residue R x₀ := by
      rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine ⟨x, y₀, hns ?_ hres rfl, hres, rfl⟩
    rw [equation_iff', ← neg_eq_zero, ← hx.eq_zero]
    simp [hg]
    ring
  · -- lift the `y`-coordinate as a simple root of the monic quadratic `W(x₀, Y)`
    rw [equation_iff'] at he
    set f : R[X] := X ^ 2 + C (W.a₁ * x₀ + W.a₃) * X -
      C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hf
    have hfm : f.Monic := by rw [hf]; monicity!
    obtain ⟨y, hy, hyy₀⟩ := HenselianLocalRing.is_henselian f hfm y₀
      (by
        rw [← residue_eq_zero_iff, ← he]
        simp [hf]
        ring)
      (by
        rw [← residue_ne_zero_iff_isUnit]
        convert hY using 1
        simp [hf, derivative_pow, map_ofNat]
        ring)
    have hres : residue R y = residue R y₀ := by
      rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine ⟨x₀, y, hns ?_ rfl hres, rfl, hres⟩
    rw [equation_iff', ← hy.eq_zero]
    simp [hf]
    ring

end Hensel

namespace Point

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]

/-! ### Reduction of a sum -/

/-- **Reduction commutes with addition of points with nonsingular reduction.** If the reductions
of `P` and `Q` are nonsingular points of the reduced curve, the reduction of `P + Q` is the sum of
the reductions on the reduced curve. No hypothesis on the discriminant is needed. -/
theorem reduction_add_of_nonsingularLift [DecidableEq F] {P Q : W.Point}
    (hP : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v P))
    (hQ : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v Q)) :
    reduction v (P + Q) =
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toProjective.addMap
        (reduction v P) (reduction v Q) := by
  obtain ⟨X, hX, hX₁, hPX⟩ := exists_isUnimodular_toProjective_point_eq v P
  obtain ⟨Y, hY, hY₁, hQY⟩ := exists_isUnimodular_toProjective_point_eq v Q
  rw [reduction_eq_mk v hX₁ hPX] at hP
  rw [reduction_eq_mk v hY₁ hQY] at hQ
  -- one primitive integral vector `S` represents both the sum and the sum of the reductions
  obtain ⟨S, -, hS₁, hS⟩ :=
    Projective.exists_isUnimodular_map_equiv_add_of_nonsingular hX hY hP hQ
  -- `baseChange` is `map` along `algebraMap`
  have hW : (integralModel v.valuationSubring W).toProjective.map
      (algebraMap v.valuationSubring F) = W.toProjective :=
    baseChange_integralModel_eq v.valuationSubring W
  -- over `F`, the representatives of `P` and `Q` are nonsingular
  have hXF := hPX ▸ P.toProjective.nonsingular
  have hYF := hQY ▸ Q.toProjective.nonsingular
  rw [← hW] at hXF hYF
  have hPQ : (P + Q).toProjective.point = ⟦algebraMap v.valuationSubring F ∘ S⟧ := by
    have hadd : (P + Q).toProjective = P.toProjective + Q.toProjective := by
      simpa only [Projective.Point.toAffineAddEquiv_symm_apply] using
        _root_.map_add (Projective.Point.toAffineAddEquiv W.toProjective).symm P Q
    have hSF := hS (algebraMap v.valuationSubring F) hXF hYF
    rw [hW] at hSF
    rw [hadd, Projective.Point.add_point, hPX, hQY, Projective.addMap_eq]
    exact (Quotient.sound hSF).symm
  rw [reduction_eq_mk v hS₁ hPQ, reduction_eq_mk v hX₁ hPX, reduction_eq_mk v hY₁ hQY,
    Projective.addMap_eq]
  exact Quotient.sound (hS (residue v.valuationSubring) hP hQ)

/-! ### The subgroup `E₀` -/

variable [DecidableEq F]

variable (W) in
/-- **The points with nonsingular reduction**, the subgroup `E₀(F)` of `W(F)` of points whose
reduction is a nonsingular point of the reduced curve. When the integral model has unit
discriminant every point lies in it; in general it contains the points whose `x`-coordinate has a
pole (`some_mem_nonsingularReduction_of_one_lt`), and an affine point with integral coordinates lies
in it exactly when the residues of its coordinates are a nonsingular point
(`some_mem_nonsingularReduction_iff_of_valuation_le_one`). -/
noncomputable def nonsingularReduction : AddSubgroup W.Point where
  carrier := {P | ((integralModel v.valuationSubring W).map
    (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v P)}
  zero_mem' := by
    simpa only [Set.mem_ofPred_eq, reduction_zero] using Projective.nonsingularLift_zero
  add_mem' {P Q} hP hQ := by
    simp only [Set.mem_ofPred_eq, reduction_add_of_nonsingularLift v hP hQ]
    exact Projective.nonsingularLift_addMap hP hQ
  neg_mem' {P} hP := by
    simp only [Set.mem_ofPred_eq, reduction_neg]
    exact Projective.nonsingularLift_negMap hP

theorem mem_nonsingularReduction_iff {P : W.Point} :
    P ∈ nonsingularReduction v W ↔ ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v P) :=
  Iff.rfl

/-- An affine point with integral `x`-coordinate, whose `y`-coordinate is then integral too, has
nonsingular reduction exactly when the residues of its coordinates are a nonsingular point of the
reduced curve. -/
@[simp]
theorem some_mem_nonsingularReduction_iff_of_valuation_le_one {x y : F} (h : W.Nonsingular x y)
    (hx : v x ≤ 1) :
    some x y h ∈ nonsingularReduction v W ↔
      ((integralModel v.valuationSubring W).map
        (residue v.valuationSubring)).toAffine.Nonsingular
          (residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
          (residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
            (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩) := by
  rw [mem_nonsingularReduction_iff, reduction_some_of_valuation_le_one v h hx,
    Projective.nonsingularLift_some]

/-- A point whose `x`-coordinate has a pole reduces to the point at infinity, which is nonsingular,
so it has nonsingular reduction. -/
@[simp]
theorem some_mem_nonsingularReduction_of_one_lt {x y : F} (h : W.Nonsingular x y)
    (hx : 1 < v x) : some x y h ∈ nonsingularReduction v W := by
  rw [mem_nonsingularReduction_iff, reduction_some_of_one_lt v h hx]
  exact Projective.nonsingularLift_zero

/-! ### The reduction homomorphism on `E₀` -/

variable [DecidableEq (ResidueField v.valuationSubring)]

variable (W) in
/-- **The reduction homomorphism** on the points with nonsingular reduction, a group homomorphism
`E₀(F) →+ W_k(k)` to the nonsingular points of the reduced curve: a point with integral
`x`-coordinate goes to the residues of its coordinates
(`nonsingularReductionHom_some_of_valuation_le_one`), and the other points go to the point at
infinity. -/
noncomputable def nonsingularReductionHom :
    nonsingularReduction v W →+
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toAffine.Point where
  toFun P := Projective.Point.toAffineLift ⟨P.2⟩
  map_zero' := by
    rw [← Projective.Point.toAffineLift_zero]
    exact congrArg _ (Projective.Point.ext (reduction_zero v))
  map_add' P Q := by
    rw [← Projective.Point.toAffineLift_add]
    exact congrArg _ (Projective.Point.ext (reduction_add_of_nonsingularLift v P.2 Q.2))

/-- The reduction homomorphism, read in projective coordinates, is the reduction of points. -/
@[simp]
theorem nonsingularReductionHom_toProjective_point (P : nonsingularReduction v W) :
    (nonsingularReductionHom v W P).toProjective.point = reduction v (P : W.Point) :=
  congrArg Projective.Point.point ((Projective.Point.toAffineAddEquiv _).symm_apply_apply ⟨P.2⟩)

/-- A point with integral `x`-coordinate and nonsingular reduction reduces to the residues of its
coordinates. -/
theorem nonsingularReductionHom_some_of_valuation_le_one {x y : F} (h : W.Nonsingular x y)
    (hx : v x ≤ 1)
    (h' : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toAffine.Nonsingular
        (residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
        (residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩)) :
    nonsingularReductionHom v W
        ⟨some x y h, (some_mem_nonsingularReduction_iff_of_valuation_le_one v h hx).mpr h'⟩ =
      some _ _ h' :=
  (Projective.Point.toAffineAddEquiv _).symm.injective <| Projective.Point.ext <|
    (nonsingularReductionHom_toProjective_point v _).trans
      (reduction_some_of_valuation_le_one v h hx)

/-- A point whose `x`-coordinate has a pole reduces to the point at infinity. -/
@[simp]
theorem nonsingularReductionHom_some_of_one_lt {x y : F} (h : W.Nonsingular x y) (hx : 1 < v x) :
    nonsingularReductionHom v W ⟨some x y h, some_mem_nonsingularReduction_of_one_lt v h hx⟩ = 0 :=
  (Projective.Point.toAffineAddEquiv _).symm.injective <| Projective.Point.ext <|
    (nonsingularReductionHom_toProjective_point v _).trans (reduction_some_of_one_lt v h hx)

/-- **The kernel of reduction** on `E₀(F)`: a point with nonsingular reduction reduces to the point
at infinity exactly when it is the point at infinity or its `x`-coordinate has a pole. These points
form the kernel of reduction `E₁(F)`. -/
theorem nonsingularReductionHom_eq_zero_iff (P : nonsingularReduction v W) :
    nonsingularReductionHom v W P = 0 ↔ (P : W.Point) = 0 ∨ 1 < v (P : W.Point).xCoord := by
  rw [← reduction_eq_zero_iff, ← nonsingularReductionHom_toProjective_point,
    ← (Projective.Point.toAffineAddEquiv _).symm.injective.eq_iff, _root_.map_zero,
    Projective.Point.toAffineAddEquiv_symm_apply, Projective.Point.ext_iff,
    Projective.Point.zero_point]

/-- **Reduction onto the nonsingular points.** If the valuation ring is Henselian, for instance
complete, every nonsingular point of the reduced curve is the reduction of a point of `W(F)` with
nonsingular reduction. -/
theorem nonsingularReductionHom_surjective [HenselianLocalRing v.valuationSubring] :
    Function.Surjective (nonsingularReductionHom v W) := by
  rintro (_ | ⟨a, b, hab⟩)
  · exact ⟨0, by rw [_root_.map_zero]; rfl⟩
  obtain ⟨x₀, rfl⟩ := residue_surjective a
  obtain ⟨y₀, rfl⟩ := residue_surjective b
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_nonsingular_residue_eq hab
  -- the lifted point is a point of `W(F)` with integral coordinates
  have hF : W.Nonsingular (x : F) (y : F) := by
    have := ((integralModel v.valuationSubring W).toAffine.map_nonsingular
      (IsFractionRing.injective v.valuationSubring F) x y).mpr hxy
    rwa [← baseChange_integralModel_eq v.valuationSubring W]
  have hxv : v (x : F) ≤ 1 := (v.mem_valuationSubring_iff _).mp x.2
  refine ⟨⟨some _ _ hF, (some_mem_nonsingularReduction_iff_of_valuation_le_one v hF hxv).mpr
    (hx ▸ hy ▸ hab)⟩, ?_⟩
  rw [nonsingularReductionHom_some_of_valuation_le_one v hF hxv (hx ▸ hy ▸ hab)]
  simp only [hx, hy]

end WeierstrassCurve.Affine.Point

end
