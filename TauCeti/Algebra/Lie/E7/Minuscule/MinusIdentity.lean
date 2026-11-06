/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Frobenius
public import TauCeti.Algebra.Lie.E7.Minuscule.Braid
public import TauCeti.Algebra.Lie.E7.Minuscule.Weyl

/-!
# Minus the identity as a root word in the E7 minuscule carrier

Write `xᵢ(u) = rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd u)` and
`yᵢ(u) = rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd u)` for the numbered positive and
negative simple-root points of the full-weight type-`E₇` minuscule carrier, and
`nᵢ = simpleWeylPoint i R = xᵢ(1) yᵢ(-1) xᵢ(1)` for its simple Weyl representatives. The word

```text
n₁² n₄² n₆²
```

in the zero-based nodes `1`, `4`, `6` (Bourbaki nodes `2`, `5`, `7`) has matrix `-1` on the
fifty-six-dimensional minuscule module. Each `nᵢ²` is the torus point `hᵢ(-1)`, acting on the
weight `λ` by `(-1) ^ λᵢ`, and the three chosen nodes are those at which `ϖ₇` has a half-integral
coefficient in the simple-root basis, so every weight of the orbit pairs oddly with
`α₂^∨ + α₅^∨ + α₇^∨` (`TauCeti.DynkinType.odd_e7MinusculeWeight_add_add`).

The resulting point `TauCeti.E7Minuscule.negOnePoint R` lies in every subgroup containing the
fourteen unit-parameter simple-root points, is central in the carrier, squares to one, and is
fixed by every Frobenius endomorphism. Its order divides two, and is exactly two when `1 ≠ -1`
in `R`; in characteristic two it is the identity. It is the central element needed to identify
the centre of the derived subgroup of the Frobenius-fixed subgroup
`fixedSubgroup (frobenius p k R)`, without assuming that the root points generate the carrier's
points.

## Main declarations

* `TauCeti.E7Minuscule.negOnePoint`: the root word `n₁² n₄² n₆²`.
* `TauCeti.E7Minuscule.coe_negOnePoint`: its matrix is `-1`.
* `TauCeti.E7Minuscule.map_negOnePoint`: naturality in the ring of points.
* `TauCeti.E7Minuscule.negOnePoint_mem` and `negOnePoint_mem_center`: it lies in every subgroup
  containing the unit root points, and in the centre of the carrier.
* `TauCeti.E7Minuscule.negOnePoint_pow_two` and `negOnePoint_eq_one_iff`: it squares to one and
  is trivial exactly when `1 = -1` in the ring of points.
* `TauCeti.E7Minuscule.frobenius_simpleWeylPoint`, `frobenius_negOnePoint` and
  `negOnePoint_mem_fixedSubgroup_frobenius`: Frobenius fixes the Weyl representatives and the
  word.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI, for the expression of
  `ϖ₇` in the simple roots.
-/

public section

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType

universe v v'

noncomputable section

variable (R : Type v) [CommRing R]

/-- The product of the three sign factors at the nodes `1`, `4`, `6` is `-1` on every weight. -/
private theorem weight_sign_product (a : Fin 56) :
    (if e7MinusculeWeight a 1 = 0 then (1 : R) else -1) *
        (if e7MinusculeWeight a 4 = 0 then (1 : R) else -1) *
        (if e7MinusculeWeight a 6 = 0 then (1 : R) else -1) = -1 := by
  have h := Int.odd_iff.mp (odd_e7MinusculeWeight_add_add a)
  rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a 1 with h₁ | h₁ | h₁ <;>
    rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a 4 with h₄ | h₄ | h₄ <;>
    rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a 6 with h₆ | h₆ | h₆ <;>
    simp_all

/-- **The root word `n₁² n₄² n₆²` whose matrix is minus the identity.** -/
def negOnePoint : points R :=
  simpleWeylPoint 1 R ^ 2 * simpleWeylPoint 4 R ^ 2 * simpleWeylPoint 6 R ^ 2

/-- The defining product of the root word for minus the identity. -/
theorem negOnePoint_def :
    negOnePoint R =
      simpleWeylPoint 1 R ^ 2 * simpleWeylPoint 4 R ^ 2 * simpleWeylPoint 6 R ^ 2 :=
  (rfl)

/-- The root word for minus the identity is natural in the ring of points. -/
@[simp↓]
theorem map_negOnePoint {A : Type v} {B : Type v'} [CommRing A] [CommRing B] (f : A →+* B) :
    (pointsPresentation A).map (pointsPresentation B) f (negOnePoint A) = negOnePoint B := by
  simp only [negOnePoint_def, map_mul, map_pow]
  rw [map_simpleWeylPoint, map_simpleWeylPoint, map_simpleWeylPoint]

/-- The root word acts as minus the identity on all fifty-six weights. -/
@[simp]
theorem coe_negOnePoint :
    ((negOnePoint R : Matrix.GeneralLinearGroup (Fin 56) R) :
      Matrix (Fin 56) (Fin 56) R) = -1 := by
  simp only [negOnePoint_def, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul,
    Units.val_pow_eq_pow_val, coe_simpleWeylPoint, weightTable.simpleWeylMatrix_pow_two,
    Matrix.diagonal_mul_diagonal]
  rw [weightTable_weight, ← Matrix.diagonal_one, Matrix.diagonal_neg]
  exact congrArg Matrix.diagonal (funext (weight_sign_product R))

/-- Minus the identity belongs to every subgroup containing the fourteen unit root points. -/
theorem negOnePoint_mem (H : Subgroup (points R))
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ H) :
    negOnePoint R ∈ H :=
  H.mul_mem (H.mul_mem (H.pow_mem (simpleWeylPoint_mem 1 (hroots _) (hroots _)) 2)
    (H.pow_mem (simpleWeylPoint_mem 4 (hroots _) (hroots _)) 2))
    (H.pow_mem (simpleWeylPoint_mem 6 (hroots _) (hroots _)) 2)

/-- Minus the identity is central in the carrier. -/
theorem negOnePoint_mem_center : negOnePoint R ∈ Subgroup.center (points R) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_negOnePoint]
  simp

/-- The root word squares to the identity, including in characteristic two. -/
@[simp]
theorem negOnePoint_pow_two : negOnePoint R ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one]
  rw [coe_negOnePoint]
  simp

/-- The word is trivial exactly when `1 = -1` in the ring of points. -/
theorem negOnePoint_eq_one_iff : negOnePoint R = 1 ↔ (1 : R) = -1 := by
  constructor
  · intro h
    have hm := coe_negOnePoint R
    rw [h] at hm
    have hentry := congrFun (congrFun hm 0) 0
    simpa using hentry
  · intro h
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_one, Units.val_one]
    rw [coe_negOnePoint]
    ext a b
    simp only [Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · exact h.symm
    · exact neg_zero

/-- Frobenius fixes every simple Weyl representative. -/
@[simp]
theorem frobenius_simpleWeylPoint (p k : ℕ) [ExpChar R p] (i : Fin 7) :
    frobenius p k R (simpleWeylPoint i R) = simpleWeylPoint i R := by
  rw [frobenius_def, map_simpleWeylPoint]

/-- Frobenius fixes the root word for minus the identity. -/
@[simp]
theorem frobenius_negOnePoint (p k : ℕ) [ExpChar R p] :
    frobenius p k R (negOnePoint R) = negOnePoint R := by
  rw [frobenius_def, map_negOnePoint]

/-- Every Frobenius fixed subgroup contains the root word for minus the identity. -/
theorem negOnePoint_mem_fixedSubgroup_frobenius (p k : ℕ) [ExpChar R p] :
    negOnePoint R ∈ fixedSubgroup (frobenius p k R) :=
  mem_fixedSubgroup.2 (frobenius_negOnePoint R p k)

end

end TauCeti.E7Minuscule
