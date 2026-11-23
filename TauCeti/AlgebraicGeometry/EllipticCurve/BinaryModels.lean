/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.FieldTheory.Finite.Basic

/-!
# The five Weierstrass models over `𝔽₂`

There are `2⁵ = 32` Weierstrass equations

`y² + a₁ x y + a₃ y = x³ + a₂ x² + a₄ x + a₆`

with coefficients in `𝔽₂ = ZMod 2`, and exactly sixteen of them are elliptic. This file sorts
them into isomorphism classes. Over `𝔽₂` every element satisfies `a² = a`, so the discriminant
collapses to `a₃` when `a₁ = 0` and to `a₆ + a₄ + a₃ (a₄ + a₂)` when `a₁ = 1`; the only unit is
`1`, so a change of variables is a triple `(r, s, t)` with `u = 1`, and the `j`-invariant of an
elliptic equation is `a₁`.

The five models `TauCeti.F2Model i`, `i : Fin 5`, are

| `i` | equation | points |
|-----|----------|--------|
| 0 | `y² + y = x³ + x² + 1` | 1 |
| 1 | `y² + x y = x³ + x² + x` | 2 |
| 2 | `y² + y = x³` | 3 |
| 3 | `y² + x y = x³ + x` | 4 |
| 4 | `y² + y = x³ + x²` | 5 |

Every elliptic equation is carried onto exactly one of them by a change of variables, the orbits
having sizes `2, 4, 4, 4, 2`. Existence is a finite check over the sixteen elliptic equations,
with these witnesses `(r, s, t)`:

| `(a₁, a₂, a₃, a₄, a₆)` | model | `(r, s, t)` |
|------------------------|-------|-------------|
| `(0, 0, 1, 0, 0)` | 2 | `(0, 0, 0)` |
| `(0, 0, 1, 0, 1)` | 2 | `(1, 1, 0)` |
| `(0, 0, 1, 1, 0)` | 4 | `(0, 1, 0)` |
| `(0, 0, 1, 1, 1)` | 0 | `(0, 1, 0)` |
| `(0, 1, 1, 0, 0)` | 4 | `(0, 0, 0)` |
| `(0, 1, 1, 0, 1)` | 0 | `(0, 0, 0)` |
| `(0, 1, 1, 1, 0)` | 2 | `(0, 1, 0)` |
| `(0, 1, 1, 1, 1)` | 2 | `(1, 0, 0)` |
| `(1, 0, 0, 0, 1)` | 3 | `(0, 0, 1)` |
| `(1, 0, 0, 1, 0)` | 3 | `(0, 0, 0)` |
| `(1, 0, 1, 0, 1)` | 1 | `(1, 0, 0)` |
| `(1, 0, 1, 1, 1)` | 1 | `(1, 0, 1)` |
| `(1, 1, 0, 0, 1)` | 1 | `(0, 0, 1)` |
| `(1, 1, 0, 1, 0)` | 1 | `(0, 0, 0)` |
| `(1, 1, 1, 0, 0)` | 3 | `(1, 0, 0)` |
| `(1, 1, 1, 1, 0)` | 3 | `(1, 0, 1)` |

Uniqueness comes from the point counts `1, …, 5`, which a change of variables preserves
(`WeierstrassCurve.variableChange_pointCount`). So the point count alone classifies elliptic
equations over `𝔽₂` up to change of variables. Ellipticity is needed for this: the cuspidal
equation `y² = x³` also has three points. The `j`-invariant does not classify: the models `0`, `2`
and `4` all have `j = 0`.

Finally the four-point group of model `3` is cyclic: on `y² + x y = x³ + x` the point `(1, 0)` has
order four, with `2 • (1, 0) = (0, 0)`.

## Main definitions

* `TauCeti.F2Model`: the five Weierstrass models over `ZMod 2`, indexed by `Fin 5` in increasing
  order of point count.

## Main results

* `WeierstrassCurve.Δ_of_zmod_two`: the discriminant of a Weierstrass equation over `ZMod 2`.
* `WeierstrassCurve.isElliptic_iff_of_zmod_two`: the sixteen elliptic equations.
* `WeierstrassCurve.variableChange_of_zmod_two`: the action of a change of variables over `ZMod 2`.
* `WeierstrassCurve.j_of_zmod_two`: the `j`-invariant of an elliptic equation over `ZMod 2` is
  `a₁`.
* `TauCeti.pointCount_F2Model`: the `i`-th model has `i + 1` points.
* `WeierstrassCurve.exists_variableChange_smul_eq_F2Model`: every elliptic equation over `ZMod 2`
  is carried onto some model by a change of variables.
* `TauCeti.exists_variableChange_smul_F2Model_eq_iff`: the models lie in distinct orbits.
* `WeierstrassCurve.existsUnique_variableChange_smul_eq_F2Model`: every elliptic equation over
  `ZMod 2` lies in the orbit of exactly one model, the one with the same number of points.
* `WeierstrassCurve.exists_variableChange_smul_eq_iff_pointCount_eq`: two elliptic equations
  over `ZMod 2` are related by a change of variables exactly when they have the same number of
  points.
* `TauCeti.addOrderOf_F2Model_three_some_one_zero` and `TauCeti.isAddCyclic_F2Model_three`: the
  point `(1, 0)` of model `3` has order four, so the four-point group of model `3` is cyclic.

## References

* S. Schröer, *There is no Enriques surface over the integers*, arXiv:2004.07025v3,
  Proposition 3.3 and the table preceding it, for the five classes and their point counts.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, Appendix A.
-/

public section

namespace WeierstrassCurve

variable (W : WeierstrassCurve (ZMod 2))

/-- **The discriminant over `𝔽₂`**: it is `a₃` when `a₁ = 0` and `a₆ + a₄ + a₃ (a₄ + a₂)` when
`a₁ = 1`. The formula uses `a² = a` in `𝔽₂` and does not hold over larger fields of
characteristic two. -/
theorem Δ_of_zmod_two :
    W.Δ = if W.a₁ = 0 then W.a₃ else W.a₆ + W.a₄ + W.a₃ * (W.a₄ + W.a₂) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₆⟩ := W
  revert a₁ a₂ a₃ a₄ a₆
  decide

/-- **The elliptic equations over `𝔽₂`**: either `a₁ = 0` and `a₃ = 1`, with `a₂, a₄, a₆` free,
or `a₁ = 1` and `a₆ = 1 + a₄ + a₃ (a₄ + a₂)`, with `a₂, a₃, a₄` free. These are sixteen of the
thirty-two equations. -/
theorem isElliptic_iff_of_zmod_two :
    W.IsElliptic ↔
      W.a₁ = 0 ∧ W.a₃ = 1 ∨ W.a₁ = 1 ∧ W.a₆ = 1 + W.a₄ + W.a₃ * (W.a₄ + W.a₂) := by
  rw [isElliptic_iff, Δ_of_zmod_two, isUnit_iff_ne_zero]
  obtain ⟨a₁, a₂, a₃, a₄, a₆⟩ := W
  revert a₁ a₂ a₃ a₄ a₆
  decide

/-- **The `j`-invariant over `𝔽₂`**: an elliptic equation over `ZMod 2` has `j = a₁`. In
particular `j` takes only the values `0` and `1`, and it does not separate the five
isomorphism classes. -/
theorem j_of_zmod_two [W.IsElliptic] : W.j = W.a₁ := by
  have h := W.j_eq_zero_iff_of_char_two
  generalize W.j = j at h ⊢
  revert j
  generalize W.a₁ = a
  revert a
  decide

/-- **A change of variables over `𝔽₂`.** Its `u` is `1`, the only unit of `ZMod 2`, and with
`x² = x` the action on coefficients takes the displayed form. -/
theorem variableChange_of_zmod_two (C : VariableChange (ZMod 2)) :
    C • W = ⟨W.a₁, W.a₂ + C.s * W.a₁ + C.r + C.s, W.a₃ + C.r * W.a₁,
      W.a₄ + C.s * W.a₃ + (C.t + C.r * C.s) * W.a₁ + C.r,
      W.a₆ + C.r * W.a₄ + C.r * W.a₂ + C.r + C.t * W.a₃ + C.t + C.r * C.t * W.a₁⟩ := by
  have hu : C.u = 1 := Subsingleton.elim _ _
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hr : C.r ^ 2 = C.r := ZMod.pow_card C.r
  have hs : C.s ^ 2 = C.s := ZMod.pow_card C.s
  have ht : C.t ^ 2 = C.t := ZMod.pow_card C.t
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, hu, inv_one, Units.val_one, one_pow, one_mul]
  · linear_combination C.s * h2
  · linear_combination (-C.s * W.a₁ + C.r - C.s) * h2 - hs
  · linear_combination C.t * h2
  · linear_combination
      (-C.s * W.a₃ + C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + C.r ^ 2 - C.s * C.t) * h2 + hr
  · linear_combination (-C.t * W.a₃ - C.t - C.r * C.t * W.a₁) * h2 + (W.a₂ + C.r + 1) * hr - ht

end WeierstrassCurve

namespace TauCeti

open WeierstrassCurve

/-- **The five Weierstrass models over `𝔽₂`**, indexed in increasing order of point count: the
`i`-th model has `i + 1` points (`TauCeti.pointCount_F2Model`). Every elliptic equation over
`ZMod 2` is carried onto exactly one of them by a change of variables. -/
def F2Model : Fin 5 → WeierstrassCurve (ZMod 2) :=
  ![⟨0, 1, 1, 0, 1⟩, ⟨1, 1, 0, 1, 0⟩, ⟨0, 0, 1, 0, 0⟩, ⟨1, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0⟩]

/-- The model with one point: `y² + y = x³ + x² + 1`. -/
@[simp]
theorem F2Model_zero : F2Model 0 = ⟨0, 1, 1, 0, 1⟩ := (rfl)

/-- The model with two points: `y² + x y = x³ + x² + x`. -/
@[simp]
theorem F2Model_one : F2Model 1 = ⟨1, 1, 0, 1, 0⟩ := (rfl)

/-- The model with three points: `y² + y = x³`. -/
@[simp]
theorem F2Model_two : F2Model 2 = ⟨0, 0, 1, 0, 0⟩ := (rfl)

/-- The model with four points: `y² + x y = x³ + x`. -/
@[simp]
theorem F2Model_three : F2Model 3 = ⟨1, 0, 0, 1, 0⟩ := (rfl)

/-- The model with five points: `y² + y = x³ + x²`. -/
@[simp]
theorem F2Model_four : F2Model 4 = ⟨0, 1, 1, 0, 0⟩ := (rfl)

/-- Every model has discriminant `1`. -/
@[simp]
theorem Δ_F2Model (i : Fin 5) : (F2Model i).Δ = 1 := by
  rw [Δ_of_zmod_two]
  fin_cases i <;> decide

instance (i : Fin 5) : (F2Model i).IsElliptic :=
  (isElliptic_iff _).2 <| by rw [Δ_F2Model]; exact isUnit_one

/-- The `j`-invariants of the five models are `0, 1, 0, 1, 0`. -/
theorem j_F2Model (i : Fin 5) : (F2Model i).j = ![0, 1, 0, 1, 0] i := by
  rw [j_of_zmod_two]
  fin_cases i <;> rfl

/-! ### Affine solutions and point counts -/

/-- **The affine solutions of the five models**: none for model `0`; `(0, 0)` for model `1`;
`(0, 0)` and `(0, 1)` for model `2`; `(0, 0)`, `(1, 0)` and `(1, 1)` for model `3`; and all four
points of the affine plane for model `4`. -/
theorem setOf_equation_F2Model (i : Fin 5) :
    {p : ZMod 2 × ZMod 2 | (F2Model i).toAffine.Equation p.1 p.2} =
      ![∅, {(0, 0)}, {(0, 0), (0, 1)}, {(0, 0), (1, 0), (1, 1)}, Set.univ] i := by
  ext ⟨x, y⟩
  revert x y
  fin_cases i <;> simp +decide [Affine.equation_iff]

/-- **The `i`-th model has `i + 1` points**, the point at infinity included. -/
theorem pointCount_F2Model (i : Fin 5) : (F2Model i).pointCount = i + 1 := by
  rw [pointCount_def, ← Set.coe_ofPred, setOf_equation_F2Model, Nat.card_coe_set_eq]
  fin_cases i <;> simp [Set.ncard_insert_of_notMem]

/-- Two models have the same number of points only when they are the same model. -/
theorem pointCount_F2Model_inj {i j : Fin 5} :
    (F2Model i).pointCount = (F2Model j).pointCount ↔ i = j := by
  rw [pointCount_F2Model, pointCount_F2Model, add_left_inj, Fin.val_inj]

/-- The five models are distinct. -/
theorem F2Model_injective : Function.Injective F2Model := fun _ _ h ↦
  pointCount_F2Model_inj.1 (congrArg pointCount h)

/-! ### Classification up to change of variables -/

/-- **The models lie in distinct orbits**: a change of variables carries the `i`-th model onto
the `j`-th only when `i = j`, since it preserves the point count. A model can have nontrivial
automorphisms, so the change itself need not be the identity. -/
theorem exists_variableChange_smul_F2Model_eq_iff (i j : Fin 5) :
    (∃ C : VariableChange (ZMod 2), C • F2Model i = F2Model j) ↔ i = j := by
  refine ⟨fun ⟨C, h⟩ ↦ pointCount_F2Model_inj.1 ?_, fun h ↦ ⟨1, by rw [one_smul, h]⟩⟩
  rw [← h, variableChange_pointCount]

end TauCeti

namespace WeierstrassCurve

open TauCeti

/-- **Every elliptic equation over `𝔽₂` is carried onto a model by a change of variables.** The
witnesses are listed in the module docstring. -/
theorem exists_variableChange_smul_eq_F2Model (W : WeierstrassCurve (ZMod 2)) [W.IsElliptic] :
    ∃ i, ∃ C : VariableChange (ZMod 2), C • W = F2Model i := by
  have h := (isElliptic_iff_of_zmod_two W).1 ‹_›
  suffices ∃ i, ∃ r s t : ZMod 2, (⟨1, r, s, t⟩ : VariableChange (ZMod 2)) • W = F2Model i by
    obtain ⟨i, r, s, t, h⟩ := this
    exact ⟨i, _, h⟩
  simp only [variableChange_of_zmod_two, WeierstrassCurve.ext_iff]
  revert h
  generalize W.a₁ = a₁, W.a₂ = a₂, W.a₃ = a₃, W.a₄ = a₄, W.a₆ = a₆
  revert a₁ a₂ a₃ a₄ a₆
  decide

/-- An elliptic equation over `𝔽₂` is carried onto the `i`-th model exactly when it has `i + 1`
points. -/
theorem exists_variableChange_smul_eq_F2Model_iff (W : WeierstrassCurve (ZMod 2)) [W.IsElliptic]
    (i : Fin 5) :
    (∃ C : VariableChange (ZMod 2), C • W = F2Model i) ↔ W.pointCount = i + 1 := by
  refine ⟨fun ⟨C, h⟩ ↦ by rw [← variableChange_pointCount W C, h, pointCount_F2Model], fun h ↦ ?_⟩
  obtain ⟨j, C, hC⟩ := exists_variableChange_smul_eq_F2Model W
  rw [← variableChange_pointCount W C, hC, ← pointCount_F2Model i, pointCount_F2Model_inj] at h
  exact ⟨C, by rw [hC, h]⟩

/-- **Every elliptic equation over `𝔽₂` lies in the orbit of exactly one model.** By
`WeierstrassCurve.exists_variableChange_smul_eq_F2Model_iff`, that model is the one with the same
number of points, so an elliptic equation over `𝔽₂` has between one and five points. -/
theorem existsUnique_variableChange_smul_eq_F2Model (W : WeierstrassCurve (ZMod 2))
    [W.IsElliptic] : ∃! i, ∃ C : VariableChange (ZMod 2), C • W = F2Model i := by
  obtain ⟨i, C, hC⟩ := exists_variableChange_smul_eq_F2Model W
  refine ⟨i, ⟨C, hC⟩, fun j ⟨D, hD⟩ ↦ ?_⟩
  refine (exists_variableChange_smul_F2Model_eq_iff i j).1 ⟨D * C⁻¹, ?_⟩ |>.symm
  rw [mul_smul, ← hC, inv_smul_smul, hD]

/-- **The point count classifies elliptic equations over `𝔽₂`**: two of them are related by a
change of variables exactly when they have the same number of points. Ellipticity is needed: the
cuspidal equation `y² = x³` has three points, as does the elliptic `y² + y = x³`. -/
theorem exists_variableChange_smul_eq_iff_pointCount_eq (W V : WeierstrassCurve (ZMod 2))
    [W.IsElliptic] [V.IsElliptic] :
    (∃ C : VariableChange (ZMod 2), C • W = V) ↔ W.pointCount = V.pointCount := by
  refine ⟨fun ⟨C, h⟩ ↦ by rw [← h, variableChange_pointCount], fun h ↦ ?_⟩
  obtain ⟨i, C, hC⟩ := exists_variableChange_smul_eq_F2Model W
  obtain ⟨D, hD⟩ := (exists_variableChange_smul_eq_F2Model_iff V i).2 <| by
    rw [← h, ← variableChange_pointCount W C, hC, pointCount_F2Model]
  exact ⟨D⁻¹ * C, by rw [mul_smul, hC, ← hD, inv_smul_smul]⟩

end WeierstrassCurve

namespace TauCeti

open WeierstrassCurve

/-! ### The point group of model `3` -/

/-- `(1, 0)` is a nonsingular point of `y² + x y = x³ + x`. -/
theorem nonsingular_F2Model_three_one_zero : (F2Model 3).toAffine.Nonsingular 1 0 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff, F2Model_three]
  decide

/-- `(0, 0)` is a nonsingular point of `y² + x y = x³ + x`. -/
theorem nonsingular_F2Model_three_zero_zero : (F2Model 3).toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff, F2Model_three]
  decide

/-- On `y² + x y = x³ + x`, doubling `(1, 0)` gives `(0, 0)`: the tangent at `(1, 0)` has
slope `0`. -/
theorem F2Model_three_some_one_zero_add_self :
    (Affine.Point.some _ _ nonsingular_F2Model_three_one_zero +
        Affine.Point.some _ _ nonsingular_F2Model_three_one_zero : (F2Model 3).toAffine.Point) =
      Affine.Point.some _ _ nonsingular_F2Model_three_zero_zero := by
  have hy : (0 : ZMod 2) ≠ (F2Model 3).toAffine.negY 1 0 := by
    simp only [Affine.negY, F2Model_three]
    decide
  -- the tangent at `(1, 0)` has slope `(3 x² + 2 a₂ x + a₄ - a₁ y) / (2 y + a₁ x + a₃) = 4 / 1`
  have hℓ : (F2Model 3).toAffine.slope 1 1 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy, div_eq_zero_iff, F2Model_three]
    exact Or.inl (by decide)
  rw [Affine.Point.add_of_Y_ne hy, Affine.Point.some.injEq, hℓ]
  simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, F2Model_three]
  decide

/-- On `y² + x y = x³ + x`, the point `(0, 0)` has order two: its tangent is vertical. -/
theorem F2Model_three_some_zero_zero_add_self :
    (Affine.Point.some _ _ nonsingular_F2Model_three_zero_zero +
        Affine.Point.some _ _ nonsingular_F2Model_three_zero_zero : (F2Model 3).toAffine.Point) =
      0 :=
  Affine.Point.add_self_of_Y_eq <| by simp only [Affine.negY, F2Model_three]; decide

/-- On `y² + x y = x³ + x`, the point `(1, 0)` has order four. -/
theorem addOrderOf_F2Model_three_some_one_zero :
    addOrderOf (Affine.Point.some _ _ nonsingular_F2Model_three_one_zero :
      (F2Model 3).toAffine.Point) = 4 := by
  have h2 : 2 • (Affine.Point.some _ _ nonsingular_F2Model_three_one_zero :
      (F2Model 3).toAffine.Point) = Affine.Point.some _ _ nonsingular_F2Model_three_zero_zero := by
    rw [two_nsmul, F2Model_three_some_one_zero_add_self]
  refine addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, h2]
    exact Affine.Point.some_ne_zero _
  · rw [pow_succ, pow_one, mul_nsmul, h2, two_nsmul, F2Model_three_some_zero_zero_add_self]

/-- **The four-point group of `y² + x y = x³ + x` is cyclic**, generated by `(1, 0)`; it is not
the Klein four-group. -/
theorem isAddCyclic_F2Model_three : IsAddCyclic (F2Model 3).toAffine.Point := by
  have hcard : Nat.card (F2Model 3).toAffine.Point = 4 := by
    rw [← pointCount_eq_card_point, pointCount_F2Model]
    rfl
  have : Finite (F2Model 3).toAffine.Point := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  exact isAddCyclic_of_addOrderOf_eq_card _ <|
    addOrderOf_F2Model_three_some_one_zero.trans hcard.symm

end TauCeti
