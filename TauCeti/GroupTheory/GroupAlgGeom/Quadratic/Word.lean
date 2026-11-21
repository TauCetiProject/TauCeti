/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Basic
public import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The quadratic words `S₀` and `S₁`

Let `G` be a group, `X` a set of variables, `xᵢ`, `yᵢ` (`i = 1, …, n`), `zⱼ` (`j = 1, …, m`) and
`uₖ` (`k = 1, …, r`) variables, and `cⱼ ∈ G`. This file defines, as elements of the free
`G`-group `G[X]`, the atoms of a quadratic equation: the conjugates `zⱼ⁻¹ cⱼ zⱼ`, the commutators
`[xᵢ, yᵢ] = xᵢ⁻¹ yᵢ⁻¹ xᵢ yᵢ` and the squares `uₖ²`. Their products are the word
`S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]` of an orientable quadratic equation ([IFT], §7.1) and the word
`S₁ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ] ∏ₖ uₖ²` of the mixed form (113), (114) of a non-orientable one
([IFT], §7.5). Both are the product of the atoms that carry variables; the equation multiplies
it by a constant of `G`.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.coeffAtom`, `commAtom`, `sqAtom`: the atoms `zⱼ⁻¹ cⱼ zⱼ`,
  `[xᵢ, yᵢ]` and `uₖ²`.
* `TauCeti.GroupAlgGeom.Quadratic.basicWord`: the word `S₀`.
* `TauCeti.GroupAlgGeom.Quadratic.basicMixedAtoms`, `basicMixedWord`: the atoms of `S₁`, in
  order, and the word `S₁`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.eval_coeffAtom`, `eval_commAtom`, `eval_sqAtom`,
  `eval_basicWord`, `eval_basicMixedWord`: the values of the atoms and of the words at a point.
* `TauCeti.GroupAlgGeom.Quadratic.basicMixedWord_eq_basicWord_mul`: `S₁` is `S₀` followed by the
  squares.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1 and §7.5, (113) and (114).
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic

variable {G X : Type*} [Group G] {n m r : ℕ}

variable (x y : Fin n → X) (z : Fin m → X) (u : Fin r → X) (c : Fin m → G)

/-- The conjugate `z_j⁻¹ c_j z_j` of the coefficient `c_j` by the variable `z_j`. -/
def coeffAtom (j : Fin m) : GX G X :=
  (inr (.of (z j)))⁻¹ * inl (c j) * inr (.of (z j))

/-- The commutator `[x_i, y_i] = x_i⁻¹ y_i⁻¹ x_i y_i` of two variables. -/
def commAtom (i : Fin n) : GX G X :=
  ⁅(inr (.of (x i)) : GX G X)⁻¹, (inr (.of (y i)))⁻¹⁆

/-- The square `uₖ²` of a variable. -/
def sqAtom (k : Fin r) : GX G X :=
  inr (.of (u k)) ^ 2

/-- The word `S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]` of [IFT], §7.1. -/
def basicWord : GX G X :=
  (List.ofFn (coeffAtom z c)).prod * (List.ofFn (commAtom (G := G) x y)).prod

/-- The atoms of the word `S₁`, in order: the conjugates `zⱼ⁻¹ cⱼ zⱼ`, then the commutators
`[xᵢ, yᵢ]`, then the squares `uₖ²`. -/
def basicMixedAtoms : List (GX G X) :=
  List.ofFn (coeffAtom z c) ++ (List.ofFn (commAtom x y) ++ List.ofFn (sqAtom u))

/-- The word `S₁ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ] ∏ₖ uₖ²` of [IFT], §7.5: the product of the atoms that
carry variables in the mixed form (113), (114) of a non-orientable quadratic equation, whose left
side is `S₁` times a constant. -/
def basicMixedWord : GX G X :=
  (basicMixedAtoms x y z u c).prod

theorem coeffAtom_def (j : Fin m) :
    coeffAtom z c j = (inr (.of (z j)))⁻¹ * inl (c j) * inr (.of (z j)) := (rfl)

theorem commAtom_def (i : Fin n) :
    commAtom (G := G) x y i = ⁅(inr (.of (x i)) : GX G X)⁻¹, (inr (.of (y i)))⁻¹⁆ := (rfl)

theorem sqAtom_def (k : Fin r) : sqAtom (G := G) u k = inr (.of (u k)) ^ 2 := (rfl)

theorem basicWord_def :
    basicWord x y z c =
      (List.ofFn (coeffAtom z c)).prod * (List.ofFn (commAtom (G := G) x y)).prod := (rfl)

theorem basicMixedAtoms_def :
    basicMixedAtoms x y z u c =
      List.ofFn (coeffAtom z c) ++ (List.ofFn (commAtom x y) ++ List.ofFn (sqAtom u)) := (rfl)

theorem basicMixedWord_def : basicMixedWord x y z u c = (basicMixedAtoms x y z u c).prod := (rfl)

/-- The word `S₁` is the word `S₀` followed by the squares `uₖ²`. -/
theorem basicMixedWord_eq_basicWord_mul :
    basicMixedWord x y z u c = basicWord x y z c * (List.ofFn (sqAtom (G := G) u)).prod := by
  simp [basicMixedWord_def, basicMixedAtoms_def, basicWord_def, mul_assoc]

variable {H : Type*} [Group H] (ι : G →* H) (v : X → H)

@[simp]
theorem eval_coeffAtom (j : Fin m) :
    eval ι v (coeffAtom z c j) = (v (z j))⁻¹ * ι (c j) * v (z j) := by
  simp [coeffAtom_def]

@[simp]
theorem eval_commAtom (i : Fin n) : eval ι v (commAtom x y i) = ⁅(v (x i))⁻¹, (v (y i))⁻¹⁆ := by
  simp [commAtom_def, map_commutatorElement]

@[simp]
theorem eval_sqAtom (k : Fin r) : eval ι v (sqAtom (G := G) u k) = v (u k) ^ 2 := by
  simp [sqAtom_def]

/-- The value of the word `S₀` at a point `v`: `∏ⱼ v(zⱼ)⁻¹ ι(cⱼ) v(zⱼ) ∏ᵢ [v(xᵢ), v(yᵢ)]`. -/
@[simp]
theorem eval_basicWord :
    eval ι v (basicWord x y z c) =
      (List.ofFn fun j => (v (z j))⁻¹ * ι (c j) * v (z j)).prod *
        (List.ofFn fun i => ⁅(v (x i))⁻¹, (v (y i))⁻¹⁆).prod := by
  simp [basicWord_def, map_list_prod, List.map_ofFn, Function.comp_def]

/-- The value of the word `S₁` at a point `v`: the value of `S₀` times `∏ₖ v(uₖ)²`. -/
@[simp]
theorem eval_basicMixedWord :
    eval ι v (basicMixedWord x y z u c) =
      eval ι v (basicWord x y z c) * (List.ofFn fun k => v (u k) ^ 2).prod := by
  simp [basicMixedWord_eq_basicWord_mul, map_list_prod, List.map_ofFn, Function.comp_def]

end TauCeti.GroupAlgGeom.Quadratic
