/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.CubicForm
public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme
import Mathlib.Tactic.Ring

/-!
# Cubic invariance under the generators of the minuscule E₆ carrier

The integral cubic coefficients on the twenty-seven weight lines are invariant under every
numbered positive and negative root-subgroup matrix, and under the weight torus. The equations
hold over every commutative ring, including in characteristics two and three and over nonreduced
rings. They are coefficient identities, not merely identities of polynomial functions on the
rational points of a finite field.

Infinitesimal invariance alone would not justify these assertions in small characteristic.
Here the root matrices are linear in their parameter. Terms involving two or three root moves
vanish by the minuscule weight bounds, while the linear term is the integral derivation identity
proved in `TauCeti.E6Minuscule.cubicForm_raising_invariant` and its lowering counterpart.

These generator equations are inputs to identifying the carrier as a subgroup of the cubic
stabilizer, and thereby recognizing its diagonal intersection. This file does not assert
preservation by every point of the scheme-theoretic closure of the generators.

## References

* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Chapters 5 and 7.
* M. Aschbacher, *The 27-dimensional module for E6. I*, Invent. Math. **89** (1987), 159–195.
* The weight argument parallels the second-order vanishing argument in
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.CrossProduct`.
-/

public section

open scoped Matrix

namespace TauCeti.E6Minuscule

open DynkinType

private theorem cubicForm_two_reflections (i : Fin 6) (a b c : Fin 27) (ε : ℤ)
    (hε : ε = -1 ∨ ε = 1) (ha : e6MinusculeWeight a i = ε)
    (hb : e6MinusculeWeight b i = ε) :
    cubicForm (e6MinusculeReflection i a) (e6MinusculeReflection i b) c = 0 := by
  by_contra h
  have hw := congrFun ((cubicForm_ne_zero_iff _ _ _).mp h) i
  simp only [Pi.add_apply, Pi.zero_apply, e6MinusculeWeight_reflection_apply_self, ha, hb] at hw
  rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one c i with hc | hc | hc <;>
    rcases hε with rfl | rfl <;> omega

private theorem cubicForm_one_add_root (A : Type*) [CommRing A] (i : Fin 6) (ε : ℤ)
    (hε : ε = -1 ∨ ε = 1) (t : A) (a b c : Fin 27) :
    let M : Matrix (Fin 27) (Fin 27) A := fun x y =>
      (if x = y then 1 else 0) +
        if e6MinusculeWeight y i = ε ∧ x = e6MinusculeReflection i y then t else 0
    (∑ x, ∑ y, ∑ z, (cubicForm x y z : A) * M x a * M y b * M z c) =
      (cubicForm a b c : A) := by
  classical
  dsimp only
  have hlin :
      ((if e6MinusculeWeight a i = ε then cubicForm (e6MinusculeReflection i a) b c else 0) +
        (if e6MinusculeWeight b i = ε then cubicForm a (e6MinusculeReflection i b) c else 0) +
        if e6MinusculeWeight c i = ε then cubicForm a b (e6MinusculeReflection i c) else 0) =
        0 := by
    rcases hε with rfl | rfl
    · exact cubicForm_raising_invariant i a b c
    · exact cubicForm_lowering_invariant i a b c
  have hlinA := congrArg (Int.castRingHom A) hlin
  clear hlin
  have hab := cubicForm_two_reflections i a b c ε hε
  have hac := cubicForm_two_reflections i a c b ε hε
  have hbc := cubicForm_two_reflections i b c a ε hε
  have habc := cubicForm_two_reflections i a b (e6MinusculeReflection i c) ε hε
  simp only [ite_and, mul_add, add_mul, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one]
  split_ifs at hlinA ⊢ <;>
    simp_all [cubicForm_swap_left, cubicForm_swap_right] <;>
    linear_combination t * hlinA

/-- Every numbered positive or negative simple-root subgroup preserves the cubic coefficients.
The three columns in the left side are the images of the three input basis vectors. The
identity holds over any commutative ring, without division by two or three. -/
@[simp↓]
theorem cubicForm_rootSubgroupPoints_invariant (A : Type*) [CommRing A] (k : Fin 6 ⊕ Fin 6)
    (u : Multiplicative A) (a b c : Fin 27) :
    let M : Matrix (Fin 27) (Fin 27) A := (rootSubgroupPoints k A u : GL (Fin 27) A)
    (∑ x, ∑ y, ∑ z, (cubicForm x y z : A) * M x a * M y b * M z c) =
      (cubicForm a b c : A) := by
  -- The carrier formulas use the weight table's raising/lowering matrices; compare their
  -- entries with the sparse matrix used in the coefficient calculation.
  rcases k with i | i
  · convert cubicForm_one_add_root A i (-1) (Or.inl rfl) (Multiplicative.toAdd u) a b c using 1
    rw [coe_rootSubgroupPoints_inl]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
      weightTable_raisingMatrix, raisingMatrix_apply, Int.cast_ite, Int.cast_one, Int.cast_zero,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
  · convert cubicForm_one_add_root A i 1 (Or.inr rfl) (Multiplicative.toAdd u) a b c using 1
    rw [coe_rootSubgroupPoints_inr]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
      weightTable_loweringMatrix, loweringMatrix_apply, Int.cast_ite, Int.cast_one, Int.cast_zero,
      smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- Every weight-torus point preserves the cubic coefficients. The nonzero coefficients have
weight zero, so the product of their three torus characters is one. -/
@[simp↓]
theorem cubicForm_weightTorusPoints_invariant (A : Type*) [CommRing A] (s : Fin 6 → Aˣ)
    (a b c : Fin 27) :
    let M : Matrix (Fin 27) (Fin 27) A := (weightTorusPoints A s : GL (Fin 27) A)
    (∑ x, ∑ y, ∑ z, (cubicForm x y z : A) * M x a * M y b * M z c) =
      (cubicForm a b c : A) := by
  classical
  dsimp only
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  simp only [Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, weightTable_weight]
  by_cases h : cubicForm a b c = 0
  · simp [h]
  · have hw := (cubicForm_ne_zero_iff a b c).mp h
    have ht := congrArg (fun w => (torusCharacter s w : A)) hw
    simp only [torusCharacter_add, torusCharacter_zero, Units.val_mul, Units.val_one] at ht
    calc
      _ = (cubicForm a b c : A) *
          (↑(torusCharacter s (e6MinusculeWeight a)) *
            ↑(torusCharacter s (e6MinusculeWeight b)) *
            ↑(torusCharacter s (e6MinusculeWeight c))) := by ring
      _ = _ := by rw [ht, mul_one]

end TauCeti.E6Minuscule
