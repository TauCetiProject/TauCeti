/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Basic

/-!
# Unit coefficients of the height-two E₆ root operators

For adjacent numbered nodes `i`, `j`, the integral matrix `[Eᵢ,Eⱼ]` has an entry equal to one.
Choose a minuscule weight with coordinates `0`, `-1` at `i`, `j`: raising first at `j` and then
at `i` is possible, while raising first at `i` is not. This gives the unit entry without a
matrix rank computation or division by a bad prime.

Consequently the height-two root operator remains nonzero over every nontrivial ring,
and the polynomial matrix parametrization `t ↦ 1 + t [Eᵢ,Eⱼ]` is injective over every
ring. These are nondegeneracy inputs for nonsimple root subgroups of the minuscule
carrier; no group-scheme or root-subgroup identification is asserted here.

## Main results

* `TauCeti.E6Minuscule.exists_lie_raisingMatrix_apply_eq_one`: an integral unit coefficient.
* `TauCeti.E6Minuscule.one_add_smul_lie_raisingMatrix_injective`: faithful root parameters.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§13.4 and 27.
-/

public section

namespace TauCeti.E6Minuscule

attribute [local instance 100] LieRing.ofAssociativeRing

/-- At adjacent nodes the integral bracket of the simple raising matrices has an entry equal
to one. This coefficient cannot disappear after reduction modulo a prime. -/
theorem exists_lie_raisingMatrix_apply_eq_one {i j : Fin 6}
    (hij : CartanMatrix.E 6 i j = -1) :
    ∃ a b, ⁅raisingMatrix i, raisingMatrix j⁆ a b = 1 := by
  obtain ⟨b, hbi, hbj⟩ :=
    DynkinType.exists_e6MinusculeWeight_apply_eq_zero_and_eq_neg_one i j hij
  have hji : CartanMatrix.E 6 j i = -1 :=
    ((CartanMatrix.E_isSymm 6).apply i j).trans hij
  have hstep : DynkinType.e6MinusculeWeight (DynkinType.e6MinusculeReflection j b) i = -1 := by
    simpa [hbi, hbj, hji] using weightTable.weight_reflection j b i
  refine ⟨DynkinType.e6MinusculeReflection i (DynkinType.e6MinusculeReflection j b), b, ?_⟩
  simp [Ring.lie_def, Matrix.mul_apply, raisingMatrix_apply, hbi, hbj, hstep]

variable (A : Type*) [Ring A]

/-- The height-two root operator remains nonzero over every nontrivial coefficient ring. -/
theorem map_lie_raisingMatrix_ne_zero [Nontrivial A] {i j : Fin 6}
    (hij : CartanMatrix.E 6 i j = -1) :
    ⁅raisingMatrix i, raisingMatrix j⁆.map (Int.cast : ℤ → A) ≠ 0 := by
  obtain ⟨a, b, hab⟩ := exists_lie_raisingMatrix_apply_eq_one hij
  intro hzero
  have hentry := congrArg (fun M : Matrix (Fin 27) (Fin 27) A ↦ M a b) hzero
  simp only [Matrix.map_apply, hab, Int.cast_one, Matrix.zero_apply] at hentry
  exact one_ne_zero hentry

/-- The polynomial matrices of an adjacent positive root have faithful parameters over every
ring, including noncommutative rings, rings of characteristic two and nonreduced rings. -/
theorem one_add_smul_lie_raisingMatrix_injective {i j : Fin 6}
    (hij : CartanMatrix.E 6 i j = -1) :
    Function.Injective (fun t : A ↦ (1 : Matrix (Fin 27) (Fin 27) A) +
      t • ⁅raisingMatrix i, raisingMatrix j⁆.map (Int.cast : ℤ → A)) := by
  obtain ⟨a, b, hab⟩ := exists_lie_raisingMatrix_apply_eq_one hij
  intro s t h
  have hentry := congrArg (fun M : Matrix (Fin 27) (Fin 27) A ↦ M a b) h
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, hab, Int.cast_one,
    smul_eq_mul, mul_one] at hentry
  exact add_left_cancel hentry

end TauCeti.E6Minuscule
