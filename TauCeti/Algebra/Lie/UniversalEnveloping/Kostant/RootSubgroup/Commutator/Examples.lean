/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PositiveRoot
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.G2.Relations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.IntegralMatrix
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.MultiplyLacedRelations

/-!
# Explicit matrix checks for Steinberg's Chevalley commutator relations

This file instantiates the Kostant root-subgroup commutator relations via
`TauCeti.UniversalEnvelopingAlgebra.integralMatrixRootSubgroup` on three integral matrix
representations over any commutative ring `R`, checking signs and exponents in `⁅x, y⁆ = xyx⁻¹y⁻¹`:

1. **Type `A₂` on `R³`** (`a2RootMatrix`): `⁅x_α(u), x_β(v)⁆ = x_{α+β}(u * v)`, falsified upon
   negating `N_{α,β}` iff `(2 : R) ≠ 0`.
2. **Type `C₂ = Sp₄` on `R⁴`** (`c2RootMatrix`): `⁅x_α(u), x_β(v)⁆ = x_{α+β}(-(u * v)) *
   x_{α+2β}(-(u * v ^ 2))`, with `(0, 2)` entry `-1` at `u = v = 1` (falsifying `+1` iff `2 ≠ 0`).
3. **Type `G₂` on `R⁷`** (`TauCeti.G2ShortRoot.positiveRootMatrix`): checks `⁅x_α(u), x_β(v)⁆`,
   `⁅x_β(u), x_α(v)⁆`, and `⁅x_α(u), x_{α+β}(v)⁆`, falsifying `-c_{3,2}` or `-c_{2,3}` when `4 ≠ 0`
   or `2 ≠ 0`.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.a2RootMatrix`, `c2RootMatrix`, and root subgroups
  `a2RootSubgroup`, `c2RootSubgroup`, `g2PosRootSubgroup`.
* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_a2RootSubgroup`,
  `commutatorElement_c2RootSubgroup`, `commutatorElement_g2PosRootSubgroup_short_long`,
  `commutatorElement_g2PosRootSubgroup_long_short`, and
  `commutatorElement_g2PosRootSubgroup_short_short` (with `_iff` sign-falsification checks).

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15, pp. 22--25.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I, III, and IX.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§19.3 and 25--27.
-/

public section

open scoped Matrix commutatorElement
open TauCeti (coordinateLattice coordinateLatticeBasis matrixIntCastLieHom)
open TauCeti.AdditiveGroup (gaPointsMulEquiv)
open Multiplicative (ofAdd toAdd)
open _root_.UniversalEnvelopingAlgebra (ι)

namespace TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section LieHelpers

variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable abbrev gaSymm {R : Type*} [CommRing R] (u : R) :=
  (gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd u)

private theorem intLie {I : Type*} (E : I → Matrix n n ℤ) (i j k : I) (c : ℤ)
    (h : ⁅E i, E j⁆ = c • E k := by decide +kernel) :
    ⁅matrixIntCastLieHom ℚ (E i), matrixIntCastLieHom ℚ (E j)⁆ =
      c • matrixIntCastLieHom ℚ (E k) := by rw [← (matrixIntCastLieHom ℚ).map_lie, h, map_zsmul]

private theorem intZsmulLie {I : Type*} (E : I → Matrix n n ℤ) (i j k : I) (a b : ℤ)
    (h : a • ⁅E i, E j⁆ = b • E k := by decide +kernel) :
    a • ⁅matrixIntCastLieHom ℚ (E i), matrixIntCastLieHom ℚ (E j)⁆ =
      b • matrixIntCastLieHom ℚ (E k) := by
  rw [← (matrixIntCastLieHom ℚ).map_lie, ← map_zsmul, h, map_zsmul]

private theorem intLieLie {I : Type*} (E : I → Matrix n n ℤ) (i j k : I) (c : ℤ)
    (h : ⁅E i, ⁅E i, E j⁆⁆ = c • E k := by decide +kernel) :
    ⁅matrixIntCastLieHom ℚ (E i), ⁅matrixIntCastLieHom ℚ (E i), matrixIntCastLieHom ℚ (E j)⁆⁆ =
      c • matrixIntCastLieHom ℚ (E k) := by
  rw [← (matrixIntCastLieHom ℚ).map_lie, ← (matrixIntCastLieHom ℚ).map_lie, h, map_zsmul]

private theorem intLieZero {I : Type*} (E : I → Matrix n n ℤ) (i j : I)
    (h : ⁅E i, E j⁆ = 0 := by decide +kernel) :
    ⁅matrixIntCastLieHom ℚ (E i), matrixIntCastLieHom ℚ (E j)⁆ = 0 := by
  rw [← (matrixIntCastLieHom ℚ).map_lie, h, map_zero]

end LieHelpers

/-! ## Check 1: Type `A₂` on `R³` -/

section TypeA2

/-- The three positive root matrices `E₀₁`, `E₁₂`, `E₀₂` of `𝔰𝔩₃` in the standard basis. -/
def a2RootMatrix : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![Matrix.single 0 1 1, Matrix.single 1 2 1, Matrix.single 0 2 1]

/-- Each positive root matrix of `A₂` squares to zero. -/
theorem a2RootMatrix_mul_self (i : Fin 3) :
    a2RootMatrix i * a2RootMatrix i = (2 : ℕ) • 0 := by revert i; decide

/-- Each positive root matrix of `A₂` cubes to zero. -/
theorem a2RootMatrix_pow_three (i : Fin 3) : a2RootMatrix i ^ 3 = 0 := by revert i; decide

/-- The Kostant root subgroups `x_α`, `x_β`, `x_{α+β}` of `A₂` in `GL₃(R)`. -/
noncomputable abbrev a2RootSubgroup (R : Type*) [CommRing R] (i : Fin 3) :
    Multiplicative R →* _root_.Matrix.GeneralLinearGroup (Fin 3) R :=
  integralMatrixRootSubgroup a2RootMatrix 0 a2RootMatrix_mul_self a2RootMatrix_pow_three R i

private theorem a2Nil (i : Fin 3) : IsNilpotent (representation ℚ (Matrix (Fin 3) (Fin 3) ℚ)
    (Fin 3 → ℚ) (ι ℚ (matrixIntCastLieHom ℚ (a2RootMatrix i)))) :=
  isNilpotent_representation_matrix (a2RootMatrix_pow_three i)

/-- **Type-`A₂` Chevalley commutator check.** With `e_α = E₀₁`, `e_β = E₁₂`, and
`e_{α+β} = E₀₂` (`N_{α,β} = 1`), Steinberg's commutator is `⁅x_α(u), x_β(v)⁆ = x_{α+β}(u * v)`. -/
theorem commutatorElement_a2RootSubgroup {R : Type*} [CommRing R] (u v : R) :
    ⁅a2RootSubgroup R 0 (ofAdd u), a2RootSubgroup R 1 (ofAdd v)⁆ =
      a2RootSubgroup R 2 (ofAdd (u * v)) := by
  simpa only [a2RootSubgroup, integralMatrixRootSubgroup_apply, gaSymm, MulEquiv.apply_symm_apply,
    toAdd_ofAdd, Int.cast_one, one_mul] using
    commutatorElement_kostantRootSubgroupMatrix_of_lie_eq' _ _ _ _
      (kostantForm_integralMatrix_mem_coordinateLattice a2RootMatrix 0
        a2RootMatrix_mul_self a2RootMatrix_pow_three) (coordinateLatticeBasis _)
      (intLie a2RootMatrix 0 1 2 1) (intLieZero a2RootMatrix 0 2) (intLieZero a2RootMatrix 1 2)
      (a2Nil 0) (a2Nil 1) (a2Nil 2) (gaSymm u) (gaSymm v)

/-- Flipping `c_{1,1} = N_{α,β}` to `-N_{α,β}` in `A₂` falsifies the formula iff `(2 : R) ≠ 0`. -/
theorem commutatorElement_a2RootSubgroup_one_ne_neg_iff {R : Type*} [CommRing R] :
    ⁅a2RootSubgroup R 0 (ofAdd (1 : R)), a2RootSubgroup R 1 (ofAdd (1 : R))⁆ ≠
      a2RootSubgroup R 2 (ofAdd (-1 : R)) ↔ (2 : R) ≠ 0 := by
  rw [commutatorElement_a2RootSubgroup, mul_one, ne_eq,
    integralMatrixRootSubgroup_eq_iff_of_entry_unit _ _ _ _ (r := 0) (s := 2) (by decide)
      (Or.inl (by decide)) rfl]
  exact not_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

end TypeA2

/-! ## Check 2: Type `C₂ = Sp₄` on `R⁴` -/

section TypeC2

/-- The four positive root matrices of `C₂ = Sp₄` along the root string from long `α` (`E₁₃`) and
short `β` (`E₀₁ - E₃₂`): `e_{α+β} = E₀₃ + E₁₂` and `e_{α+2β} = E₀₂`. -/
def c2RootMatrix : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![Matrix.single 1 3 1, Matrix.single 0 1 1 - Matrix.single 3 2 1,
    Matrix.single 0 3 1 + Matrix.single 1 2 1, Matrix.single 0 2 1]

/-- Each positive root matrix of `C₂` in the four-dimensional symplectic basis squares to zero. -/
theorem c2RootMatrix_mul_self (i : Fin 4) :
    c2RootMatrix i * c2RootMatrix i = (2 : ℕ) • 0 := by revert i; decide

/-- Each positive root matrix of `C₂` in the four-dimensional symplectic basis cubes to zero. -/
theorem c2RootMatrix_pow_three (i : Fin 4) : c2RootMatrix i ^ 3 = 0 := by revert i; decide

/-- The Kostant root subgroups `x_α`, `x_β`, `x_{α+β}`, `x_{α+2β}` of `C₂` in `GL₄(R)`. -/
noncomputable abbrev c2RootSubgroup (R : Type*) [CommRing R] (i : Fin 4) :
    Multiplicative R →* _root_.Matrix.GeneralLinearGroup (Fin 4) R :=
  integralMatrixRootSubgroup c2RootMatrix 0 c2RootMatrix_mul_self c2RootMatrix_pow_three R i

private theorem c2Nil (i : Fin 4) : IsNilpotent (representation ℚ (Matrix (Fin 4) (Fin 4) ℚ)
    (Fin 4 → ℚ) (ι ℚ (matrixIntCastLieHom ℚ (c2RootMatrix i)))) :=
  isNilpotent_representation_matrix (c2RootMatrix_pow_three i)

/-- **Type-`C₂` Chevalley commutator check.** With `e_α = E₁₃` (long), `e_β = E₀₁ - E₃₂` (short),
`⁅e_β, e_α⁆ = e_{α+β}`, and `⁅e_β, e_{α+β}⁆ = 2 e_{α+2β}` (`M_{β,α,2} = 1`), Steinberg's commutator
is `⁅x_α(u), x_β(v)⁆ = x_{α+β}(-(u * v)) * x_{α+2β}(-(u * v ^ 2))`. -/
theorem commutatorElement_c2RootSubgroup {R : Type*} [CommRing R] (u v : R) :
    ⁅c2RootSubgroup R 0 (ofAdd u), c2RootSubgroup R 1 (ofAdd v)⁆ =
      c2RootSubgroup R 2 (ofAdd (-(u * v))) * c2RootSubgroup R 3 (ofAdd (-(u * v ^ 2))) := by
  simpa only [c2RootSubgroup, integralMatrixRootSubgroup_apply, gaSymm, MulEquiv.apply_symm_apply,
    toAdd_ofAdd, Int.cast_neg, Int.cast_one, neg_one_mul] using
    commutatorElement_kostantRootSubgroupMatrix_of_lie_lie_rev_eq' _ _ _ _
      (kostantForm_integralMatrix_mem_coordinateLattice c2RootMatrix 0
        c2RootMatrix_mul_self c2RootMatrix_pow_three) (coordinateLatticeBasis _)
      (intLie c2RootMatrix 0 1 2 (-1)) (intLieLie c2RootMatrix 1 0 3 (2 * 1))
      (intLieZero c2RootMatrix 1 3) (intLieZero c2RootMatrix 0 2)
      (c2Nil 0) (c2Nil 1) (c2Nil 2) (c2Nil 3) (gaSymm u) (gaSymm v)

/-- At `u = v = 1`, the `(0, 2)` entry of `⁅x_α(1), x_β(1)⁆` in `Sp₄(R)` is `-1`. -/
theorem commutatorElement_c2RootSubgroup_one_apply_zero_two {R : Type*} [CommRing R] :
    ((⁅c2RootSubgroup R 0 (ofAdd (1 : R)), c2RootSubgroup R 1 (ofAdd (1 : R))⁆ :
        _root_.Matrix.GeneralLinearGroup (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) 0 2 = -1 := by
  rw [commutatorElement_c2RootSubgroup, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [c2RootSubgroup, coe_integralMatrixRootSubgroup, toAdd_ofAdd]; simp [c2RootMatrix]

/-- Replacing Steinberg's `-1` sign on `c_{1,2}` by `+1` falsifies the `C₂` formula iff `2 ≠ 0`. -/
theorem commutatorElement_c2RootSubgroup_one_ne_pos_iff {R : Type*} [CommRing R] :
    ⁅c2RootSubgroup R 0 (ofAdd (1 : R)), c2RootSubgroup R 1 (ofAdd (1 : R))⁆ ≠
      c2RootSubgroup R 2 (ofAdd (-1 : R)) * c2RootSubgroup R 3 (ofAdd (1 : R)) ↔ (2 : R) ≠ 0 := by
  rw [commutatorElement_c2RootSubgroup, mul_one, one_pow, mul_one, ne_eq, mul_right_inj,
    integralMatrixRootSubgroup_eq_iff_of_entry_unit _ _ _ _ (r := 0) (s := 2) (by decide)
      (Or.inl (by decide)) rfl]
  exact not_congr ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

end TypeC2

/-! ## Check 3: Type `G₂` in its seven-dimensional representation -/

section TypeG2

open TauCeti.G2ShortRoot (positiveRootMatrix positiveRootMatrix_def positiveRootDividedSquareMatrix
  positiveRootDividedSquareMatrix_def positiveRootMatrix_mul_self positiveRootMatrix_pow_three)

/-- The Kostant root subgroups `x_γ` for all six positive roots of `G₂` in `GL₇(R)`. -/
noncomputable abbrev g2PosRootSubgroup (R : Type*) [CommRing R] (i : Fin 6) :
    Multiplicative R →* _root_.Matrix.GeneralLinearGroup (Fin 7) R :=
  integralMatrixRootSubgroup positiveRootMatrix positiveRootDividedSquareMatrix
    positiveRootMatrix_mul_self positiveRootMatrix_pow_three R i

private noncomputable abbrev g2E (k : Fin 6) := matrixIntCastLieHom ℚ (positiveRootMatrix k)
private abbrev g2Mem := kostantForm_integralMatrix_mem_coordinateLattice positiveRootMatrix
  positiveRootDividedSquareMatrix positiveRootMatrix_mul_self positiveRootMatrix_pow_three
private theorem g2Nil (i : Fin 6) : IsNilpotent (representation ℚ (Matrix (Fin 7) (Fin 7) ℚ)
    (Fin 7 → ℚ) (ι ℚ (g2E i))) := isNilpotent_representation_matrix (positiveRootMatrix_pow_three i)
private theorem g2Lie (i j k : Fin 6) (c : ℤ) (h : ⁅positiveRootMatrix i, positiveRootMatrix j⁆ =
    c • positiveRootMatrix k := by rw [positiveRootMatrix_def]; decide +kernel) :
    ⁅g2E i, g2E j⁆ = c • g2E k := intLie positiveRootMatrix i j k c h
private theorem g2ZLie (i j k : Fin 6) (a b : ℤ)
    (h : a • ⁅positiveRootMatrix i, positiveRootMatrix j⁆ = b • positiveRootMatrix k := by
      rw [positiveRootMatrix_def]; decide +kernel) :
    a • ⁅g2E i, g2E j⁆ = b • g2E k := intZsmulLie positiveRootMatrix i j k a b h
private theorem g2Zero (i j : Fin 6) (h : ⁅positiveRootMatrix i, positiveRootMatrix j⁆ = 0 := by
    rw [positiveRootMatrix_def]; decide +kernel) :
    ⁅g2E i, g2E j⁆ = 0 := intLieZero positiveRootMatrix i j h

/-- **Type-`G₂` Chevalley commutator check (`α` short, `β` long).** On `R⁷`,
`⁅x_α(u), x_β(v)⁆ = x_{α+β}(uv) x_{2α+β}(u²v) x_{3α+β}(u³v) x_{3α+2β}(2 u³v²)`, confirming
`c_{3,2} = (2/3) M_{α+β,α,2} = 2` (with `M_{α+β,α,2} = 3` in the normalized `e_{3α+2β}`). -/
theorem commutatorElement_g2PosRootSubgroup_short_long {R : Type*} [CommRing R] (u v : R) :
    ⁅g2PosRootSubgroup R 0 (ofAdd u), g2PosRootSubgroup R 1 (ofAdd v)⁆ =
      g2PosRootSubgroup R 2 (ofAdd (u * v)) * g2PosRootSubgroup R 3 (ofAdd (u ^ 2 * v)) *
        g2PosRootSubgroup R 4 (ofAdd (u ^ 3 * v)) *
        g2PosRootSubgroup R 5 (ofAdd (2 * (u ^ 3 * v ^ 2))) := by
  simpa only [g2PosRootSubgroup, integralMatrixRootSubgroup_apply, gaSymm,
    MulEquiv.apply_symm_apply, toAdd_ofAdd, Int.cast_one, one_mul, mul_one] using
    commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul' _ _ _ _ g2Mem
      (coordinateLatticeBasis _) (g2Lie 0 1 2 1) (g2ZLie 0 2 3 1 (2 * 1)) (g2ZLie 0 3 4 1 (3 * 1))
      (g2ZLie 3 2 5 (1 * 1) (3 * 1)) (g2Zero 0 4) (g2Zero 0 5) (g2Zero 1 2) (g2Zero 3 4)
      (g2Zero 2 5) (g2Zero 3 5) (g2Zero 4 5) (g2Nil 0) (g2Nil 1) (g2Nil 2) (g2Nil 3) (g2Nil 4)
      (g2Nil 5) (gaSymm u) (gaSymm v)

/-- **Type-`G₂` Chevalley commutator check (`β` long, `α` short).** Exchanging `e_α` and `e_β`
gives `⁅x_β(u), x_α(v)⁆ = x_{α+β}(-uv) x_{2α+β}(-uv²) x_{3α+β}(-uv³) x_{3α+2β}(u²v³)`, confirming
`c_{2,3} = (1/3) M_{α+β,α,2} = 1` (since `M_{α+β,α,2} = 3` in the normalized `e_{3α+2β}`). -/
theorem commutatorElement_g2PosRootSubgroup_long_short {R : Type*} [CommRing R] (u v : R) :
    ⁅g2PosRootSubgroup R 1 (ofAdd u), g2PosRootSubgroup R 0 (ofAdd v)⁆ =
      g2PosRootSubgroup R 2 (ofAdd (-(u * v))) * g2PosRootSubgroup R 3 (ofAdd (-(u * v ^ 2))) *
        g2PosRootSubgroup R 4 (ofAdd (-(u * v ^ 3))) *
        g2PosRootSubgroup R 5 (ofAdd (u ^ 2 * v ^ 3)) := by
  simpa only [g2PosRootSubgroup, integralMatrixRootSubgroup_apply, gaSymm,
    MulEquiv.apply_symm_apply, toAdd_ofAdd, Int.cast_neg, Int.cast_one, neg_one_mul, one_mul] using
    commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul_rev' _ _ _ _ g2Mem
      (coordinateLatticeBasis _) (g2Lie 1 0 2 (-1)) (g2ZLie 2 0 3 (-1) (2 * 1))
      (g2ZLie 0 3 4 1 (3 * 1)) (g2ZLie 2 3 5 (1 * (-1)) (3 * 1)) (g2Zero 0 4) (g2Zero 0 5)
      (g2Zero 1 2) (g2Zero 3 4) (g2Zero 2 5) (g2Zero 3 5) (g2Zero 4 5) (g2Nil 1) (g2Nil 0)
      (g2Nil 2) (g2Nil 3) (g2Nil 4) (g2Nil 5) (gaSymm u) (gaSymm v)

/-- **Type-`G₂` Chevalley commutator check for two short roots (`α` and `α + β`).** On `R⁷`,
`⁅x_α(u), x_{α+β}(v)⁆ = x_{2α+β}(2uv) x_{3α+β}(3u²v) x_{3α+2β}(-3uv²)`. -/
theorem commutatorElement_g2PosRootSubgroup_short_short {R : Type*} [CommRing R] (u v : R) :
    ⁅g2PosRootSubgroup R 0 (ofAdd u), g2PosRootSubgroup R 2 (ofAdd v)⁆ =
      g2PosRootSubgroup R 3 (ofAdd (2 * u * v)) * g2PosRootSubgroup R 4 (ofAdd (3 * u ^ 2 * v)) *
        g2PosRootSubgroup R 5 (ofAdd (-(3 * u * v ^ 2))) := by
  simpa only [g2PosRootSubgroup, integralMatrixRootSubgroup_apply, gaSymm,
    MulEquiv.apply_symm_apply, toAdd_ofAdd, Int.cast_neg, Int.cast_one, one_mul, neg_one_mul] using
    commutatorElement_kostantRootSubgroupMatrix_of_g2_short_pair' _ _ _ _ g2Mem
      (coordinateLatticeBasis _) (g2Lie 0 2 3 (2 * 1)) (g2ZLie 0 3 4 1 (3 * 1))
      (g2ZLie 3 2 5 1 (3 * 1)) (g2Zero 0 4) (g2Zero 0 5) (g2Zero 2 5) (g2Zero 3 4) (g2Zero 3 5)
      (g2Zero 4 5) (g2Nil 0) (g2Nil 2) (g2Nil 3) (g2Nil 4) (g2Nil 5) (gaSymm u) (gaSymm v)

/-- Negating `c_{3,2}` (`2 ↦ -2`) in `⁅x_α(1), x_β(1)⁆` falsifies the formula iff `(4 : R) ≠ 0`. -/
theorem commutatorElement_g2PosRootSubgroup_short_long_one_ne_neg_iff {R : Type*} [CommRing R] :
    ⁅g2PosRootSubgroup R 0 (ofAdd (1 : R)), g2PosRootSubgroup R 1 (ofAdd (1 : R))⁆ ≠
      g2PosRootSubgroup R 2 (ofAdd (1 : R)) * g2PosRootSubgroup R 3 (ofAdd (1 : R)) *
        g2PosRootSubgroup R 4 (ofAdd (1 : R)) *
        g2PosRootSubgroup R 5 (ofAdd (-2 : R)) ↔ (4 : R) ≠ 0 := by
  rw [commutatorElement_g2PosRootSubgroup_short_long, ne_eq]; simp only [one_pow, mul_one]
  rw [mul_right_inj, integralMatrixRootSubgroup_eq_iff_of_entry_unit _ _ _ _ (r := 0) (s := 5)
    (by decide) (Or.inr (by rw [positiveRootMatrix_def]; decide))
    (by rw [positiveRootDividedSquareMatrix_def]; decide)]
  exact not_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

/-- Negating `c_{2,3}` (`1 ↦ -1`) in `⁅x_β(1), x_α(1)⁆` falsifies the formula iff `(2 : R) ≠ 0`. -/
theorem commutatorElement_g2PosRootSubgroup_long_short_one_ne_neg_iff {R : Type*} [CommRing R] :
    ⁅g2PosRootSubgroup R 1 (ofAdd (1 : R)), g2PosRootSubgroup R 0 (ofAdd (1 : R))⁆ ≠
      g2PosRootSubgroup R 2 (ofAdd (-1 : R)) * g2PosRootSubgroup R 3 (ofAdd (-1 : R)) *
        g2PosRootSubgroup R 4 (ofAdd (-1 : R)) *
        g2PosRootSubgroup R 5 (ofAdd (-1 : R)) ↔ (2 : R) ≠ 0 := by
  rw [commutatorElement_g2PosRootSubgroup_long_short, ne_eq]; simp only [one_pow, mul_one]
  rw [mul_right_inj, integralMatrixRootSubgroup_eq_iff_of_entry_unit _ _ _ _ (r := 0) (s := 5)
    (by decide) (Or.inr (by rw [positiveRootMatrix_def]; decide))
    (by rw [positiveRootDividedSquareMatrix_def]; decide)]
  exact not_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

end TypeG2

end TauCeti.UniversalEnvelopingAlgebra
