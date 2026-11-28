/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Characteristic polynomial invariance under column-span perturbations

For square matrices over a commutative ring `R`, if `γ` preserves the column span of `A`
(`γ * A = A * r`) and `s` annihilates `A` (`s * A = 0`), then `γ + A * s` has the same
characteristic polynomial as `γ` (`TauCeti.charpoly_add_mul_of_mul_eq_zero`). Over a field `E`,
if an invertible matrix `γ` satisfies `γ * X = X * r` with `X ≠ 0` and `r` singular, then
`γ.charpoly` is reducible (`TauCeti.not_irreducible_charpoly_of_mul_eq_mul`). Finally, for a
form `J` over a field with involution, the isometries in `unitaryGroupOf J` preserving the column
span of `X` form a subgroup `TauCeti.spanStabilizer J X`.

## Main definitions

* `TauCeti.spanStabilizer`: the subgroup `{γ ∈ unitaryGroupOf J | ∃ r, γ * X = X * r}`.

## Main results

* `TauCeti.aeval_mul_eq_mul_aeval`: `γ * X = X * r` implies `aeval γ p * X = X * aeval r p`.
* `TauCeti.charpoly_add_mul_of_mul_eq_zero`: `(γ + A * s).charpoly = γ.charpoly`.
* `TauCeti.not_irreducible_charpoly_of_mul_eq_mul`: `¬Irreducible γ.charpoly`.
* `TauCeti.mem_spanStabilizer_iff`: membership characterization of `spanStabilizer J X`.

## References

* Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0),
  `src/Lib/Adelic/TraceFormula/IsotropicStabiliser.lean` (`New.charpoly_add_mul_of_mul_eq_zero`,
  `New.not_irreducible_charpoly_of_mul_eq_mul`, `New.spanStabilizer`).
-/

public section

open Matrix Polynomial

namespace TauCeti

/-- If `γ * X = X * r`, then `aeval γ p * X = X * aeval r p` for every polynomial `p`. -/
theorem aeval_mul_eq_mul_aeval {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {γ X r : Matrix n n R} (hkeeps : γ * X = X * r) (p : R[X]) :
    aeval γ p * X = X * aeval r p := by
  induction p using Polynomial.induction_on with
  | C c => simp [Algebra.commutes]
  | add p q hp hq => simp [map_add, add_mul, mul_add, hp, hq]
  | monomial k c ih =>
    simp only [pow_succ, ← mul_assoc, map_mul, aeval_X] at ih ⊢
    rw [Matrix.mul_assoc, hkeeps, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

/-- The stabilizer in `unitaryGroupOf J` of the column span of `X`: the isometries `γ` of `J`
such that `γ * X = X * r` for some matrix `r`. -/
def spanStabilizer {E n : Type*} [Field E] [StarRing E] [Fintype n] [DecidableEq n]
    (J X : Matrix n n E) : Subgroup (unitaryGroupOf J) where
  carrier := {γ : unitaryGroupOf J | ∃ r : Matrix n n E, ((γ : GL n E) : Matrix n n E) * X = X * r}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro γ δ ⟨r, hr⟩ ⟨t, ht⟩
    exact ⟨r * t, by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, ht, ← Matrix.mul_assoc, hr,
        Matrix.mul_assoc]⟩
  inv_mem' := by
    rintro γ ⟨r, hr⟩
    have hcop : IsCoprime ((γ : GL n E) : Matrix n n E).charpoly Polynomial.X := by
      refine (Polynomial.irreducible_X.coprime_iff_not_dvd.mpr fun hdvd ↦ ?_).symm
      have h0 : ((γ : GL n E) : Matrix n n E).charpoly.coeff 0 = 0 := by
        simpa [Polynomial.X_dvd_iff] using hdvd
      have hdet : ((γ : GL n E) : Matrix n n E).det = 0 := by
        rw [det_eq_sign_charpoly_coeff, h0, mul_zero]
      exact (isUnit_iff_isUnit_det _).mp γ.val.isUnit |>.ne_zero hdet
    obtain ⟨p, q, hpq⟩ := hcop
    have hinv : aeval ((γ : GL n E) : Matrix n n E) q * ((γ : GL n E) : Matrix n n E) = 1 := by
      simpa [aeval_self_charpoly] using congrArg (aeval ((γ : GL n E) : Matrix n n E)) hpq
    exact ⟨aeval r q, by
      rw [← aeval_mul_eq_mul_aeval hr q, Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_left hinv]⟩

/-- Membership in `spanStabilizer J X`. -/
@[simp]
theorem mem_spanStabilizer_iff {E n : Type*} [Field E] [StarRing E] [Fintype n] [DecidableEq n]
    {J X : Matrix n n E} {γ : unitaryGroupOf J} :
    γ ∈ spanStabilizer J X ↔ ∃ r : Matrix n n E, ((γ : GL n E) : Matrix n n E) * X = X * r :=
  Iff.rfl

/-- If `γ * A = A * r` and `s * A = 0`, then `γ + A * s` has the same characteristic polynomial
as `γ`. -/
theorem charpoly_add_mul_of_mul_eq_zero {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {γ A r s : Matrix n n R} (hkeeps : γ * A = A * r) (hzero : s * A = 0) :
    (γ + A * s).charpoly = γ.charpoly := by
  have hleft : fromBlocks 1 0 A 1 * fromBlocks r s (-(A * r)) γ =
      fromBlocks r s 0 (γ + A * s) := by
    simp [fromBlocks_multiply, add_comm]
  have hright : fromBlocks r s (-(A * r)) γ * fromBlocks 1 0 A 1 =
      fromBlocks r s 0 γ := by
    simp [fromBlocks_multiply, hkeeps, hzero]
  have heq : r.charpoly * (γ + A * s).charpoly = r.charpoly * γ.charpoly := by
    rw [← charpoly_fromBlocks_zero₂₁ r s, ← charpoly_fromBlocks_zero₂₁ r s, ← hleft, ← hright,
      charpoly_mul_comm]
  exact r.charpoly_monic.isRegular.left heq

/-- An invertible matrix `γ` over a field satisfying `γ * X = X * r` with `X ≠ 0` and singular `r`
has a reducible characteristic polynomial. -/
theorem not_irreducible_charpoly_of_mul_eq_mul {E n : Type*} [Field E] [Fintype n] [DecidableEq n]
    {γ X r : Matrix n n E} (hγ : γ.det ≠ 0) (hX : X ≠ 0) (hkeeps : γ * X = X * r)
    (hr : r.det = 0) : ¬Irreducible γ.charpoly := by
  intro hirred
  have hkills : aeval γ r.charpoly * X = 0 := by
    rw [aeval_mul_eq_mul_aeval hkeeps, aeval_self_charpoly, Matrix.mul_zero]
  have hdvd : γ.charpoly ∣ r.charpoly := by
    by_contra hnot
    obtain ⟨u, v, huv⟩ := hirred.coprime_iff_not_dvd.mpr hnot
    have hmul := congrArg (fun p ↦ aeval γ p * X) huv
    simp only [map_add, map_mul, map_one, aeval_self_charpoly, Matrix.mul_zero, zero_add,
      Matrix.one_mul, Matrix.mul_assoc, hkills] at hmul
    exact hX hmul.symm
  have heq : r.charpoly = γ.charpoly :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le γ.charpoly_monic r.charpoly_monic hdvd (by simp)
  exact hγ (by rw [det_eq_sign_charpoly_coeff, ← heq, ← det_eq_sign_charpoly_coeff, hr])

end TauCeti
