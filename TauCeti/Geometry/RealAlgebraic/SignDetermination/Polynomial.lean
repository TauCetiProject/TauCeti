/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Moments
import Mathlib.Basic.Sign.Basic
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Defs

/-! # Sign determination from polynomial sign sums

`signCount` counts points realizing a sign condition, and `signSum` is the
integer sum of signs on a specified finite set. `signSum_eq_sum_signCount` expresses
the sign sum of a product as a moment of these counts. `fullInverse_mulVec_signSum` inverts
the full moment system over the rationals.

For injective columns covering every point of the finite set, `mulVec_signCount`
is the restricted moment identity. Given a left inverse of that matrix,
`eq_signCount` recovers the counts and `signCount_solution_pos_iff` characterizes
realizability by positivity.

The multiplicative moment identities use a compatibly ordered commutative ring.
For root sign determination,
take the finite set to be the distinct roots of a nonzero polynomial, possibly
restricted to an interval. The zero polynomial must be handled separately:
its zero set is not represented by its empty `Polynomial.roots` multiset.

## References

M. Ben-Or, D. Kozen, and J. Reif,
[The complexity of elementary algebra and geometry](https://doi.org/10.1016/0022-0000(86)90029-2),
Journal of Computer and System Sciences 32 (1986), 251–264, for BKR sign determination.

For finite sign sums and the full ternary moment construction, see
S. Basu, R. Pollack, M.-F. Roy,
[*Algorithms in Real Algebraic Geometry*, 2nd ed.](https://doi.org/10.1007/3-540-33099-2),
Chapter 10. A formal precedent is C. Cohen, A. Mahboubi,
[Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination]
(https://doi.org/10.2168/LMCS-8(1:2)2012), LMCS 8(1), 2012.
-/

public section

open Polynomial SignType
open scoped Matrix

open Function (occCount occCount_eq_card_filter)


namespace Finset

open TauCeti.SignDetermination

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The sign sum of a product is the sum of the products of its pointwise signs. -/
private theorem signSum_prod {J : Type*} [Fintype J] (Z : Finset R) (Q : J → R[X]) :
    signSum Z (∏ j, Q j) = ∑ x : Z, ∏ j, (sign ((Q j).eval x.val) : ℤ) := by
  rw [signSum_eq_sum_subtype]
  apply Finset.sum_congr rfl
  intro x _
  rw [eval_prod]
  exact map_prod (SignType.castHom.comp signHom) (fun j => (Q j).eval x.val) Finset.univ

/-- After casting to a commutative ring, a sign sum of powers is a sum of sign products. -/
theorem signSum_prod_pow {K : Type*} [CommRing K] {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (e : J → ℕ) :
    (signSum Z (∏ j, Q j ^ e j) : K) =
      ∑ x : Z, ∏ j, (sign ((Q j).eval x.val) : K) ^ e j := by
  simp only [signSum_prod, eval_pow, sign_pow, SignType.coe_pow,
    Int.cast_sum, Int.cast_prod, Int.cast_pow, SignType.intCast_cast]

/-- The polynomial moment identity for injective candidate columns covering every
sample point, and any selected exponent rows. Exponents need not be bounded by two. -/
theorem mulVec_signCount {K : Type*} [CommRing K] {J C I : Type*} [Fintype J]
    [Fintype C] (Z : Finset R) (Q : J → R[X])
    (columns : C → (J → SignType)) (rows : I → J → ℕ)
    (hinj : Function.Injective columns)
    (cover : ∀ x ∈ Z, ∃ c, columns c = fun j => sign ((Q j).eval x)) :
    (Matrix.of fun i c => ∏ j, (columns c j : K) ^ rows i j) *ᵥ
        (fun c => (signCount Z Q (columns c) : K)) =
      fun i => (signSum Z (∏ j, Q j ^ rows i j) : K) := by
  classical
  simp_rw [signSum_prod_pow]
  simpa only [signCount_eq_occCount] using
    Function.mulVec_occCount _ columns hinj (fun x : Z => cover x.val x.property)
      (fun i σ => ∏ j, (σ j : K) ^ rows i j)

/-- A left inverse recovers polynomial sign counts for injective candidate columns
covering every sample point. Coverage is a separate hypothesis from the matrix identity. -/
theorem eq_signCount {K : Type*} [CommRing K] {J C I : Type*}
    [Fintype J] [Fintype C] [DecidableEq C] [Fintype I]
    (Z : Finset R) (Q : J → R[X]) (columns : C → (J → SignType)) (rows : I → J → ℕ)
    (hinj : Function.Injective columns)
    (cover : ∀ x ∈ Z, ∃ c, columns c = fun j => sign ((Q j).eval x))
    (A : Matrix C I K)
    (hA : A * (Matrix.of fun i c => ∏ j, (columns c j : K) ^ rows i j) = 1)
    (proposed : C → K)
    (hsolve : (Matrix.of fun i c => ∏ j, (columns c j : K) ^ rows i j) *ᵥ proposed =
      fun i => (signSum Z (∏ j, Q j ^ rows i j) : K)) :
    proposed = fun c => (signCount Z Q (columns c) : K) := by
  simp_rw [signSum_prod_pow] at hsolve
  simpa only [signCount_eq_occCount] using
    Function.eq_occCount (fun x : Z => fun j => sign ((Q j).eval x.val)) columns hinj
      (fun x => cover x.val x.property) (fun i σ => ∏ j, (σ j : K) ^ rows i j)
      A hA proposed hsolve

/-- Given a left inverse of the moment matrix and injective candidate columns
covering every sample point, positive entries of a solved polynomial moment system
are exactly its realizable sign conditions. -/
theorem signCount_solution_pos_iff {K : Type*} [CommRing K] [PartialOrder K]
    [IsOrderedRing K] [Nontrivial K] {J C I : Type*}
    [Fintype J] [Fintype C] [DecidableEq C] [Fintype I]
    (Z : Finset R) (Q : J → R[X]) (columns : C → (J → SignType)) (rows : I → J → ℕ)
    (hinj : Function.Injective columns)
    (cover : ∀ x ∈ Z, ∃ c, columns c = fun j => sign ((Q j).eval x))
    (A : Matrix C I K)
    (hA : A * (Matrix.of fun i c => ∏ j, (columns c j : K) ^ rows i j) = 1)
    (proposed : C → K)
    (hsolve : (Matrix.of fun i c => ∏ j, (columns c j : K) ^ rows i j) *ᵥ proposed =
      fun i => (signSum Z (∏ j, Q j ^ rows i j) : K)) (c : C) :
    0 < proposed c ↔ ∃ x ∈ Z, ∀ j, sign ((Q j).eval x) = columns c j := by
  rw [eq_signCount Z Q columns rows hinj cover A hA proposed hsolve]
  simp only [Nat.cast_pos, signCount_pos]

/-- All ternary moments determine the exact multiplicity of every sign pattern. -/
theorem fullInverse_mulVec_signSum {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) :
    fullInverse J *ᵥ (fun e => (signSum Z (∏ j, Q j ^ (e j).val) : ℚ)) =
      fun σ => (signCount Z Q σ : ℚ) := by
  simp_rw [signSum_prod_pow]
  simpa only [signCount_eq_occCount] using
    fullInverse_mulVec J (fun x : Z => fun j => sign ((Q j).eval x.val))

/-- The integer BKR moment identity on a finite set of sample points. -/
theorem signSum_eq_sum_signCount {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) (e : J → ℕ) :
    signSum Z (∏ j, Q j ^ e j) =
      ∑ σ : J → SignType, (∏ j, (σ j : ℤ) ^ e j) * (signCount Z Q σ : ℤ) := by
  classical
  have h := congrFun (mulVec_signCount (K := ℤ) Z Q id (fun _ : Unit => e)
    Function.injective_id (fun x _ => ⟨_, rfl⟩)) ()
  simpa only [Matrix.mulVec_apply_eq_sum, Matrix.of_apply, id_eq, Int.cast_id] using h.symm


end Finset
