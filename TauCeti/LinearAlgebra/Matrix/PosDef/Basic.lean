/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Order.Star.Rat
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.PosSemidef

/-!
# Positive definiteness over the rationals

For an integer matrix, positive definiteness over `ℤ` is equivalent to positive definiteness
after casting its entries to `ℚ`. This lets results about rational quadratic forms certify
positive definiteness of integer matrices, and conversely. Likewise a rational matrix is positive
definite exactly when its cast to `ℝ`, or to any linearly ordered field whose order is its star
order, is: a symmetric rational matrix is congruent over `ℚ` to a diagonal one, and congruence by
an invertible matrix and the positivity of diagonal entries both survive the cast.

The file also records the standard way of certifying a rational matrix as positive definite: write
it as `Bᴴ * B` for an explicit `B`, and check that it is invertible. One general fact about
`Matrix.PosDef` over any ring is recorded alongside, since Mathlib does not state it: a matrix on
an empty index type is positive definite, which is what the rank-zero members of the classical
Cartan families need. So is the `1 × 1` criterion: such a matrix over a nontrivial star-ordered
ring without zero divisors is positive definite exactly when its single entry is positive.

## Main results

* `Matrix.PosDef.of_isEmpty`: a matrix on an empty index type is positive definite.
* `Matrix.posDef_fin_one_iff`: a `1 × 1` matrix is positive definite exactly when its single
  entry is positive.
* `TauCeti.Matrix.posDef_map_intCast`: an integer matrix that is positive definite over `ℤ` is
  positive definite over `ℚ`.
* `TauCeti.Matrix.posDef_map_intCast_iff`: positive definiteness over `ℤ` and over `ℚ` agree.
* `TauCeti.Matrix.posDef_map_ratCast_iff`: positive definiteness over `ℚ` and over `ℝ` agree, and
  more generally over any linearly ordered field with the star order.
* `TauCeti.Matrix.posDef_conjTranspose_mul_self_of_isUnit`: an invertible rational matrix of the
  form `Bᴴ * B` is positive definite.
* `Matrix.PosDef.trivialStar`: over a linearly ordered field, a positive definite matrix on a
  nonempty index type forces the star to be trivial.
* `Matrix.PosDef.exists_sq_le_of_dotProduct_mulVec_le`: for a positive definite matrix `S`, the
  vectors `c` with `c ⬝ᵥ S *ᵥ c ≤ c ⬝ᵥ w` have uniformly bounded coordinates.
-/

public section

open scoped Matrix

namespace TauCeti

namespace Matrix

variable {n : Type*}

/-- Clearing denominators: a nonzero rational vector on a finite index type is a nonzero integer
vector scaled by a common nonzero denominator. -/
private theorem exists_intCast_eq_mul_of_ne_zero [Finite n] {x : n → ℚ} (hx : x ≠ 0) :
    ∃ (c : ℤ) (z : n → ℤ), c ≠ 0 ∧ z ≠ 0 ∧ ∀ i, (z i : ℚ) = (c : ℚ) * x i := by
  classical
  have _i : Fintype n := Fintype.ofFinite n
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
  have hc' : ∀ i, ∃ y : ℤ, (y : ℚ) = ((c : ℤ) : ℚ) * x i := fun i => by
    obtain ⟨y, hy⟩ := hc i
    exact ⟨y, by simpa [Algebra.smul_def] using hy⟩
  choose z hz using hc'
  have hc0 : ((c : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.coe_ne_zero c)
  have hzne : z ≠ 0 := by
    intro h
    refine hx (funext fun i ↦ ?_)
    have hi := hz i
    rw [h] at hi
    simpa [hc0] using hi.symm
  exact ⟨(c : ℤ), z, nonZeroDivisors.coe_ne_zero c, hzne, hz⟩

/-- **A matrix on an empty index type is vacuously positive definite.** This is what the
rank-zero members of the classical Cartan families `A 0`, `B 0`, `C 0` and `D 0` need. -/
theorem _root_.Matrix.PosDef.of_isEmpty {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    [IsEmpty n] (A : _root_.Matrix n n R) : A.PosDef :=
  ⟨_root_.Matrix.ext fun i _ ↦ isEmptyElim i,
    fun _ hx ↦ (hx (Finsupp.ext fun i ↦ isEmptyElim i)).elim⟩

/-- A `1 × 1` matrix over a nontrivial star-ordered ring without zero divisors, such as `ℝ` or
`ℂ`, is positive definite exactly when its single entry is positive. -/
@[simp]
theorem _root_.Matrix.posDef_fin_one_iff {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [NoZeroDivisors R] [Nontrivial R] (M : _root_.Matrix (Fin 1) (Fin 1) R) :
    M.PosDef ↔ 0 < M 0 0 := by
  have hdiag : M = _root_.Matrix.diagonal ![M 0 0] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hdiag, _root_.Matrix.posDef_diagonal_iff]
  simp

/-- The finite case of `TauCeti.Matrix.posDef_map_intCast`, where positive definiteness can be
tested against ordinary vectors. -/
private theorem posDef_map_intCast_of_finite [Finite n] {A : Matrix n n ℤ} (hA : A.PosDef) :
    (A.map (Int.cast : ℤ → ℚ)).PosDef := by
  classical
  have _i : Fintype n := Fintype.ofFinite n
  refine _root_.Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · ext i j
    simpa using congrArg (fun m : ℤ ↦ (m : ℚ)) (hA.isHermitian.apply i j)
  -- Clear the denominators of `x`, producing a nonzero integer vector `z = c • x`.
  obtain ⟨c, z, hc0, hzne, hz⟩ := exists_intCast_eq_mul_of_ne_zero hx
  -- The two quadratic forms differ by the square of the common denominator.
  have key : ((star z ⬝ᵥ (A *ᵥ z) : ℤ) : ℚ) =
      (c : ℚ) ^ 2 * (star x ⬝ᵥ ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x)) := by
    simp only [_root_.Matrix.dot_mulVec_eq_sum_sum, star_trivial, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hz, hz, _root_.Matrix.map_apply]
    ring
  have hpos : (0 : ℚ) < ((star z ⬝ᵥ (A *ᵥ z) : ℤ) : ℚ) := by
    exact_mod_cast hA.dotProduct_mulVec_pos hzne
  rw [key] at hpos
  have hsq : (0 : ℚ) < (c : ℚ) ^ 2 := by positivity
  exact (mul_pos_iff_of_pos_left hsq).mp hpos

/-- **An integer matrix positive definite over `ℤ` is positive definite over `ℚ`.** -/
theorem posDef_map_intCast {A : Matrix n n ℤ} (hA : A.PosDef) :
    (A.map (Int.cast : ℤ → ℚ)).PosDef := by
  classical
  refine ⟨?_, fun x hx ↦ ?_⟩
  · ext i j
    simpa using congrArg (fun m : ℤ ↦ (m : ℚ)) (hA.isHermitian.apply i j)
  -- A test vector is supported on a finite set, so it is enough to know the finite case for the
  -- principal submatrix on the support of `x`.
  set e : {a // a ∈ x.support} → n := Subtype.val
  have hinj : Function.Injective e := Subtype.val_injective
  have hsupp : ↑x.support ⊆ Set.range e := fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩
  have hmap : Finsupp.mapDomain e (Finsupp.comapDomain e x hinj.injOn) = x :=
    Finsupp.mapDomain_comapDomain _ hinj x hsupp
  have hsub : ((A.map (Int.cast : ℤ → ℚ)).submatrix e e).PosDef := by
    rw [_root_.Matrix.submatrix_map]
    exact posDef_map_intCast_of_finite (hA.submatrix hinj)
  have hne : Finsupp.comapDomain e x hinj.injOn ≠ 0 := fun h ↦ hx (by rw [← hmap, h]; simp)
  rw [← hmap]
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hsub.2 hne

/-- **An integer matrix is positive definite over `ℤ` exactly when its cast to `ℚ` is positive
definite.** This transfers positive definiteness results between integer and rational matrices. -/
theorem posDef_map_intCast_iff {A : Matrix n n ℤ} :
    (A.map (Int.cast : ℤ → ℚ)).PosDef ↔ A.PosDef := by
  refine ⟨fun hA ↦ ⟨?_, fun x hx ↦ ?_⟩, posDef_map_intCast⟩
  · ext i j
    have h := hA.isHermitian.apply i j
    simp only [_root_.Matrix.map_apply, star_trivial, Int.cast_inj] at h
    simp [h]
  · have hy : x.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero ≠ 0 := by
      rw [← Finsupp.mapRange_zero (f := (Int.cast : ℤ → ℚ)) (hf := Int.cast_zero)]
      exact (Finsupp.mapRange_injective _ Int.cast_zero Int.cast_injective).ne hx
    have h := hA.2 hy
    rw [Finsupp.sum_mapRange_index fun i ↦ by simp] at h
    simp only [Finsupp.sum_mapRange_index, star_trivial, _root_.Matrix.map_apply, mul_zero,
      implies_true] at h
    exact_mod_cast h

/-- **A rational matrix is positive definite exactly when its cast to `ℝ` is**, and more generally
its cast to any linearly ordered field `K` whose order is the star order of the trivial star. -/
theorem posDef_map_ratCast_iff {K : Type*} [Field K] [LinearOrder K] [StarRing K]
    [StarOrderedRing K] [Finite n] {A : Matrix n n ℚ} :
    (A.map (Rat.cast : ℚ → K)).PosDef ↔ A.PosDef := by
  classical
  have _i : Fintype n := Fintype.ofFinite n
  by_cases hA : A.IsSymm
  · obtain ⟨P, d, hP, hPAP⟩ := hA.exists_isUnit_transpose_mul_mul_eq_diagonal
    have hP' : IsUnit (P.map (Rat.cast : ℚ → K)) := hP.map (Rat.castHom K).mapMatrix
    -- The congruence `Pᵀ * A * P = diagonal d` survives the cast.
    have hPAP' : star (P.map (Rat.cast : ℚ → K)) * A.map Rat.cast * P.map Rat.cast =
        _root_.Matrix.diagonal fun i ↦ (d i : K) := by
      have h := congrArg (Rat.castHom K).mapMatrix hPAP
      simp only [map_mul, RingHom.mapMatrix_apply, Rat.coe_castHom] at h
      rw [_root_.Matrix.star_eq_conjTranspose, _root_.Matrix.conjTranspose_eq_transpose_of_trivial,
        ← _root_.Matrix.transpose_map, h, _root_.Matrix.diagonal_map Rat.cast_zero]
    rw [← _root_.Matrix.IsUnit.posDef_star_left_conjugate_iff hP,
      ← _root_.Matrix.IsUnit.posDef_star_left_conjugate_iff hP', hPAP',
      _root_.Matrix.star_eq_conjTranspose, _root_.Matrix.conjTranspose_eq_transpose_of_trivial,
      hPAP, _root_.Matrix.posDef_diagonal_iff, _root_.Matrix.posDef_diagonal_iff]
    simp only [Rat.cast_pos]
  · -- A positive definite matrix over either field is symmetric, since the star is trivial.
    refine iff_of_false (fun h ↦ hA ?_) (fun h ↦ hA ?_)
    · ext i j
      simpa using h.isHermitian.apply i j
    · ext i j
      simpa using h.isHermitian.apply i j

/-- **An invertible rational matrix of the form `Bᴴ * B` is positive definite.** Being of that
form gives positive *semi*definiteness for free; invertibility upgrades it, by way of the
injectivity hypothesis of `Matrix.PosDef.conjTranspose_mul_self`.

Mathlib's `Matrix.PosSemidef.posDef_iff_isUnit` says the same thing in one step, but only over an
`RCLike` field, which `ℚ` is not; `Matrix.PosDef.conjTranspose_mul_self` is the criterion that does
apply here, needing only `StarOrderedRing` and `NoZeroDivisors`. -/
theorem posDef_conjTranspose_mul_self_of_isUnit {m : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (B : _root_.Matrix m n ℚ) (hunit : IsUnit (Bᴴ * B)) : (Bᴴ * B).PosDef := by
  refine _root_.Matrix.PosDef.conjTranspose_mul_self B fun x y hxy ↦ ?_
  apply _root_.Matrix.mulVec_injective_iff_isUnit.mpr hunit
  rw [← _root_.Matrix.mulVec_mulVec x Bᴴ B, ← _root_.Matrix.mulVec_mulVec y Bᴴ B, hxy]

end Matrix

end TauCeti

namespace Matrix.PosDef

section TrivialStar

variable {B K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] [StarRing K]

/-- **A positive definite matrix on a nonempty index type forces the star of `K` to be trivial.**
This supplies the `TrivialStar K` instance, so that the ordinary quadratic-form results over a
linearly ordered commutative ring apply to such a matrix. -/
theorem trivialStar [Nonempty B] {S : Matrix B B K} (hS : S.PosDef) : TrivialStar K := by
  classical
  -- If `s ≠ star s`, the vector supported at one index with entry `s - star s` has a
  -- nonpositive quadratic form, contradicting positive definiteness.
  obtain ⟨k₀⟩ := ‹Nonempty B›
  exact ⟨fun s ↦ by
    by_contra hne
    have ht : s - star s ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h := hS.2 (x := Finsupp.single k₀ (s - star s)) (Finsupp.single_ne_zero.mpr ht)
    have hpos : 0 < S k₀ k₀ := hS.diag_pos
    have htt : 0 < (s - star s) * (s - star s) := mul_self_pos.mpr ht
    rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)] at h
    simp only [star_sub, star_star] at h
    nlinarith [mul_pos htt hpos]⟩

end TrivialStar

variable {B K : Type*} [Fintype B] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [StarRing K]

/-- **A positive definite quadratic inequality bounds every coordinate.** For a positive definite
matrix `S` and a linear functional `w`, the vectors `c` with `c ⬝ᵥ S *ᵥ c ≤ c ⬝ᵥ w` have squared
coordinates bounded independently of `c`. -/
theorem exists_sq_le_of_dotProduct_mulVec_le {S : Matrix B B K} (hS : S.PosDef) (w : B → K) :
    ∃ M : K, ∀ c : B → K, c ⬝ᵥ S *ᵥ c ≤ c ⬝ᵥ w → ∀ k, c k ^ 2 ≤ M := by
  classical
  rcases isEmpty_or_nonempty B with hB | hB
  · exact ⟨0, fun _ _ k ↦ isEmptyElim k⟩
  have := hS.trivialStar
  set F : LinearMap.BilinForm K (B → K) := Matrix.toBilin' S with hFdef
  have hFapply : ∀ u v : B → K, F u v = u ⬝ᵥ S *ᵥ v := fun u v ↦ Matrix.toBilin'_apply' S u v
  have hnonneg : ∀ u : B → K, 0 ≤ F u u := fun u ↦ by
    simpa [hFapply] using hS.posSemidef.dotProduct_mulVec_nonneg u
  have hsymmB : F.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hS.isHermitian.isSymm
  have hsymm : LinearMap.IsSymm F := LinearMap.BilinForm.isSymm_iff.mp hsymmB
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.mpr hS.isUnit
  obtain ⟨z, hz⟩ := hsurj w
  choose u hu using fun k : B ↦ hsurj (Pi.single k 1)
  refine ⟨F z z * ∑ k, F (u k) (u k), fun c hc k ↦ ?_⟩
  have hle : F c c ≤ F c z := by rwa [hFapply, hFapply, hz]
  calc c k ^ 2 = F c (u k) ^ 2 := by rw [hFapply, hu, dotProduct_single_one]
    _ ≤ F z z * F (u k) (u k) := F.apply_sq_le_mul_of_apply_le_apply hnonneg hsymm hle _
    _ ≤ F z z * ∑ k, F (u k) (u k) := mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ ↦ hnonneg (u j)) (Finset.mem_univ k)) (hnonneg z)

end Matrix.PosDef
