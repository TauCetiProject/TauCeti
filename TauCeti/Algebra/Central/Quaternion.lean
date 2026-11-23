/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Matrix.Basic
import TauCeti.Algebra.Quaternion.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.LinearCombination

/-!
# The centre of the Hamilton quaternions

The Hamilton quaternions `ℍ[R]` over a commutative ring `R` are the free `R`-module on `1, i, j, k`
with `i² = j² = k² = -1`. This file computes their centre, and deduces that `ℍ[R]` is a *central*
`R`-algebra whenever `2` is a regular element of `R`. Over `ℝ` this makes `ℍ[ℝ]` a central simple
`ℝ`-algebra, since a division ring is a simple ring; the file closes by showing that this central
simple algebra is not split, that is, not isomorphic to a matrix algebra over `R`.

The computation runs through `TauCeti.Quaternion.commute_iff`, which says that two quaternions
commute exactly when `2` annihilates the three coordinates of the cross product of their imaginary
parts. That criterion holds over an arbitrary commutative ring, with no regularity assumption: in
characteristic two `ℍ[R]` really is commutative, and the criterion records that degeneration rather
than excluding it.

## Main results

* `TauCeti.Quaternion.commute_iff`: two quaternions commute iff `2` annihilates the cross product
  of their imaginary parts, and `TauCeti.Quaternion.commute_iff'`, its classical form for `2`
  regular: two quaternions commute iff the cross product of their imaginary parts vanishes, that
  is, iff the three `2 × 2` minors of the pair of imaginary parts all vanish. Over a field that is
  the statement that the imaginary parts are parallel; over a general commutative ring vanishing
  minors are weaker than one imaginary part being a scalar multiple of the other.
* `TauCeti.Quaternion.mem_center_iff`: a quaternion is central iff `2` annihilates each of its
  three imaginary coordinates.
* `TauCeti.Quaternion.center_eq_bot`: if `2` is left regular in `R`, the centre of `ℍ[R]` is the
  image of `R`; `TauCeti.Quaternion.mem_center_iff_im_eq_zero` says equivalently that the central
  quaternions are those with vanishing imaginary part, and
  `TauCeti.Quaternion.forall_mul_comm_iff_im_eq_zero` restates this as commuting with every
  quaternion.
* `TauCeti.Quaternion.forall_sub_mul_eq_zero_iff` and
  `TauCeti.Quaternion.forall_mul_sub_eq_zero_iff`: when `ℍ[R]` has no zero divisors (for instance
  over a linearly ordered commutative ring), a commutator with `x` multiplied by a fixed `c`
  vanishes identically iff `c = 0` or `x` is real.
* `TauCeti.Quaternion.im_inv_eq_zero_iff`: over a linearly ordered field, `x⁻¹` is real iff `x` is.
* `TauCeti.Quaternion.instIsCentral`: `ℍ[R]` is a central `R`-algebra when `R` has no zero divisors
  and `2 ≠ 0` in `R`; in particular `ℍ[ℝ]` is a central `ℝ`-algebra.
* `TauCeti.Quaternion.isEmpty_algEquiv_matrix`: when `R` is nontrivial and `ℍ[R]` has no zero
  divisors, `ℍ[R]` is not isomorphic to a matrix algebra of any size, so over a field
  for which `ℍ[R]` is a division ring its Brauer class is nontrivial.

## Implementation notes

The Hamilton computation here is for `Quaternion R = ℍ[R]`, with `i² = j² = k² = -1`. The centre
genuinely depends on the structure constants, and the general algebra need not be central even over
`ℝ`. For instance in
`ℍ[ℝ, 0, 0, 0]` the products of `k` with each imaginary unit all vanish (`i * k = k * i = 0`,
`j * k = k * j = 0` and `k * k = 0`), so `k` is a central element outside the image of `ℝ`; the
other products of imaginary units are not all zero there, since `i * j = k` and `j * i = -k`.

The regularity hypothesis of `center_eq_bot` is carried as `IsLeftRegular (2 : R)`, which is exactly
what the proof consumes. `instIsCentral` restates it with the typeclass assumptions
`[NoZeroDivisors R] [NeZero (2 : R)]` so that instance search can discharge it, as it does for
`R = ℝ`. Conversely, if `ℍ[R]` itself has no zero divisors then `2` is automatically left regular
in `R`, since `(r + r i)² = 2 r² i` (`Quaternion.isLeftRegular_two`); the results stated under
`[NoZeroDivisors ℍ[R]]` use this.

## References

The centrality of `ℍ` and the nonsplitting statement are the two halves of the classical
computation of the Brauer group of `ℝ`; see for instance P. Gille and T. Szamuely,
*Central Simple Algebras and Galois Cohomology*, CUP (2006), §1.1 and §2.1.
-/

public section

open scoped Quaternion

namespace TauCeti

namespace Quaternion

section CommRing

variable {R : Type*} [CommRing R] {x y : ℍ[R]}

/-- **Two quaternions commute exactly when `2` annihilates the cross product of their imaginary
parts.** The real part of a commutator always vanishes, and its three imaginary coordinates are
twice the coordinates of the cross product `Im x × Im y`.

No regularity assumption on `2` is made, so the statement also covers characteristic two, where
`ℍ[R]` is commutative and all three conditions hold vacuously. -/
theorem commute_iff :
    Commute x y ↔
      2 * (x.imJ * y.imK - x.imK * y.imJ) = 0 ∧
        2 * (x.imK * y.imI - x.imI * y.imK) = 0 ∧
        2 * (x.imI * y.imJ - x.imJ * y.imI) = 0 := by
  simp only [_root_.commute_iff_eq, _root_.Quaternion.ext_iff, _root_.Quaternion.re_mul,
    _root_.Quaternion.imI_mul, _root_.Quaternion.imJ_mul, _root_.Quaternion.imK_mul]
  constructor
  · rintro ⟨-, hI, hJ, hK⟩
    exact ⟨by linear_combination hI, by linear_combination hJ, by linear_combination hK⟩
  · rintro ⟨hI, hJ, hK⟩
    exact ⟨by ring, by linear_combination hI, by linear_combination hJ, by linear_combination hK⟩

/-- **Two quaternions commute exactly when the cross product of their imaginary parts vanishes**,
once `2` is a left regular element of `R`. This is the classical form of
`TauCeti.Quaternion.commute_iff`: two quaternions commute precisely when the three `2 × 2` minors
of their imaginary parts vanish. Over a field that says the imaginary parts are parallel, but over
a general commutative ring vanishing minors do not force one imaginary part to be a scalar multiple
of the other. -/
theorem commute_iff' (h2 : IsLeftRegular (2 : R)) :
    Commute x y ↔
      x.imJ * y.imK = x.imK * y.imJ ∧
        x.imK * y.imI = x.imI * y.imK ∧
        x.imI * y.imJ = x.imJ * y.imI := by
  have key : ∀ a c : R, 2 * (a - c) = 0 ↔ a = c := fun a c ↦
    ⟨fun h ↦ sub_eq_zero.mp (h2 (by simpa using h)), fun h ↦ by simp [h]⟩
  rw [commute_iff, key, key, key]

/-- **A quaternion is central exactly when `2` annihilates each of its imaginary coordinates.**
Commuting with `i` and with `j` already forces all three conditions, and conversely those conditions
make the cross product criterion of `TauCeti.Quaternion.commute_iff` hold against every
quaternion. -/
@[simp]
theorem mem_center_iff :
    x ∈ Subalgebra.center R ℍ[R] ↔ 2 * x.imI = 0 ∧ 2 * x.imJ = 0 ∧ 2 * x.imK = 0 := by
  rw [Subalgebra.mem_center_iff]
  constructor
  · intro h
    -- Test `x` against `i` and against `j`.
    have hi : Commute x (⟨0, 1, 0, 0⟩ : ℍ[R]) := (h ⟨0, 1, 0, 0⟩).symm
    have hj : Commute x (⟨0, 0, 1, 0⟩ : ℍ[R]) := (h ⟨0, 0, 1, 0⟩).symm
    obtain ⟨-, hi₂, hi₃⟩ := commute_iff.mp hi
    obtain ⟨-, -, hj₃⟩ := commute_iff.mp hj
    -- Reduce the coordinates of the two literal quaternions `i` and `j`.
    dsimp only at hi₂ hi₃ hj₃
    refine ⟨by linear_combination hj₃, by linear_combination -hi₃, by linear_combination hi₂⟩
  · rintro ⟨hI, hJ, hK⟩ z
    refine (commute_iff.mpr ⟨?_, ?_, ?_⟩).symm.eq
    · linear_combination z.imK * hJ - z.imJ * hK
    · linear_combination z.imI * hK - z.imK * hI
    · linear_combination z.imJ * hI - z.imI * hJ

/-- **The centre of `ℍ[R]` is the image of `R`** as soon as `2` is a left regular element of `R`. -/
theorem center_eq_bot (h2 : IsLeftRegular (2 : R)) :
    Subalgebra.center R ℍ[R] = ⊥ := by
  refine le_antisymm (fun x hx ↦ Algebra.mem_bot.mpr ⟨x.re, ?_⟩) bot_le
  obtain ⟨hI, hJ, hK⟩ := mem_center_iff.mp hx
  ext <;> simp [h2.mul_left_eq_zero_iff.mp hI, h2.mul_left_eq_zero_iff.mp hJ,
    h2.mul_left_eq_zero_iff.mp hK]

/-- **A quaternion is central exactly when its imaginary part vanishes**, as soon as `2` is a left
regular element of `R`. -/
theorem mem_center_iff_im_eq_zero (h2 : IsLeftRegular (2 : R)) :
    x ∈ Subalgebra.center R ℍ[R] ↔ x.im = 0 := by
  rw [center_eq_bot h2, Algebra.mem_bot]
  refine ⟨fun ⟨r, hr⟩ ↦ hr ▸ _root_.Quaternion.im_coe r, fun h ↦ ⟨x.re, ?_⟩⟩
  simpa [h] using _root_.Quaternion.re_add_im x

/-- **A quaternion commutes with every quaternion exactly when its imaginary part vanishes**, as
soon as `2` is a left regular element of `R`. -/
theorem forall_mul_comm_iff_im_eq_zero (h2 : IsLeftRegular (2 : R)) :
    (∀ y, x * y = y * x) ↔ x.im = 0 := by
  rw [← mem_center_iff_im_eq_zero h2, Subalgebra.mem_center_iff]
  exact forall_congr' fun _ ↦ eq_comm

/-- **The Hamilton quaternions are a central algebra.** Over a commutative ring with no zero
divisors in which `2 ≠ 0`, the centre of `ℍ[R]` is exactly the image of `R`. Specialized to
`R = ℝ` this is the centrality half of the statement that `ℍ[ℝ]` is a central simple `ℝ`-algebra. -/
instance instIsCentral [NoZeroDivisors R] [NeZero (2 : R)] : Algebra.IsCentral R ℍ[R] :=
  ⟨(center_eq_bot fun _ _ h ↦ mul_left_cancel₀ (NeZero.ne (2 : R)) h).le⟩

end CommRing

section NoZeroDivisors

variable {R : Type*} [CommRing R] [NoZeroDivisors ℍ[R]]

variable {x c : ℍ[R]}

/-- The commutator with `x` followed by right multiplication by `c` vanishes identically exactly
when `c = 0` or `x` is real. -/
theorem forall_sub_mul_eq_zero_iff : (∀ y, (x * y - y * x) * c = 0) ↔ c = 0 ∨ x.im = 0 := by
  rw [← forall_mul_comm_iff_im_eq_zero _root_.Quaternion.isLeftRegular_two]
  simp only [mul_eq_zero, sub_eq_zero, forall_or_right, or_comm]

/-- Left multiplication by `c` of the commutator with `x` vanishes identically exactly when `c = 0`
or `x` is real. -/
theorem forall_mul_sub_eq_zero_iff : (∀ y, c * (y * x - x * y) = 0) ↔ c = 0 ∨ x.im = 0 := by
  rw [← forall_mul_comm_iff_im_eq_zero _root_.Quaternion.isLeftRegular_two]
  simp only [mul_eq_zero, sub_eq_zero, forall_or_left, eq_comm]

variable (R) [Nontrivial R]

/-- **The Hamilton quaternions are not split once they have no zero divisors**: `ℍ[R]` is then not
isomorphic, as an `R`-algebra, to any matrix algebra `Matrix n n R`. For `n` with at least two
elements such a matrix algebra has nonzero zero divisors; for `n` with at most one element it is
commutative, whereas a commutative `ℍ[R]` forces `2 = 0` in `R` and then `(1 + i) ^ 2 = 0`. This
applies in particular over a linearly ordered commutative ring.

Together with `TauCeti.Quaternion.instIsCentral` and the simplicity of a division ring this says,
for a field `R` over which `ℍ[R]` is a division ring, that the Brauer class of `ℍ[R]` is
nontrivial; over `ℝ` it is the nonidentity element of the Brauer group. -/
theorem isEmpty_algEquiv_matrix (n : Type*) [Fintype n] [DecidableEq n] :
    IsEmpty (ℍ[R] ≃ₐ[R] Matrix n n R) := by
  refine ⟨fun f ↦ ?_⟩
  rcases subsingleton_or_nontrivial n with hn | hn
  · -- At most one index: the matrix algebra, hence `ℍ[R]`, is commutative.
    have hcomm (a b : Matrix n n R) : a * b = b * a := by
      ext i j
      obtain rfl := Subsingleton.elim i j
      rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_subsingleton _ i,
        Fintype.sum_subsingleton _ i, mul_comm]
    have hH (x y : ℍ[R]) : x * y = y * x := f.injective (by rw [map_mul, map_mul, hcomm])
    have := congrArg QuaternionAlgebra.imI
      ((forall_mul_comm_iff_im_eq_zero _root_.Quaternion.isLeftRegular_two).mp
        (hH ⟨0, 1, 0, 0⟩))
    simp at this
  · -- Two distinct diagonal matrix units are nonzero with vanishing product; pulling them back
    -- along `f` contradicts the absence of zero divisors in `ℍ[R]`.
    obtain ⟨i, j, hij⟩ := exists_pair_ne n
    have h : f.symm (Matrix.single i i 1) * f.symm (Matrix.single j j 1) = 0 := by
      rw [← map_mul, Matrix.single_mul_single_of_ne _ _ _ _ hij, map_zero]
    rcases mul_eq_zero.mp h with h | h
    · simpa using congr_fun₂ ((map_eq_zero_iff _ f.symm.injective).mp h) i i
    · simpa using congr_fun₂ ((map_eq_zero_iff _ f.symm.injective).mp h) j j

end NoZeroDivisors

section LinearOrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {x : ℍ[R]}

/-- A quaternion is real exactly when its inverse is. -/
@[simp]
theorem im_inv_eq_zero_iff : x⁻¹.im = 0 ↔ x.im = 0 := by
  simp_rw [← forall_mul_comm_iff_im_eq_zero _root_.Quaternion.isLeftRegular_two, ← commute_iff_eq]
  exact ⟨fun H y ↦ by simpa using (H y).inv_left₀, fun H y ↦ (H y).inv_left₀⟩

end LinearOrderedField

end Quaternion

end TauCeti
