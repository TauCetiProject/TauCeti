/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Basic results on graded algebras

For a `ℤ`-graded algebra concentrated in nonnegative degrees, the degree-zero component of a
product is the product of the degree-zero components, as for gradings by a canonically ordered
monoid (`GradedRing.projZeroRingHom`). Consequently an idempotent with no degree-zero component
vanishes: its powers have no components below any given degree.

In any graded ring, multiplication by a homogeneous element `a` of degree `i` shifts every
homogeneous component by `i`. If `a` is moreover left regular, then the components of `b` can be
read off from those of `a * b`; in particular, if `a * b` is homogeneous of degree `i + j`, then
`b` is homogeneous of degree `j`. For instance, dividing a homogeneous polynomial by a linear form
that divides it produces a homogeneous polynomial of one degree less. Pairing against a functional
that vanishes off a single degree `d` sees, against an element of degree `l`, only the component
of degree `i` with `i + l = d`.

## Main results

* `TauCeti.GradedAlgebra.mul_le_grade_add`: the product of two homogeneous components is
  contained in the component indexed by the sum of their degrees.
* `TauCeti.GradedAlgebra.coe_decompose_mul_zero_of_nonneg`: in nonnegative degrees, the degree-zero
  component is multiplicative.
* `TauCeti.GradedAlgebra.eq_zero_of_isIdempotentElem_of_decompose_zero`: in nonnegative degrees,
  an idempotent with zero degree-zero component is zero.
* `TauCeti.GradedAlgebra.mem_of_mul_mem_add_of_isLeftRegular`: if `a ∈ 𝒜 i` is left regular and
  `a * b ∈ 𝒜 (i + j)`, then `b ∈ 𝒜 j`.
* `TauCeti.GradedAlgebra.proj_mem`: the degree-`i` projection lands in the degree-`i` component.
* `TauCeti.GradedAlgebra.proj_of_mem_same` and `TauCeti.GradedAlgebra.proj_of_mem_ne`: the
  degree-`j` projection fixes elements of degree `j` and kills elements of any other degree.
* `TauCeti.GradedAlgebra.apply_coe_decompose_mul_of_forall_ne`: for a functional vanishing off
  one degree `d`, pairing with an element of degree `l` only sees the component of degree `i`,
  where `i + l = d`.
* `TauCeti.GradedAlgebra.isScalarTower_gradeZero`: the scalars act on a graded algebra through its
  degree-zero part.
* `SetLike.neg_one_mem_graded`, `SetLike.neg_mem_graded`: in a graded ring, `-1` has degree zero
  and every homogeneous component is closed under negation.
-/

public section

namespace TauCeti.GradedAlgebra

open DirectSum

section Mul

variable {R A ι : Type*} [Add ι] [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [SetLike.GradedMul 𝒜]

/-- The product of two homogeneous components lies in the component of the sum of the degrees. -/
theorem mul_le_grade_add (i j : ι) : 𝒜 i * 𝒜 j ≤ 𝒜 (i + j) :=
  Submodule.mul_le.mpr fun _ ha _ hb ↦ SetLike.mul_mem_graded ha hb

end Mul

section Nonneg

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]

/-- **The degree-zero component is multiplicative in nonnegative degrees.** This is the
`ℤ`-graded counterpart of `GradedRing.projZeroRingHom`, which needs a canonically ordered grading
monoid. -/
theorem coe_decompose_mul_zero_of_nonneg (hneg : ∀ p < 0, 𝒜 p = ⊥) (x y : A) :
    (decompose 𝒜 (x * y) 0 : A) = decompose 𝒜 x 0 * decompose 𝒜 y 0 := by
  have hzero {p : ℤ} (hp : p < 0) {c : A} (hc : c ∈ 𝒜 p) : c = 0 := by
    rwa [hneg p hp, Submodule.mem_bot] at hc
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, decompose_add, DirectSum.add_apply, Submodule.coe_add,
    hx, hx']
  | @homogeneous i x =>
    obtain ⟨c, hc⟩ := x
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add y y' hy hy' =>
      simp only [mul_add, decompose_add, DirectSum.add_apply, Submodule.coe_add, hy, hy']
    | @homogeneous j y =>
      obtain ⟨c', hc'⟩ := y
      dsimp only
      rcases lt_or_ge i 0 with hi | hi
      · simp [hzero hi hc]
      rcases lt_or_ge j 0 with hj | hj
      · simp [hzero hj hc']
      by_cases h : i + j = 0
      · obtain rfl : i = 0 := by omega
        obtain rfl : j = 0 := by omega
        rw [decompose_of_mem_same 𝒜 (by simpa using SetLike.GradedMul.mul_mem hc hc'),
          decompose_of_mem_same 𝒜 hc, decompose_of_mem_same 𝒜 hc']
      · rw [decompose_of_mem_ne 𝒜 (SetLike.GradedMul.mul_mem hc hc') h]
        rcases eq_or_ne i 0 with rfl | h'
        · rw [decompose_of_mem_ne 𝒜 hc' (by omega), mul_zero]
        · rw [decompose_of_mem_ne 𝒜 hc h', zero_mul]

/-- **An idempotent with no degree-zero component vanishes** in nonnegative degrees. -/
theorem eq_zero_of_isIdempotentElem_of_decompose_zero (hneg : ∀ p < 0, 𝒜 p = ⊥) {f : A}
    (hf : IsIdempotentElem f) (h0 : (decompose 𝒜 f 0 : A) = 0) : f = 0 := by
  -- The components of `f` vanish below degree one, so those of `f ^ n` vanish below degree `n`,
  -- and `f` is its own `n`th power for every `n ≥ 1`.
  have hzero {p : ℤ} (hp : p < 0) {c : A} (hc : c ∈ 𝒜 p) : c = 0 := by
    rwa [hneg p hp, Submodule.mem_bot] at hc
  set r := decompose 𝒜 f with hr
  have hr1 : ∀ i < (1 : ℤ), r i = 0 := by
    intro i hi
    rcases lt_or_eq_of_le (show i ≤ 0 by omega) with hi | rfl
    · exact Subtype.ext (hzero hi (r i).property)
    · exact Subtype.ext h0
  have hpow (n : ℕ) : r = r ^ (n + 1) := by
    have h : decompose 𝒜 (f ^ (n + 1)) = decompose 𝒜 f ^ (n + 1) :=
      map_pow (decomposeRingEquiv 𝒜) f (n + 1)
    rw [hr, ← h, hf.pow_succ_eq]
  have hvan : ∀ n : ℕ, ∀ i < ((n + 1 : ℕ) : ℤ), r i = 0 := by
    intro n
    induction n with
    | zero => simpa using hr1
    | succ n ih =>
      intro i hi
      rw [hpow (n + 1), pow_succ, ← hpow n]
      exact mul_apply_eq_zero ih hr1 (by push_cast at hi ⊢; omega)
  have : r = 0 := by
    ext i : 1
    exact hvan i.toNat i (by omega)
  simpa [hr] using congrArg (decompose 𝒜).symm this

end Nonneg

section Regular

variable {A ι σ : Type*} [AddLeftCancelMonoid ι] [DecidableEq ι] [Semiring A] [SetLike σ A]
  [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- **Cancelling a homogeneous regular factor.** If `a` is homogeneous of degree `i` and left
regular, and `a * b` is homogeneous of degree `i + j`, then `b` is homogeneous of degree `j`. -/
theorem mem_of_mul_mem_add_of_isLeftRegular {a b : A} {i j : ι} (ha : a ∈ 𝒜 i)
    (hreg : IsLeftRegular a) (hab : a * b ∈ 𝒜 (i + j)) : b ∈ 𝒜 j := by
  -- Every component of `b` away from degree `j` is killed by `a`, hence vanishes.
  have hk (k : ι) (hk : k ≠ j) : decompose 𝒜 b k = 0 := Subtype.ext <| by
    rw [ZeroMemClass.coe_zero, ← hreg.mul_left_eq_zero_iff,
      ← coe_decompose_mul_add_of_left_mem 𝒜 ha,
      decompose_of_mem_ne 𝒜 hab ((add_right_injective i).ne hk.symm)]
  have hb : decompose 𝒜 b = DirectSum.of _ j (decompose 𝒜 b j) := by
    ext k : 1
    by_cases hkj : k = j
    · subst hkj
      rw [DirectSum.of_eq_same]
    · rw [hk k hkj, DirectSum.of_eq_of_ne _ _ _ hkj]
  rw [← (decompose 𝒜).symm_apply_apply b, hb, decompose_symm_of]
  exact (decompose 𝒜 b j).property

end Regular

section Proj

variable {R A ι : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
  [Algebra R A] (𝒜 : ι → Submodule R A) [_root_.GradedAlgebra 𝒜]

/-- The degree-`i` projection of a graded algebra lands in the degree-`i` component. -/
theorem proj_mem (i : ι) (a : A) : _root_.GradedAlgebra.proj 𝒜 i a ∈ 𝒜 i := by
  rw [_root_.GradedAlgebra.proj_apply]
  exact (decompose 𝒜 a i).property

variable {𝒜}

/-- The degree-`i` projection fixes elements of degree `i`. -/
theorem proj_of_mem_same {i : ι} {a : A} (ha : a ∈ 𝒜 i) : _root_.GradedAlgebra.proj 𝒜 i a = a := by
  rw [_root_.GradedAlgebra.proj_apply, decompose_of_mem_same 𝒜 ha]

/-- The degree-`j` projection kills elements of degree `i ≠ j`. -/
theorem proj_of_mem_ne {i j : ι} {a : A} (ha : a ∈ 𝒜 i) (hij : i ≠ j) :
    _root_.GradedAlgebra.proj 𝒜 j a = 0 := by
  rw [_root_.GradedAlgebra.proj_apply, decompose_of_mem_ne 𝒜 ha hij]

end Proj

section Functional

variable {A ι σ F M : Type*} [AddRightCancelMonoid ι] [DecidableEq ι] [Semiring A] [SetLike σ A]
  [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] [AddCommMonoid M] [FunLike F A M]
  [AddMonoidHomClass F A M]

/-- **Pairing against a functional concentrated in one degree.** If `φ` vanishes on every
homogeneous component except that of degree `d`, then pairing `x` with an element `c` of degree
`l` only sees the component of `x` of the complementary degree `i`, where `i + l = d`. -/
theorem apply_coe_decompose_mul_of_forall_ne {φ : F} {d : ι} (hφ : ∀ i ≠ d, ∀ a ∈ 𝒜 i, φ a = 0)
    (x : A) {i l : ι} {c : A} (hc : c ∈ 𝒜 l) (hil : i + l = d) :
    φ ((decompose 𝒜 x i : A) * c) = φ (x * c) := by
  classical
  conv_rhs => rw [← sum_support_decompose 𝒜 x]
  rw [Finset.sum_mul, map_sum, Finset.sum_eq_single i]
  · intro i' _ hi'
    exact hφ _ (fun h ↦ hi' (add_right_cancel (h.trans hil.symm))) _
      (SetLike.mul_mem_graded (SetLike.coe_mem _) hc)
  · intro hi
    rw [DFinsupp.notMem_support_iff.mp hi]
    simp

end Functional

section GradeZero

variable {R A ι : Type*} [AddMonoid ι] [CommSemiring R] [CommSemiring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]

/-- The scalars of an algebra with a graded monoid of submodules act on it through its degree-zero
part. Only the multiplicative structure of the grading is used, not a decomposition. -/
instance isScalarTower_gradeZero : IsScalarTower R (𝒜 0) A :=
  ⟨fun r a b ↦ by
    simp only [Algebra.smul_def (A := A) (R := 𝒜 0), SetLike.GradeZero.algebraMap_apply,
      Submodule.coe_smul, smul_mul_assoc]⟩

end GradeZero

end TauCeti.GradedAlgebra

namespace SetLike

section Ring

variable {ι σ A : Type*} [Ring A] [SetLike σ A] [AddSubmonoidClass σ A]
  [DecidableEq ι] [AddMonoid ι]

/-- In a graded ring, `-1` is homogeneous of degree zero. -/
theorem neg_one_mem_graded (𝒜 : ι → σ) [GradedRing 𝒜] : (-1 : A) ∈ 𝒜 0 := by
  have h : (DirectSum.decompose 𝒜 (-1 : A) 0 : A) + 1 = 0 := by
    calc (DirectSum.decompose 𝒜 (-1 : A) 0 : A) + 1
        = (DirectSum.decompose 𝒜 (-1 : A) 0 : A) + (DirectSum.decompose 𝒜 (1 : A) 0 : A) := by
          rw [DirectSum.decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem]
      _ = (DirectSum.decompose 𝒜 (-1 + 1 : A) 0 : A) := by
          rw [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      _ = 0 := by simp
  rw [← eq_neg_iff_add_eq_zero.mpr h]
  exact SetLike.coe_mem _

/-- In a graded ring, every homogeneous component is closed under negation. -/
theorem neg_mem_graded {𝒜 : ι → σ} [GradedRing 𝒜] ⦃k : ι⦄ {a : A} (ha : a ∈ 𝒜 k) :
    -a ∈ 𝒜 k := by
  simpa only [neg_one_mul, zero_add] using SetLike.GradedMul.mul_mem (neg_one_mem_graded 𝒜) ha

end Ring

end SetLike
