/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
import TauCeti.Algebra.DirectSum.Supported

/-!
# Basic results on graded algebras

For a `ℤ`-graded algebra concentrated in nonnegative degrees, the degree-zero component of a
product is the product of the degree-zero components, as for gradings by a canonically ordered
monoid (`GradedRing.projZeroRingHom`). Bundling `a ↦ decompose 𝒜 a 0` therefore gives an
`R`-algebra homomorphism `projZeroAlgHom : A →ₐ[R] 𝒜 0` whose kernel is the positive-degree part
`⨆ i > 0, 𝒜 i`, which is closed under right multiplication by arbitrary elements of `A`.
Consequently an idempotent with no degree-zero component vanishes: its powers have no components
below any given degree.

In any graded ring, multiplication by a homogeneous element `a` of degree `i` shifts every
homogeneous component by `i`. If `a` is moreover left regular, then the components of `b` can be
read off from those of `a * b`; in particular, if `a * b` is homogeneous of degree `i + j`, then
`b` is homogeneous of degree `j`. For instance, dividing a homogeneous polynomial by a linear form
that divides it produces a homogeneous polynomial of one degree less. Pairing against a functional
that vanishes off a single degree `d` sees, against an element of degree `l`, only the component
of degree `i` with `i + l = d`.

## Main definitions

* `TauCeti.GradedAlgebra.projZeroAlgHom`: degree-zero projection `A →ₐ[R] 𝒜 0` for a nonnegatively
  `ℤ`-graded `R`-algebra.

## Main results

* `TauCeti.GradedAlgebra.mul_le_grade_add`: the product of two homogeneous components is
  contained in the component indexed by the sum of their degrees.
* `TauCeti.GradedAlgebra.coe_decompose_mul_zero_of_nonneg`: in nonnegative degrees, the degree-zero
  component is multiplicative.
* `TauCeti.GradedAlgebra.projZeroAlgHom_eq_zero_iff`: `projZeroAlgHom hneg a = 0` iff
  `a ∈ ⨆ i > 0, 𝒜 i`.
* `TauCeti.GradedAlgebra.mul_mem_positive_of_left`: `⨆ i > 0, 𝒜 i` is closed under right
  multiplication by arbitrary elements of `A`.
* `TauCeti.GradedAlgebra.eq_zero_of_isIdempotentElem_of_decompose_zero`: in nonnegative degrees,
  an idempotent with zero degree-zero component is zero.
* `TauCeti.GradedAlgebra.mem_of_mul_mem_add_of_isLeftRegular`: if `a ∈ 𝒜 i` is left regular and
  `a * b ∈ 𝒜 (i + j)`, then `b ∈ 𝒜 j`.
* `TauCeti.GradedAlgebra.apply_coe_decompose_mul_of_forall_ne`: for a functional vanishing off
  one degree `d`, pairing with an element of degree `l` only sees the component of degree `i`,
  where `i + l = d`.
* `TauCeti.GradedAlgebra.isScalarTower_gradeZero`: the scalars act on a graded algebra through its
  degree-zero part.
-/

public section

namespace TauCeti.GradedAlgebra

open _root_.DirectSum

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

/-- Projection onto the degree-zero subalgebra `𝒜 0` of a nonnegatively `ℤ`-graded `R`-algebra.
This is the `ℤ`-graded algebra counterpart of `GradedRing.projZeroRingHom`. -/
noncomputable def projZeroAlgHom (hneg : ∀ i < 0, 𝒜 i = ⊥) : A →ₐ[R] 𝒜 0 where
  toFun a := decompose 𝒜 a 0
  map_one' := Subtype.ext (decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (coe_decompose_mul_zero_of_nonneg hneg x y)
  commutes' c := Subtype.ext <| by
    simpa using decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 c)

/-- Applying `projZeroAlgHom` extracts the degree-zero component `decompose 𝒜 a 0`. -/
@[simp]
theorem projZeroAlgHom_apply (hneg : ∀ i < 0, 𝒜 i = ⊥) (a : A) :
    projZeroAlgHom hneg a = decompose 𝒜 a 0 :=
  (rfl)

/-- The underlying element of `projZeroAlgHom hneg a` is the degree-zero component of `a`. -/
theorem coe_projZeroAlgHom_apply (hneg : ∀ i < 0, 𝒜 i = ⊥) (a : A) :
    (projZeroAlgHom hneg a : A) = decompose 𝒜 a 0 :=
  (rfl)

/-- `projZeroAlgHom` restricts to the identity on `𝒜 0`. -/
theorem projZeroAlgHom_apply_coe (hneg : ∀ i < 0, 𝒜 i = ⊥) (a : 𝒜 0) :
    projZeroAlgHom hneg (a : A) = a :=
  Subtype.ext (decompose_of_mem_same 𝒜 a.property)

/-- Homogeneous elements of strictly positive degree map to zero under `projZeroAlgHom`. -/
theorem projZeroAlgHom_eq_zero_of_mem_pos (hneg : ∀ i < 0, 𝒜 i = ⊥) {i : ℤ} (hi : 0 < i)
    {a : A} (ha : a ∈ 𝒜 i) : projZeroAlgHom hneg a = 0 :=
  Subtype.ext (decompose_of_mem_ne 𝒜 ha (ne_of_gt hi))

/-- In a nonnegatively graded algebra, an element has vanishing degree-zero projection if and only
if it lies in the positive-degree submodule `⨆ i > 0, 𝒜 i`. -/
theorem projZeroAlgHom_eq_zero_iff (hneg : ∀ i < 0, 𝒜 i = ⊥) {a : A} :
    projZeroAlgHom hneg a = 0 ↔ a ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
  classical
  have hiSup : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) = ⨆ i : {i : ℤ | 0 < i}, 𝒜 i :=
    (iSup_subtype'' {i : ℤ | 0 < i} 𝒜).symm
  rw [hiSup, TauCeti.DirectSum.mem_iSup_iff_decompose_eq_zero]
  refine ⟨fun ha0 i hi ↦ ?_, fun h ↦ Subtype.ext (h 0 (by simp))⟩
  rcases lt_or_eq_of_le (not_lt.mp (Set.notMem_ofPred_iff.mp hi)) with hi' | rfl
  · simpa [hneg i hi'] using (decompose 𝒜 a i).property
  · exact congrArg Subtype.val ha0

/-- In a nonnegatively graded algebra, the positive-degree part `⨆ i > 0, 𝒜 i` is closed under
right multiplication by arbitrary elements of `A`. -/
theorem mul_mem_positive_of_left (hneg : ∀ i < 0, 𝒜 i = ⊥) {a : A}
    (ha : a ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) (b : A) :
    a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
  rw [← projZeroAlgHom_eq_zero_iff hneg] at ha ⊢
  simp [map_mul, ha]

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
