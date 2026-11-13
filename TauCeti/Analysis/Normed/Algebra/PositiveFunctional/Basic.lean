/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.RingTheory.Binomial
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Algebra.Spectrum
public import TauCeti.Analysis.StarAlgebra.CauchySchwarz
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Positive functionals on Banach ⋆-algebras

Let `A` be a unital complex Banach ⋆-algebra with an isometric involution (`NormedStarGroup A`).
No C⋆-identity and no normalization `‖1‖ = 1` of the identity norm are assumed. This file
establishes the automatic continuity and norm theory of algebraically square-positive functionals
`φ : A →ₗ[ℂ] ℂ` (bundled as `TauCeti.StarPositiveFunctional A`):

* `TauCeti.sqrtOneSub`: for `‖h‖ < 1` in a unital real Banach algebra, the binomial series
  `∑' n, Ring.choose (1 / 2 : ℝ) n • (-h) ^ n` converges in norm to a square root of `1 - h`,
  which is selfadjoint whenever `h` is selfadjoint. Unlike the local inverse-function square root
  `TauCeti.sqrtNearOne`, this series converges on the entire open unit ball `‖h‖ < 1`, allowing
  scaling by arbitrary radii `r > ‖h‖` and passage to the limit for closed-ball positivity.
* `TauCeti.StarPositiveFunctional.continuous` and `LinearMap.continuous_of_star_mul_nonneg`:
  every algebraically positive functional on a unital complex Banach ⋆-algebra with isometric
  involution is continuous, with `‖φ a‖ ≤ (φ 1).re * ‖a‖` and
  `(φ (star a * a)).re ≤ (φ 1).re * ‖a‖ ^ 2`. When `A` is nontrivial,
  `(φ 1).re / ‖(1 : A)‖ ≤ ‖φ‖ ≤ (φ 1).re`, with equality `‖φ‖ = (φ 1).re` when `‖(1 : A)‖ = 1`.
* `TauCeti.StarPositiveFunctional.fromCompletion`: a continuous positive functional on a possibly
  incomplete unital normed ⋆-algebra with isometric involution extends positively to its Banach
  completion, yielding the same norm bounds and quadratic-form inequality
  `φ (star b * star a * a * b) ≤ (‖a‖ : ℂ) ^ 2 * φ (star b * b)`.
* `NonUnitalStarAlgHom.norm_apply_le_of_normedStarGroup`: every algebraic ⋆-homomorphism from a
  possibly nonunital complex Banach ⋆-algebra with isometric involution to a C⋆-algebra is
  contractive (`‖f a‖ ≤ ‖a‖`).

## References

* M. A. Rieffel, *C⋆-algebras*, Math 208 lectures, UC Berkeley, Spring 2008, notes by
  T. Johnson-Freyd, pp. 11–14.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §1.3.
-/

public section

noncomputable section

open scoped ComplexOrder

namespace TauCeti

section BinomialSqrt

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The binomial coefficients for the square root `1 / 2` have absolute value at most `1`. -/
private theorem abs_choose_one_half_le_one (n : ℕ) : |Ring.choose (1 / 2 : ℝ) n| ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases n with _ | n
    · norm_num [Ring.choose_one_right]
    · have hrec : Ring.choose (1 / 2 : ℝ) (n + 2) =
          Ring.choose (1 / 2 : ℝ) (n + 1) * ((1 / 2 : ℝ) - (n + 1)) / (n + 2) := by
        have h := congrArg (· / ((n + 2).factorial : ℝ))
          (Ring.descPochhammer_eq_factorial_smul_choose (1 / 2 : ℝ) (n + 2))
        have hprev := Ring.descPochhammer_eq_factorial_smul_choose (1 / 2 : ℝ) (n + 1)
        rw [descPochhammer_succ_right, Polynomial.smeval_mul, hprev,
          Polynomial.smeval_sub, Polynomial.smeval_X, pow_one, Polynomial.smeval_natCast,
          pow_zero, nsmul_one, Nat.cast_succ] at h
        have hf : ((n + 2).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        rw [nsmul_eq_mul, nsmul_eq_mul, mul_div_cancel_left₀ _ hf] at h
        rw [← h, Nat.factorial_succ (n + 1), Nat.factorial_succ n, Nat.cast_mul, Nat.cast_mul]
        push_cast
        field_simp
        ring
      have hle : |(1 / 2 : ℝ) - ((n : ℝ) + 1)| ≤ (n : ℝ) + 2 := by
        rw [abs_le]
        constructor <;> linarith
      rw [hrec, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
      have hdiv : |(1 / 2 : ℝ) - ((n : ℝ) + 1)| / ((n : ℝ) + 2) ≤ 1 :=
        div_le_one_of_le₀ hle (by positivity)
      calc
        |Ring.choose (1 / 2 : ℝ) (n + 1)| * |(1 / 2 : ℝ) - ((n : ℝ) + 1)| / ((n : ℝ) + 2)
          = |Ring.choose (1 / 2 : ℝ) (n + 1)| *
              (|(1 / 2 : ℝ) - ((n : ℝ) + 1)| / ((n : ℝ) + 2)) := mul_div_assoc _ _ _
        _ ≤ 1 * 1 := mul_le_mul ih hdiv (by positivity) zero_le_one
        _ = 1 := one_mul 1

/-- The binomial series for `(1 - h) ^ (1 / 2)` is norm-summable whenever `‖h‖ < 1`. -/
theorem summable_norm_sqrtOneSub_term {h : A} (hh : ‖h‖ < 1) :
    Summable fun n : ℕ => ‖Ring.choose (1 / 2 : ℝ) n • (-h) ^ n‖ := by
  refine ((summable_geometric_of_lt_one (norm_nonneg h) hh).mul_left
    (max ‖(1 : A)‖ 1)).of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_
  calc
    ‖Ring.choose (1 / 2 : ℝ) n • (-h) ^ n‖
      ≤ ‖Ring.choose (1 / 2 : ℝ) n‖ * ‖(-h) ^ n‖ := norm_smul_le _ _
    _ ≤ 1 * ‖(-h) ^ n‖ := by
        gcongr
        simpa only [Real.norm_eq_abs] using abs_choose_one_half_le_one n
    _ = ‖(-h) ^ n‖ := one_mul _
    _ ≤ max ‖(1 : A)‖ 1 * ‖h‖ ^ n := by
        cases n with
        | zero => simp
        | succ n =>
          calc
            ‖(-h) ^ (n + 1)‖ ≤ ‖-h‖ ^ (n + 1) := norm_pow_le' _ n.succ_pos
            _ = 1 * ‖h‖ ^ (n + 1) := by rw [norm_neg, one_mul]
            _ ≤ max ‖(1 : A)‖ 1 * ‖h‖ ^ (n + 1) := by gcongr; exact le_max_right _ _

variable (A) in
/-- The binomial series `∑' n, Ring.choose (1 / 2 : ℝ) n • (-h) ^ n`, which equals a selfadjoint
square root of `1 - h` in a unital real Banach algebra when `‖h‖ < 1`. -/
def sqrtOneSub (h : A) : A :=
  ∑' n : ℕ, Ring.choose (1 / 2 : ℝ) n • (-h) ^ n

/-- For `‖h‖ < 1` in a unital real Banach algebra, `sqrtOneSub h` squares to `1 - h`. -/
theorem sqrtOneSub_mul_self [CompleteSpace A] {h : A} (hh : ‖h‖ < 1) :
    sqrtOneSub A h * sqrtOneSub A h = 1 - h := by
  have hs := summable_norm_sqrtOneSub_term hh
  rw [sqrtOneSub, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs]
  have hterm : ∀ k : ℕ,
      (∑ i ∈ Finset.antidiagonal k,
        (Ring.choose (1 / 2 : ℝ) i.1 • (-h) ^ i.1) *
          (Ring.choose (1 / 2 : ℝ) i.2 • (-h) ^ i.2)) =
        Ring.choose (1 : ℝ) k • (-h) ^ k := by
    intro k
    have hsum : (∑ i ∈ Finset.antidiagonal k,
        (Ring.choose (1 / 2 : ℝ) i.1 • (-h) ^ i.1) *
          (Ring.choose (1 / 2 : ℝ) i.2 • (-h) ^ i.2)) =
        (∑ i ∈ Finset.antidiagonal k,
          Ring.choose (1 / 2 : ℝ) i.1 * Ring.choose (1 / 2 : ℝ) i.2) • (-h) ^ k := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_antidiagonal] at hi
      rw [smul_mul_smul_comm, ← pow_add, hi]
    rw [hsum, ← Ring.add_choose_eq k (Commute.all (1 / 2 : ℝ) (1 / 2 : ℝ))]
    norm_num
  simp_rw [hterm]
  have hzero : ∀ k : ℕ, k ∉ ({0, 1} : Finset ℕ) → Ring.choose (1 : ℝ) k • (-h) ^ k = 0 := by
    intro k hk
    have hk0 : k ≠ 0 := fun h0 => hk (by simp [h0])
    have hk1 : k ≠ 1 := fun h1 => hk (by simp [h1])
    have hch : Ring.choose (1 : ℝ) k = 0 := by
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega)]
      simp
    simp [hch]
  rw [tsum_eq_sum hzero]
  simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, Ring.choose_zero_right, pow_zero, one_smul, Ring.choose_one_right,
    pow_one]
  exact (sub_eq_add_neg 1 h).symm

/-- If `h` is selfadjoint, then `sqrtOneSub h` is selfadjoint. -/
theorem isSelfAdjoint_sqrtOneSub [StarRing A] [ContinuousStar A] [StarModule ℝ A] {h : A}
    (hh : IsSelfAdjoint h) : IsSelfAdjoint (sqrtOneSub A h) :=
  IsSelfAdjoint.tsum fun n =>
    IsSelfAdjoint.smul (star_trivial _) (hh.neg.pow n)

end BinomialSqrt

/-- Compatibility of `StarModule ℂ A` with real scalar multiplication, used locally for the real
binomial series. -/
private theorem starModuleReal (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A]
    [StarModule ℂ A] : StarModule ℝ A where
  star_smul r a := by
    rw [← Complex.coe_smul, star_smul, Complex.star_def, Complex.conj_ofReal, Complex.coe_smul,
      star_trivial (R := ℝ)]

namespace StarPositiveFunctional

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [NormedStarGroup A]
  [StarModule ℂ A] (φ : StarPositiveFunctional A)

section Complete

variable [CompleteSpace A]

/-- On a unital complex Banach ⋆-algebra, a positive functional is nonnegative on `1 - h` for
every selfadjoint `h` with `‖h‖ < 1`. -/
theorem map_one_sub_nonneg_of_isSelfAdjoint_of_norm_lt_one {h : A} (hsa : IsSelfAdjoint h)
    (hh : ‖h‖ < 1) : 0 ≤ φ (1 - h) := by
  let := starModuleReal A
  have hs := isSelfAdjoint_sqrtOneSub hsa
  rw [← sqrtOneSub_mul_self hh]
  nth_rw 1 [← hs.star_eq]
  exact φ.square_nonneg (sqrtOneSub A h)

/-- For a selfadjoint element `h` of a unital complex Banach ⋆-algebra,
`|(φ h).re| ≤ (φ 1).re * ‖h‖`. -/
theorem re_apply_le_of_isSelfAdjoint {h : A} (hsa : IsSelfAdjoint h) :
    |(φ h).re| ≤ (φ 1).re * ‖h‖ := by
  let := starModuleReal A
  have h1 : 0 ≤ (φ 1).re := by simpa using (φ.square_nonneg 1).1
  -- For every strict upper bound `r > ‖h‖`, `‖r⁻¹ • h‖ < 1` gives `±(φ h).re ≤ r * (φ 1).re`.
  have hbound : ∀ x : A, IsSelfAdjoint x → (φ x).re ≤ (φ 1).re * ‖x‖ := by
    intro x hx
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    set r : ℝ := ‖x‖ + ε / ((φ 1).re + 1)
    have hr0 : 0 < r := add_pos_of_nonneg_of_pos (norm_nonneg x) (div_pos hε (by linarith))
    have hxr : ‖r⁻¹ • x‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le), inv_mul_lt_one₀ hr0]
      exact lt_add_of_pos_right _ (div_pos hε (by linarith))
    have hsub := (φ.map_one_sub_nonneg_of_isSelfAdjoint_of_norm_lt_one
      (IsSelfAdjoint.smul (star_trivial r⁻¹) hx) hxr).1
    rw [← Complex.coe_smul, map_sub, map_smul, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.zero_re, sub_nonneg] at hsub
    have hxr_le : (φ x).re ≤ r * (φ 1).re := by
      have := mul_le_mul_of_nonneg_left hsub hr0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul] at this
    calc
      (φ x).re ≤ (‖x‖ + ε / ((φ 1).re + 1)) * (φ 1).re := hxr_le
      _ = (φ 1).re * ‖x‖ + ε * ((φ 1).re / ((φ 1).re + 1)) := by ring
      _ < (φ 1).re * ‖x‖ + ε := by
        gcongr
        exact mul_lt_of_lt_one_right hε ((div_lt_one (by linarith)).mpr (by linarith))
  rw [abs_le]
  refine ⟨?_, hbound h hsa⟩
  have hneg := hbound (-h) hsa.neg
  simp only [map_neg, Complex.neg_re, norm_neg] at hneg
  linarith

/-- **Closed-ball positivity**: on a unital complex Banach ⋆-algebra, a positive functional is
nonnegative on `1 - h` for every selfadjoint `h` with `‖h‖ ≤ 1`. -/
theorem map_one_sub_nonneg_of_isSelfAdjoint_of_norm_le_one {h : A} (hsa : IsSelfAdjoint h)
    (hh : ‖h‖ ≤ 1) : 0 ≤ φ (1 - h) := by
  have him : (φ (1 - h)).im = 0 := by
    have h1 : (φ 1).im = 0 := by simpa using (φ.square_nonneg 1).2.symm
    have hstar : φ (star h) = star (φ h) := φ.map_star h
    rw [hsa.star_eq, Complex.ext_iff, Complex.star_def, Complex.conj_im] at hstar
    have hh_im : (φ h).im = 0 := by linarith [hstar.2]
    simp [h1, hh_im]
  have h1 : 0 ≤ (φ 1).re := by simpa using (φ.square_nonneg 1).1
  have hre : 0 ≤ (φ (1 - h)).re := by
    have hle := (abs_le.mp (φ.re_apply_le_of_isSelfAdjoint hsa)).2
    have hle1 : (φ h).re ≤ (φ 1).re := hle.trans (mul_le_of_le_one_right h1 hh)
    simpa [sub_nonneg] using hle1
  exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩

/-- On a unital complex Banach ⋆-algebra with isometric involution,
`(φ (star a * a)).re ≤ (φ 1).re * ‖a‖ ^ 2`. -/
theorem map_star_mul_self_re_le (a : A) :
    (φ (star a * a)).re ≤ (φ 1).re * ‖a‖ ^ 2 := by
  have hre := (abs_le.mp (φ.re_apply_le_of_isSelfAdjoint (IsSelfAdjoint.star_mul_self a))).2
  have h1 : 0 ≤ (φ 1).re := by simpa using (φ.square_nonneg 1).1
  calc
    (φ (star a * a)).re ≤ (φ 1).re * ‖star a * a‖ := hre
    _ ≤ (φ 1).re * (‖star a‖ * ‖a‖) := by gcongr; exact norm_mul_le _ _
    _ = (φ 1).re * ‖a‖ ^ 2 := by rw [norm_star, sq]

/-- **Automatic norm bound**: an algebraically positive functional on a unital complex Banach
⋆-algebra with isometric involution satisfies `‖φ a‖ ≤ (φ 1).re * ‖a‖`. -/
theorem norm_apply_le (a : A) : ‖φ a‖ ≤ (φ 1).re * ‖a‖ := by
  have h1 : 0 ≤ (φ 1).re := by simpa using (φ.square_nonneg 1).1
  refine nonneg_le_nonneg_of_sq_le_sq (mul_nonneg h1 (norm_nonneg a)) ?_
  have hcs := φ.toLinearMap.norm_map_star_mul_sq_le φ.square_nonneg 1 a
  simp only [toLinearMap_apply, star_one, one_mul] at hcs
  have h1_norm : ‖φ 1‖ = (φ 1).re :=
    (Complex.re_eq_norm.mpr (by simpa using φ.square_nonneg 1)).symm
  have ha_norm : ‖φ (star a * a)‖ = (φ (star a * a)).re :=
    (Complex.re_eq_norm.mpr (φ.square_nonneg a)).symm
  rw [h1_norm, ha_norm] at hcs
  calc
    ‖φ a‖ * ‖φ a‖ = ‖φ a‖ ^ 2 := (sq _).symm
    _ ≤ (φ 1).re * (φ (star a * a)).re := hcs
    _ ≤ (φ 1).re * ((φ 1).re * ‖a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (φ.map_star_mul_self_re_le a) h1
    _ = ((φ 1).re * ‖a‖) * ((φ 1).re * ‖a‖) := by ring

/-- **Automatic continuity**: every algebraically positive functional on a unital complex Banach
⋆-algebra with isometric involution is continuous. -/
@[continuity]
theorem continuous : Continuous φ :=
  AddMonoidHomClass.continuous_of_bound φ (φ 1).re φ.norm_apply_le

/-- View a positive functional on a unital complex Banach ⋆-algebra as a continuous linear map. -/
def toContinuousLinearMap : A →L[ℂ] ℂ :=
  ⟨φ.toLinearMap, φ.continuous⟩

@[simp]
theorem toContinuousLinearMap_apply (a : A) : φ.toContinuousLinearMap a = φ a := (rfl)

/-- The operator norm of a positive functional on a unital complex Banach ⋆-algebra is at most
`(φ 1).re`. -/
theorem opNorm_toContinuousLinearMap_le : ‖φ.toContinuousLinearMap‖ ≤ (φ 1).re :=
  ContinuousLinearMap.opNorm_le_bound _ (by simpa using (φ.square_nonneg 1).1) φ.norm_apply_le

/-- For a nontrivial unital complex Banach ⋆-algebra, `(φ 1).re / ‖(1 : A)‖ ≤ ‖φ‖`. -/
theorem div_norm_one_le_opNorm_toContinuousLinearMap [Nontrivial A] :
    (φ 1).re / ‖(1 : A)‖ ≤ ‖φ.toContinuousLinearMap‖ := by
  rw [div_le_iff₀ (norm_pos_iff.mpr one_ne_zero)]
  have h1 : ‖φ 1‖ = (φ 1).re := (Complex.re_eq_norm.mpr (by simpa using φ.square_nonneg 1)).symm
  simpa only [toContinuousLinearMap_apply, h1] using φ.toContinuousLinearMap.le_opNorm 1

/-- When `‖(1 : A)‖ = 1`, the operator norm of a positive functional equals `(φ 1).re`. -/
theorem opNorm_toContinuousLinearMap_eq_of_normOneClass [NormOneClass A] :
    ‖φ.toContinuousLinearMap‖ = (φ 1).re := by
  have : Nontrivial A := nontrivial_of_ne (1 : A) 0 fun h => by
    have hnorm := congrArg norm h
    simp at hnorm
  refine le_antisymm φ.opNorm_toContinuousLinearMap_le ?_
  simpa using φ.div_norm_one_le_opNorm_toContinuousLinearMap

end Complete

section Completion

open UniformSpace

/-- Extend a continuous positive functional on a possibly incomplete unital normed ⋆-algebra to a
positive functional on its Banach completion. -/
def fromCompletion (hc : Continuous φ) : StarPositiveFunctional (Completion A) where
  toLinearMap := (ContinuousLinearMap.fromCompletion ⟨φ.toLinearMap, hc⟩).toLinearMap
  square_nonneg x := by
    refine Completion.induction_on x ?_ fun a => ?_
    · exact isClosed_le continuous_const
        ((ContinuousLinearMap.fromCompletion ⟨φ.toLinearMap, hc⟩).continuous.comp
          (continuous_star.mul continuous_id))
    · have hcoe : (ContinuousLinearMap.fromCompletion ⟨φ.toLinearMap, hc⟩)
          ((star (a : Completion A)) * (a : Completion A)) = φ (star a * a) := by
        rw [← Completion.coe_star, ← Completion.coe_mul]
        exact ContinuousLinearMap.fromCompletion_apply_coe ⟨φ.toLinearMap, hc⟩ (star a * a)
      simpa only [toLinearMap_apply, ContinuousLinearMap.coe_coe, hcoe] using
        φ.square_nonneg a

omit [StarModule ℂ A] in
@[simp]
theorem fromCompletion_apply_coe (hc : Continuous φ) (a : A) :
    φ.fromCompletion hc (a : Completion A) = φ a :=
  ContinuousLinearMap.fromCompletion_apply_coe ⟨φ.toLinearMap, hc⟩ a

omit [StarModule ℂ A] in
@[simp]
theorem fromCompletion_one (hc : Continuous φ) :
    φ.fromCompletion hc 1 = φ 1 := by
  rw [← Completion.coe_one, φ.fromCompletion_apply_coe hc 1]

/-- A continuous positive functional on a possibly incomplete unital normed ⋆-algebra with
isometric involution satisfies `‖φ a‖ ≤ (φ 1).re * ‖a‖`. -/
theorem norm_apply_le_of_continuous (hc : Continuous φ) (a : A) :
    ‖φ a‖ ≤ (φ 1).re * ‖a‖ := by
  let : NormedAlgebra ℂ (Completion A) := ⟨norm_smul_le⟩
  have h := (φ.fromCompletion hc).norm_apply_le (a : Completion A)
  simpa only [fromCompletion_apply_coe, fromCompletion_one, Completion.norm_coe] using h

/-- A continuous positive functional on a possibly incomplete unital normed ⋆-algebra with
isometric involution satisfies `(φ (star a * a)).re ≤ (φ 1).re * ‖a‖ ^ 2`. -/
theorem map_star_mul_self_re_le_of_continuous (hc : Continuous φ) (a : A) :
    (φ (star a * a)).re ≤ (φ 1).re * ‖a‖ ^ 2 := by
  let : NormedAlgebra ℂ (Completion A) := ⟨norm_smul_le⟩
  have h := (φ.fromCompletion hc).map_star_mul_self_re_le (a : Completion A)
  simpa only [← Completion.coe_star, ← Completion.coe_mul, fromCompletion_apply_coe,
    fromCompletion_one, Completion.norm_coe] using h

/-- For a continuous positive functional on a possibly incomplete unital normed ⋆-algebra with
isometric involution, `φ (star b * star a * a * b) ≤ (‖a‖ : ℂ) ^ 2 * φ (star b * b)`. -/
theorem map_star_mul_star_mul_self_le_of_continuous (hc : Continuous φ) (a b : A) :
    φ (star b * star a * a * b) ≤ (‖a‖ : ℂ) ^ 2 * φ (star b * b) := by
  let ψ : StarPositiveFunctional A :=
    { toFun c := φ (star b * c * b)
      map_add' c d := by simp only [mul_add, add_mul, map_add]
      map_smul' r c := by simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply]
      square_nonneg c := by
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, star_mul, mul_assoc, toLinearMap_apply] using
          φ.square_nonneg (c * b) }
  have hψc : Continuous ψ :=
    hc.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hre := ψ.map_star_mul_self_re_le_of_continuous hψc a
  have hψ1 : ψ 1 = φ (star b * b) := by simp [ψ]
  have hψa : ψ (star a * a) = φ (star b * star a * a * b) := by simp [ψ, mul_assoc]
  rw [hψ1, hψa] at hre
  have hnonneg : 0 ≤ φ (star b * star a * a * b) := by
    simpa only [star_mul, mul_assoc, toLinearMap_apply] using φ.square_nonneg (a * b)
  rw [← Complex.ofReal_pow, Complex.le_def, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  have himb : (φ (star b * b)).im = 0 := by simpa using (φ.square_nonneg b).2.symm
  refine ⟨by linarith, ?_⟩
  rw [← hnonneg.2, himb, mul_zero, Complex.zero_im]

/-- On a unital complex Banach ⋆-algebra with isometric involution, every positive functional
satisfies the GNS boundedness inequality
`φ (star b * star a * a * b) ≤ (‖a‖ : ℂ) ^ 2 * φ (star b * b)`. -/
theorem map_star_mul_star_mul_self_le [CompleteSpace A] (a b : A) :
    φ (star b * star a * a * b) ≤ (‖a‖ : ℂ) ^ 2 * φ (star b * b) :=
  φ.map_star_mul_star_mul_self_le_of_continuous φ.continuous a b

end Completion

end Banach

end StarPositiveFunctional

end TauCeti

namespace LinearMap

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [NormedStarGroup A] [StarModule ℂ A]

/-- **Automatic continuity of positive functionals**: every algebraically square-positive linear
functional on a unital complex Banach ⋆-algebra with isometric involution is continuous. -/
theorem continuous_of_star_mul_nonneg (φ : A →ₗ[ℂ] ℂ) (hφ : ∀ a, 0 ≤ φ (star a * a)) :
    Continuous φ :=
  TauCeti.StarPositiveFunctional.continuous ⟨φ, hφ⟩

/-- An algebraically square-positive linear functional on a unital complex Banach ⋆-algebra with
isometric involution satisfies `‖φ a‖ ≤ (φ 1).re * ‖a‖`. -/
theorem norm_apply_le_of_star_mul_nonneg (φ : A →ₗ[ℂ] ℂ) (hφ : ∀ a, 0 ≤ φ (star a * a)) (a : A) :
    ‖φ a‖ ≤ (φ 1).re * ‖a‖ :=
  TauCeti.StarPositiveFunctional.norm_apply_le ⟨φ, hφ⟩ a

end Banach

end LinearMap

namespace NonUnitalStarAlgHom

open scoped NNReal

/-- Every algebraic ⋆-homomorphism from a possibly nonunital complex Banach ⋆-algebra with
isometric involution into a C⋆-algebra is norm contractive (`‖φ a‖₊ ≤ ‖a‖₊`). -/
theorem nnNorm_apply_le_of_normedStarGroup {F A B : Type*}
    [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [CompleteSpace A] [StarRing A] [NormedStarGroup A]
    [NonUnitalCStarAlgebra B] [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (φ : F) (a : A) : ‖φ a‖₊ ≤ ‖a‖₊ := by
  refine nonneg_le_nonneg_of_sq_le_sq zero_le ?_
  let ψ : A →⋆ₙₐ[ℂ] Unitization ℂ B :=
    (Unitization.inrNonUnitalStarAlgHom ℂ B).comp (NonUnitalStarAlgHom.ofClass φ : A →⋆ₙₐ[ℂ] B)
  have hsa : IsSelfAdjoint (ψ (star a * a)) := (IsSelfAdjoint.star_mul_self a).map ψ
  have hspec : (‖ψ (star a * a)‖₊ : ENNReal) = spectralRadius ℂ (ψ (star a * a)) := by
    rw [← hsa.spectralRadius_eq_nnNorm]
  have hle : spectralRadius ℂ (ψ (star a * a)) ≤ spectralRadius ℂ (star a * a) :=
    NonUnitalAlgHom.spectralRadius_apply_le ψ (star a * a)
  have hnorm : spectralRadius ℂ (star a * a) ≤ ‖star a * a‖₊ :=
    spectralRadius_le_nnNorm (star a * a)
  have hsq : (‖φ a‖₊ : ENNReal) ^ 2 ≤ (‖a‖₊ : ENNReal) ^ 2 := by
    calc
      (‖φ a‖₊ : ENNReal) ^ 2 = (‖star (φ a) * φ a‖₊ : ENNReal) := by
        rw [CStarRing.nnNorm_star_mul_self, sq, ENNReal.coe_mul]
      _ = (‖ψ (star a * a)‖₊ : ENNReal) := by
        rw [← StarHomClass.map_star φ, ← map_mul φ, ← Unitization.nnNorm_inr (𝕜 := ℂ)]
        simp [ψ]
      _ = spectralRadius ℂ (ψ (star a * a)) := hspec
      _ ≤ spectralRadius ℂ (star a * a) := hle
      _ ≤ (‖star a * a‖₊ : ENNReal) := hnorm
      _ ≤ (‖star a‖₊ * ‖a‖₊ : ℝ≥0) := by exact_mod_cast nnNorm_mul_le (star a) a
      _ = (‖a‖₊ : ENNReal) ^ 2 := by rw [nnNorm_star, ← sq, ENNReal.coe_pow]
  rw [sq, sq] at hsq
  exact_mod_cast hsq

/-- Every algebraic ⋆-homomorphism from a possibly nonunital complex Banach ⋆-algebra with
isometric involution into a C⋆-algebra is norm contractive (`‖φ a‖ ≤ ‖a‖`). -/
theorem norm_apply_le_of_normedStarGroup {F A B : Type*}
    [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [CompleteSpace A] [StarRing A] [NormedStarGroup A]
    [NonUnitalCStarAlgebra B] [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (φ : F) (a : A) : ‖φ a‖ ≤ ‖a‖ :=
  mod_cast nnNorm_apply_le_of_normedStarGroup φ a

/-- Every algebraic ⋆-homomorphism from a possibly nonunital complex Banach ⋆-algebra with
isometric involution into a C⋆-algebra is continuous. -/
theorem continuous_of_normedStarGroup {F A B : Type*}
    [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [CompleteSpace A] [StarRing A] [NormedStarGroup A]
    [NonUnitalCStarAlgebra B] [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (φ : F) : Continuous φ :=
  AddMonoidHomClass.continuous_of_bound φ 1 fun a => by
    simpa only [one_mul] using norm_apply_le_of_normedStarGroup φ a

end NonUnitalStarAlgHom
