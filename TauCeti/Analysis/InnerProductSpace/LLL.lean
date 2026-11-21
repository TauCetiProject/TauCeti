/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# LLL-reduced families and the short-vector bound

The Gram–Schmidt coefficients of an ordered real family determine the size and Lovász
conditions for Lenstra–Lenstra–Lovász reduction. At parameters `1/2` and `3/4`, the
squared lengths of successive Gram–Schmidt vectors can decrease by at most a factor of two.
For a nonzero integer combination, its last nonzero coefficient has absolute value at least
one. Orthogonal projection onto the corresponding Gram–Schmidt vector then bounds that
vector's length by the length of the combination.

## Main declarations

* `TauCeti.InnerProductSpace.lllCoefficient` is the coefficient of the `j`-th orthogonalized vector
  in the `i`-th input vector.
* `TauCeti.InnerProductSpace.IsLLLReduced` expresses independence, size reduction and the Lovász
  condition.
* `TauCeti.InnerProductSpace.lll_gramSchmidt_bound` compares two orthogonalized lengths.
* `TauCeti.InnerProductSpace.lll_short_vector_factor` compares the first basis vector against any
  nonzero vector in the integer span.

## References

* [A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, *Factoring polynomials with rational
  coefficients*](https://doi.org/10.1007/BF01457454), §1, Propositions 1.6 and 1.11.
-/

public section

open Finset InnerProductSpace

namespace TauCeti.InnerProductSpace

attribute [local instance] IsWellOrder.toHasWellFounded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The Gram–Schmidt coefficient `μᵢⱼ = ⟪bᵢ, bⱼ*⟫ / ‖bⱼ*‖²`.
It is zero if the `j`-th Gram–Schmidt vector vanishes. -/
noncomputable def lllCoefficient {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (b : ι → E) (i j : ι) : ℝ :=
  inner ℝ (b i) (gramSchmidt ℝ b j) / ‖gramSchmidt ℝ b j‖ ^ 2

/-- The Gram–Schmidt coefficient is the pairing with the residual divided by its squared norm. -/
theorem lllCoefficient_def {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (b : ι → E) (i j : ι) :
    lllCoefficient b i j = inner ℝ (b i) (gramSchmidt ℝ b j) / ‖gramSchmidt ℝ b j‖ ^ 2 := (rfl)

/-- An input vector is the sum of its Gram–Schmidt residual and its earlier components. -/
theorem gramSchmidt_add_sum_lllCoefficient {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (b : ι → E) (i : ι) :
    gramSchmidt ℝ b i + ∑ j ∈ Iio i, lllCoefficient b i j • gramSchmidt ℝ b j = b i := by
  simp_rw [lllCoefficient_def, ← real_inner_comm (b i)]
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using (gramSchmidt_def'' ℝ b i).symm

/-- The coefficient of a nonzero residual in its own input vector is one. -/
theorem lllCoefficient_self {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {b : ι → E} {i : ι} (hi : gramSchmidt ℝ b i ≠ 0) : lllCoefficient b i i = 1 := by
  rw [lllCoefficient_def, real_inner_comm, inner_gramSchmidt_eq_norm_sq, RCLike.ofReal_real_eq_id,
    id_eq, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hi))]

/-- The residual at a later index has coefficient zero in an earlier input vector. -/
theorem lllCoefficient_eq_zero_of_lt {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (b : ι → E) {i j : ι} (hij : i < j) : lllCoefficient b i j = 0 := by
  rw [lllCoefficient_def, real_inner_comm, gramSchmidt_inv_triangular ℝ b hij, zero_div]

/-- For an orthogonal family, every off-diagonal Gram–Schmidt coefficient vanishes. -/
theorem lllCoefficient_eq_zero_of_orthogonal {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {b : ι → E} (hb : Pairwise fun i j ↦ inner ℝ (b i) (b j) = 0)
    {i j : ι} (hij : i ≠ j) : lllCoefficient b i j = 0 := by
  rw [lllCoefficient_def, gramSchmidt_of_orthogonal ℝ hb, hb hij, zero_div]

/-- An LLL-reduced family is linearly independent, size-reduced with parameter `1/2`, and
satisfies the Lovász condition with parameter `3/4` at each pair of adjacent indices. -/
structure IsLLLReduced (b : Fin n → E) : Prop where
  /-- The input vectors are linearly independent over `ℝ`. -/
  linearIndependent : LinearIndependent ℝ b
  /-- The coefficients of earlier Gram–Schmidt vectors have absolute value at most `1/2`. -/
  size_reduced : ∀ i j, j < i → |lllCoefficient b i j| ≤ 1 / 2
  /-- The Lovász inequality relating adjacent squared Gram–Schmidt lengths. -/
  lovasz : ∀ i j, j.val + 1 = i.val →
    (3 / 4 - lllCoefficient b i j ^ 2) * ‖gramSchmidt ℝ b j‖ ^ 2 ≤ ‖gramSchmidt ℝ b i‖ ^ 2

/-- An orthonormal family is LLL-reduced. -/
theorem _root_.Orthonormal.isLLLReduced {b : Fin n → E} (hb : Orthonormal ℝ b) :
    IsLLLReduced b := by
  refine ⟨hb.linearIndependent, ?_, ?_⟩
  · intro i j hij
    rw [lllCoefficient_eq_zero_of_orthogonal hb.2 hij.ne']
    norm_num
  · intro i j hij
    have hne : i ≠ j := by omega
    rw [lllCoefficient_eq_zero_of_orthogonal hb.2 hne, gramSchmidt_of_orthogonal ℝ hb.2]
    norm_num [hb.norm_eq_one]

private theorem half_le_lovasz_factor {μ : ℝ} (hμ : |μ| ≤ 1 / 2) :
    1 / 2 ≤ 3 / 4 - μ ^ 2 := by
  have hsq : μ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := (sq_le_sq).2 (by simpa using hμ)
  linarith

/-- The square of each Gram–Schmidt length in an LLL-reduced family is at most twice the
square of the next length. -/
theorem IsLLLReduced.gramSchmidt_bound_succ {b : Fin n → E} (h : IsLLLReduced b)
    {i j : Fin n} (hij : j.val + 1 = i.val) :
    ‖gramSchmidt ℝ b j‖ ^ 2 ≤ 2 * ‖gramSchmidt ℝ b i‖ ^ 2 := by
  have hji : j < i := by omega
  have hcoeff := half_le_lovasz_factor (h.size_reduced i j hji)
  have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖gramSchmidt ℝ b j‖)
  linarith [hmul.trans (h.lovasz i j hij)]

/-- Comparing squared Gram–Schmidt lengths in an LLL-reduced family costs at most a factor
of two per index step. -/
theorem lll_gramSchmidt_bound {b : Fin n → E} (h : IsLLLReduced b) {i j : Fin n} (hji : j ≤ i) :
    ‖gramSchmidt ℝ b j‖ ^ 2 ≤ (2 : ℝ) ^ (i.val - j.val) * ‖gramSchmidt ℝ b i‖ ^ 2 := by
  have bound (k : ℕ) (hjk : j.val ≤ k) (hkn : k < n) :
      ‖gramSchmidt ℝ b j‖ ^ 2 ≤ (2 : ℝ) ^ (k - j.val) * ‖gramSchmidt ℝ b ⟨k, hkn⟩‖ ^ 2 := by
    induction k, hjk using Nat.le_induction with
    | base => simp
    | succ k hjk ih =>
      have hk : k < n := Nat.lt_of_succ_lt hkn
      calc
        _ ≤ (2 : ℝ) ^ (k - j.val) * ‖gramSchmidt ℝ b ⟨k, hk⟩‖ ^ 2 := ih hk
        _ ≤ (2 : ℝ) ^ (k - j.val) * (2 * ‖gramSchmidt ℝ b ⟨k + 1, hkn⟩‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (h.gramSchmidt_bound_succ (i := ⟨k + 1, hkn⟩) (j := ⟨k, hk⟩)
            rfl) (by positivity)
        _ = _ := by rw [Nat.succ_sub hjk, pow_succ (2 : ℝ) (k - j.val), mul_assoc]
  exact bound i.val hji i.isLt

/-- The first vector of a nonempty LLL-reduced family has squared length at most `2^(n-1)`
times the squared length of any nonzero vector in its integer span. -/
theorem lll_short_vector_factor {b : Fin n → E} (h : IsLLLReduced b) (hn : 0 < n)
    {x : E} (hx : x ∈ Submodule.span ℤ (Set.range b)) (hx0 : x ≠ 0) :
    ‖b ⟨0, hn⟩‖ ^ 2 ≤ (2 : ℝ) ^ (n - 1) * ‖x‖ ^ 2 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  have hne : (univ.filter fun i ↦ c i ≠ 0).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    by_contra! hc
    exact hx0 (by simp [fun i ↦ hc i (mem_univ i)])
  obtain ⟨j, hj, hjmax⟩ := exists_max_image _ id hne
  have hj0 : c j ≠ 0 := (mem_filter.mp hj).2
  have hjlater (i : Fin n) (hi : j < i) : c i = 0 := by
    by_contra hci
    exact hi.not_ge (hjmax i (mem_filter.mpr ⟨mem_univ _, hci⟩))
  have hnorm := norm_gramSchmidt_le_norm_sum_zsmul (𝕜 := ℝ) (b := b) hj0 hjlater
  have hfirst : gramSchmidt ℝ b ⟨0, hn⟩ = b ⟨0, hn⟩ := by
    -- On a successor-sized `Fin`, the locally finite order with bottom is the canonical one
    -- used by `gramSchmidt_bot`.
    cases n with
    | zero => omega
    | succ n => exact gramSchmidt_bot ℝ b
  calc
    ‖b ⟨0, hn⟩‖ ^ 2 ≤ (2 : ℝ) ^ j.val * ‖gramSchmidt ℝ b j‖ ^ 2 := by
      simpa only [hfirst, Fin.val_mk, Nat.sub_zero] using
        lll_gramSchmidt_bound h (i := j) (j := ⟨0, hn⟩) (Nat.zero_le j.val)
    _ ≤ (2 : ℝ) ^ (n - 1) * ‖∑ i, c i • b i‖ ^ 2 :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
        (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (sq_nonneg _) (by positivity)

section Examples

local notation "e" => EuclideanSpace.basisFun (Fin 2) ℝ

private noncomputable def planar (a c d : ℝ) : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
  ![a • e 0, c • e 0 + d • e 1]

private theorem planar_zero (a c d : ℝ) : planar a c d 0 = a • e 0 := rfl

private theorem planar_one (a c d : ℝ) : planar a c d 1 = c • e 0 + d • e 1 := rfl

private theorem planar_coefficient (a c d : ℝ) :
    lllCoefficient (planar a c d) 1 0 = c / a := by
  have hzero := gramSchmidt_bot ℝ (planar a c d)
  rw [bot_eq_zero, planar_zero] at hzero
  by_cases ha : a = 0
  · rw [lllCoefficient_def, hzero, ha]
    simp
  have h00 : inner ℝ (e 0) (e 0) = 1 := by
    rw [real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one e, one_pow]
  have h10 : inner ℝ (e 1) (e 0) = 0 := OrthonormalBasis.inner_eq_zero e (by decide)
  rw [lllCoefficient_def, hzero, planar_one]
  simp only [real_inner_smul_right, inner_add_left, real_inner_smul_left, h00, h10,
    mul_one, mul_zero, add_zero, norm_smul, OrthonormalBasis.norm_eq_one e, Real.norm_eq_abs,
    sq_abs]
  field_simp

private theorem planar_gramSchmidt_one {a c d : ℝ} (ha : a ≠ 0) :
    gramSchmidt ℝ (planar a c d) 1 = d • e 1 := by
  have h := gramSchmidt_add_sum_lllCoefficient (planar a c d) (1 : Fin 2)
  have hzero := gramSchmidt_bot ℝ (planar a c d)
  rw [bot_eq_zero, planar_zero] at hzero
  rw [show Iio (1 : Fin 2) = {0} by decide, Finset.sum_singleton, planar_coefficient, hzero,
    smul_smul, div_mul_cancel₀ _ ha, planar_one, add_comm (c • e 0)] at h
  exact add_right_cancel h

private theorem planar_linearIndependent {a c d : ℝ} (ha : a ≠ 0) (hd : d ≠ 0) :
    LinearIndependent ℝ (planar a c d) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) hf
  have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) hf
  norm_num [planar, Fin.sum_univ_two, EuclideanSpace.basisFun_apply]
    at h0 h1
  have hf1 : f 1 = 0 := h1.resolve_right hd
  have hf0 : f 0 = 0 := (show f 0 = 0 ∨ a = 0 by simpa [hf1] using h0).resolve_right ha
  fin_cases i <;> assumption

private theorem planar_reduced {a c d : ℝ} (ha : a ≠ 0)
    (hsize : |c / a| ≤ 1 / 2) (hlovasz : (3 / 4 - (c / a) ^ 2) * a ^ 2 ≤ d ^ 2) :
    IsLLLReduced (planar a c d) := by
  have hfactor := (show (0 : ℝ) < 1 / 2 by norm_num).trans_le (half_le_lovasz_factor hsize)
  have hd := sq_pos_iff.mp ((mul_pos hfactor (sq_pos_of_ne_zero ha)).trans_le hlovasz)
  have indices : ∀ {i j : Fin 2}, j < i → i = 1 ∧ j = 0 := by decide
  refine ⟨planar_linearIndependent ha hd, ?_, ?_⟩
  · intro i j hij
    obtain ⟨rfl, rfl⟩ := indices hij
    simpa only [planar_coefficient] using hsize
  · intro i j hij
    obtain ⟨rfl, rfl⟩ := indices (show j < i by omega)
    have hzero := gramSchmidt_bot ℝ (planar a c d)
    rw [bot_eq_zero, planar_zero] at hzero
    simpa only [planar_coefficient, hzero, planar_gramSchmidt_one ha, norm_smul,
      OrthonormalBasis.norm_eq_one e, mul_one, Real.norm_eq_abs, sq_abs] using hlovasz

example : lllCoefficient (planar 1 (1 / 2) 1) 1 0 = 1 / 2 ∧
    IsLLLReduced (planar 1 (1 / 2) 1) := by
  refine ⟨?_, planar_reduced (by norm_num) (by norm_num) (by norm_num)⟩
  rw [planar_coefficient, div_one]

example : lllCoefficient (planar 1 0 1) 1 0 = 0 ∧ IsLLLReduced (planar 1 0 1) := by
  refine ⟨?_, planar_reduced (by norm_num) (by norm_num) (by norm_num)⟩
  rw [planar_coefficient, zero_div]

-- The two size-reduced families below have different off-diagonal coefficients. Both violate
-- Lovász because the first Gram–Schmidt vector is too long.
example (c : ℝ) (hc : c = 0 ∨ c = 1) :
    |lllCoefficient (planar 2 c 1) 1 0| ≤ 1 / 2 ∧ ¬ IsLLLReduced (planar 2 c 1) := by
  constructor
  · rw [planar_coefficient]
    rcases hc with rfl | rfl <;> norm_num
  intro h
  have hl := h.lovasz 1 0 rfl
  have hzero := gramSchmidt_bot ℝ (planar 2 c 1)
  rw [bot_eq_zero, planar_zero] at hzero
  rcases hc with rfl | rfl <;>
    norm_num [planar_coefficient, hzero,
      planar_gramSchmidt_one (by norm_num : (2 : ℝ) ≠ 0), norm_smul, OrthonormalBasis.norm_eq_one e,
      Real.norm_eq_abs] at hl

example : ¬ IsLLLReduced (planar 1 2 0) := by
  intro h
  have h0 : gramSchmidt ℝ (planar 1 2 0) 1 = 0 := by
    rw [planar_gramSchmidt_one one_ne_zero, zero_smul]
  exact gramSchmidt_ne_zero 1 h.linearIndependent h0

example : IsLLLReduced (planar 1 (1 / 2) (Real.sqrt (1 / 2))) ∧
    ‖gramSchmidt ℝ (planar 1 (1 / 2) (Real.sqrt (1 / 2))) 0‖ ^ 2 =
      2 * ‖gramSchmidt ℝ (planar 1 (1 / 2) (Real.sqrt (1 / 2))) 1‖ ^ 2 := by
  have hs := Real.sq_sqrt (x := 1 / 2) (by norm_num)
  refine ⟨planar_reduced one_ne_zero (by norm_num) (by rw [hs]; norm_num), ?_⟩
  have hzero := gramSchmidt_bot ℝ (planar 1 (1 / 2) (Real.sqrt (1 / 2)))
  rw [bot_eq_zero, planar_zero] at hzero
  simp only [hzero, planar_gramSchmidt_one (one_ne_zero : (1 : ℝ) ≠ 0),
    norm_smul, OrthonormalBasis.norm_eq_one e, mul_one, Real.norm_eq_abs, sq_abs, hs]
  norm_num

private theorem line_gramSchmidt_one (c : ℝ) :
    gramSchmidt ℝ (![1, c] : Fin 2 → ℝ) 1 = 0 := by
  have hzero := gramSchmidt_bot ℝ (![1, c] : Fin 2 → ℝ)
  rw [bot_eq_zero] at hzero
  rw [gramSchmidt_def, show Iio (1 : Fin 2) = {0} by decide, Finset.sum_singleton, hzero,
    Submodule.starProjection_singleton]
  simp [RCLike.ofReal_real_eq_id]

example : lllCoefficient (![1, 1 / 2] : Fin 2 → ℝ) 1 0 = 1 / 2 := by
  have hzero := gramSchmidt_bot ℝ (![1, 1 / 2] : Fin 2 → ℝ)
  rw [bot_eq_zero] at hzero
  rw [lllCoefficient_def, hzero]
  norm_num [Real.inner_apply]

example :
    gramSchmidt ℝ (![1, 1] : Fin 2 → ℝ) 1 = 0 ∧
    lllCoefficient (![1, 1] : Fin 2 → ℝ) 0 1 = 0 ∧
    ¬ IsLLLReduced (![1, 1] : Fin 2 → ℝ) := by
  refine ⟨line_gramSchmidt_one 1, by simp [lllCoefficient_def, line_gramSchmidt_one], fun h ↦ ?_⟩
  exact gramSchmidt_ne_zero 1 h.linearIndependent (line_gramSchmidt_one 1)

example (b : Fin 0 → ℝ) : IsLLLReduced b :=
  ⟨linearIndependent_empty_type, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩

example {b : Fin 1 → E} {x : E} (hx : x ∈ Submodule.span ℤ (Set.range b)) (hx0 : x ≠ 0) :
    ‖b 0‖ ≤ ‖x‖ := by
  have hb : b 0 ≠ 0 := by
    intro hb
    rw [Set.range_unique, Fin.default_eq_zero, hb,
      Submodule.span_singleton_eq_bot.mpr rfl] at hx
    exact hx0 (by simpa using hx)
  have noLt : ∀ i j : Fin 1, ¬ j < i := by decide
  have noAdj : ∀ i j : Fin 1, j.val + 1 ≠ i.val := by decide
  have h : IsLLLReduced b := ⟨linearIndependent_unique_iff.mpr hb,
    fun i j hij ↦ (noLt i j hij).elim, fun i j hij ↦ (noAdj i j hij).elim⟩
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    simpa using lll_short_vector_factor h Nat.one_pos hx hx0)

-- Real coordinates do not give the integer-coordinate bound, even in rank one.
example : (1 / 2 : ℝ) ∈ Submodule.span ℝ (Set.range (![1] : Fin 1 → ℝ)) ∧
    ‖(1 / 2 : ℝ)‖ < ‖(1 : ℝ)‖ := by
  constructor
  · simp
  · norm_num [Real.norm_eq_abs]

end Examples

end TauCeti.InnerProductSpace
