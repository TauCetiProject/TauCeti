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

* `InnerProductSpace.lllCoefficient` is the coefficient of the `j`-th orthogonalized vector
  in the `i`-th input vector.
* `InnerProductSpace.IsLLLReduced` expresses independence, size reduction and the Lovász condition.
* `InnerProductSpace.lll_gramSchmidt_bound` compares two orthogonalized lengths.
* `InnerProductSpace.lll_short_vector_factor` compares the first basis vector against any
  nonzero vector in the integer span.

## References

* [A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, *Factoring polynomials with rational
  coefficients*](https://doi.org/10.1007/BF01457454), §1, Propositions 1.6 and 1.11.
-/

@[expose] public section

open Finset

namespace InnerProductSpace

attribute [local instance] IsWellOrder.toHasWellFounded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The Gram–Schmidt coefficient `μᵢⱼ = ⟪bᵢ, bⱼ*⟫ / ‖bⱼ*‖²`.
It is zero if the `j`-th Gram–Schmidt vector vanishes. -/
noncomputable def lllCoefficient {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (b : ι → E) (i j : ι) : ℝ :=
  inner ℝ (b i) (gramSchmidt ℝ b j) / ‖gramSchmidt ℝ b j‖ ^ 2

/-- For an orthogonal family, every off-diagonal Gram–Schmidt coefficient vanishes. -/
theorem lllCoefficient_eq_zero_of_orthogonal {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {b : ι → E} (hb : Pairwise fun i j ↦ inner ℝ (b i) (b j) = 0)
    {i j : ι} (hij : i ≠ j) : lllCoefficient b i j = 0 := by
  rw [lllCoefficient, gramSchmidt_of_orthogonal ℝ hb, hb hij, zero_div]

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

/-- In a linearly independent family, each Gram–Schmidt coefficient has a positive denominator. -/
theorem gramSchmidt_norm_sq_pos {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {b : ι → E} (hb : LinearIndependent ℝ b) (j : ι) :
    0 < ‖gramSchmidt ℝ b j‖ ^ 2 :=
  pow_pos (norm_pos_iff.mpr (gramSchmidt_ne_zero j hb)) _

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

private theorem norm_gramSchmidt_le_norm_sum_zsmul {b : Fin n → E} {c : Fin n → ℤ} {j : Fin n}
    (hcj : c j ≠ 0) (hc : ∀ i, j < i → c i = 0) :
    ‖gramSchmidt ℝ b j‖ ≤ ‖∑ i, c i • b i‖ := by
  let g := gramSchmidt ℝ b j
  have hinner : inner ℝ g (∑ i, c i • b i) = (c j : ℝ) * ‖g‖ ^ 2 := by
    simp only [inner_sum, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]
    rw [Finset.sum_eq_single j]
    · simp only [g, inner_gramSchmidt_eq_norm_sq, RCLike.ofReal_real_eq_id, id_eq]
    · intro i _ hij
      rcases hij.lt_or_gt with hlt | hgt
      · rw [gramSchmidt_inv_triangular ℝ b hlt, mul_zero]
      · simp [hc i hgt]
    · simp
  have habs : (1 : ℝ) ≤ |(c j : ℝ)| := by exact_mod_cast Int.one_le_abs hcj
  have hprod : ‖g‖ ^ 2 ≤ ‖g‖ * ‖∑ i, c i • b i‖ := calc
    ‖g‖ ^ 2 ≤ |(c j : ℝ)| * ‖g‖ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) habs
    _ = |inner ℝ g (∑ i, c i • b i)| := by rw [hinner, abs_mul, abs_of_nonneg (sq_nonneg ‖g‖)]
    _ ≤ _ := abs_real_inner_le_norm _ _
  by_contra! hlt
  exact (mul_lt_mul_of_pos_left hlt ((norm_nonneg _).trans_lt hlt)).not_ge
    (by simpa only [pow_two] using hprod)

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
  have hnorm := norm_gramSchmidt_le_norm_sum_zsmul hj0 hjlater (b := b)
  have hfirst : gramSchmidt ℝ b ⟨0, hn⟩ = b ⟨0, hn⟩ :=
    gramSchmidt_eq_self_of_inner_eq_zero fun i hi ↦ (Nat.not_lt_zero i.val hi).elim
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

private theorem planar_gramSchmidt_zero (a c d : ℝ) :
    gramSchmidt ℝ (planar a c d) 0 = a • e 0 := by
  apply gramSchmidt_eq_self_of_inner_eq_zero (f := planar a c d) (i := 0)
  intro i hi
  exact (Fin.not_lt_zero i hi).elim

private theorem planar_coefficient (a c d : ℝ) :
    lllCoefficient (planar a c d) 1 0 = c / a := by
  by_cases ha : a = 0
  · simp [ha, lllCoefficient, planar_gramSchmidt_zero]
  have h00 : inner ℝ (e 0) (e 0) = 1 := by
    rw [real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one e, one_pow]
  have h10 : inner ℝ (e 1) (e 0) = 0 := OrthonormalBasis.inner_eq_zero e (by decide)
  rw [lllCoefficient, planar_gramSchmidt_zero]
  change inner ℝ (c • e 0 + d • e 1) (a • e 0) / ‖a • e 0‖ ^ 2 = c / a
  simp only [real_inner_smul_right, inner_add_left, real_inner_smul_left, h00, h10,
    mul_one, mul_zero, add_zero, norm_smul, OrthonormalBasis.norm_eq_one e, Real.norm_eq_abs,
    sq_abs]
  field_simp

private theorem planar_gramSchmidt_one {a c d : ℝ} (ha : a ≠ 0) :
    gramSchmidt ℝ (planar a c d) 1 = d • e 1 := by
  have h := gramSchmidt_def'' ℝ (planar a c d) (1 : Fin 2)
  simp only [show Iio (1 : Fin 2) = {0} by decide, Finset.sum_singleton, RCLike.ofReal_real_eq_id,
    id_eq] at h
  rw [real_inner_comm, ← lllCoefficient, planar_coefficient a c d, planar_gramSchmidt_zero,
    smul_smul, div_mul_cancel₀ _ ha] at h
  change c • e 0 + d • e 1 = _ at h
  rw [add_comm (c • e 0)] at h
  exact (add_right_cancel h).symm

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
  refine ⟨planar_linearIndependent ha hd, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    change |lllCoefficient (planar a c d) 1 0| ≤ 1 / 2
    simpa only [planar_coefficient a c d] using hsize
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    change (3 / 4 - lllCoefficient (planar a c d) 1 0 ^ 2) *
      ‖gramSchmidt ℝ (planar a c d) 0‖ ^ 2 ≤ ‖gramSchmidt ℝ (planar a c d) 1‖ ^ 2
    simpa only [planar_coefficient a c d, planar_gramSchmidt_zero, planar_gramSchmidt_one ha,
      norm_smul, OrthonormalBasis.norm_eq_one e, mul_one, Real.norm_eq_abs, sq_abs] using hlovasz

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
  rcases hc with rfl | rfl <;>
    norm_num [planar_coefficient, planar_gramSchmidt_zero,
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
  simp only [planar_gramSchmidt_zero, planar_gramSchmidt_one (one_ne_zero : (1 : ℝ) ≠ 0),
    norm_smul, OrthonormalBasis.norm_eq_one e, mul_one, Real.norm_eq_abs, sq_abs, hs]
  norm_num

private theorem line_gramSchmidt_zero (c : ℝ) :
    gramSchmidt ℝ (![1, c] : Fin 2 → ℝ) 0 = 1 :=
  gramSchmidt_eq_self_of_inner_eq_zero fun i hi ↦ (Fin.not_lt_zero i hi).elim

private theorem line_gramSchmidt_one (c : ℝ) :
    gramSchmidt ℝ (![1, c] : Fin 2 → ℝ) 1 = 0 := by
  rw [gramSchmidt_def, show Iio (1 : Fin 2) = {0} by decide, Finset.sum_singleton,
    line_gramSchmidt_zero, Submodule.starProjection_singleton]
  simp [RCLike.ofReal_real_eq_id]

example : lllCoefficient (![1, 1 / 2] : Fin 2 → ℝ) 1 0 = 1 / 2 := by
  norm_num [lllCoefficient, line_gramSchmidt_zero, Real.inner_apply]

example :
    gramSchmidt ℝ (![1, 1] : Fin 2 → ℝ) 1 = 0 ∧
    lllCoefficient (![1, 1] : Fin 2 → ℝ) 0 1 = 0 ∧
    ¬ IsLLLReduced (![1, 1] : Fin 2 → ℝ) := by
  refine ⟨line_gramSchmidt_one 1, by simp [lllCoefficient, line_gramSchmidt_one], fun h ↦ ?_⟩
  exact gramSchmidt_ne_zero 1 h.linearIndependent (line_gramSchmidt_one 1)

example (b : Fin 0 → ℝ) : IsLLLReduced b :=
  ⟨linearIndependent_empty_type, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {b : Fin 1 → E}
    (h : IsLLLReduced b) {x : E} (hx : x ∈ Submodule.span ℤ (Set.range b)) (hx0 : x ≠ 0) :
    ‖b 0‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simpa using lll_short_vector_factor h Nat.one_pos hx hx0

-- Real coordinates do not give the integer-coordinate bound, even in rank one.
example : (1 / 2 : ℝ) ∈ Submodule.span ℝ (Set.range (![1] : Fin 1 → ℝ)) ∧
    ‖(1 / 2 : ℝ)‖ < ‖(1 : ℝ)‖ := by
  constructor
  · simp
  · norm_num [Real.norm_eq_abs]

end Examples

end InnerProductSpace
