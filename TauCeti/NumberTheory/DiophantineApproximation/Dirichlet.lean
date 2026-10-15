/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Group.GeometryOfNumbers

/-!
# Dirichlet's theorem for systems of linear forms

Let `A` be a real `m × n` matrix, viewed as a system of `m` linear forms in `n` variables.
Dirichlet's theorem says that for every `Q > 1` there is a nonzero integer vector `y` with
`‖y‖∞ ≤ Q` such that every coordinate of `A y` lies within `Q ^ (-n / m)` of an integer.
Specializing to a single column gives simultaneous approximation of `m` real numbers by
rationals with a common denominator, and to a single row gives small values of one linear
form. Under the condition that no nonzero integer vector is sent to an integer vector, the
same bounds hold with `Q` replaced by `‖y‖∞` for infinitely many solutions; these are the
lower bounds behind exponents of approximation.

## Main results

* `Matrix.exists_int_abs_sum_mul_sub_le`: for `P, δ ≥ 0` with `δ < 1` and `P ^ n δ ^ m ≥ 1`
  there is a nonzero `y ∈ ℤⁿ` with `|yⱼ| ≤ P` and `x ∈ ℤᵐ` with `|(A y)ᵢ - xᵢ| ≤ δ`.
* `Matrix.dirichlet_linearForms`: Dirichlet's theorem with the bounds `Q` and `Q ^ (-n / m)`.
* `Matrix.dirichlet_linearForms_infinite`: if `A y` is never an integer vector for nonzero
  integral `y`, there are infinitely many solutions of `|(A y)ᵢ - xᵢ| ≤ ‖y‖∞ ^ (-n / m)`.
* `TauCeti.simultaneous_dirichlet`: for `α ∈ ℝᵐ` and `Q > 1` there are integers `x` and
  `0 < y ≤ Q ^ m` with `|xᵢ - αᵢ y| ≤ Q⁻¹`.
* `TauCeti.dirichlet_linearForm_infinite`: the case of a single linear form.

## Implementation notes

The proof applies Minkowski's convex body theorem
(`MeasureTheory.exists_ne_zero_int_vec_mem_of_two_pow_le_volume`) to the integer lattice in
`ℝ^(κ ⊕ ι)` and the preimage of a box under the integral shear `(y, x) ↦ (y, A y - x)`, an
involution of determinant `±1`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes, Chapter 1, Theorems 1.1, 1.3
  and 1.4, and Chapter 2, Corollaries 2.6 and 2.7 and Exercise 2.6.
* W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785, Chapter II.
-/

public section

open MeasureTheory Filter

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Dirichlet's theorem for linear forms, with general bounds.** Let `A` be a real matrix
with rows indexed by `ι` and columns indexed by the nonempty type `κ`. If `P, δ ≥ 0`,
`δ < 1` and `P ^ |κ| δ ^ |ι| ≥ 1`, then there are a nonzero integer vector `y` with
`|yⱼ| ≤ P` and an integer vector `x` with `|∑ⱼ Aᵢⱼ yⱼ - xᵢ| ≤ δ` for every `i`. -/
theorem exists_int_abs_sum_mul_sub_le [Nonempty κ] (A : Matrix ι κ ℝ) {P δ : ℝ}
    (hP : 0 ≤ P) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (h : 1 ≤ P ^ Fintype.card κ * δ ^ Fintype.card ι) :
    ∃ (y : κ → ℤ) (x : ι → ℤ), y ≠ 0 ∧ (∀ j, |(y j : ℝ)| ≤ P) ∧
      ∀ i, |∑ j, A i j * y j - x i| ≤ δ := by
  classical
  -- The shear `(y, x) ↦ (y, A y - x)` is an involution, so it has determinant `±1`.
  set M : Matrix (κ ⊕ ι) (κ ⊕ ι) ℝ := fromBlocks 1 0 A (-1)
  set T := toLin' M
  have hT : ∀ v, T v = Sum.elim (fun j ↦ v (.inl j))
      (fun i ↦ ∑ j, A i j * v (.inl j) - v (.inr i)) := fun v ↦ by
    ext (j | i) <;> simp [T, M, mulVec, dotProduct, one_apply, sub_eq_add_neg]
  have hTT : Function.Involutive T := fun v ↦ by
    ext (j | i) <;> simp [hT]
  have hdet : |LinearMap.det T| = 1 := by
    have h2 := congrArg LinearMap.det (LinearMap.ext hTT : T ∘ₗ T = LinearMap.id)
    rw [LinearMap.det_comp, LinearMap.det_id] at h2
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 (by rw [sq_abs, sq, h2])
  -- Minkowski's theorem for the integer lattice and the preimage of a box under the shear.
  set r : κ ⊕ ι → ℝ := Sum.elim (fun _ ↦ P) (fun _ ↦ δ)
  have hr : 0 ≤ r := fun k ↦ by cases k <;> simp [r, hP, hδ₀]
  set S := T ⁻¹' Set.Icc (-r) r
  have hsymm : ∀ v ∈ S, -v ∈ S := fun v hv ↦ by
    simp only [S, Set.mem_preimage, map_neg, Set.mem_Icc] at hv ⊢
    exact ⟨neg_le_neg hv.2, by simpa using neg_le_neg hv.1⟩
  have hcpt : IsCompact S := by
    have hS : T '' Set.Icc (-r) r = S := congrFun hTT.image_eq_preimage_symm _
    exact hS ▸ isCompact_Icc.image (LinearMap.continuous_of_finiteDimensional T)
  have hvol : 2 ^ Fintype.card (κ ⊕ ι) ≤ volume S := by
    rw [Measure.addHaar_preimage_linearMap _ (by simp [← abs_ne_zero, hdet]), abs_inv, hdet,
      inv_one, ENNReal.ofReal_one, one_mul, Real.volume_Icc_pi, Fintype.prod_sum_type,
      Fintype.card_sum]
    simp only [r, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, sub_neg_eq_add, Finset.prod_const,
      Finset.card_univ]
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow zero_le_two]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (2 : ℝ) ^ (Fintype.card κ + Fintype.card ι)
        ≤ 2 ^ (Fintype.card κ + Fintype.card ι) * (P ^ Fintype.card κ * δ ^ Fintype.card ι) :=
          le_mul_of_one_le_right (by positivity) h
      _ = (P + P) ^ Fintype.card κ * (δ + δ) ^ Fintype.card ι := by ring
  obtain ⟨z, hz0, hzS⟩ := exists_ne_zero_int_vec_mem_of_two_pow_le_volume hsymm
    ((convex_Icc _ _).linear_preimage T) hcpt hvol
  have hk : ∀ k, |T (fun k ↦ (z k : ℝ)) k| ≤ r k := fun k ↦ abs_le.2 ⟨hzS.1 k, hzS.2 k⟩
  refine ⟨fun j ↦ z (.inl j), fun i ↦ z (.inr i), ?_, fun j ↦ by simpa [hT, r] using hk (.inl j),
    fun i ↦ by simpa [hT, r] using hk (.inr i)⟩
  -- If `y = 0`, then every `|xᵢ| ≤ δ < 1`, so the lattice point would be zero.
  intro hy
  have hy' : ∀ j, z (.inl j) = 0 := congrFun hy
  have hx : ∀ i, z (.inr i) = 0 := fun i ↦ by
    have := hk (.inr i)
    simp only [hT, hy', r, Sum.elim_inr, Int.cast_zero, mul_zero, Finset.sum_const_zero,
      zero_sub, abs_neg] at this
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this.trans_lt hδ₁)
  exact hz0 (funext fun k ↦ by cases k <;> simp [hy', hx])

/-- **Dirichlet's theorem for systems of linear forms.** Let `A` be a real matrix with
`m = |ι| ≥ 1` rows and `n = |κ| ≥ 1` columns, and let `Q > 1`. There are a nonzero integer
vector `y` with `|yⱼ| ≤ Q` and an integer vector `x` with `|∑ⱼ Aᵢⱼ yⱼ - xᵢ| ≤ Q ^ (-n / m)` for
every `i`. -/
theorem dirichlet_linearForms [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) {Q : ℝ}
    (hQ : 1 < Q) :
    ∃ (y : κ → ℤ) (x : ι → ℤ), y ≠ 0 ∧ (∀ j, |(y j : ℝ)| ≤ Q) ∧
      ∀ i, |∑ j, A i j * y j - x i| ≤ Q ^ (-(Fintype.card κ : ℝ) / Fintype.card ι) := by
  have hQ₀ : 0 < Q := zero_lt_one.trans hQ
  have hm : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  refine A.exists_int_abs_sum_mul_sub_le hQ₀.le (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg hQ (div_neg_of_neg_of_pos (neg_lt_zero.2 hn) hm))
    (le_of_eq ?_)
  rw [← Real.rpow_mul_natCast hQ₀.le, div_mul_cancel₀ _ hm.ne', Real.rpow_neg hQ₀.le,
    Real.rpow_natCast, mul_inv_cancel₀ (by positivity)]

/-- **Dirichlet's theorem for systems of linear forms, infinitely many solutions.** Let `A` be
a real matrix with `m = |ι|` rows and `n = |κ| ≥ 1` columns such that `A y` is an integer
vector for an integer vector `y` only when `y = 0`. Then infinitely many pairs of integer
vectors `(y, x)` with `y ≠ 0` satisfy `|∑ⱼ Aᵢⱼ yⱼ - xᵢ| ≤ ‖y‖ ^ (-n / m)` for every `i`, where
`‖y‖` is the sup norm. -/
theorem dirichlet_linearForms_infinite [Nonempty κ] (A : Matrix ι κ ℝ)
    (hA : ∀ y : κ → ℤ, (∀ i, ∃ k : ℤ, ∑ j, A i j * y j = k) → y = 0) :
    {p : (κ → ℤ) × (ι → ℤ) | p.1 ≠ 0 ∧ ∀ i, |∑ j, A i j * p.1 j - p.2 i| ≤
      ‖p.1‖ ^ (-(Fintype.card κ : ℝ) / Fintype.card ι)}.Infinite := by
  -- Without rows, the hypothesis would force every integer vector to vanish.
  have : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    exact one_ne_zero (hA 1 isEmptyElim)
  have he : 0 < (Fintype.card κ : ℝ) / Fintype.card ι :=
    div_pos (Nat.cast_pos.2 Fintype.card_pos) (Nat.cast_pos.2 Fintype.card_pos)
  intro hS
  set S := {p : (κ → ℤ) × (ι → ℤ) | p.1 ≠ 0 ∧ ∀ i, |∑ j, A i j * p.1 j - p.2 i| ≤
    ‖p.1‖ ^ (-(Fintype.card κ : ℝ) / Fintype.card ι)}
  -- Every solution has a nonzero error vector, by the hypothesis on `A`.
  set err : (κ → ℤ) × (ι → ℤ) → ℝ := fun p ↦ ‖fun i ↦ ∑ j, A i j * p.1 j - p.2 i‖
  have herr : ∀ p ∈ S, 0 < err p := by
    rintro p ⟨hp, -⟩
    refine norm_pos_iff.2 fun h0 ↦ hp (hA _ fun i ↦ ⟨p.2 i, ?_⟩)
    simpa [sub_eq_zero] using congrFun h0 i
  -- Take `Q` so large that `Q ^ (-n / m)` is below every such error.
  obtain ⟨Q, hQ, hQS⟩ := ((eventually_gt_atTop 1).and <| (eventually_all_finite hS).2
    fun p hp ↦ (tendsto_rpow_neg_atTop he).eventually (gt_mem_nhds (herr p hp))).exists
  obtain ⟨y, x, hy, hyQ, hx⟩ := A.dirichlet_linearForms hQ
  have hyQ' : ‖y‖ ≤ Q :=
    (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j ↦ by simpa [Int.norm_eq_abs] using hyQ j
  simp only [neg_div] at hx hQS
  have hmem : (y, x) ∈ S := ⟨hy, fun i ↦ (hx i).trans <| by
    simpa only [neg_div] using
      Real.rpow_le_rpow_of_nonpos (norm_pos_iff.2 hy) hyQ' (neg_nonpos.2 he.le)⟩
  refine (hQS _ hmem).not_ge ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_)
  simpa [Real.norm_eq_abs] using hx i

end Matrix

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Simultaneous Dirichlet approximation.** For real numbers `αᵢ`, `i ∈ ι`, and `Q > 1`
there are integers `xᵢ` and `0 < y ≤ Q ^ |ι|` with `|xᵢ - αᵢ y| ≤ Q⁻¹` for every `i`. -/
theorem simultaneous_dirichlet (α : ι → ℝ) {Q : ℝ} (hQ : 1 < Q) :
    ∃ (x : ι → ℤ) (y : ℤ), 0 < y ∧ (y : ℝ) ≤ Q ^ Fintype.card ι ∧
      ∀ i, |x i - α i * y| ≤ Q⁻¹ := by
  have hQ₀ : 0 < Q := zero_lt_one.trans hQ
  obtain ⟨y, x, hy, hyQ, hx⟩ := (Matrix.of fun i (_ : Unit) ↦ α i).exists_int_abs_sum_mul_sub_le
    (P := Q ^ Fintype.card ι) (by positivity) (by positivity) (inv_lt_one_of_one_lt₀ hQ)
    (by simp [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hQ₀.ne')])
  have hy0 : y () ≠ 0 := fun h ↦ hy (funext fun _ ↦ h)
  simp only [Fintype.univ_unit, Finset.sum_singleton, Matrix.of_apply] at hx
  rcases hy0.lt_or_gt with hneg | hpos
  · refine ⟨-x, -y (), neg_pos.2 hneg, ?_, fun i ↦ ?_⟩
    · simpa [abs_of_neg (Int.cast_lt_zero.2 hneg)] using hyQ ()
    · simpa [neg_add_eq_sub] using hx i
  · refine ⟨x, y (), hpos, ?_, fun i ↦ ?_⟩
    · simpa [abs_of_pos (Int.cast_pos.2 hpos)] using hyQ ()
    · simpa [abs_sub_comm] using hx i

/-- **Dirichlet's theorem for one linear form, infinitely many solutions.** Let `αⱼ`, `j ∈ κ`,
be real numbers, `n = |κ| ≥ 1`, such that `∑ⱼ αⱼ yⱼ` is an integer for an integer vector `y`
only when `y = 0`. Then infinitely many pairs `(x, y)` with `y ≠ 0` satisfy
`|∑ⱼ αⱼ yⱼ - x| ≤ ‖y‖ ^ (-n)`, where `‖y‖` is the sup norm. -/
theorem dirichlet_linearForm_infinite [Nonempty κ] (α : κ → ℝ)
    (hα : ∀ y : κ → ℤ, (∃ k : ℤ, ∑ j, α j * y j = k) → y = 0) :
    {p : ℤ × (κ → ℤ) | p.2 ≠ 0 ∧
      |∑ j, α j * p.2 j - p.1| ≤ ‖p.2‖ ^ (-(Fintype.card κ : ℝ))}.Infinite := by
  refine Set.infinite_of_injOn_mapsTo (f := fun p : (κ → ℤ) × (Unit → ℤ) ↦ (p.2 (), p.1))
    (fun p _ q _ h ↦ ?_) (fun p hp ↦ ?_)
    ((Matrix.of fun (_ : Unit) j ↦ α j).dirichlet_linearForms_infinite fun y hy ↦ hα y (hy ()))
  · simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 (funext fun _ ↦ h.1)
  · simpa [Unique.forall_iff] using hp

end TauCeti
