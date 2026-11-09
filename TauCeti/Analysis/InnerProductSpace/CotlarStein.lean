/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# The Cotlar–Stein almost-orthogonality lemma

Let `T i : E →L[𝕜] F` be bounded operators between Hilbert spaces. If
`∑ j, √‖(T i)† ∘L T j‖ ≤ A` and `∑ j, √‖T i ∘L (T j)†‖ ≤ A` for every `i`, then the operator
norm of `∑ i, T i` is at most `A`, although the triangle inequality only gives the bound
`∑ i, ‖T i‖`, which may be as large as `A` times the number of summands.
For infinitely many operators the series `∑ i, T i x` then converges for every `x`, and its
sum is a bounded operator of norm at most `A`.

This is the almost-orthogonality principle behind the `L²` boundedness of
pseudodifferential operators with symbols of order zero (Calderón–Vaillancourt): such an
operator is decomposed dyadically, and the pieces are almost orthogonal in the above sense.

## Main results

* `TauCeti.norm_sum_le_of_almost_orthogonal`: the finite Cotlar–Stein lemma.
* `TauCeti.exists_hasSum_apply_of_almost_orthogonal`: the Cotlar–Stein lemma for an arbitrary
  family; the series converges in the strong operator topology to an operator of norm at
  most `A`.

## Implementation notes

For a finite family with sum `S`, the C⋆-identity gives `‖S‖ ^ (2 * 2 ^ k) = ‖(S† S) ^ 2 ^ k‖`.
Expanding `(S† S) ^ n = (∑ i j, (T i)† T j) ^ n` gives a sum of words
`(T i₁)† T j₁ ⋯ (T iₙ)† T jₙ`. The norm of each word is bounded both by the product of the
norms of its factors `(T iₘ)† T jₘ` and by `‖T i₁‖ ‖T j₁ (T i₂)†‖ ⋯ ‖T jₙ‖`, hence by the
geometric mean of these two bounds. Summing the geometric means one index at a time bounds
`‖(S† S) ^ n‖` by `card ι * A ^ (2 * n)`, and letting `n → ∞` removes the factor `card ι`.

For an infinite family, the vectors on which the series converges form a closed subspace, by
the uniform bound on the finite partial sums
(`ContinuousLinearMap.isClosed_setOf_summable_apply`). It contains the range of every `(T j)†`,
on which the series converges absolutely, so its orthogonal complement is killed by every `T j`,
hence is zero.

## References

* M. Cotlar, *A combinatorial inequality and its applications to L²-spaces*,
  Rev. Mat. Cuyana 1 (1955), 41–55.
* A. W. Knapp and E. M. Stein, *Intertwining operators for semisimple groups*,
  Ann. of Math. 93 (1971), 489–578.
* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VII, §2.
-/

public section

open ContinuousLinearMap Filter Finset
open scoped InnerProduct InnerProductSpace Topology

namespace TauCeti

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

variable (T : ι → E →L[𝕜] F)

/-- The word `(T i₁)† T j₁ ⋯ (T iₙ)† T jₙ` attached to `w = ((i₁, j₁), …, (iₙ, jₙ))`. -/
private noncomputable def wordOp : (n : ℕ) → (Fin n → ι × ι) → E →L[𝕜] E
  | 0, _ => .id 𝕜 E
  | n + 1, w => (T (w 0).1)† ∘L T (w 0).2 ∘L wordOp n (Fin.tail w)

/-- The bound `‖T k (T i₁)†‖ ‖T j₁ (T i₂)†‖ ⋯ ‖T jₙ‖` for `T k` followed by a word. -/
private noncomputable def chainBound : (n : ℕ) → ι → (Fin n → ι × ι) → ℝ
  | 0, k, _ => ‖T k‖
  | n + 1, k, w => ‖T k ∘L (T (w 0).1)†‖ * chainBound n (w 0).2 (Fin.tail w)

private lemma sum_pow_eq_sum_wordOp [Fintype ι] :
    ∀ n : ℕ, (∑ p : ι × ι, (T p.1)† ∘L T p.2) ^ n = ∑ w : Fin n → ι × ι, wordOp T n w
  | 0 => by simp [wordOp, one_def]
  | n + 1 => by
    rw [pow_succ', sum_pow_eq_sum_wordOp n, sum_mul_sum]
    conv_rhs => rw [← (Fin.consEquiv fun _ ↦ ι × ι).sum_comp, Fintype.sum_prod_type]
    simp [wordOp, ContinuousLinearMap.mul_def, comp_assoc, Fin.consEquiv_apply]

private lemma norm_comp_wordOp_le :
    ∀ (n : ℕ) (k : ι) (w : Fin n → ι × ι), ‖T k ∘L wordOp T n w‖ ≤ chainBound T n k w
  | 0, k, w => by simp [wordOp, chainBound]
  | n + 1, k, w => by
    rw [wordOp, chainBound, ← comp_assoc]
    exact (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_comp_wordOp_le n _ _) (norm_nonneg _))

private lemma norm_wordOp_le_prod :
    ∀ (n : ℕ) (w : Fin n → ι × ι), ‖wordOp T n w‖ ≤ ∏ m, ‖(T (w m).1)† ∘L T (w m).2‖
  | 0, w => by simpa [wordOp] using norm_id_le
  | n + 1, w => by
    rw [wordOp, Fin.prod_univ_succ, ← comp_assoc]
    exact (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_wordOp_le_prod n _) (norm_nonneg _))

private lemma norm_wordOp_succ_le (n : ℕ) (w : Fin (n + 1) → ι × ι) :
    ‖wordOp T (n + 1) w‖ ≤ ‖T (w 0).1‖ * chainBound T n (w 0).2 (Fin.tail w) := by
  rw [wordOp]
  refine (opNorm_comp_le _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (norm_comp_wordOp_le T n _ _) (norm_nonneg _)

/-- Each word is bounded by the geometric mean of its two bounds. -/
private lemma norm_wordOp_le_sqrt_mul_sqrt (n : ℕ) (w : Fin (n + 1) → ι × ι) :
    ‖wordOp T (n + 1) w‖ ≤ √(∏ m, ‖(T (w m).1)† ∘L T (w m).2‖) *
      √(‖T (w 0).1‖ * chainBound T n (w 0).2 (Fin.tail w)) := by
  have hX := norm_wordOp_le_prod T (n + 1) w
  have hY := norm_wordOp_succ_le T n w
  have h0 := norm_nonneg (wordOp T (n + 1) w)
  rw [← Real.sqrt_mul (h0.trans hX), ← Real.sqrt_mul_self h0]
  exact Real.sqrt_le_sqrt (mul_le_mul hX hY h0 (h0.trans hX))

variable [Fintype ι] {A : ℝ}

private lemma norm_le_of_sum_le (h₁ : ∀ i, ∑ j, √‖(T i)† ∘L T j‖ ≤ A) (i : ι) : ‖T i‖ ≤ A := by
  calc ‖T i‖ = √‖(T i)† ∘L T i‖ := by
        rw [norm_adjoint_comp_self, Real.sqrt_mul_self (norm_nonneg _)]
    _ ≤ ∑ j, √‖(T i)† ∘L T j‖ :=
        single_le_sum (f := fun j ↦ √‖(T i)† ∘L T j‖) (fun _ _ ↦ Real.sqrt_nonneg _)
          (mem_univ i)
    _ ≤ A := h₁ i

/-- One step of the summation of the geometric-mean bounds: splitting off the first pair of
indices of the words of length `n + 1` that follow an operator with norms `f i`. -/
private lemma sum_sqrt_mul_sqrt_succ_le {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h₁ : ∀ i, ∑ j, √‖(T i)† ∘L T j‖ ≤ A)
    (ih : ∀ k, ∑ w : Fin n → ι × ι,
      √(∏ m, ‖(T (w m).1)† ∘L T (w m).2‖) * √(chainBound T n k w) ≤ C)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ w : Fin (n + 1) → ι × ι, √(∏ m, ‖(T (w m).1)† ∘L T (w m).2‖) *
      √(f (w 0).1 * chainBound T n (w 0).2 (Fin.tail w)) ≤ C * ∑ j, √(f j) * A := by
  calc ∑ w : Fin (n + 1) → ι × ι, √(∏ m, ‖(T (w m).1)† ∘L T (w m).2‖) *
        √(f (w 0).1 * chainBound T n (w 0).2 (Fin.tail w))
      = ∑ p : ι × ι, √(f p.1) * √‖(T p.1)† ∘L T p.2‖ *
          ∑ w : Fin n → ι × ι,
            √(∏ m, ‖(T (w m).1)† ∘L T (w m).2‖) * √(chainBound T n p.2 w) := by
        rw [← (Fin.consEquiv fun _ ↦ ι × ι).sum_comp, Fintype.sum_prod_type]
        refine sum_congr rfl fun p _ ↦ ?_
        rw [mul_sum]
        refine sum_congr rfl fun w _ ↦ ?_
        simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
          Fin.tail_cons]
        rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (hf _)]
        ring
    _ ≤ ∑ p : ι × ι, √(f p.1) * √‖(T p.1)† ∘L T p.2‖ * C :=
        sum_le_sum fun p _ ↦ mul_le_mul_of_nonneg_left (ih p.2) (by positivity)
    _ = C * ∑ j, √(f j) * ∑ l, √‖(T j)† ∘L T l‖ := by
        rw [Fintype.sum_prod_type, mul_sum]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun l _ ↦ ?_
        ring
    _ ≤ C * ∑ j, √(f j) * A :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (h₁ j) (Real.sqrt_nonneg _)) hC

/-- Summing the geometric-mean bounds of the words that follow `T k`, one index at a time. -/
private lemma sum_sqrt_mul_sqrt_chainBound_le (hA : 0 ≤ A)
    (h₁ : ∀ i, ∑ j, √‖(T i)† ∘L T j‖ ≤ A) (h₂ : ∀ i, ∑ j, √‖T i ∘L (T j)†‖ ≤ A) :
    ∀ (n : ℕ) (k : ι), ∑ w : Fin n → ι × ι,
      √(∏ m, ‖(T (w m).1)† ∘L T (w m).2‖) * √(chainBound T n k w) ≤ √A * (A ^ 2) ^ n
  | 0, k => by
    simpa [chainBound] using Real.sqrt_le_sqrt (norm_le_of_sum_le T h₁ k)
  | n + 1, k => by
    simp only [chainBound]
    calc _ ≤ √A * (A ^ 2) ^ n * ∑ j, √‖T k ∘L (T j)†‖ * A :=
          sum_sqrt_mul_sqrt_succ_le T (by positivity) h₁
            (sum_sqrt_mul_sqrt_chainBound_le hA h₁ h₂ n) (fun i ↦ ‖T k ∘L (T i)†‖)
            fun _ ↦ norm_nonneg _
      _ ≤ √A * (A ^ 2) ^ n * (A * A) := by
          rw [← sum_mul]
          gcongr
          exact h₂ k
      _ = √A * (A ^ 2) ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- The key estimate: the sum of the norms of the words of length `n + 1` is at most
`card ι * A ^ (2 * (n + 1))`. -/
private lemma sum_norm_wordOp_le (hA : 0 ≤ A)
    (h₁ : ∀ i, ∑ j, √‖(T i)† ∘L T j‖ ≤ A) (h₂ : ∀ i, ∑ j, √‖T i ∘L (T j)†‖ ≤ A) (n : ℕ) :
    ∑ w : Fin (n + 1) → ι × ι, ‖wordOp T (n + 1) w‖ ≤ Fintype.card ι * (A ^ 2) ^ (n + 1) := by
  calc ∑ w : Fin (n + 1) → ι × ι, ‖wordOp T (n + 1) w‖
      ≤ ∑ w : Fin (n + 1) → ι × ι, √(∏ m, ‖(T (w m).1)† ∘L T (w m).2‖) *
          √(‖T (w 0).1‖ * chainBound T n (w 0).2 (Fin.tail w)) :=
        sum_le_sum fun w _ ↦ norm_wordOp_le_sqrt_mul_sqrt T n w
    _ ≤ √A * (A ^ 2) ^ n * ∑ j, √‖T j‖ * A :=
        sum_sqrt_mul_sqrt_succ_le T (by positivity) h₁
          (sum_sqrt_mul_sqrt_chainBound_le T hA h₁ h₂ n) (fun i ↦ ‖T i‖) fun _ ↦ norm_nonneg _
    _ ≤ √A * (A ^ 2) ^ n * ∑ _j : ι, √A * A :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (norm_le_of_sum_le T h₁ j)) hA) (by positivity)
    _ = Fintype.card ι * (A ^ 2) ^ (n + 1) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        have : √A * √A = A := Real.mul_self_sqrt hA
        linear_combination (Fintype.card ι * (A ^ 2) ^ n * A) * this

/-- The finite Cotlar–Stein lemma, for a family indexed by a finite type. -/
private lemma norm_sum_le_of_almost_orthogonal_fintype (hA : 0 ≤ A)
    (h₁ : ∀ i, ∑ j, √‖(T i)† ∘L T j‖ ≤ A) (h₂ : ∀ i, ∑ j, √‖T i ∘L (T j)†‖ ≤ A) :
    ‖∑ i, T i‖ ≤ A := by
  set S := ∑ i, T i
  have hU : S† ∘L S = ∑ p : ι × ι, (T p.1)† ∘L T p.2 := by
    simp only [S, map_sum, comp_finsetSum, finsetSum_comp, Fintype.sum_prod_type]
    exact sum_comm
  have hsa : IsSelfAdjoint (S† ∘L S) := by
    rw [isSelfAdjoint_iff', adjoint_comp, adjoint_adjoint]
  have key : ∀ k : ℕ, (‖S‖ ^ 2) ^ 2 ^ k ≤ Fintype.card ι * (A ^ 2) ^ 2 ^ k := by
    intro k
    obtain ⟨n, hn⟩ : ∃ n, 2 ^ k = n + 1 := Nat.exists_eq_add_one.mpr (by positivity)
    calc (‖S‖ ^ 2) ^ 2 ^ k = ‖(S† ∘L S) ^ 2 ^ k‖ := by
          rw [hsa.norm_pow_two_pow, norm_adjoint_comp_self, sq]
      _ ≤ Fintype.card ι * (A ^ 2) ^ 2 ^ k := by
          rw [hU, sum_pow_eq_sum_wordOp, hn]
          exact (norm_sum_le _ _).trans (sum_norm_wordOp_le T hA h₁ h₂ n)
  -- If `A < ‖S‖`, then `1 ≤ card ι * (A / ‖S‖) ^ (2 * 2 ^ k)` for all `k`, which is absurd.
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hA two_ne_zero).mp (le_of_not_gt fun hlt ↦ ?_)
  have hS : 0 < ‖S‖ ^ 2 := (pow_nonneg hA 2).trans_lt hlt
  have hr0 : 0 ≤ A ^ 2 / ‖S‖ ^ 2 := by positivity
  have hr1 : A ^ 2 / ‖S‖ ^ 2 < 1 := (div_lt_one hS).mpr hlt
  have hlim : Tendsto (fun k : ℕ ↦ Fintype.card ι * (A ^ 2 / ‖S‖ ^ 2) ^ 2 ^ k) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).const_mul (Fintype.card ι : ℝ)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists
  have hSk : 0 < (‖S‖ ^ 2) ^ 2 ^ k := pow_pos hS _
  have : (‖S‖ ^ 2) ^ 2 ^ k ≤
      Fintype.card ι * (A ^ 2 / ‖S‖ ^ 2) ^ 2 ^ k * (‖S‖ ^ 2) ^ 2 ^ k := by
    rw [div_pow, mul_assoc, div_mul_cancel₀ _ hSk.ne']
    exact key k
  nlinarith

omit [Fintype ι]

/-- **The Cotlar–Stein lemma**, finite form. If the operators `T i`, `i ∈ s`, between Hilbert
spaces are almost orthogonal in the sense that `∑ j ∈ s, √‖(T i)† ∘L T j‖ ≤ A` and
`∑ j ∈ s, √‖T i ∘L (T j)†‖ ≤ A` for every `i ∈ s`, then `‖∑ i ∈ s, T i‖ ≤ A`. -/
theorem norm_sum_le_of_almost_orthogonal (s : Finset ι) (hA : 0 ≤ A)
    (h₁ : ∀ i ∈ s, ∑ j ∈ s, √‖(T i)† ∘L T j‖ ≤ A)
    (h₂ : ∀ i ∈ s, ∑ j ∈ s, √‖T i ∘L (T j)†‖ ≤ A) :
    ‖∑ i ∈ s, T i‖ ≤ A := by
  rw [← sum_coe_sort s]
  refine norm_sum_le_of_almost_orthogonal_fintype (fun i : s ↦ T i) hA (fun i ↦ ?_) fun i ↦ ?_
  · simpa only [sum_coe_sort s (fun j ↦ √‖(T i)† ∘L T j‖)] using h₁ i i.2
  · simpa only [sum_coe_sort s (fun j ↦ √‖T i ∘L (T j)†‖)] using h₂ i i.2

/-- On the range of `(T j)†`, the series `∑ i, T i x` converges absolutely: the norm of
`T i ∘L (T j)†` is at most `A * √‖T j ∘L (T i)†‖` when every `‖T i‖ ≤ A`. -/
private lemma summable_apply_adjoint_apply (hA : 0 ≤ A) (hnorm : ∀ i, ‖T i‖ ≤ A) {j : ι}
    (h₂ : ∀ s : Finset ι, ∑ i ∈ s, √‖T j ∘L (T i)†‖ ≤ A) (y : F) :
    Summable fun i ↦ T i (((T j)†) y) := by
  have hsum : Summable fun i ↦ √‖T j ∘L (T i)†‖ :=
    summable_of_sum_le (fun _ ↦ Real.sqrt_nonneg _) h₂
  refine Summable.of_norm_bounded ((hsum.mul_left A).mul_right ‖y‖) fun i ↦ ?_
  have hsym : ‖T i ∘L (T j)†‖ = ‖T j ∘L (T i)†‖ := by
    rw [← LinearIsometryEquiv.norm_map adjoint (T j ∘L (T i)†), adjoint_comp, adjoint_adjoint]
  have hsqrt : √‖T j ∘L (T i)†‖ ≤ A := by
    rw [Real.sqrt_le_left hA]
    calc ‖T j ∘L (T i)†‖ ≤ ‖T j‖ * ‖(T i)†‖ := opNorm_comp_le _ _
      _ ≤ A * A := by
          rw [LinearIsometryEquiv.norm_map]
          exact mul_le_mul (hnorm j) (hnorm i) (norm_nonneg _) hA
      _ = A ^ 2 := (sq A).symm
  calc ‖T i (((T j)†) y)‖ ≤ ‖T i ∘L (T j)†‖ * ‖y‖ := le_opNorm (T i ∘L (T j)†) y
    _ ≤ A * √‖T j ∘L (T i)†‖ * ‖y‖ := by
        gcongr
        calc ‖T i ∘L (T j)†‖ = √‖T j ∘L (T i)†‖ * √‖T j ∘L (T i)†‖ := by
              rw [hsym, Real.mul_self_sqrt (norm_nonneg _)]
          _ ≤ A * √‖T j ∘L (T i)†‖ := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)

/-- **The Cotlar–Stein lemma**. Let `T i` be operators between Hilbert spaces which are almost
orthogonal in the sense that `∑ j, √‖(T i)† ∘L T j‖ ≤ A` and `∑ j, √‖T i ∘L (T j)†‖ ≤ A` for
every `i`, the sums over `j` being taken over arbitrary finite sets. Then for every `x` the
series `∑ i, T i x` converges unconditionally, and its sum is a bounded operator of norm at
most `A`. -/
theorem exists_hasSum_apply_of_almost_orthogonal (hA : 0 ≤ A)
    (h₁ : ∀ i (s : Finset ι), ∑ j ∈ s, √‖(T i)† ∘L T j‖ ≤ A)
    (h₂ : ∀ i (s : Finset ι), ∑ j ∈ s, √‖T i ∘L (T j)†‖ ≤ A) :
    ∃ S : E →L[𝕜] F, ‖S‖ ≤ A ∧ ∀ x, HasSum (fun i ↦ T i x) (S x) := by
  have hfin (s : Finset ι) : ‖∑ i ∈ s, T i‖ ≤ A :=
    norm_sum_le_of_almost_orthogonal T s hA (fun i _ ↦ h₁ i s) fun i _ ↦ h₂ i s
  have hnorm (i : ι) : ‖T i‖ ≤ A := by simpa using hfin {i}
  -- The vectors on which the series converges form a closed subspace `D`, which contains the
  -- range of every adjoint `(T j)†`.
  let D : Submodule 𝕜 E :=
    { carrier := {x | Summable fun i ↦ T i x}
      add_mem' := fun {x y} hx hy ↦ by simpa using hx.add hy
      zero_mem' := by simp
      smul_mem' := fun c x hx ↦ by simpa using hx.const_smul c }
  have hmemD (x : E) : x ∈ D ↔ Summable fun i ↦ T i x := Iff.rfl
  have hclosed : IsClosed (D : Set E) := isClosed_setOf_summable_apply hfin
  have hrange (j : ι) (y : F) : ((T j)†) y ∈ D :=
    summable_apply_adjoint_apply T hA hnorm (h₂ j) y
  -- Every vector orthogonal to `D` is killed by every `T j`, so lies in `D`, so is zero.
  have hD : D = ⊤ := by
    have horth : Dᗮ = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
      have hT (j : ι) : T j x = 0 := by
        have := Submodule.inner_right_of_mem_orthogonal (hrange j (T j x)) hx
        rwa [adjoint_inner_left, inner_self_eq_zero] at this
      have hxD : x ∈ D := by simp [hmemD, hT]
      exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hxD hx)
    rw [← hclosed.submodule_topologicalClosure_eq]
    exact Submodule.topologicalClosure_eq_top_iff.mpr horth
  have hsum (x : E) : Summable fun i ↦ T i x := (hmemD x).mp (hD ▸ Submodule.mem_top)
  let L : E →ₗ[𝕜] F :=
    { toFun := fun x ↦ ∑' i, T i x
      map_add' := fun x y ↦ by simpa using (hsum x).tsum_add (hsum y)
      map_smul' := fun c x ↦ by simpa using (hsum x).tsum_const_smul c }
  have hbound (x : E) : ‖L x‖ ≤ A * ‖x‖ := by
    refine le_of_tendsto' (hsum x).hasSum.norm fun s ↦ ?_
    calc ‖∑ i ∈ s, T i x‖ = ‖(∑ i ∈ s, T i) x‖ := by rw [sum_apply]
      _ ≤ ‖∑ i ∈ s, T i‖ * ‖x‖ := le_opNorm _ _
      _ ≤ A * ‖x‖ := by gcongr; exact hfin s
  exact ⟨L.mkContinuous A hbound, LinearMap.mkContinuous_norm_le _ hA _,
    fun x ↦ (hsum x).hasSum⟩

end TauCeti

end
