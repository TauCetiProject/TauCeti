/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Scaling.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Diagonal scalings of a nonnegative kernel with zero entries

Let `K : Matrix ι κ ℝ` be a nonnegative kernel, possibly with zero entries, and let `a : ι → ℝ`
and `b : κ → ℝ` be prescribed row and column sums. A diagonal scaling `u i * K i j * v j` of `K`
by strictly positive factors vanishes exactly where `K` does. This file proves the converse
criterion: such a scaling with row sums `a` and column sums `b` exists exactly when some
nonnegative matrix with these row and column sums has the zero pattern of `K`
(`Matrix.exists_sinkhorn_scaling_iff`). For a strictly positive kernel and strictly positive
marginals of equal total mass the product matrix `a i * b j / ∑ k, a k` is such a matrix, which is
the case of the Sinkhorn–Knopp theorem `Matrix.exists_sinkhorn_scaling`. The zero pattern of `K`
can rule a scaling out: for `K = !![1, 1; 0, 1]` and `a = b = 1` the only nonnegative matrix with
these row and column sums vanishing where `K` does is the identity, which vanishes at the entry
`(0, 1)` where `K` does not, so `K` has no such scaling.

The scaled matrix is found as a minimiser of the relative entropy `Matrix.relEntropy · K` among
the nonnegative matrices with the prescribed row and column sums that vanish wherever `K` does.
These form a compact convex set, nonempty as soon as the transport polytope meets the support of
`K` (`Matrix.exists_relEntropy_minOn_support`). On a convex set of nonnegative matrices, a
minimiser of the relative entropy has the largest support (`Matrix.pos_of_isMinOn_relEntropy`),
so a feasible matrix with the zero pattern of `K` forces the minimiser to have that zero pattern
too. The first-order condition on that support then says that `log P - log K` is orthogonal to
every direction with zero row and column sums supported where `K` is positive, and such a matrix
is a function of the row plus a function of the column on that support
(`Matrix.exists_forall_mem_eq_add_iff`). Exponentiating these two functions gives the factors.

## Main results

* `Matrix.exists_forall_mem_eq_add_iff`: on a set `s` of cells, a matrix is `f i + g j` exactly
  when it is orthogonal to every matrix vanishing off `s` with zero row and column sums.
* `Matrix.pos_of_isMinOn_relEntropy`: a minimiser of the relative entropy over a convex set of
  nonnegative matrices is positive wherever some matrix of the set is.
* `Matrix.exists_relEntropy_minOn_support`: the relative entropy against `K` attains a minimum on
  the nonnegative matrices with given row and column sums vanishing where `K` does, as soon as
  there is one such matrix.
* `Matrix.pos_of_relEntropy_minOn_support`: such a minimiser is positive wherever some competitor
  is.
* `Matrix.exists_isDiagonalScaling_of_relEntropy_minOn_support`: if some competitor has the zero
  pattern of `K`, the minimiser is a diagonal scaling of `K` by strictly positive factors.
* `Matrix.exists_sinkhorn_scaling_iff`: **the scaling criterion** for a nonnegative kernel.

## References

* M. V. Menon, *Matrix links, an extremization problem, and the reduction of a non-negative
  matrix to one with prescribed row and column sums*, Canad. J. Math. 20 (1968), 225--232.
* R. A. Brualdi, *Convex sets of non-negative matrices*, Canad. J. Math. 20 (1968), 144--157.
* M. Idel, *A review of matrix scaling and Sinkhorn's normal form for matrices and positive
  maps*, arXiv:1609.06349 (2016), Section 3.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probab. 3 (1975), 146--158, for the support of a relative-entropy minimiser.
-/

public section

open scoped BigOperators

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Matrices orthogonal to the zero-marginal directions on a support -/

/-- On a set `s` of cells, a matrix `H` is the sum `f i + g j` of a function of the row and a
function of the column exactly when `∑ i, ∑ j, D i j * H i j = 0` for every matrix `D` that
vanishes off `s` and has zero row and column sums. -/
theorem exists_forall_mem_eq_add_iff (s : Set (ι × κ)) (H : Matrix ι κ ℝ) :
    (∃ (f : ι → ℝ) (g : κ → ℝ), ∀ i j, (i, j) ∈ s → H i j = f i + g j) ↔
      ∀ D : Matrix ι κ ℝ, (∀ i j, (i, j) ∉ s → D i j = 0) → HasMarginals D 0 0 →
        ∑ i, ∑ j, D i j * H i j = 0 := by
  classical
  constructor
  · rintro ⟨f, g, hfg⟩ D hDs hD
    calc ∑ i, ∑ j, D i j * H i j = ∑ i, ∑ j, D i j * (f i + g j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases h : (i, j) ∈ s
          · rw [hfg i j h]
          · rw [hDs i j h, zero_mul, zero_mul]
      _ = 0 := by simp [hD.sum_sum_mul_add f g]
  · intro hH
    -- The matrices equal to `f i + g j` on `s` and to `0` off `s` form the range of `T`, and `H`
    -- restricted to `s` lies in it because every functional killing that range kills `H`.
    let T : ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] Matrix ι κ ℝ :=
      { toFun := fun fg => of fun i j => if (i, j) ∈ s then fg.1 i + fg.2 j else 0
        map_add' := fun x y => by
          ext i j
          simp only [of_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
          split_ifs <;> ring
        map_smul' := fun c x => by
          ext i j
          simp only [of_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply, Matrix.smul_apply]
          split_ifs <;> ring }
    have hT : ∀ fg i j, T fg i j = if (i, j) ∈ s then fg.1 i + fg.2 j else 0 :=
      fun _ _ _ => of_apply _ _ _
    -- A linear functional on matrices is the pairing with its values on the matrix units.
    have hφ : ∀ (φ : Module.Dual ℝ (Matrix ι κ ℝ)) (M : Matrix ι κ ℝ),
        φ M = ∑ i, ∑ j, M i j * φ (Matrix.single i j 1) := by
      intro φ M
      conv_lhs => rw [matrix_eq_sum_single M]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
    have hmem : of (fun i j => if (i, j) ∈ s then H i j else 0) ∈ LinearMap.range T := by
      refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range T) _).mp
        fun φ hφT => ?_
      rw [Submodule.mem_dualAnnihilator] at hφT
      set D : Matrix ι κ ℝ := of fun i j => if (i, j) ∈ s then φ (Matrix.single i j 1) else 0
        with hD_def
      have hTD : ∀ fg : (ι → ℝ) × (κ → ℝ), ∑ i, ∑ j, D i j * (fg.1 i + fg.2 j) = 0 := by
        intro fg
        rw [← hφT (T fg) (LinearMap.mem_range_self T fg), hφ]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hT, hD_def, of_apply]
        split_ifs <;> ring
      have hD : HasMarginals D 0 0 := by
        refine (hasMarginals_def _ _ _).2 ⟨fun i => ?_, fun j => ?_⟩
        · simpa [Pi.single_apply] using hTD (Pi.single i 1, 0)
        · simpa [Pi.single_apply] using hTD (0, Pi.single j 1)
      have hDs : ∀ i j, (i, j) ∉ s → D i j = 0 := fun i j h => by
        rw [hD_def, of_apply, ite_eq_right_iff.2 fun h' => absurd h' h]
      rw [hφ]
      refine Eq.trans ?_ (hH D hDs hD)
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hD_def, of_apply, of_apply]
      split_ifs <;> ring
    obtain ⟨fg, hfg⟩ := hmem
    refine ⟨fg.1, fg.2, fun i j hij => ?_⟩
    have h := congrFun (congrFun hfg i) j
    rw [hT, of_apply, ite_eq_left_iff.2 fun h' => absurd hij h',
      ite_eq_left_iff.2 fun h' => absurd hij h'] at h
    exact h.symm

/-! ### The minimiser has the largest support -/

/-- A minimiser `P` of the relative entropy against `K` over a convex set `C` of nonnegative
matrices has the largest support in `C`: every entry at which some matrix of `C` is positive is
a positive entry of `P`. There is no hypothesis on `K`. -/
theorem pos_of_isMinOn_relEntropy {K : Matrix ι κ ℝ} {C : Set (Matrix ι κ ℝ)} (hC : Convex ℝ C)
    (hC0 : ∀ Q ∈ C, ∀ i j, 0 ≤ Q i j) {P Q : Matrix ι κ ℝ} (hPC : P ∈ C)
    (hmin : IsMinOn (relEntropy · K) C P) (hQC : Q ∈ C) {i : ι} {j : κ} (hQ : 0 < Q i j) :
    0 < P i j := by
  classical
  refine (hC0 P hPC i j).lt_of_ne fun hP0 => ?_
  -- Moving from `P` towards `Q` by `t` changes `x * log x` at the entry `(i, j)` by
  -- `t * Q i j * log (t * Q i j)`, and at every other entry by at most `t` times the change from
  -- `P` to `Q`, by convexity. For small `t` the logarithm of `t` dominates, and the relative
  -- entropy decreases.
  set q : ℝ := Q i j with hq
  set A : ℝ := ∑ x, ∑ y, (Q x y * Real.log (Q x y) - P x y * Real.log (P x y))
    - ∑ x, ∑ y, (Q x y - P x y) * Real.log (K x y) with hA
  set t : ℝ := Real.exp (-(|A| + 1) / q) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by linarith [abs_nonneg A]) hQ.le)
  have hlogt : q * Real.log t = -(|A| + 1) := by
    rw [ht, Real.log_exp]
    field_simp
  set R : Matrix ι κ ℝ := (1 - t) • P + t • Q with hR
  have hRapply : ∀ x y, R x y = (1 - t) * P x y + t * Q x y := fun x y => by
    simp [hR]
  have hRC : R ∈ C := hC hPC hQC (by linarith) ht0.le (by ring)
  have hcell : ∀ x y, R x y * Real.log (R x y) - P x y * Real.log (P x y) ≤
      t * (Q x y * Real.log (Q x y) - P x y * Real.log (P x y))
        + if x = i ∧ y = j then t * (q * Real.log t) else 0 := by
    intro x y
    split_ifs with hxy
    · obtain ⟨rfl, rfl⟩ := hxy
      rw [hRapply, ← hP0, ← hq, mul_zero, zero_add, Real.log_mul ht0.ne' hQ.ne']
      simp only [zero_mul, sub_zero]
      exact le_of_eq (by ring)
    · have hconv := Real.convexOn_mul_log.2 (Set.mem_Ici.2 (hC0 P hPC x y))
        (Set.mem_Ici.2 (hC0 Q hQC x y)) (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
      simp only [smul_eq_mul] at hconv
      rw [hRapply]
      linarith
  have hdiff : relEntropy R K - relEntropy P K ≤ t * (A + q * Real.log t) := by
    have hsplit : relEntropy R K - relEntropy P K
        = ∑ x, ∑ y, (R x y * Real.log (R x y) - P x y * Real.log (P x y))
          - t * ∑ x, ∑ y, (Q x y - P x y) * Real.log (K x y) := by
      simp only [relEntropy_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [hRapply]
      ring
    have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hcell x y
    have hδ : ∀ c : ℝ, ∑ x, ∑ y, (if x = i ∧ y = j then c else 0) = c := fun c => by
      rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
      simp
    have hite : ∑ x, ∑ y, (t * (Q x y * Real.log (Q x y) - P x y * Real.log (P x y))
        + if x = i ∧ y = j then t * (q * Real.log t) else 0)
        = t * ∑ x, ∑ y, (Q x y * Real.log (Q x y) - P x y * Real.log (P x y))
          + t * (q * Real.log t) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, hδ]
    rw [hsplit, hA]
    linarith
  have hneg : t * (A + q * Real.log t) < 0 :=
    mul_neg_of_pos_of_neg ht0 (by rw [hlogt]; linarith [le_abs_self A])
  have hle : relEntropy P K ≤ relEntropy R K := isMinOn_iff.mp hmin R hRC
  linarith

/-! ### Minimisers supported where the kernel is -/

/-- The relative entropy against `K` attains a minimum on the nonnegative matrices with row sums
`a` and column sums `b` that vanish wherever `K` does, as soon as there is one such matrix. -/
theorem exists_relEntropy_minOn_support (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (hfeas : ∃ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) ∧ HasMarginals Q a b ∧
      ∀ i j, K i j = 0 → Q i j = 0) :
    ∃ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b ∧
      (∀ i j, K i j = 0 → P i j = 0) ∧
      ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
        (∀ i j, K i j = 0 → Q i j = 0) → relEntropy P K ≤ relEntropy Q K := by
  have hclosed : IsClosed {P : Matrix ι κ ℝ | ∀ i j, K i j = 0 → P i j = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) continuous_const
  obtain ⟨Q, hQ0, hQa, hQK⟩ := hfeas
  obtain ⟨P, ⟨⟨hP0, hPa⟩, hPK⟩, hmin⟩ :=
    ((isCompact_setOf_nonneg_hasMarginals a b).inter_right hclosed).exists_isMinOn
      ⟨Q, ⟨hQ0, hQa⟩, hQK⟩ (continuous_relEntropy K).continuousOn
  exact ⟨P, hP0, hPa, hPK, fun Q hQ0 hQa hQK => isMinOn_iff.mp hmin Q ⟨⟨hQ0, hQa⟩, hQK⟩⟩

/-- A minimiser of the relative entropy against `K` among the nonnegative matrices with row sums
`a` and column sums `b` that vanish wherever `K` does is positive at every entry where some such
matrix is positive. -/
theorem pos_of_relEntropy_minOn_support {K : Matrix ι κ ℝ} {a : ι → ℝ} {b : κ → ℝ}
    {P Q : Matrix ι κ ℝ} (hP : ∀ i j, 0 ≤ P i j) (hPa : HasMarginals P a b)
    (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      (∀ i j, K i j = 0 → Q i j = 0) → relEntropy P K ≤ relEntropy Q K)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQa : HasMarginals Q a b) (hQK : ∀ i j, K i j = 0 → Q i j = 0)
    {i : ι} {j : κ} (hQij : 0 < Q i j) : 0 < P i j := by
  have hC : Convex ℝ {M : Matrix ι κ ℝ |
      (∀ i j, 0 ≤ M i j) ∧ HasMarginals M a b ∧ ∀ i j, K i j = 0 → M i j = 0} := by
    rintro M ⟨hM0, hMa, hMK⟩ N ⟨hN0, hNa, hNK⟩ s t hs ht hst
    refine ⟨fun i j => ?_, ?_, fun i j h => ?_⟩
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg hs (hM0 i j)) (mul_nonneg ht (hN0 i j))
    · simpa only [Convex.combo_self hst] using (hMa.smul s).add (hNa.smul t)
    · simp [hMK i j h, hNK i j h]
  exact pos_of_isMinOn_relEntropy hC (fun M hM => hM.1) ⟨hP, hPa, hPK⟩
    (isMinOn_iff.mpr fun M hM => hmin M hM.1 hM.2.1 hM.2.2) ⟨hQ, hQa, hQK⟩ hQij

/-- If some nonnegative matrix with row sums `a` and column sums `b` has the zero pattern of the
nonnegative kernel `K`, then every minimiser of the relative entropy against `K` among the
nonnegative matrices with these row and column sums that vanish wherever `K` does is a diagonal
scaling of `K` by strictly positive row and column factors. -/
theorem exists_isDiagonalScaling_of_relEntropy_minOn_support {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 ≤ K i j) {a : ι → ℝ} {b : κ → ℝ} {P Q : Matrix ι κ ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hPa : HasMarginals P a b) (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      (∀ i j, K i j = 0 → Q i j = 0) → relEntropy P K ≤ relEntropy Q K)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQa : HasMarginals Q a b) (hQK : ∀ i j, Q i j = 0 ↔ K i j = 0) :
    ∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧ IsDiagonalScaling P K u v := by
  -- The minimiser has the zero pattern of `Q`, which is that of `K`.
  have hPpos : ∀ i j, K i j ≠ 0 → 0 < P i j := fun i j h =>
    pos_of_relEntropy_minOn_support hP hPa hPK hmin hQ hQa (fun i j h => (hQK i j).2 h)
      ((hQ i j).lt_of_ne fun h' => h ((hQK i j).1 h'.symm))
  have hPK' : ∀ i j, P i j = 0 ↔ K i j = 0 := fun i j =>
    ⟨fun h => by_contra fun hK0 => (hPpos i j hK0).ne' h, hPK i j⟩
  -- On the support of `K`, the first-order condition makes `log P - log K` a function of the row
  -- plus a function of the column.
  obtain ⟨f, g, hfg⟩ := (exists_forall_mem_eq_add_iff {x : ι × κ | K x.1 x.2 ≠ 0}
    fun i j => Real.log (P i j) - Real.log (K i j)).2 fun D hDs hD =>
      sum_sum_mul_log_sub_log_eq_zero_of_relEntropy_minOn_support K hP hPa
        (fun Q hQ hQa hQP => hmin Q hQ hQa fun i j h => hQP i j ((hPK' i j).2 h)) hD
        fun i j h => hDs i j fun hs => (Set.mem_ofPred.mp hs) ((hPK' i j).1 h)
  refine ⟨fun i => Real.exp (f i), fun j => Real.exp (g j), fun _ => Real.exp_pos _,
    fun _ => Real.exp_pos _, (isDiagonalScaling_def _ _ _ _).2 fun i j => ?_⟩
  by_cases hKij : K i j = 0
  · simp [hPK i j hKij, hKij]
  have hK' : 0 < K i j := (hK i j).lt_of_ne' hKij
  calc P i j = Real.exp (Real.log (P i j) - Real.log (K i j)) * K i j := by
        rw [Real.exp_sub, Real.exp_log (hPpos i j hKij), Real.exp_log hK',
          div_mul_cancel₀ _ hK'.ne']
    _ = Real.exp (f i) * K i j * Real.exp (g j) := by
        rw [hfg i j hKij, Real.exp_add]
        ring

/-! ### The scaling criterion -/

/-- **The scaling criterion** for a nonnegative kernel: a nonnegative matrix `K` admits strictly
positive row factors `u` and column factors `v` such that the diagonal scaling `u i * K i j * v j`
has row sums `a` and column sums `b` exactly when some nonnegative matrix with row sums `a` and
column sums `b` vanishes exactly where `K` does.

There is no hypothesis on `a` and `b`: their nonnegativity and equal total mass follow from either
side. -/
theorem exists_sinkhorn_scaling_iff {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 ≤ K i j) {a : ι → ℝ}
    {b : κ → ℝ} :
    (∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      (∀ i, ∑ j, u i * K i j * v j = a i) ∧ ∀ j, ∑ i, u i * K i j * v j = b j) ↔
      ∃ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) ∧ (∀ i j, Q i j = 0 ↔ K i j = 0) ∧
        HasMarginals Q a b := by
  constructor
  · rintro ⟨u, v, hu, hv, ha, hb⟩
    refine ⟨fun i j => u i * K i j * v j,
      fun i j => mul_nonneg (mul_nonneg (hu i).le (hK i j)) (hv j).le, fun i j => ?_,
      (hasMarginals_def _ _ _).2 ⟨ha, hb⟩⟩
    simp [(hu i).ne', (hv j).ne']
  · rintro ⟨Q, hQ, hQK, hQa⟩
    obtain ⟨P, hP, hPa, hPK, hmin⟩ :=
      exists_relEntropy_minOn_support K a b ⟨Q, hQ, hQa, fun i j h => (hQK i j).2 h⟩
    obtain ⟨u, v, hu, hv, hPuv⟩ :=
      exists_isDiagonalScaling_of_relEntropy_minOn_support hK hP hPa hPK hmin hQ hQa hQK
    rw [hasMarginals_def] at hPa
    rw [isDiagonalScaling_def] at hPuv
    refine ⟨u, v, hu, hv, fun i => ?_, fun j => ?_⟩
    · rw [← hPa.1 i]
      exact Finset.sum_congr rfl fun j _ => (hPuv i j).symm
    · rw [← hPa.2 j]
      exact Finset.sum_congr rfl fun i _ => (hPuv i j).symm

end Matrix
