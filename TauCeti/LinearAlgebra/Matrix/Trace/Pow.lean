/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Logic.Equiv.Fin.Rotate
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.Cycle.Enumeration

/-!
# Entries and traces of matrix powers as sums over walks

For a square matrix `A` over a commutative semiring, the `(i, j)` entry of `A ^ (k + 1)` is the
sum, over all walks `i = v₀ → v₁ → ⋯ → vₖ → vₖ₊₁ = j` of `k + 1` steps, of the products
`A v₀ v₁ * A v₁ v₂ * ⋯ * A vₖ vₖ₊₁` of the entries along the walk. Taking the trace closes the
walks up: for `k ≠ 0`,

`trace (A ^ k) = ∑ w : Fin k → ι, ∏ t, A (w t) (w (t + 1))`,

where the indices of the closed walk `w` are read cyclically through `finRotate k`.

This is the trace-word expansion on which the moment method for random matrices rests: the
expected moments of a random matrix are expanded into expectations of products of entries
indexed by closed walks, which are then analysed combinatorially.

## Main results

* `Matrix.pow_succ_apply_eq_sum_prod`: the entries of `A ^ (k + 1)` as sums over walks.
* `Matrix.trace_pow_eq_sum_prod`: the trace of `A ^ k`, `k ≠ 0`, as a sum over closed walks.
* `Matrix.trace_mul_pow_eq_sum_prod`: the analogous expansion for a rectangular product.
* `Matrix.trace_mul_conjTranspose_pow_eq_sum_prod`: the trace of `(X * Xᴴ) ^ k` for a rectangular
  matrix `X`, `k ≠ 0`, as a sum over closed walks alternating between row and column indices.
* `Matrix.list_ofFn_prod_apply`, `Matrix.trace_list_ofFn_prod`: entries and trace of a product of
  indexed matrices along `List.ofFn` as sums over walks and closed cyclic walks.
* `Matrix.sum_prod_apply_perm_eq_prod_trace_list_ofFn_orbit`: splits the cyclic coordinate sum of
  matrices over the orbits of a permutation into a product, over the orbits, of traces of the
  ordered matrix products along each orbit.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3.
-/

public section

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- The `(i, j)` entry of `A ^ (k + 1)` is the sum, over the interior vertices `w` of the walks
of `k + 1` steps from `i` to `j`, of the product of the entries of `A` along the walk
`i, w 0, …, w (k - 1), j`. -/
theorem pow_succ_apply_eq_sum_prod (A : Matrix ι ι R) (k : ℕ) (i j : ι) :
    (A ^ (k + 1)) i j = ∑ w : Fin k → ι,
      ∏ t : Fin (k + 1),
        A ((Fin.cons i w : Fin (k + 1) → ι) t) ((Fin.snoc w j : Fin (k + 1) → ι) t) := by
  induction k generalizing i with
  | zero => simp [Fin.snoc]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, ← (Fin.consEquiv fun _ ↦ ι).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Fin.consEquiv_apply, ← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ (n := k + 1)]
    simp

/-- **Trace-word expansion.** For `k ≠ 0`, the trace of `A ^ k` is the sum, over all closed walks
`w : Fin k → ι` of length `k`, of the product of the entries of `A` along the steps
`w t → w (t + 1)`, the indices being read cyclically. For `k = 0` the left side is the size of `ι`
while the right side is `1`. -/
theorem trace_pow_eq_sum_prod (A : Matrix ι ι R) {k : ℕ} (hk : k ≠ 0) :
    (A ^ k).trace = ∑ w : Fin k → ι, ∏ t, A (w t) (w (finRotate k t)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp_rw [trace, diag_apply, pow_succ_apply_eq_sum_prod, Fin.snoc_eq_cons_rotate]
  rw [← (Fin.consEquiv fun _ ↦ ι).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv_apply]

/-- **Trace-word expansion of a rectangular product.** For `k ≠ 0`, the trace of
`(A * B) ^ k` is the sum over closed walks alternating between the row and column indices
of `A`, with factors from `A` on the outward steps and from `B` on the return steps. -/
theorem trace_mul_pow_eq_sum_prod {κ : Type*} [Fintype κ]
    (A : Matrix ι κ R) (B : Matrix κ ι R) {k : ℕ} (hk : k ≠ 0) :
    ((A * B) ^ k).trace = ∑ u : Fin k → ι, ∑ v : Fin k → κ,
      ∏ t, A (u t) (v t) * B (v t) (u (finRotate k t)) := by
  rw [trace_pow_eq_sum_prod _ hk]
  simp only [Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **Trace-word expansion of `X * Xᴴ`.** For a rectangular matrix `X` and `k ≠ 0`, the trace of
`(X * Xᴴ) ^ k` is the sum, over the closed walks `u 0, v 0, u 1, v 1, …, v (k - 1), u 0`
alternating between row indices `u : Fin k → ι` and column indices `v : Fin k → κ`, of the
products of the entries `X (u t) (v t)` and `star (X (u (t + 1)) (v t))` read along the walk,
the row indices being read cyclically. -/
theorem trace_mul_conjTranspose_pow_eq_sum_prod [Star R] {κ : Type*} [Fintype κ]
    (X : Matrix ι κ R) {k : ℕ} (hk : k ≠ 0) :
    ((X * Xᴴ) ^ k).trace = ∑ u : Fin k → ι, ∑ v : Fin k → κ,
      ∏ t, X (u t) (v t) * star (X (u (finRotate k t)) (v t)) := by
  simpa only [conjTranspose_apply] using trace_mul_pow_eq_sum_prod X Xᴴ hk

/-- Entries of a product of `k + 1` matrices as sums over intermediate index paths. -/
theorem list_ofFn_prod_apply {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommSemiring R]
    {k : ℕ} (A : Fin (k + 1) → Matrix κ κ R) (i j : κ) :
    (List.ofFn A).prod i j =
      ∑ d : Fin k → κ,
        ∏ t : Fin (k + 1),
          A t (@Fin.cons k (fun _ ↦ κ) i d t) (@Fin.snoc k (fun _ ↦ κ) d j t) := by
  induction k generalizing i with
  | zero =>
    rw [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Fintype.sum_unique, Fin.prod_univ_one, Fin.cons_zero,
      show (0 : Fin 1) = Fin.last 0 from Fin.last_zero.symm, Fin.snoc_last]
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    have hsum :
        (∑ x : κ, A 0 i x * (List.ofFn fun s : Fin (k + 1) ↦ A s.succ).prod x j) =
          ∑ x : κ, A 0 i x * ∑ d : Fin k → κ,
            ∏ t : Fin (k + 1),
              A t.succ (@Fin.cons k (fun _ ↦ κ) x d t) (@Fin.snoc k (fun _ ↦ κ) d j t) :=
      Finset.sum_congr rfl fun x _ ↦ by rw [ih (fun s ↦ A s.succ) x]
    rw [hsum]
    simp_rw [Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) ↦ κ).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Fin.consEquiv_apply, ← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ (n := k + 1)]
    simp

/-- The trace of a product of `k` matrices (`k ≠ 0`) as a cyclic path sum. -/
theorem trace_list_ofFn_prod {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommSemiring R]
    {k : ℕ} [NeZero k] (A : Fin k → Matrix κ κ R) :
    (List.ofFn A).prod.trace =
      ∑ c : Fin k → κ, ∏ t : Fin k, A t (c t) (c (finRotate k t)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  simp only [Matrix.trace, Matrix.diag]
  simp_rw [list_ofFn_prod_apply A _ _]
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) ↦ κ).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun d _ ↦
    Finset.prod_congr rfl fun t _ ↦ ?_
  rw [Fin.consEquiv_apply]
  refine congrArg (A t (@Fin.cons m (fun _ ↦ κ) i d t)) ?_
  refine Fin.lastCases ?_ (fun s ↦ ?_) t <;> simp

open scoped Classical in
/-- Splits a cyclic coordinate sum of matrix products over the orbits of a permutation into a
product, over the orbits, of the traces of the ordered matrix products along each orbit. -/
theorem sum_prod_apply_perm_eq_prod_trace_list_ofFn_orbit {R ι κ : Type*} [CommSemiring R]
    [Fintype ι] [Fintype κ] [DecidableEq κ] (σ : Equiv.Perm ι) (A : ι → Matrix κ κ R) :
    (∑ p : ι → κ, ∏ i : ι, A i (p i) (p (σ i))) =
      ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
        (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
          A ((σ ^ (t : ℕ)) ω.out)).prod.trace := by
  let e := σ.orbitElemEquiv
  let fEquiv :
      (∀ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
          Fin (Function.minimalPeriod (σ • ·) ω.out) → κ) ≃ (ι → κ) :=
    (Equiv.piCurry (fun ω _ ↦ κ)).symm.trans (Equiv.piCongrLeft' (fun _ ↦ κ) e)
  rw [← fEquiv.sum_comp]
  have hstep :
      (∑ c : ∀ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
          Fin (Function.minimalPeriod (σ • ·) ω.out) → κ,
          ∏ i : ι, A i (fEquiv c i) (fEquiv c (σ i))) =
        ∑ c : ∀ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
          Fin (Function.minimalPeriod (σ • ·) ω.out) → κ,
          ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
            ∏ t : Fin (Function.minimalPeriod (σ • ·) ω.out),
              A ((σ ^ (t : ℕ)) ω.out) (c ω t) (c ω (finRotate _ t)) := by
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [← Fintype.prod_equiv e _ _ fun _ ↦ rfl, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun ω _ ↦ Finset.prod_congr rfl fun t _ ↦ ?_
    have hnext : σ (e ⟨ω, t⟩) =
        e ⟨ω, finRotate (Function.minimalPeriod (σ • ·) ω.out) t⟩ :=
      Equiv.Perm.orbitElemEquiv_succ σ ω t
    have hp : ∀ p, fEquiv c (e p) = c p.1 p.2 := fun p ↦ by
      simp only [fEquiv, Equiv.trans_apply, Equiv.piCongrLeft'_apply, Equiv.piCurry_symm_apply,
        Sigma.uncurry]
      rw [Equiv.symm_apply_apply]
    rw [hp, hnext, hp, show e ⟨ω, t⟩ = _ from Equiv.Perm.orbitElemEquiv_apply σ ω t]
  rw [hstep]
  have hrhs :
      (∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
          (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) ω.out) ↦
            A ((σ ^ (t : ℕ)) ω.out)).prod.trace) =
        ∑ c : ∀ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
            Fin (Function.minimalPeriod (σ • ·) ω.out) → κ,
          ∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
            ∏ t : Fin (Function.minimalPeriod (σ • ·) ω.out),
              A ((σ ^ (t : ℕ)) ω.out) (c ω t) (c ω (finRotate _ t)) := by
    trans (∏ ω : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ι,
        ∑ c_ω : Fin (Function.minimalPeriod (σ • ·) ω.out) → κ,
          ∏ t : Fin (Function.minimalPeriod (σ • ·) ω.out),
            A ((σ ^ (t : ℕ)) ω.out) (c_ω t) (c_ω (finRotate _ t)))
    · refine Finset.prod_congr rfl fun ω _ ↦ ?_
      have : NeZero (Function.minimalPeriod (σ • ·) ω.out) :=
        ⟨(Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts ω.out)).ne'⟩
      rw [Matrix.trace_list_ofFn_prod]
    · rw [Fintype.prod_sum]
  rw [hrhs]

end Matrix
