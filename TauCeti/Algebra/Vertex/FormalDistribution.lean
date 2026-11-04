/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.VertexOperator
public import Mathlib.RingTheory.Binomial

/-!
# Delta expansions of local formal distributions

A two-variable formal distribution is an arbitrary coefficient family, with normalized indexing
`c m n` for the coefficient of `z^(-m-1) w^(-n-1)`. Unlike a Hahn series, it need not have
well-ordered support. Multiplication by `z - w` and residue in `z` are nevertheless defined:
they use only finitely many coefficients.

`FormalDistribution.deltaTerm j A` denotes `A(w) ∂_w^[j] δ(z,w)`, where the derivative is a
Hasse (divided-power) derivative and `δ(z,w) = ∑ₘ z^(-m-1) w^m`. Its coefficients are
`choose m j • A (m+n-j)`. Integer binomial coefficients make this meaningful over every
abelian group, with no division or characteristic hypothesis.

Every distribution killed by `(z-w)^N` has a unique expansion in these terms for `j < N`.
The coefficient of the `j`th term is exactly `Res_z (z-w)^j c`. Applied to the commutator of
native vertex operators, this gives the formal delta expansion of mutual locality.
No multiplication of arbitrary distributions or convergence of infinite sums is asserted.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.1 and §2.3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.2.
-/

public section

noncomputable section

namespace TauCeti

/-- A two-variable formal distribution, indexed by the powers `z^(-m-1) w^(-n-1)`. -/
abbrev FormalDistribution (M : Type*) := ℤ → ℤ → M

namespace FormalDistribution

variable {M : Type*} [AddCommGroup M]

/-- Multiplication of a formal distribution by `z - w`. -/
def mulSub : AddMonoid.End (FormalDistribution M) where
  toFun c m n := c (m + 1) n - c m (n + 1)
  map_zero' := by ext m n; simp
  map_add' c d := by ext m n; simp; abel

@[simp]
theorem mulSub_apply (c : FormalDistribution M) (m n : ℤ) :
    mulSub c m n = c (m + 1) n - c m (n + 1) := (rfl)

/-- The residue in the first variable, as a distribution in the second variable. -/
def residue : FormalDistribution M →+ (ℤ → M) :=
  Pi.evalAddMonoidHom _ 0

@[simp]
theorem residue_apply (c : FormalDistribution M) (n : ℤ) : residue c n = c 0 n := (rfl)

/-- The well-defined product `A(w) ∂_w^[j] δ(z,w)`, using divided-power derivatives. -/
def deltaTerm (j : ℕ) : (ℤ → M) →+ FormalDistribution M where
  toFun A m n := Ring.choose m j • A (m + n - j)
  map_zero' := by ext m n; simp
  map_add' A B := by ext m n; simp [smul_add]

/-- The coefficients of a delta term, valid also for negative mode indices. -/
@[simp]
theorem deltaTerm_apply (j : ℕ) (A : ℤ → M) (m n : ℤ) :
    deltaTerm j A m n = Ring.choose m j • A (m + n - j) := (rfl)

@[simp]
theorem residue_deltaTerm_zero (A : ℤ → M) : residue (deltaTerm 0 A) = A := by
  ext n
  simp

@[simp]
theorem residue_deltaTerm_succ (j : ℕ) (A : ℤ → M) :
    residue (deltaTerm (j + 1) A) = 0 := by
  ext n
  simp [deltaTerm]

@[simp]
theorem mulSub_deltaTerm_zero (A : ℤ → M) : mulSub (deltaTerm 0 A) = 0 := by
  ext m n
  simp [add_comm, add_left_comm]

/-- Multiplication by `z-w` lowers the delta derivative order by one. -/
@[simp]
theorem mulSub_deltaTerm_succ (j : ℕ) (A : ℤ → M) :
    mulSub (deltaTerm (j + 1) A) = deltaTerm j A := by
  ext m n
  simp only [mulSub_apply, deltaTerm_apply, Ring.choose_succ_succ, add_smul]
  have h₁ : m + 1 + n - ↑(j + 1) = m + n - j := by omega
  have h₂ : m + (n + 1) - ↑(j + 1) = m + n - j := by omega
  rw [h₁, h₂]
  abel

/-- A distribution killed by `z-w` is its residue times the formal delta function. -/
theorem eq_deltaTerm_zero_of_mulSub_eq_zero {c : FormalDistribution M}
    (hc : mulSub c = 0) : c = deltaTerm 0 (residue c) := by
  have hstep (m n : ℤ) : c (m + 1) n = c m (n + 1) :=
    sub_eq_zero.mp (congrFun (congrFun hc m) n)
  have hline (m : ℤ) : ∀ s, c m (s - m) = c 0 s := by
    induction m using Int.induction_on with
    | zero => intro s; simp
    | succ i ih =>
      intro s
      have h := hstep i (s - (i + 1))
      have hindex : s - ((i : ℤ) + 1) + 1 = s - i := by omega
      rw [hindex] at h
      exact h.trans (ih s)
    | pred i ih =>
      intro s
      have h := hstep (-i - 1) (s + i)
      have h₁ : -(i : ℤ) - 1 + 1 = -i := by omega
      have h₂ : s + (i : ℤ) = s - -i := by omega
      have h₃ : s - -(i : ℤ) + 1 = s - (-i - 1) := by omega
      rw [h₁, h₂] at h
      simpa only [h₃] using h.symm.trans (ih s)
  ext m n
  simpa using hline m (m + n)

/-- Residues extract the coefficient of the matching delta derivative. -/
@[simp]
theorem residue_iterate_mulSub_deltaTerm (k j : ℕ) (A : ℤ → M) :
    residue (mulSub^[k] (deltaTerm j A)) = if k = j then A else 0 := by
  simp only [← AddMonoid.End.coe_pow]
  induction k generalizing j with
  | zero =>
    cases j <;> simp
  | succ k ih =>
    cases j with
    | zero => simp [pow_succ]
    | succ j => simpa [pow_succ, Nat.succ_eq_add_one] using ih j

/-- Each delta derivative is annihilated by every sufficiently high power of `z-w`. -/
theorem mulSub_pow_deltaTerm_eq_zero {j N : ℕ} (h : j < N) (A : ℤ → M) :
    (mulSub ^ N) (deltaTerm j A) = 0 := by
  induction N generalizing j with
  | zero => omega
  | succ N ih =>
    cases j with
    | zero => simp [pow_succ]
    | succ j => simpa [pow_succ] using ih (by omega : j < N)

/-- **Delta expansion.** A distribution of locality order `N` is the sum of its delta terms,
whose coefficients are the successive residues `Res_z (z-w)^j c`. -/
theorem eq_sum_deltaTerm {c : FormalDistribution M} {N : ℕ}
    (hc : (mulSub ^ N) c = 0) :
    c = ∑ j ∈ Finset.range N, deltaTerm j (residue ((mulSub ^ j) c)) := by
  induction N generalizing c with
  | zero => simpa using hc
  | succ N ih =>
    let d := ∑ j ∈ Finset.range N, deltaTerm (j + 1) (residue ((mulSub ^ (j + 1)) c))
    have hd : mulSub d = mulSub c := by
      rw [ih (c := mulSub c) (by simpa [pow_succ] using hc)]
      simp [d, map_sum, pow_succ]
    have hcd : mulSub (c - d) = 0 := by simp [hd]
    have hres : residue d = 0 := by simp [d, map_sum]
    have heq := eq_deltaTerm_zero_of_mulSub_eq_zero hcd
    rw [map_sub, hres, sub_zero] at heq
    rw [Finset.sum_range_succ', ← sub_eq_iff_eq_add']
    exact heq

/-- The delta coefficients are recovered by residues, without any locality assumption. -/
theorem residue_mulSub_pow_sum_deltaTerm (N k : ℕ) (A : ℕ → ℤ → M) (hk : k < N) :
    residue ((mulSub ^ k) (∑ j ∈ Finset.range N, deltaTerm j (A j))) = A k := by
  rw [map_sum, map_sum]
  simp only [AddMonoid.End.coe_pow, residue_iterate_mulSub_deltaTerm]
  simp only [Finset.sum_ite_eq, Finset.mem_range, hk, ite_true]

/-- **Uniqueness of delta expansion.** Two finite delta expansions agree exactly when all
of their coefficient distributions agree. -/
theorem sum_deltaTerm_inj (N : ℕ) (A B : ℕ → ℤ → M) :
    (∑ j ∈ Finset.range N, deltaTerm j (A j)) =
      (∑ j ∈ Finset.range N, deltaTerm j (B j)) ↔ ∀ j < N, A j = B j := by
  refine ⟨fun h j hj ↦ ?_, fun h ↦ Finset.sum_congr rfl fun j hj ↦ congrArg (deltaTerm j)
    (h j (Finset.mem_range.mp hj))⟩
  have hr := congrArg (fun c ↦ residue ((mulSub ^ j) c)) h
  rwa [residue_mulSub_pow_sum_deltaTerm N j A hj,
    residue_mulSub_pow_sum_deltaTerm N j B hj] at hr

/-- A finite delta expansion has locality order at most its number of terms. -/
theorem mulSub_pow_sum_deltaTerm_eq_zero (N : ℕ) (A : ℕ → ℤ → M) :
    (mulSub ^ N) (∑ j ∈ Finset.range N, deltaTerm j (A j)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j hj ↦
    mulSub_pow_deltaTerm_eq_zero (Finset.mem_range.mp hj) (A j)

/-- The binomial coefficient formula for multiplication by `(z-w)^N`. -/
theorem mulSub_pow_apply (N : ℕ) (c : FormalDistribution M) (m n : ℤ) :
    (mulSub ^ N) c m n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal N,
      N.choose ij.1 • (-1 : ℤ) ^ ij.2 • c (m + ij.1) (n + ij.2) := by
  induction N generalizing m n with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, mulSub_apply, ih, ih,
      Finset.sum_antidiagonal_choose_succ_nsmul
        (fun i j ↦ (-1 : ℤ) ^ j • c (m + i) (n + j)) N]
    have h₁ : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ (ij.2 + 1) •
        c (m + ij.1) (n + ↑(ij.2 + 1)) =
        -(N.choose ij.1 • (-1 : ℤ) ^ ij.2 • c (m + ij.1) (n + 1 + ij.2)) := by
      intro ij _
      have hindex : n + ↑(ij.2 + 1) = n + 1 + ij.2 := by omega
      rw [hindex, pow_succ]
      module
    have h₂ : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal N, N.choose ij.2 • (-1 : ℤ) ^ ij.2 •
        c (m + ↑(ij.1 + 1)) (n + ij.2) =
        N.choose ij.1 • (-1 : ℤ) ^ ij.2 • c (m + 1 + ij.1) (n + ij.2) := by
      intro ij hij
      have hindex : m + ↑(ij.1 + 1) = m + 1 + ij.1 := by omega
      rw [Nat.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.mp hij).symm,
        hindex]
    rw [Finset.sum_congr rfl h₁, Finset.sum_congr rfl h₂, Finset.sum_neg_distrib]
    abel

end FormalDistribution

end TauCeti

namespace VertexOperator

open TauCeti VertexOperator
open scoped VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The commutator of fields as a two-variable formal distribution. This does not require
multiplying Hahn series with incompatible support orders. -/
def commutatorDistribution (A B : VertexOperator R V) : FormalDistribution (Module.End R V) :=
  fun m n ↦ A[[m]] * B[[n]] - B[[n]] * A[[m]]

@[simp]
theorem commutatorDistribution_apply (A B : VertexOperator R V) (m n : ℤ) :
    A.commutatorDistribution B m n = A[[m]] * B[[n]] - B[[n]] * A[[m]] := (rfl)

/-- Coefficientwise locality is precisely annihilation of the commutator by `(z-w)^N`. -/
theorem isLocalOfOrder_iff_mulSub_pow_eq_zero (A B : VertexOperator R V) (N : ℕ) :
    A.IsLocalOfOrder B N ↔ (FormalDistribution.mulSub ^ N) (A.commutatorDistribution B) = 0 := by
  rw [isLocalOfOrder_iff, funext_iff]
  simp only [funext_iff, FormalDistribution.mulSub_pow_apply, commutatorDistribution_apply,
    Pi.zero_apply]

/-- The delta expansion of a local field commutator, with coefficients given by its residues. -/
theorem IsLocalOfOrder.commutatorDistribution_eq_sum_deltaTerm {A B : VertexOperator R V}
    {N : ℕ} (h : A.IsLocalOfOrder B N) :
    A.commutatorDistribution B = ∑ j ∈ Finset.range N,
      FormalDistribution.deltaTerm j (FormalDistribution.residue
        ((FormalDistribution.mulSub ^ j) (A.commutatorDistribution B))) :=
  FormalDistribution.eq_sum_deltaTerm ((isLocalOfOrder_iff_mulSub_pow_eq_zero A B N).mp h)

end VertexOperator
