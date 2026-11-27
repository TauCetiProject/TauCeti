/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Algebra.Algebra.PPowerCommutator.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.CharP.Lemmas

/-!
# The `p`-power commutator subspace of a split algebra

For matrices over a commutative ring `R`, the commutator submodule is the kernel of the trace:
the matrix units `E_ij` with `i ≠ j` and the differences `E_ii - E_jj` are commutators. Over a
reduced commutative ring `k` of prime characteristic `p` the `p`-power commutator subspace
`T(M_n(k))` is also the kernel of the trace, since `tr (a ^ (p ^ m)) = (tr a) ^ (p ^ m)` (Webb,
Lemma 9.3.1(iii)). So for `n ≥ 1` the quotient `M_n(k) / T(M_n(k))` is one-dimensional over a
field `k`.

Let `A` be a finite-dimensional algebra over a field `k` of characteristic `p` with
`A / rad A ≅ ∏_{i ∈ ι} M_{n_i}(k)`, `n_i ≥ 1`, that is, `k` is a splitting field for `A`. As the
radical consists of nilpotent elements, `A / T(A) ≅ (A / rad A) / T(A / rad A)`, and `T` of the
product is the product of the `T`s, so `dim_k A / T(A)` is the number `|ι|` of matrix factors
(Webb, Proposition 9.3.3).

## Main results

* `TauCeti.commutatorSubmodule_matrix_eq_ker_trace`: `[M_n(R), M_n(R)] = ker tr`.
* `TauCeti.trace_pow_char_pow`: `tr (a ^ (p ^ m)) = (tr a) ^ (p ^ m)` in characteristic `p`.
* `TauCeti.pPowerCommutatorSubmodule_matrix_eq_ker_trace`: `T(M_n(k)) = ker tr`.
* `TauCeti.finrank_quotient_pPowerCommutatorSubmodule_matrix`: `dim M_n(k) / T(M_n(k)) = 1`.
* `TauCeti.finrank_quotient_pPowerCommutatorSubmodule_of_algEquiv_pi_matrix`: if
  `A / rad A ≅ ∏_{i ∈ ι} M_{n_i}(k)` with every `n_i ≥ 1`, then `dim_k A / T(A) = |ι|`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Cambridge Studies in Advanced
  Mathematics 161, Cambridge University Press, 2016, Lemma 9.3.1, Proposition 9.3.3.
-/

public section

namespace TauCeti

open Matrix Module

section CommRing

variable (R : Type*) [CommRing R] (n : Type*) [Fintype n]

/-- The commutators of a matrix algebra over a commutative ring span the kernel of the trace. -/
theorem commutatorSubmodule_matrix_eq_ker_trace :
    commutatorSubmodule R (Matrix n n R) = LinearMap.ker (traceLinearMap n R R) := by
  classical
  refine le_antisymm ((commutatorSubmodule_le_ker_iff _).2 fun x y ↦ trace_mul_comm x y)
    fun a ha ↦ ?_
  set C := commutatorSubmodule R (Matrix n n R)
  rw [LinearMap.mem_ker, traceLinearMap_apply] at ha
  -- Off-diagonal matrix units and differences of diagonal ones are commutators.
  have hoff : ∀ i j, i ≠ j → ∀ r : R, single i j r ∈ C := fun i j hij r ↦ by
    simpa [hij.symm] using
      mul_sub_mul_mem_commutatorSubmodule R _ (single i j r) (single j j (1 : R))
  have hdiag : ∀ i j (r : R), single i i r - single j j r ∈ C := fun i j r ↦ by
    simpa using mul_sub_mul_mem_commutatorSubmodule R _ (single i j r) (single j i (1 : R))
  cases isEmpty_or_nonempty n with
  | inl _ => simp [Subsingleton.elim a 0]
  | inr h =>
    obtain ⟨i₀⟩ := h
    have ha' : a = ∑ i, ∑ j,
        (single i j (a i j) - if i = j then single i₀ i₀ (a i j) else 0) := by
      have hsum : ∑ i : n, single i₀ i₀ (a i i) = 0 := by
        have h : ∑ i : n, single i₀ i₀ (a i i) = single i₀ i₀ (∑ i, a i i) :=
          (map_sum (singleAddMonoidHom (α := R) i₀ i₀) (fun i ↦ a i i) Finset.univ).symm
        rw [h]
        change single i₀ i₀ (trace a) = 0
        rw [ha, single_zero]
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hsum,
        sub_zero]
      exact matrix_eq_sum_single a
    rw [ha']
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ ?_
    by_cases hij : i = j
    · subst hij
      simpa using hdiag i i₀ (a i i)
    · simpa [hij] using hoff i j hij (a i j)

variable [DecidableEq n] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

include hp in
/-- In characteristic `p`, the trace of the `p ^ m`-th power of a matrix is the `p ^ m`-th power of
its trace (Webb, Lemma 9.3.1(iii)). -/
theorem trace_pow_char_pow (a : Matrix n n R) (m : ℕ) :
    trace (a ^ p ^ m) = trace a ^ p ^ m := by
  classical
  -- `a` differs from its diagonal by a matrix of trace zero, hence by commutators.
  have hd : a - diagonal (diag a) ∈ commutatorSubmodule R (Matrix n n R) := by
    rw [commutatorSubmodule_matrix_eq_ker_trace, LinearMap.mem_ker, traceLinearMap_apply,
      trace_sub, trace_diagonal]
    exact sub_self _
  have h := pow_char_pow_sub_pow_char_pow_mem_commutatorSubmodule p R hd m
  rw [commutatorSubmodule_matrix_eq_ker_trace, LinearMap.mem_ker, traceLinearMap_apply,
    trace_sub, sub_eq_zero, diagonal_pow, trace_diagonal] at h
  simp only [Pi.pow_apply] at h
  rw [h, trace, sum_pow_char_pow]

include hp in
/-- Over a reduced commutative ring of characteristic `p`, the `p`-power commutator subspace of a
matrix algebra is the kernel of the trace (Webb, Lemma 9.3.1(iii)). -/
theorem pPowerCommutatorSubmodule_matrix_eq_ker_trace [IsReduced R] :
    pPowerCommutatorSubmodule p R (Matrix n n R) = LinearMap.ker (traceLinearMap n R R) := by
  refine le_antisymm (fun a ha ↦ ?_) ((commutatorSubmodule_matrix_eq_ker_trace R n).symm.le.trans
    (commutatorSubmodule_le_pPowerCommutatorSubmodule p R))
  obtain ⟨m, hm⟩ := (mem_pPowerCommutatorSubmodule p R).1 ha
  rw [commutatorSubmodule_matrix_eq_ker_trace, LinearMap.mem_ker, traceLinearMap_apply,
    trace_pow_char_pow] at hm
  rw [LinearMap.mem_ker, traceLinearMap_apply]
  exact IsReduced.eq_zero _ ⟨_, hm⟩

end CommRing

section Field

variable (p : ℕ) [hp : Fact p.Prime] (k : Type*) [Field k] [CharP k p]

include hp in
/-- Over a field of characteristic `p`, the quotient of `M_n(k)`, `n ≥ 1`, by its `p`-power
commutator subspace is one-dimensional. -/
theorem finrank_quotient_pPowerCommutatorSubmodule_matrix (n : Type*) [Fintype n] [DecidableEq n]
    [Nonempty n] :
    finrank k (Matrix n n k ⧸ pPowerCommutatorSubmodule p k (Matrix n n k)) = 1 := by
  obtain ⟨i⟩ := ‹Nonempty n›
  have hsurj : Function.Surjective (traceLinearMap n k k) := fun r ↦
    ⟨single i i r, by simp⟩
  rw [(Submodule.quotEquivOfEq _ _
      (pPowerCommutatorSubmodule_matrix_eq_ker_trace k n p)).finrank_eq,
    (LinearMap.quotKerEquivOfSurjective _ hsurj).finrank_eq, finrank_self]

include hp in
/-- **The `p`-power commutator subspace counts the matrix factors of a split algebra** (Webb,
Proposition 9.3.3): if `A` is a finite-dimensional algebra over a field `k` of characteristic `p`
and `A / rad A ≅ ∏_{i ∈ ι} M_{n_i}(k)` with every `n_i` nonempty, then `A / T(A)` has dimension
`|ι|`. -/
theorem finrank_quotient_pPowerCommutatorSubmodule_of_algEquiv_pi_matrix {A : Type*} [Ring A]
    [Algebra k A] [FiniteDimensional k A] {ι : Type*} [Fintype ι] {n : ι → Type*}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [∀ i, Nonempty (n i)]
    (e : (A ⧸ Ring.jacobson A) ≃ₐ[k] Π i, Matrix (n i) (n i) k) :
    finrank k (A ⧸ pPowerCommutatorSubmodule p k A) = Fintype.card ι := by
  classical
  have := IsArtinianRing.of_finite k A
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson A
  have hJ : ∀ x ∈ Ring.jacobson A, IsNilpotent x := fun x hx ↦
    ⟨N, by simpa [hN] using Ideal.pow_mem_pow hx N⟩
  rw [(quotientPPowerCommutatorEquivOfIsNilpotent p k _ hJ).finrank_eq,
    (quotientPPowerCommutatorEquiv p k e).finrank_eq,
    (Submodule.quotEquivOfEq _ _ (pPowerCommutatorSubmodule_pi p k _)).finrank_eq,
    (Submodule.quotientPi _).finrank_eq, finrank_pi_fintype]
  simp [finrank_quotient_pPowerCommutatorSubmodule_matrix p k]

end Field

end TauCeti
