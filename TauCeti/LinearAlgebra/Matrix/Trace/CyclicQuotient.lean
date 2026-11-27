/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Algebra.Algebra.PPowerCommutator.Basic
import Mathlib.Algebra.CharP.Lemmas

/-!
# Matrix traces and the commutator submodule

The trace of a finite square matrix whose entries form an additive commutative monoid with a
commutative multiplication is invariant under exchanging the two factors of a product.  Hence the
trace of a multiplicative `k`-linear map `f` to such matrices kills the commutator submodule
`TauCeti.commutatorSubmodule` over the semiring `k`: an element `x` with `(f x).trace ≠ 0` does
not lie in it.  When `k` is a ring, such an `x` therefore has nonzero class in the cyclic quotient
`TauCeti.cyclicQuotient k A`, which is `A / [A, A]`.

For matrices over a commutative ring `R` the commutator submodule is exactly the kernel of the
trace: the matrix units `E_ij` with `i ≠ j` and the differences `E_ii - E_jj` are commutators. In
characteristic `p` this gives `tr (a ^ (p ^ m)) = (tr a) ^ (p ^ m)` (Webb, Lemma 9.3.1(iii)), as
the `p ^ m`-th power map is additive modulo commutators.

## Main results

* `TauCeti.trace_map_eq_zero_of_mem_commutatorSubmodule`: for a multiplicative `k`-linear map `f`
  from `A` to square matrices with finitely many indices and entries in a commutative magma `R`
  which is an additive `k`-module, the trace of `f x` vanishes for every `x` in the commutator
  submodule over `k`.
* `TauCeti.commutatorSubmodule_matrix_eq_ker_trace`: `[M_n(R), M_n(R)] = ker tr`.
* `TauCeti.mem_commutatorSubmodule_matrix_iff`: `a ∈ [M_n(R), M_n(R)] ↔ tr a = 0`.
* `TauCeti.trace_pow_char_pow`: `tr (a ^ (p ^ m)) = (tr a) ^ (p ^ m)` in characteristic `p`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Cambridge Studies in Advanced
  Mathematics 161, Cambridge University Press, 2016, Lemma 9.3.1.
-/

public section

namespace TauCeti

/-- **The trace of a matrix representation kills commutators**: if `f` is a multiplicative
`k`-linear map to square matrices with finitely many indices and entries in `R`, where `R` is an
additive `k`-module with a commutative (not necessarily distributive or associative)
multiplication, then the trace of `f x` vanishes for every `x` in the commutator submodule. -/
theorem trace_map_eq_zero_of_mem_commutatorSubmodule {k A n R F : Type*} [Semiring k]
    [NonUnitalNonAssocRing A] [Module k A] [Fintype n] [AddCommMonoid R] [CommMagma R]
    [Module k R] [FunLike F A (Matrix n n R)] [MulHomClass F A (Matrix n n R)]
    [LinearMapClass F k A (Matrix n n R)] (f : F) {x : A} (hx : x ∈ commutatorSubmodule k A) :
    (f x).trace = 0 := by
  -- the trace of `f`, as a `k`-linear map, is invariant under exchanging the factors of a product
  have hle := (commutatorSubmodule_le_ker_iff
    ((Matrix.traceLinearMap n k R).comp (f : A →ₗ[k] Matrix n n R))).2 fun x y => by
      simpa only [LinearMap.comp_apply, LinearMap.coe_ofClass, map_mul,
        Matrix.traceLinearMap_apply] using Matrix.trace_mul_comm (f x) (f y)
  simpa only [LinearMap.comp_apply, LinearMap.coe_ofClass, Matrix.traceLinearMap_apply] using
    LinearMap.mem_ker.1 (hle hx)

section CommRing

open Matrix

variable (R : Type*) [CommRing R] (n : Type*) [Fintype n]

/-- The commutators of a matrix algebra over a commutative ring span the kernel of the trace. -/
theorem commutatorSubmodule_matrix_eq_ker_trace :
    commutatorSubmodule R (Matrix n n R) = LinearMap.ker (traceLinearMap n R R) := by
  classical
  refine le_antisymm ((commutatorSubmodule_le_ker_iff _).2 fun x y ↦ trace_mul_comm x y)
    fun a ha ↦ ?_
  set C := commutatorSubmodule R (Matrix n n R)
  rw [LinearMap.mem_ker, traceLinearMap_apply] at ha
  simp only [trace, diag_apply] at ha
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
        rw [h, ha, single_zero]
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hsum,
        sub_zero]
      exact matrix_eq_sum_single a
    rw [ha']
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ ?_
    by_cases hij : i = j
    · subst hij
      simpa using hdiag i i₀ (a i i)
    · simpa [hij] using hoff i j hij (a i j)

/-- A matrix over a commutative ring is a sum of commutators exactly when its trace vanishes. -/
theorem mem_commutatorSubmodule_matrix_iff {a : Matrix n n R} :
    a ∈ commutatorSubmodule R (Matrix n n R) ↔ trace a = 0 := by
  rw [commutatorSubmodule_matrix_eq_ker_trace, LinearMap.mem_ker, traceLinearMap_apply]

variable [DecidableEq n] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

include hp in
/-- In characteristic `p`, the trace of the `p ^ m`-th power of a matrix is the `p ^ m`-th power of
its trace (Webb, Lemma 9.3.1(iii)). -/
theorem trace_pow_char_pow (a : Matrix n n R) (m : ℕ) :
    trace (a ^ p ^ m) = trace a ^ p ^ m := by
  classical
  -- `a` differs from its diagonal by a matrix of trace zero, hence by commutators.
  have hd : a - diagonal (diag a) ∈ commutatorSubmodule R (Matrix n n R) := by
    rw [mem_commutatorSubmodule_matrix_iff, trace_sub, trace_diagonal]
    exact sub_self _
  have h := pow_char_pow_sub_pow_char_pow_mem_commutatorSubmodule p R hd m
  rw [mem_commutatorSubmodule_matrix_iff, trace_sub, sub_eq_zero, diagonal_pow,
    trace_diagonal] at h
  simp only [Pi.pow_apply] at h
  rw [h, trace, sum_pow_char_pow]

end CommRing

end TauCeti
