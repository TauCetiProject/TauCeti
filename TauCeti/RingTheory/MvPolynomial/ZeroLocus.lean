/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.Polynomial.Roots

/-!
# Zariski closures contain the limits of punctured lines

Let `K` be an infinite field and `k` a field with `K` a `k`-algebra. If a set `S ⊆ K^σ` contains
every point `x + t • v` with `t ≠ 0` of a line through `x`, then `x` lies in the Zariski closure of
`S`, the zero locus of its vanishing ideal in `k[X_σ]`: a polynomial vanishing on `S` restricts to
a one-variable polynomial with infinitely many roots, so it also vanishes at `t = 0`.

This is the algebraic form of a degeneration argument: a point that is the limit at `t = 0` of a
family `x + t • v` lying in `S` for `t ≠ 0` is in the Zariski closure of `S`, over any infinite
field. Over a topological field the corresponding statement for the usual closure is the
continuity of `t ↦ x + t • v`.

## Main results

* `MvPolynomial.mem_zeroLocus_vanishingIdeal_of_forall_add_smul_mem`: the Zariski closure of a set
  containing a punctured line contains the missing point.
-/

public section

open Polynomial

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Infinite K]

/-- Over an infinite field, a point `x` lies in the Zariski closure of any set `S` containing the
points `x + t • v` for all `t ≠ 0`. -/
theorem mem_zeroLocus_vanishingIdeal_of_forall_add_smul_mem {S : Set (σ → K)} {x v : σ → K}
    (h : ∀ t : K, t ≠ 0 → x + t • v ∈ S) : x ∈ zeroLocus K (vanishingIdeal k S) := by
  refine mem_zeroLocus_iff.2 fun p hp => ?_
  -- The restriction of `p` to the line through `x` in direction `v`, as a polynomial in `t`.
  set Q : K[X] := aeval (fun s => Polynomial.C (x s) + Polynomial.C (v s) * Polynomial.X) p
  have hQ (t : K) : Q.eval t = aeval (x + t • v) p := by
    have := congrArg (· p) (comp_aeval (R := k)
      (fun s => Polynomial.C (x s) + Polynomial.C (v s) * Polynomial.X)
      ((Polynomial.aeval t).restrictScalars k))
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    rw [Polynomial.coe_aeval_eq_eval] at this
    rw [this]
    congr 2
    funext s
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hQ0 : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q
      ((Set.finite_singleton (0 : K)).infinite_compl.mono fun t ht => ?_)
    rw [Set.mem_ofPred_eq, IsRoot, hQ]
    exact mem_vanishingIdeal_iff.1 hp _ (h t ht)
  simpa [hQ0] using (hQ 0).symm

end MvPolynomial
