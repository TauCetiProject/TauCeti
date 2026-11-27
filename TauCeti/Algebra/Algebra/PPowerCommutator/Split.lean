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
import TauCeti.LinearAlgebra.Matrix.Trace.CyclicQuotient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.Artinian.Ring

/-!
# The `p`-power commutator subspace of a split algebra

For matrices over a commutative ring `R`, the commutator submodule is the kernel of the trace
(`TauCeti.commutatorSubmodule_matrix_eq_ker_trace`). Over a reduced commutative ring `k` of prime
characteristic `p` the `p`-power commutator subspace `T(M_n(k))` is also the kernel of the trace,
since `tr (a ^ (p ^ m)) = (tr a) ^ (p ^ m)` (`TauCeti.trace_pow_char_pow`, Webb,
Lemma 9.3.1(iii)). So for `n ≥ 1` the quotient `M_n(k) / T(M_n(k))` is one-dimensional over a
field `k`.

Let `A` be a finite-dimensional algebra over a field `k` of characteristic `p` with
`A / rad A ≅ ∏_{i ∈ ι} M_{n_i}(k)`, `n_i ≥ 1`, that is, `k` is a splitting field for `A`. As the
radical consists of nilpotent elements, `A / T(A) ≅ (A / rad A) / T(A / rad A)`, and `T` of the
product is the product of the `T`s, so `dim_k A / T(A)` is the number `|ι|` of matrix factors
(Webb, Proposition 9.3.3).

## Main results

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

variable (R : Type*) [CommRing R] (n : Type*) [Fintype n] [DecidableEq n]
variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

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
