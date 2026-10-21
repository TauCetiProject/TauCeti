/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Trace

import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.Algebra.Ring.Commutator
import TauCeti.LinearAlgebra.Trace.Idempotent

/-!
# Traces and nilpotent endomorphisms in characteristic zero

Over a field of characteristic zero, an endomorphism `f` of a finite-dimensional vector space is
nilpotent exactly when the traces of all its positive powers vanish. One direction holds over any
reduced ring. For the other, factor the characteristic polynomial as `X ^ m * q` with `q(0) ≠ 0`
and choose a Bézout identity `a * X ^ (m + 1) + b * q = 1`. Then `a(f) * f ^ (m + 1)` is an
idempotent polynomial in `f` with zero constant term. Its trace is its rank and also vanishes, so it
is zero, `q(f)` is invertible, and `f ^ m = 0`.

Two consequences for a pair of endomorphisms `A`, `B` with `⁅A, ⁅A, B⁆⁆ = 0` follow.

* **Jacobson's lemma**: `⁅A, B⁆` is nilpotent. Indeed `⁅A, B⁆ ^ (k + 1)` is the commutator of `A`
  with `⁅A, B⁆ ^ k * B`, because `⁅A, B⁆` commutes with `A`, so all these traces vanish.
* If moreover `A` is nilpotent, then `trace (A * B) = 0`. The subspaces `V i = ker (A ^ i)` exhaust
  the space, `A` maps `V (i + 1)` into `V i`, and `B` maps `V i` into `V (i + 1)`. Commuting the
  two restricted maps under the trace, and using that `⁅A, B⁆` is nilpotent on each `V i`, shows
  that the trace of `A * B` on `V i` does not depend on `i`; it vanishes on `V 0 = 0`.

Applied to the adjoint representation, the last statement says that an ad-nilpotent element is
Killing-orthogonal to every element that its adjoint action kills twice. This is the input to the
construction of the neutral element of an `sl₂`-triple in the Jacobson–Morozov theorem.

## Main results

* `LinearMap.isNilpotent_iff_forall_trace_pow_eq_zero`: in characteristic zero, an endomorphism is
  nilpotent if and only if all traces of its positive powers vanish.
* `LinearMap.isNilpotent_lie_of_lie_lie_eq_zero`: Jacobson's lemma.
* `LinearMap.trace_mul_eq_zero_of_isNilpotent_of_lie_lie_eq_zero`: if `A` is nilpotent and
  `⁅A, ⁅A, B⁆⁆ = 0`, then `trace (A * B) = 0`.

## References

* N. Jacobson, *Rational methods in the theory of Lie algebras*, Ann. of Math. **36** (1935),
  875–881, for the nilpotence of `⁅A, B⁆`.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter III, §11, for its use in the proof of
  the Jacobson–Morozov theorem.
-/

public section

namespace LinearMap

open Module Polynomial

section KerPow

variable {R N : Type*} [Semiring R] [AddCommGroup N] [Module R N] {A B : Module.End R N}

/-- An endomorphism commuting with `A` preserves `ker (A ^ i)`. -/
private theorem apply_mem_ker_pow_of_commute {C : Module.End R N} (hc : Commute A C) {i : ℕ}
    {v : N} (hv : v ∈ ker (A ^ i)) : C v ∈ ker (A ^ i) := by
  rw [mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, (hc.pow_left i).eq, Module.End.mul_apply, hv, map_zero]

/-- If `A` commutes with `⁅A, B⁆`, then `B` maps `ker (A ^ i)` into `ker (A ^ (i + 1))`. -/
private theorem apply_mem_ker_pow_succ_of_commute_lie (hc : Commute A ⁅A, B⁆) {i : ℕ} {v : N}
    (hv : v ∈ ker (A ^ i)) : B v ∈ ker (A ^ (i + 1)) := by
  have hCv := apply_mem_ker_pow_of_commute hc hv
  rw [mem_ker] at hv hCv ⊢
  -- Both terms of `A ^ (i + 1) * B = B * A ^ (i + 1) + (i + 1) • (A ^ i * ⁅A, B⁆)` applied to
  -- `v` vanish, since `A ^ i` kills `v` and `⁅A, B⁆ v`.
  have hv' : (A ^ (i + 1)) v = 0 := by rw [pow_succ', Module.End.mul_apply, hv, map_zero]
  rw [← Module.End.mul_apply, TauCeti.Associative.pow_mul_eq_mul_pow_add_nsmul_of_commutator_eq
    (sub_eq_iff_eq_add'.1 (Ring.lie_def A B).symm) hc (i + 1), Nat.add_sub_cancel]
  simp only [add_apply, smul_apply, Module.End.mul_apply, hv', hCv, map_zero, smul_zero, add_zero]

/-- `A` maps `ker (A ^ (i + 1))` into `ker (A ^ i)`. -/
private theorem apply_mem_ker_pow_of_mem_ker_pow_succ {i : ℕ} {v : N}
    (hv : v ∈ ker (A ^ (i + 1))) : A v ∈ ker (A ^ i) := by
  rw [mem_ker] at hv ⊢
  rwa [← Module.End.mul_apply, ← pow_succ]

/-- If `A` commutes with `⁅A, B⁆`, then `A * B` preserves `ker (A ^ i)`. -/
private theorem mul_apply_mem_ker_pow_of_commute_lie (hc : Commute A ⁅A, B⁆) {i : ℕ} {v : N}
    (hv : v ∈ ker (A ^ i)) : (A * B) v ∈ ker (A ^ i) :=
  apply_mem_ker_pow_of_mem_ker_pow_succ (apply_mem_ker_pow_succ_of_commute_lie hc hv)

end KerPow

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- **Trace criterion for nilpotence.** Over a field of characteristic zero, an endomorphism of a
finite-dimensional vector space is nilpotent if and only if the traces of all its positive powers
vanish. -/
theorem isNilpotent_iff_forall_trace_pow_eq_zero [CharZero K] {f : Module.End K M} :
    IsNilpotent f ↔ ∀ k, 0 < k → trace K M (f ^ k) = 0 := by
  refine ⟨fun hf k hk => (isNilpotent_trace_of_isNilpotent (hf.pow_of_pos hk.ne')).eq_zero,
    fun hf => ?_⟩
  -- A polynomial in `f` without constant term is traceless.
  have htr0 {p : K[X]} (hp : p.coeff 0 = 0) : trace K M (aeval f p) = 0 := by
    rw [aeval_eq_sum_range, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hp, zero_smul, map_zero]
    · rw [map_smul, hf k hk, smul_zero]
  -- Split off the factor `X ^ m` of the characteristic polynomial.
  obtain ⟨q, hpq, hq⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd f.charpoly f.charpoly_monic.ne_zero 0
  set m := f.charpoly.rootMultiplicity 0
  rw [map_zero, sub_zero] at hpq hq
  obtain ⟨a, b, hab⟩ := ((irreducible_X.coprime_iff_not_dvd.2 hq).pow_left (m := m + 1))
  -- `P = a(f) * f ^ (m + 1)` is an idempotent without constant term.
  set P := aeval f (a * X ^ (m + 1)) with hPdef
  have hPP : P * P = (1 : K) • P := by
    have h : (a * X ^ (m + 1)) * (a * X ^ (m + 1)) - a * X ^ (m + 1) =
        -(a * b * X) * f.charpoly := by
      linear_combination (a * X ^ (m + 1)) * hab + (a * b * X) * hpq
    have h' := congrArg (aeval f) h
    rw [map_sub, map_mul (aeval f) (a * X ^ (m + 1)), map_mul (aeval f) (-(a * b * X)),
      aeval_self_charpoly, mul_zero, sub_eq_zero] at h'
    rw [one_smul]
    exact h'
  have hP : P = 0 := by
    have htr := TauCeti.LinearMap.trace_eq_mul_finrank_range hPP
    rw [htr0 (by simp [mul_coeff_zero]), one_mul,
      eq_comm, Nat.cast_eq_zero, Submodule.finrank_eq_zero, range_eq_bot] at htr
    exact htr
  -- Hence `b(f) * q(f) = 1`, and `f ^ m * q(f) = 0` forces `f ^ m = 0`.
  have hbq : aeval f b * aeval f q = 1 := by
    have h1 := congrArg (aeval f) hab
    rw [map_add, map_one, map_mul (aeval f) b] at h1
    rwa [← hPdef, hP, zero_add] at h1
  have hfq : aeval f q * f ^ m = 0 := by
    rw [← aeval_X_pow (R := K), ← map_mul, mul_comm, ← hpq, aeval_self_charpoly]
  refine ⟨m, ?_⟩
  calc f ^ m = aeval f b * aeval f q * f ^ m := by rw [hbq, one_mul]
    _ = 0 := by rw [mul_assoc, hfq, mul_zero]

variable [CharZero K] {A B : Module.End K M}

/-- **Jacobson's lemma** on commutators. In characteristic zero, if `A` commutes with `⁅A, B⁆`,
then `⁅A, B⁆` is nilpotent: each of its positive powers is a commutator with `A`, hence
traceless. -/
theorem isNilpotent_lie_of_lie_lie_eq_zero (h : ⁅A, ⁅A, B⁆⁆ = 0) : IsNilpotent ⁅A, B⁆ := by
  have hc : Commute A ⁅A, B⁆ := commute_iff_lie_eq.2 h
  -- Left multiplication of `⁅A, B⁆` by anything commuting with `A` gives a commutator with `A`.
  have hcomm (D : Module.End K M) (hD : Commute A D) :
      D * ⁅A, B⁆ = A * (D * B) - D * B * A := by
    simp only [Ring.lie_def, mul_sub, ← mul_assoc, hD.eq]
  refine isNilpotent_iff_forall_trace_pow_eq_zero.2 fun k hk => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [zero_add, pow_succ, hcomm _ (hc.pow_right k), map_sub, trace_mul_comm, sub_self]

/-- If `A` commutes with `⁅A, B⁆`, then the trace of `A * B` on `ker (A ^ (i + 1))` equals its
trace on `ker (A ^ i)`: on `ker (A ^ (i + 1))`, `A * B` is `B * A` plus the nilpotent `⁅A, B⁆`, and
`B * A` and `A * B` are the two products of `A : ker (A ^ (i + 1)) → ker (A ^ i)` and
`B : ker (A ^ i) → ker (A ^ (i + 1))`. -/
private theorem trace_restrict_mul_ker_pow_succ (hc : Commute A ⁅A, B⁆) (i : ℕ) :
    trace K (ker (A ^ (i + 1)))
        ((A * B).restrict fun _ => mul_apply_mem_ker_pow_of_commute_lie hc) =
      trace K (ker (A ^ i))
        ((A * B).restrict fun _ => mul_apply_mem_ker_pow_of_commute_lie hc) := by
  have hAV (v : M) (hv : v ∈ ker (A ^ (i + 1))) : A v ∈ ker (A ^ i) :=
    apply_mem_ker_pow_of_mem_ker_pow_succ hv
  have hBV (v : M) (hv : v ∈ ker (A ^ i)) : B v ∈ ker (A ^ (i + 1)) :=
    apply_mem_ker_pow_succ_of_commute_lie hc hv
  have hsplit : (A * B).restrict (fun _ => mul_apply_mem_ker_pow_of_commute_lie hc (i := i + 1)) =
      (B * A).restrict (fun _ hv => hBV _ (hAV _ hv)) +
        ⁅A, B⁆.restrict (fun _ => apply_mem_ker_pow_of_commute hc) := by
    ext v
    simp [Ring.lie_def]
  have hnil : trace K (ker (A ^ (i + 1)))
      (⁅A, B⁆.restrict (fun _ => apply_mem_ker_pow_of_commute hc)) = 0 :=
    (isNilpotent_trace_of_isNilpotent (Module.End.isNilpotent.restrict _
      (isNilpotent_lie_of_lie_lie_eq_zero (commute_iff_lie_eq.1 hc)))).eq_zero
  have hBA : (B * A).restrict (fun _ hv => hBV _ (hAV _ hv)) =
      (B.restrict hBV) ∘ₗ (A.restrict hAV) := by
    ext v
    simp
  have hAB : (A * B).restrict (fun _ => mul_apply_mem_ker_pow_of_commute_lie hc (i := i)) =
      (A.restrict hAV) ∘ₗ (B.restrict hBV) := by
    ext v
    simp
  rw [hsplit, map_add, hnil, add_zero, hBA, hAB, trace_comp_comm']

/-- **The trace of `A * B` vanishes when `A` is nilpotent and commutes with `⁅A, B⁆`.**
In characteristic zero, the trace of `A * B` on `ker (A ^ i)` is independent of `i`, since `B`
raises and `A` lowers the index by one and `⁅A, B⁆` is nilpotent by Jacobson's lemma. -/
theorem trace_mul_eq_zero_of_isNilpotent_of_lie_lie_eq_zero (hA : IsNilpotent A)
    (h : ⁅A, ⁅A, B⁆⁆ = 0) : trace K M (A * B) = 0 := by
  have hc : Commute A ⁅A, B⁆ := commute_iff_lie_eq.2 h
  have hABV (i : ℕ) : ∀ v ∈ ker (A ^ i), (A * B) v ∈ ker (A ^ i) :=
    fun _ => mul_apply_mem_ker_pow_of_commute_lie hc
  have hconst (i : ℕ) : trace K (ker (A ^ i)) ((A * B).restrict (hABV i)) = 0 := by
    induction i with
    | zero =>
      have : Subsingleton (ker (A ^ 0)) := by
        rw [Submodule.subsingleton_iff_eq_bot]
        simp [Module.End.one_eq_id]
      rw [Subsingleton.elim ((A * B).restrict (hABV 0)) 0, map_zero]
    | succ i ih => rw [trace_restrict_mul_ker_pow_succ hc, ih]
  obtain ⟨n, hn⟩ := hA
  rw [← hconst n, trace_restrict_eq_of_forall_mem]
  intro v
  simp only [mem_ker, hn, zero_apply]

end LinearMap
