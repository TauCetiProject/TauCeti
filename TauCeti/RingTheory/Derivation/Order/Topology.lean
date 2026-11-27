/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.Derivation.Order.Basic
public import TauCeti.RingTheory.Smooth.Regular
import TauCeti.RingTheory.RegularLocalRing.Smooth

/-!
# Zariski closedness of order-threshold loci

Over a characteristic-zero field `k`, on a regular ring `R` (`[IsRegularRing R]`, so every
localization `R_p` is regular local) with finitely generated projective Kähler differentials
`Ω[R⁄k]` — in particular on any smooth `k`-algebra or any regular `k`-algebra of finite type —
every order-threshold locus `{p | c ≤ I.orderAt p}` is Zariski closed in `PrimeSpectrum R`:
for `c = n + 1` it is the zero locus of `(Ideal.derivativeIdeal k)^[n] I`, and for `c = ⊤` it is
the intersection of those zero loci over all `n`.

## Main results

Common hypotheses: `k` is a characteristic-zero field and `R` is a regular `k`-algebra
(`[IsRegularRing R]`, derived via `TauCeti.IsRegularRing.of_smooth` in
`Ideal.isClosed_setOf_le_orderAt_of_smooth`).

* `Ideal.setOf_natCast_add_one_le_orderAt_eq_zeroLocus`: assuming `Ω[R⁄k]` is finitely generated
  and projective over `R`, `{p | ((n + 1 : ℕ) : ℕ∞) ≤ I.orderAt p}` equals
  `PrimeSpectrum.zeroLocus ((Ideal.derivativeIdeal k)^[n] I)`.
* `Ideal.isClosed_setOf_le_orderAt`: assuming `Ω[R⁄k]` is finitely generated and projective over
  `R`, `{p | c ≤ I.orderAt p}` is Zariski closed for every `c : ℕ∞`.
* `Ideal.isClosed_setOf_le_orderAt_of_smooth`: Zariski closedness for smooth `k`-algebras.
* `Ideal.isClosed_setOf_le_orderAt_of_finiteType`: Zariski closedness for regular `k`-algebras
  of finite type.

## References

* E. Bierstone and P. D. Milman, *Canonical desingularization in characteristic zero by blowing
  up the maximum strata of a local invariant*, Invent. Math. 128 (1997), §4.1–4.2 and
  Proposition 4.12.
-/

public section

namespace Ideal

section Topology

variable (k : Type*) [Field k] [CharZero k] {R : Type*} [CommRing R] [Algebra k R]

/-- Over a characteristic-zero field, on a regular ring with finitely generated projective
differentials, the order-threshold locus `{p | n + 1 ≤ I.orderAt p}` is the zero locus of the
`n`-th iterated derivative ideal. -/
theorem setOf_natCast_add_one_le_orderAt_eq_zeroLocus [Module.Projective R Ω[R⁄k]]
    [Module.Finite R Ω[R⁄k]] [IsRegularRing R] (I : Ideal R) (n : ℕ) :
    {p : PrimeSpectrum R | ((n + 1 : ℕ) : ℕ∞) ≤ I.orderAt p} =
      PrimeSpectrum.zeroLocus (((derivativeIdeal k)^[n] I) : Set R) := by
  ext p
  simp only [Set.mem_ofPred_eq, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  exact natCast_add_one_le_orderAt_iff_iterate_derivativeIdeal_le k I p n

/-- **Order-threshold loci are Zariski closed.** Over a characteristic-zero field, on a regular
ring with finitely generated projective differentials, `{p | c ≤ I.orderAt p}` is closed in
`PrimeSpectrum R` for every `c : ℕ∞` (including `c = ⊤`). -/
theorem isClosed_setOf_le_orderAt [Module.Projective R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    [IsRegularRing R] (I : Ideal R) (c : ℕ∞) :
    IsClosed {p : PrimeSpectrum R | c ≤ I.orderAt p} := by
  cases c with
  | top =>
    have heq : {p : PrimeSpectrum R | (⊤ : ℕ∞) ≤ I.orderAt p} =
        ⋂ n : ℕ, {p : PrimeSpectrum R | ((n + 1 : ℕ) : ℕ∞) ≤ I.orderAt p} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      refine ⟨fun hp n ↦ le_top.trans hp, fun hp ↦ ENat.forall_natCast_le_iff_le.mp fun n _ ↦ ?_⟩
      exact le_trans (by exact_mod_cast n.le_succ) (hp n)
    rw [heq]
    refine isClosed_iInter fun n ↦ ?_
    rw [setOf_natCast_add_one_le_orderAt_eq_zeroLocus k I n]
    exact PrimeSpectrum.isClosed_zeroLocus _
  | coe d =>
    cases d with
    | zero => simp
    | succ n =>
      rw [setOf_natCast_add_one_le_orderAt_eq_zeroLocus k I n]
      exact PrimeSpectrum.isClosed_zeroLocus _

/-- On a smooth algebra over a characteristic-zero field, every order-threshold locus
`{p | c ≤ I.orderAt p}` is Zariski closed. -/
theorem isClosed_setOf_le_orderAt_of_smooth [Algebra.Smooth k R] (I : Ideal R) (c : ℕ∞) :
    IsClosed {p : PrimeSpectrum R | c ≤ I.orderAt p} := by
  have : IsRegularRing R := TauCeti.IsRegularRing.of_smooth (R := k)
  exact isClosed_setOf_le_orderAt k I c

/-- On a regular algebra of finite type over a characteristic-zero field, every order-threshold
locus `{p | c ≤ I.orderAt p}` is Zariski closed. -/
theorem isClosed_setOf_le_orderAt_of_finiteType [Algebra.FiniteType k R] [IsRegularRing R]
    (I : Ideal R) (c : ℕ∞) :
    IsClosed {p : PrimeSpectrum R | c ≤ I.orderAt p} := by
  have : Algebra.Smooth k R := TauCeti.smooth_of_isRegularRing (k := k)
  exact isClosed_setOf_le_orderAt k I c

end Topology

end Ideal
