/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.RingTheory.Ideal.Quotient.Frobenius
public import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Frobenius on quotients of the power-bounded subring

Let `R` be a nonarchimedean topological ring with power-bounded subring `R°`, and let `ϖ ∈ R°`
be a unit of `R`. The Frobenius `R° ⧸ ϖ → R° ⧸ ϖ ^ p`, `[x] ↦ [x ^ p]`, is injective: `R°` is
integrally closed in `R`, so `ϖ ^ p ∣ y ^ p` forces `ϖ ∣ y`. This is the automatic half of the
bijectivity asked of a perfectoid Tate ring.

## Main results

* `TauCeti.Huber.quotientFrobenius_powerBoundedSubring_injective`: the Frobenius
  `R° ⧸ ϖ → R° ⧸ ϖ ^ p` is injective for every `ϖ ∈ R°` that is a unit of `R`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Remarks 3.2–3.3.
-/

public section

open Ideal

namespace TauCeti.Huber

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [TopologicalSpace R]
  [NonarchimedeanAddGroup R] [SeparatelyContinuousMul R]

/-- **Injectivity of the Frobenius `R° ⧸ ϖ → R° ⧸ ϖ ^ p` is automatic** for every `ϖ ∈ R°` that is
a unit of `R`: the power-bounded subring is integrally closed in `R`. -/
theorem quotientFrobenius_powerBoundedSubring_injective {ϖ : powerBoundedSubring R}
    (hϖ : IsUnit (ϖ : R)) (hp : (p : powerBoundedSubring R) ∈ span {ϖ ^ p})
    (hpow : ∀ x ∈ span {ϖ}, x ^ p ∈ span {ϖ ^ p}) :
    Function.Injective (quotientFrobenius (span {ϖ}) (span {ϖ ^ p}) p hp hpow) := by
  rw [quotientFrobenius_injective_iff]
  intro y hy
  rw [mem_span_singleton] at hy ⊢
  exact (IsIntegrallyClosedIn.pow_dvd_pow_iff (Fact.out : p.Prime).ne_zero hϖ).mp hy

end TauCeti.Huber
