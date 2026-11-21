/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem

/-!
# Prime-to-`p` corollaries of Tate's local Euler characteristic formula

Tate's local Euler characteristic formula for unbundled finite discrete
`AbsoluteGaloisGroup K`-modules (`TauCeti.ClassFieldTheory.natCard_H1_eq_mul`) gives
`#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M) · p ^ ([K : ℚ_p] · v_p(#M))`. This file records the
prime-to-`p` corollaries `#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M)` when `p ∤ #M` or when `M` is
killed by `n` with `p ∤ n`.

## Main results

* `TauCeti.ClassFieldTheory.natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd`:
  `#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M)` when `p ∤ #M`.
* `TauCeti.ClassFieldTheory.natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd_exponent`:
  `#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M)` when `M` is killed by `n` with `p ∤ n`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable (p : ℕ) [Fact p.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [FinitePadicExtension K p]

/-- **Prime-to-`p` local Euler characteristic on explicit cohomology (by order).** For any finite
discrete `G_K`-module `M` over a finite extension `K` of `ℚ_p` with `p ∤ #M`,
`#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M)`. -/
theorem natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hpM : ¬ p ∣ Nat.card M) :
    Nat.card (H1 (AbsoluteGaloisGroup K) M) =
      Nat.card (H0 (AbsoluteGaloisGroup K) M) * Nat.card (H2 (AbsoluteGaloisGroup K) M) := by
  rw [natCard_H1_eq_mul p K M, Nat.padicValNat_def,
    multiplicity_eq_zero_of_not_dvd hpM, mul_zero, pow_zero, mul_one]

/-- **Prime-to-`p` local Euler characteristic on explicit cohomology (by exponent).** If `M` is a
finite discrete `G_K`-module over a finite extension `K` of `ℚ_p` killed by `n` with `p ∤ n`, then
`#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M)`. -/
theorem natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd_exponent {n : ℕ} (hpn : ¬ p ∣ n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    Nat.card (H1 (AbsoluteGaloisGroup K) M) =
      Nat.card (H0 (AbsoluteGaloisGroup K) M) * Nat.card (H2 (AbsoluteGaloisGroup K) M) := by
  refine natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd p M fun hpM ↦ ?_
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hpM
  exact hpn (hx ▸ addOrderOf_dvd_of_nsmul_eq_zero (hM x))

end TauCeti.ClassFieldTheory
