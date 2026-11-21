/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.Power
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit.FiniteSupport

/-!
# Roots of a finitely generated subgroup of `Kˣ`

Let `R` be a Dedekind domain whose unit group is finitely generated, with fraction field `K`;
the ring of integers of a number field is the motivating case. For a finitely generated subgroup
`Γ` of `Kˣ`, a single exponent `u ≠ 0` brings back into `Γ` every element of `Kˣ` having a nonzero
power in `Γ`. The reason is that `Γ` lies in the `S`-units for a finite set `S` of primes, an
element with a nonzero power in the `S`-units is itself an `S`-unit, and the `S`-units are finitely
generated, so the classes of these elements form the finite torsion subgroup of a finitely
generated abelian group. Without finite generation of `Rˣ` this fails: over `R = K = ℂ` the subgroup
`Γ = 1` has roots of unity of every order.

Consequently, to show that `x ∈ Γ` is the `n`-th power of an element of `Γ`, it suffices to show
that `x` is an `n * u`-th power in `Kˣ`. This is the first reduction in Chevalley's proof that
powers in a finitely generated subgroup of the multiplicative group of a number field are detected
by congruences: it trades `n`-th powers in `Γ` for `n * u`-th powers in the field, where local and
Galois-theoretic arguments apply.

## Main results

* `Subgroup.FG.exists_pow_mem_of_pow_mem`: there is `u ≠ 0` with `y ^ u ∈ Γ` for every `y : Kˣ`
  having a nonzero power in `Γ`.
* `Subgroup.FG.exists_pow_eq_of_pow_mul_eq`: there is `u ≠ 0` such that every `x ∈ Γ` that is an
  `n * u`-th power in `Kˣ` is the `n`-th power of an element of `Γ`.

## References

* C. Chevalley, *Deux théorèmes d'arithmétique*, J. Math. Soc. Japan **3** (1951), 36–44,
  Théorème 1 and the reduction at the start of its proof.
-/

public section

open IsDedekindDomain

namespace Subgroup.FG

variable (R : Type*) {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Monoid.FG Rˣ]

-- `R` enters the statements only through `Monoid.FG Rˣ` and the fraction-field structure on `K`
include R

/-- **The roots of a finitely generated subgroup of `Kˣ` have bounded exponent over it.** If `Rˣ`
is finitely generated and `Γ ≤ Kˣ` is finitely generated, there is a single `u ≠ 0` such that
`y ^ u ∈ Γ` for every `y : Kˣ` with a nonzero power in `Γ`. -/
theorem exists_pow_mem_of_pow_mem {Γ : Subgroup Kˣ} (hΓ : Γ.FG) :
    ∃ u ≠ 0, ∀ y : Kˣ, ∀ a ≠ 0, y ^ a ∈ Γ → y ^ u ∈ Γ := by
  obtain ⟨S, hS⟩ := exists_finset_le_unit R hΓ
  obtain ⟨u, hu, h⟩ := (fg_of_le_unit
    (le_refl ((S : Set (HeightOneSpectrum R)).unit K))).exists_pow_mem_of_mem_of_pow_mem Γ
  exact ⟨u, hu, fun y a ha hy ↦ h y ((Set.pow_mem_unit_iff _ K ha).mp (hS hy)) a ha hy⟩

/-- **Powers in a finitely generated subgroup of `Kˣ` are detected by powers in `Kˣ`.** If `Rˣ` is
finitely generated and `Γ ≤ Kˣ` is finitely generated, there is `u ≠ 0` such that, for every `n`,
an element of `Γ` that is an `n * u`-th power in `Kˣ` is the `n`-th power of an element of `Γ`. -/
theorem exists_pow_eq_of_pow_mul_eq {Γ : Subgroup Kˣ} (hΓ : Γ.FG) :
    ∃ u ≠ 0, ∀ n : ℕ, ∀ x ∈ Γ, (∃ y : Kˣ, y ^ (n * u) = x) → ∃ z ∈ Γ, z ^ n = x := by
  obtain ⟨u, hu, h⟩ := exists_pow_mem_of_pow_mem R hΓ
  refine ⟨u, hu, fun n x hx ⟨y, hy⟩ ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨1, one_mem Γ, by rw [← hy, zero_mul, pow_zero, pow_zero]⟩
  · exact ⟨y ^ u, h y (n * u) (mul_ne_zero hn hu) (hy ▸ hx), by rw [← pow_mul, mul_comm, hy]⟩

end Subgroup.FG
