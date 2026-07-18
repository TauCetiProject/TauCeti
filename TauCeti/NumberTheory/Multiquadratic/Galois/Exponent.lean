/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Exponent
public import TauCeti.NumberTheory.Multiquadratic.Galois.Group

/-!
# The Galois group of a multiquadratic field has exponent two

Over a field `K` in which `2 ≠ 0`, a multiquadratic field `M = K(rootᵢ : i)` (with
`rootᵢ ^ 2 = dᵢ ∈ K`) is Galois, and every automorphism sends each generator to `± rootᵢ`; applying
such an automorphism twice restores every generator, so it is an involution
(`TauCeti.NumberTheory.Multiquadratic.Galois`, `aut_mul_self_eq_one`). Together with the
commutativity of the group (`aut_commute`) this says `Gal(M/K)` is an **elementary abelian
`2`-group**. This file records that structural fact through the group **exponent**: the exponent
of `Gal(M/K)` divides `2` unconditionally, and equals `2` exactly when the extension is
nontrivial — the case square-class independence over a nonempty index type guarantees.

This is the explicit "exponent-`2`" half of the multiquadratic roadmap's Layer-0 Galois milestone
(`TauCetiRoadmap/Multiquadratic/README.md`, "the `IsGalois` and exponent-2 / abelian facts are the
easy half"). The full `Gal(M/K) ≃ (ℤ/2)ⁿ` isomorphism is
`TauCeti.NumberTheory.Multiquadratic.Galois.Group`; the exponent reading here is the coarse
invariant it refines — an exponent-`2` abelian group is exactly an `𝔽₂`-vector space.

## Main results

* `TauCeti.Multiquadratic.aut_pow_two_eq_one`: every automorphism of `M` squares to the identity.
* `TauCeti.Multiquadratic.orderOf_aut_dvd_two` and
  `TauCeti.Multiquadratic.orderOf_aut_eq_two_of_ne_one`: each automorphism has order dividing `2`,
  and a nontrivial one has order exactly `2`.
* `TauCeti.Multiquadratic.aut_exponent_dvd_two`: `Monoid.exponent (Gal(M/K)) ∣ 2`, no hypothesis
  beyond the radicand equations.
* `TauCeti.Multiquadratic.aut_nontrivial`: under square-class independence over a nonempty index
  type, `Gal(M/K)` is nontrivial.
* `TauCeti.Multiquadratic.aut_exponent_eq_two`: under those hypotheses,
  `Monoid.exponent (Gal(M/K)) = 2`.

## Provenance

The involution and commutativity facts this packages are migrated, with the rest of the
multiquadratic Layer 0, from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where the sign-change
automorphisms of one concrete multiquadratic field were analysed; here the exponent is read off for
an arbitrary such tower.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- **Every automorphism of a multiquadratic field squares to the identity.** Fixing `K` forces the
image of each generator to have the same square as the generator, so applying the automorphism
twice fixes the generators; this is the `pow`-form of `aut_mul_self_eq_one`. -/
theorem aut_pow_two_eq_one (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :
    σ ^ 2 = 1 := by
  rw [pow_two]
  exact aut_mul_self_eq_one hroot σ

/-- **Each automorphism of a multiquadratic field has order dividing two.** -/
theorem orderOf_aut_dvd_two (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :
    orderOf σ ∣ 2 :=
  orderOf_dvd_of_pow_eq_one (aut_pow_two_eq_one hroot σ)

/-- **A nontrivial automorphism of a multiquadratic field has order exactly two.** Its order
divides `2` and is not `1` (which would make it the identity), so it is `2`. -/
theorem orderOf_aut_eq_two_of_ne_one (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    {σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)} (hσ : σ ≠ 1) :
    orderOf σ = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_aut_dvd_two hroot σ) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hσ
  · exact h

/-- **The Galois group of a multiquadratic field has exponent dividing two.** Every automorphism is
an involution, so the group exponent divides `2`. No square-class independence is needed. -/
theorem aut_exponent_dvd_two (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    Monoid.exponent (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) ∣ 2 := by
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  exact fun σ => aut_pow_two_eq_one hroot σ

/-- **A multiquadratic field over a nonempty family of independent radicands has a nontrivial Galois
group.** Transported along the isomorphism `Gal(M/K) ≃ (ℤ/2)^ι`, which is nontrivial because
`ι → ℤ/2` is over a nonempty index type. -/
theorem aut_nontrivial [Finite ι] [NeZero (2 : K)] [Nonempty ι]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    Nontrivial (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :=
  (galoisGroupEquiv hroot hindep).toEquiv.nontrivial

/-- **The Galois group of a nontrivial multiquadratic field has exponent exactly two.** Under
square-class independence over a nonempty index type the exponent divides `2` and is not `1` (the
group is nontrivial), hence equals `2`: `Gal(M/K)` is an elementary abelian `2`-group of positive
rank. -/
theorem aut_exponent_eq_two [Finite ι] [NeZero (2 : K)] [Nonempty ι]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    Monoid.exponent (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) = 2 := by
  haveI := aut_nontrivial hroot hindep
  rcases (Nat.dvd_prime Nat.prime_two).mp (aut_exponent_dvd_two hroot) with h | h
  · rw [Monoid.exp_eq_one_iff] at h
    exact absurd h (not_subsingleton _)
  · exact h

end TauCeti.Multiquadratic
