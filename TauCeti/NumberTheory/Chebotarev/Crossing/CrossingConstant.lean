/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Crossing.TaggedCount
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.NumberTheory.Chebotarev.AuxiliaryPrime

/-!
# The crossing constant of an auxiliary cyclic group

The cyclotomic crossing bounds the density of a Frobenius fibre from below by a quantity built
from one auxiliary prime: the proportion of the auxiliary cyclic group `H` taken up by the tags —
the elements whose order is divisible by the residue degree `f` — divided in addition by the order
of `Aut_K(L)`.  Equivalently it is the proportion of `Aut_K(L) × H` represented by one
automorphism paired with the tags.  This file defines that quantity, `crossingConstant`, and
bounds it below.

What the bound provides is uniformity: it depends on `f` only through the number of primes
dividing `f`, and on the auxiliary group only through the level `r` in `f ^ r ∣ #H`. Raising `r`
therefore pushes the crossing constant of every cyclic group of that level towards
`1 / #Aut_K(L)`, uniformly in the group; the file closes with this limit, in the form a consumer
choosing one auxiliary group per target value needs.

## Main definitions

* `TauCeti.NumberField.Chebotarev.crossingConstant`: the tag proportion in `H`, divided by the
  order of `Aut_K(L)`.

## Main results

* `TauCeti.NumberField.Chebotarev.crossingConstant_nonneg`: the constant is nonnegative.
* `TauCeti.NumberField.Chebotarev.le_crossingConstant`: once `f ^ r` divides `#H`, the crossing
  constant is at least `(1 - 2 ^ (-r)) ^ #f.primeFactors` divided by the order of `Aut_K(L)`.
* `TauCeti.NumberField.Chebotarev.exists_forall_lt_crossingConstant`: as the level `r` grows, that
  bound tends to `1 / #Aut_K(L)`, so every `δ < 1 / #Aut_K(L)` lies below the crossing constant of
  every cyclic group whose order is divisible by `f ^ r`, for a single `r`.
* `TauCeti.NumberField.Chebotarev.exists_prime_coprime_lt_crossingConstant`: for number fields,
  that level is realised by `(ZMod q)ˣ` for a prime `q` coprime to the discriminant of `L`, the
  auxiliary prime of the cyclotomic crossing.

## References

The crossing construction follows R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
-/

public section

namespace TauCeti.NumberField.Chebotarev

open Finset Filter
open scoped Topology

variable (K L : Type*) [CommSemiring K] [Semiring L] [Algebra K L]
variable {H : Type*} [Group H] [Fintype H]

/-- **The crossing constant.**  The number of tagged elements of the auxiliary cyclic group `H` —
those whose order is divisible by `f` — divided by `#Aut_K(L) * #H`.

That is the tag proportion within `H`, divided in addition by the order of `Aut_K(L)`, which
enters only through its order: the denominator that turns a count of tags into the density
contributed by one auxiliary prime. -/
noncomputable def crossingConstant (f : ℕ) : ℝ :=
  ((taggedElements (H := H) f).card : ℝ) /
    ((Nat.card (L ≃ₐ[K] L) : ℝ) * (Nat.card H : ℝ))

/-- **The crossing constant, written out.**  The characteristic rewrite: a consumer uses this
rather than unfolding the definition.

Deliberately not a `simp` lemma.  `crossingConstant` is itself the normal form — the bound
`le_crossingConstant` is stated in terms of it, so unfolding it on sight would dissolve the
conclusion a consumer is trying to apply. -/
theorem crossingConstant_def (f : ℕ) : crossingConstant K L (H := H) f =
    ((taggedElements (H := H) f).card : ℝ) /
      ((Nat.card (L ≃ₐ[K] L) : ℝ) * (Nat.card H : ℝ)) :=
  (rfl)

/-- **The crossing constant is nonnegative.**  It is a ratio of cardinalities, so a consumer
squeezing a density between bounds gets this without unfolding the definition. -/
theorem crossingConstant_nonneg (f : ℕ) : 0 ≤ crossingConstant K L (H := H) f := by
  rw [crossingConstant_def]
  positivity

/-- **The lower bound for the crossing constant.**  When `f ^ r` divides the order of the cyclic
auxiliary group `H`, the crossing constant is at least `(1 - 2 ^ (-r)) ^ #f.primeFactors` divided
by the order of `Aut_K(L)`.  The bound no longer mentions `#H`: the auxiliary group enters only
through the level `r`.

`Aut_K(L)` is not assumed finite; when it is infinite both sides are `0`. -/
theorem le_crossingConstant [IsCyclic H] (f r : ℕ) (hrpos : 0 < r) (hf : f ^ r ∣ Nat.card H) :
    (1 - (2 : ℝ) ^ (-(r : ℤ))) ^ f.primeFactors.card / (Nat.card (L ≃ₐ[K] L) : ℝ) ≤
      crossingConstant K L (H := H) f := by
  rw [crossingConstant_def, div_mul_eq_div_div_swap]
  gcongr
  exact (le_div_iff₀ (mod_cast Nat.card_pos)).mpr <| le_card_taggedElements_cyclic f r hrpos hf

/-- **The crossing constant approaches `1 / #Aut_K(L)`.**  For every `δ < 1 / #Aut_K(L)` there is
a level `r` such that the crossing constant of every cyclic group whose order is divisible by
`f ^ r` exceeds `δ`.

The level depends only on `δ`, `f` and the order of `Aut_K(L)`, not on the cyclic group, so a
consumer that can choose an auxiliary group of any level pushes the crossing bound arbitrarily
close to `1 / #Aut_K(L)`. -/
theorem exists_forall_lt_crossingConstant (f : ℕ) {δ : ℝ}
    (hδ : δ < 1 / (Nat.card (L ≃ₐ[K] L) : ℝ)) :
    ∃ r : ℕ, ∀ (H : Type*) [Group H] [Fintype H] [IsCyclic H], f ^ r ∣ Nat.card H →
      δ < crossingConstant K L (H := H) f := by
  -- The bound of `le_crossingConstant` tends to `1 / #Aut_K(L)` as the level grows.
  have h2 : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ (-(r : ℤ))) atTop (𝓝 0) := by
    simpa [zpow_neg, zpow_natCast, inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).sub h2).pow
    f.primeFactors.card).div_const (Nat.card (L ≃ₐ[K] L) : ℝ)
  rw [sub_zero, one_pow] at hlim
  obtain ⟨r, hr, hδr⟩ := ((eventually_gt_atTop 0).and (hlim.eventually (lt_mem_nhds hδ))).exists
  exact ⟨r, fun H _ _ _ hf ↦ hδr.trans_le (le_crossingConstant K L f r hr hf)⟩

section NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **An auxiliary prime with a large crossing constant.**  For every `δ < 1 / #Aut_K(L)` and every
`f ≠ 0` there is a prime `q`, coprime to the discriminant of `L`, such that the crossing constant of
`(ZMod q)ˣ` at `f` exceeds `δ`.

Coprimality to the discriminant is what the joint restriction
`IsCyclotomicExtension.galEquivProd` needs to split the Galois group of `L(μ_q) / K` as
`Aut_K(L) × (ZMod q)ˣ`. -/
theorem exists_prime_coprime_lt_crossingConstant {f : ℕ} (hf : f ≠ 0) {δ : ℝ}
    (hδ : δ < 1 / (Nat.card (L ≃ₐ[K] L) : ℝ)) :
    ∃ q : ℕ, ∃ _ : Fact q.Prime, (NumberField.discr L).natAbs.Coprime q ∧
      δ < crossingConstant K L (H := (ZMod q)ˣ) f := by
  -- Choose the level first, then an auxiliary prime of that level larger than `|disc L|`.
  obtain ⟨r, hr⟩ := exists_forall_lt_crossingConstant K L f hδ
  obtain ⟨q, hq, hqN, -, hfq, -, -, -⟩ :=
    NumberField.exists_auxiliaryPrime K L (f ^ r) (NumberField.discr L).natAbs (pow_ne_zero r hf)
  have : Fact q.Prime := ⟨hq⟩
  refine ⟨q, this, (Nat.coprime_of_lt_prime (Int.natAbs_ne_zero.mpr
    (NumberField.discr_ne_zero L)) hqN hq).symm, hr _ ?_⟩
  rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]

end NumberField

end TauCeti.NumberField.Chebotarev
