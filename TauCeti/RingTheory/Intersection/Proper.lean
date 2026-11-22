/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Intersection.Basic
public import TauCeti.RingTheory.CohenMacaulay.RegularSequence
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Local intersection multiplicities of products of equations

Let `R` be a two-dimensional Cohen–Macaulay Noetherian local ring. If each pair `(f, gᵢ)`
has radical the maximal ideal, then

`length R/(f, ∏ᵢ gᵢ^nᵢ) = ∑ᵢ nᵢ length R/(f, gᵢ)`.

Neither the fixed curve `f = 0` nor any of the curves `gᵢ = 0` is required to be
irreducible or reduced. This gives local additivity, with multiplicities, for Cartier
curves meeting properly on a regular surface, since regular local rings are
Cohen–Macaulay. In particular the fixed curve may itself be a union of special-fibre
components with their multiplicities. This is the local input to additivity of
intersection numbers over effective divisors; no global degree formula is asserted here.

The proper-intersection hypothesis supplies the nonzerodivisors needed by the order of
vanishing API: each pair is a system of parameters, hence a regular sequence. The right-hand
side is cast from a natural number, recording that none of the lengths in the formula is
infinite. Empty products and zero exponents are allowed.

## Main results

* `Module.IsCohenMacaulay.mk_mem_nonZeroDivisors_of_radical_eq`: in a two-dimensional
  Cohen–Macaulay local ring, if `(f, g)` has radical the maximal ideal, then `g` is a
  non-zero-divisor on `R ⧸ (f)`; this uses `Module.IsCohenMacaulay.isRegular_of_le_radical`.
* `TauCeti.length_quotient_span_pair_prod_pow_eq_sum_of_isCohenMacaulay`: the finite formula
  above for proper intersections on a two-dimensional Cohen–Macaulay local ring, deduced from
  the general non-zero-divisor formula
  `TauCeti.length_quotient_span_pair_prod_pow_eq_sum_of_mem_nonZeroDivisors` of
  `TauCeti.RingTheory.Intersection.Basic`.

## References

* J.-P. Serre, *Local Algebra*, Chapter V, §3, local intersection multiplicities and
  additivity.
* The Stacks Project, Proposition 10.103.4 (Tag 00N6), regularity of systems of
  parameters on Cohen–Macaulay modules.
-/

public section

open Ideal IsLocalRing RingTheory.Sequence

namespace Module.IsCohenMacaulay

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **A proper-intersection partner is a non-zero-divisor on the first curve.** In a
two-dimensional Cohen–Macaulay local ring, if `(f, g)` has radical the maximal ideal, then the
image of `g` in `R ⧸ (f)` is a non-zero-divisor. The pair is a system of parameters, hence a
regular sequence by `Module.IsCohenMacaulay.isRegular_of_le_radical`, and its last entry is
left-regular modulo the first by `RingTheory.Sequence.IsWeaklyRegular.isLeftRegular_mk_ofList`.
Neither `f` nor `g` needs to be prime. -/
theorem mk_mem_nonZeroDivisors_of_radical_eq (hR : IsCohenMacaulay R R)
    (hd : ringKrullDim R = 2) {f g : R} (hfg : (span {f, g}).radical = maximalIdeal R) :
    Ideal.Quotient.mk (span {f}) g ∈ nonZeroDivisors (R ⧸ span {f}) := by
  have hle : span {f, g} ≤ maximalIdeal R := (le_radical (I := span {f, g})).trans_eq hfg
  have hann : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hlist : ofList [f, g] = span {f, g} := by
    rw [ofList_cons, ofList_singleton, ← span_insert]
  have hrs : RingTheory.Sequence.IsRegular R [f, g] :=
    hR.isRegular_of_le_radical (rs := [f, g])
      (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hle (subset_span (by simp))
        · exact hle (subset_span (by simp)))
      (by simpa only [hlist, hann, sup_bot_eq] using hfg.ge)
      (by simp [Module.supportDim_self_eq_ringKrullDim, hd])
  have hg := IsWeaklyRegular.isLeftRegular_mk_ofList (rs := [f]) hrs.toIsWeaklyRegular
  rw [ofList_singleton] at hg
  exact isRegular_iff_mem_nonZeroDivisors.mp ((Commute.isRegular_iff fun _ ↦ mul_comm _ _).mpr hg)

end Module.IsCohenMacaulay

namespace TauCeti

section CohenMacaulay

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Local intersection multiplicity is additive over a finite product with arbitrary
nonnegative multiplicities on a two-dimensional Cohen–Macaulay local ring. Every factor
must meet the fixed curve properly, but neither curve needs to be irreducible or reduced.
The right-hand side is a natural number, so the equality also asserts finiteness. -/
theorem length_quotient_span_pair_prod_pow_eq_sum_of_isCohenMacaulay
    (hR : Module.IsCohenMacaulay R R) (hd : ringKrullDim R = 2)
    {ι : Type*} (s : Finset ι) (f : R) (g : ι → R) (n : ι → ℕ)
    (hfg : ∀ i ∈ s, (span {f, g i}).radical = maximalIdeal R) :
    Module.length R (R ⧸ span {f, ∏ i ∈ s, g i ^ n i}) =
      ((∑ i ∈ s, n i * (Module.length R (R ⧸ span {f, g i})).toNat : ℕ) : ℕ∞) := by
  rw [length_quotient_span_pair_prod_pow_eq_sum_of_mem_nonZeroDivisors s f g n
    (fun i hi ↦ hR.mk_mem_nonZeroDivisors_of_radical_eq hd (hfg i hi)), Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_length_quotient_span_pair (hfg i hi)
  rw [hm, ENat.toNat_natCast, nsmul_eq_mul, Nat.cast_mul]

end CohenMacaulay

end TauCeti
