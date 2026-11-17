/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Intersection.Basic
public import TauCeti.RingTheory.CohenMacaulay.RegularSequence
import TauCeti.RingTheory.OrderOfVanishing

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
* `TauCeti.length_quotient_span_pair_prod_pow_eq_sum_of_mem_nonZeroDivisors`: in any commutative
  ring, the possibly infinite length `length R/(f, ∏ᵢ gᵢ^nᵢ)` is `∑ᵢ nᵢ • length R/(f, gᵢ)` when
  each `gᵢ` is a non-zero-divisor on `R ⧸ (f)`, by Mathlib's `Ring.ord_pow` and the
  finite-product order formula `TauCeti.Ring.ord_prod`.
* `TauCeti.length_quotient_span_pair_prod_pow_eq_sum_of_isCohenMacaulay`: the finite formula
  above for proper intersections on a two-dimensional Cohen–Macaulay local ring.

## References

* J.-P. Serre, *Local Algebra*, Chapter V, §3, local intersection multiplicities and
  additivity.
* The Stacks Project, Proposition 10.103.4 (Tag 00N6), regularity of systems of
  parameters on Cohen–Macaulay modules.
-/

public section

open Ideal IsLocalRing RingTheory.Sequence
open scoped Pointwise

namespace Module.IsCohenMacaulay

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **A proper-intersection partner is a non-zero-divisor on the first curve.** In a
two-dimensional Cohen–Macaulay local ring, if `(f, g)` has radical the maximal ideal, then the
image of `g` in `R ⧸ (f)` is a non-zero-divisor. The pair is a system of parameters, hence a
regular sequence by `Module.IsCohenMacaulay.isRegular_of_le_radical`; regularity of `g` on
`QuotSMulTop f R`, the quotient by the scalar submodule `f • ⊤`, is then transported to
`R ⧸ (f)` along the equality `f • ⊤ = (f)`. Neither `f` nor `g` needs to be prime. -/
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
  have hg := (isRegular_cons_iff R f [g]).mp hrs
  have hg' := (isWeaklyRegular_singleton_iff (QuotSMulTop f R) g).mp hg.2.toIsWeaklyRegular
  -- `QuotSMulTop f R` uses the scalar submodule `f • ⊤`; the order API uses `(f)`.
  have heq : f • (⊤ : Submodule R R) = span {f} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top]
  have hg'' : IsSMulRegular (R ⧸ span {f}) g :=
    ((Submodule.quotEquivOfEq _ _ heq).isSMulRegular_congr g).mp hg'
  exact (isRegular_iff_mem_nonZeroDivisors).mp
    ((Commute.isRegular_iff (fun _ ↦ mul_comm _ _)).mpr
      ((isSMulRegular_algebraMap_iff (R ⧸ span {f})).mpr hg'').isLeftRegular)

end Module.IsCohenMacaulay

namespace TauCeti

section Quotient

variable {R : Type*} [CommRing R]

/-- **The length of the quotient by an equation and a finite product of powers is the weighted
sum of the lengths.** If the image of each `gᵢ` in `R ⧸ (f)` is a non-zero-divisor, then
`length R/(f, ∏ᵢ gᵢ^nᵢ) = ∑ᵢ nᵢ • length R/(f, gᵢ)`. This is the n-ary form of
`TauCeti.length_quotient_span_pair_mul_eq_add_of_mem_nonZeroDivisors`: no hypothesis on `R`
beyond commutativity is placed and no finiteness is assumed, so the lengths may be infinite. -/
theorem length_quotient_span_pair_prod_pow_eq_sum_of_mem_nonZeroDivisors
    {ι : Type*} (s : Finset ι) (f : R) (g : ι → R) (n : ι → ℕ)
    (hg : ∀ i ∈ s, Ideal.Quotient.mk (span {f}) (g i) ∈ nonZeroDivisors (R ⧸ span {f})) :
    Module.length R (R ⧸ span {f, ∏ i ∈ s, g i ^ n i}) =
      ∑ i ∈ s, n i • Module.length R (R ⧸ span {f, g i}) := by
  rw [← ord_eq_length_quotient_span_pair, map_prod]
  simp_rw [map_pow]
  rw [Ring.ord_prod (fun i hi ↦ pow_mem (hg i hi) _)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [_root_.Ring.ord_pow (hg i hi), ord_eq_length_quotient_span_pair]

end Quotient

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
