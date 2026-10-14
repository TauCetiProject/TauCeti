/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Hilbert.Invariant
public import TauCeti.NumberTheory.ClassFieldTheory.Global.InvariantSum
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.Kummer.Cyclic
import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Compositum
import TauCeti.NumberTheory.ClassFieldTheory.Local.CyclicClass
import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.Embedding

/-!
# Hilbert reciprocity for cyclotomic radicands

Let `K` be a number field and `a, b ∈ Kˣ`. Hilbert's reciprocity law says that the local Hilbert
invariants of `a` and `b` at all the places of `K` sum to zero. In its cohomological form it is
the statement that the local invariants of the Brauer class `(a) ∪ (b)`, the cup product of the
Kummer classes of `a` and `b`, sum to zero: by `finiteInvAt_kummerBrauerClass` and
`infiniteInvAt_kummerBrauerClass` these local invariants are the Hilbert invariants read in
`ℚ/ℤ` (`sumLocalInv_brLocalization_kummerBrauerClass`).

This file proves that law whenever a square root of `b` lies in a cyclotomic extension of `K`
(`hilbertProductFormula_of_mem_adjoin`), and more generally the vanishing of the sum of the local
invariants of the Kummer-cup class `(a) ∪ (b)` of exponent `n` whenever an `n`-th root `s` of `b`
does (`sumLocalInv_brLocalization_kummerBrauerClass_eq_zero_of_mem_adjoin`). The class
`(a) ∪ (b)` is split by the cyclic Kummer extension `K(s)/K`: it is minus the inflation of the
cyclic class of `a` (`kummerBrauerClass_eq_neg_relBrInfl_cyclicClass`). If `K(s)` lies in
`K(μ_m)`, the sum of the local invariants of every class split by `K(s)` vanishes
(`sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_adjoin_nth_roots`), by the product formula
for the local Artin symbols of the cyclotomic extensions.

Every square root of a rational number lies in a cyclotomic field
(`TauCeti.Multiquadratic.mem_of_sq_eq_ratCast`). So the law holds over every number field for a
rational radicand `b` (`hilbertProductFormula_of_coe_eq_ratCast`), and in particular for all
`a, b ∈ ℚˣ` (`hilbertProductFormula_rat`), which is Hilbert's reciprocity law over `ℚ`.

## Main results

* `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_kummerBrauerClass`: the sum of the local
  invariants of the quadratic Kummer-cup class is the sum of the Hilbert invariants, read in
  `ℚ/ℤ`.
* `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_kummerBrauerClass_eq_zero_of_mem_adjoin`:
  the local invariants of `(a) ∪ (b)` sum to zero when an `n`-th root of `b` lies in a cyclotomic
  extension.
* `TauCeti.ClassFieldTheory.hilbertProductFormula_of_mem_adjoin`: Hilbert reciprocity when a
  square root of `b` lies in a cyclotomic extension.
* `TauCeti.ClassFieldTheory.hilbertProductFormula_of_coe_eq_ratCast`: Hilbert reciprocity for a
  rational radicand `b`.
* `TauCeti.ClassFieldTheory.hilbertProductFormula_rat`: Hilbert reciprocity over `ℚ`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Example 8.2, Lemmas 8.4 and 8.5.
* J. Neukirch, *Algebraic Number Theory*, Springer (1999), Chapter VI, §8.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter III, §2, Theorem 3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.NumberField _root_.IntermediateField

variable {K : Type} [Field K] [NumberField K]

/-- **The sum of the local invariants of the quadratic Kummer-cup class is the sum of the Hilbert
invariants.** For `a, b ∈ Kˣ`, the sum of the local invariants of the Brauer class `(a) ∪ (b)`
over all places of `K` is the sum of the Hilbert invariants of `a` and `b`, read in `ℚ/ℤ` through
`k ↦ k/2`. -/
theorem sumLocalInv_brLocalization_kummerBrauerClass (a b : Kˣ) :
    sumLocalInv K (brLocalization K (kummerBrauerClass (-1) (.neg_one 0 (by decide)) a b)) =
      ZMod.toRatAddCircle 2 ((∑ v ∈ finiteHilbertSupport K a b, finiteHilbertInvariantAt K v a b) +
        ∑ w : InfinitePlace K, infiniteHilbertInvariantAt K w a b) := by
  rw [sumLocalInv_brLocalization K _ (S := finiteHilbertSupport K a b) fun v hv ↦ ?_, map_add,
    map_sum, map_sum]
  · simp only [finiteInvAt_kummerBrauerClass, infiniteInvAt_kummerBrauerClass]
  · rw [mem_brauerSupport, finiteInvAt_kummerBrauerClass] at hv
    exact (mem_finiteHilbertSupport K).2 fun h ↦ hv (by rw [h, map_zero])

/-- **The product formula for a Kummer-cup class with a cyclotomic radicand.** Let `ζ ∈ K` be a
primitive `n`-th root of unity and `a, b ∈ Kˣ`. If some `n`-th root `s` of `b` in `Kˢ` lies in the
cyclotomic extension `K(μ_m)` for some `m ≠ 0`, then the local invariants of the Brauer class
`(a) ∪ (b)` sum to zero. -/
theorem sumLocalInv_brLocalization_kummerBrauerClass_eq_zero_of_mem_adjoin {n : ℕ} [NeZero n]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (a b : Kˣ) {s : SeparableClosure K}
    (hs : s ^ n = algebraMap K (SeparableClosure K) b) {m : ℕ} (hm : m ≠ 0)
    (hsm : s ∈ adjoin K {x : SeparableClosure K | x ^ m = 1}) :
    sumLocalInv K (brLocalization K (kummerBrauerClass ζ hζ a b)) = 0 := by
  -- `E = K(s)` is a cyclic Kummer extension of `K` inside `K(μ_m)`, and it splits `(a) ∪ (b)`.
  set E := K⟮s⟯
  have ht : AdjoinSimple.gen K s ^ n = algebraMap K E b :=
    Subtype.ext <| by
      simpa only [SubmonoidClass.coe_pow, AdjoinSimple.coe_gen, coe_algebraMap_apply] using hs
  have hgen : K⟮AdjoinSimple.gen K s⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top s
  have : FiniteDimensional K E := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  have := isGalois_of_pow_eq_of_adjoin_eq_top hζ b.ne_zero ht hgen
  obtain ⟨g, hg, hd, hgs⟩ := exists_forall_mem_zpowers_apply_eq hζ b.ne_zero ht hgen
  have : IsCyclic Gal(E/K) := ⟨⟨g, hg⟩⟩
  rw [kummerBrauerClass_eq_neg_relBrInfl_cyclicClass hζ a b ht hg hd hgs E.val, map_neg, map_neg,
    sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_adjoin_nth_roots E hm
      (adjoin_simple_le_iff.2 hsm), neg_zero]

/-- **Hilbert reciprocity for a cyclotomic radicand.** For `a, b ∈ Kˣ`, if some square root of `b`
in `Kˢ` lies in the cyclotomic extension `K(μ_m)` for some `m ≠ 0`, then the Hilbert invariants of
`a` and `b` at all the finite and infinite places of `K` sum to zero. -/
theorem hilbertProductFormula_of_mem_adjoin (a b : Kˣ) {s : SeparableClosure K}
    (hs : s ^ 2 = algebraMap K (SeparableClosure K) b) {m : ℕ} (hm : m ≠ 0)
    (hsm : s ∈ adjoin K {x : SeparableClosure K | x ^ m = 1}) :
    (∑ v ∈ finiteHilbertSupport K a b, finiteHilbertInvariantAt K v a b) +
        ∑ w : InfinitePlace K, infiniteHilbertInvariantAt K w a b = 0 :=
  ZMod.toRatAddCircle_injective 2 <| by
    rw [← sumLocalInv_brLocalization_kummerBrauerClass, map_zero,
      sumLocalInv_brLocalization_kummerBrauerClass_eq_zero_of_mem_adjoin _ a b hs hm hsm]

/-- **Hilbert reciprocity for a rational radicand.** For `a, b ∈ Kˣ` with `b` rational, the Hilbert
invariants of `a` and `b` at all the finite and infinite places of `K` sum to zero. -/
theorem hilbertProductFormula_of_coe_eq_ratCast (a b : Kˣ) {q : ℚ} (hb : (b : K) = q) :
    (∑ v ∈ finiteHilbertSupport K a b, finiteHilbertInvariantAt K v a b) +
        ∑ w : InfinitePlace K, infiniteHilbertInvariantAt K w a b = 0 := by
  have hq : q ≠ 0 := by
    rintro rfl
    exact b.ne_zero (hb.trans Rat.cast_zero)
  set N := 4 * (q.num * q.den).natAbs
  have hN : 0 < N := Nat.mul_pos (by decide) (Int.natAbs_pos.2
    (mul_ne_zero (Rat.num_ne_zero.2 hq) (Int.natCast_ne_zero.2 q.den_nz)))
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure K) N
  obtain ⟨s, hs⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K (SeparableClosure K) b) 2
  have hsq : s ^ 2 = (q : SeparableClosure K) := by rw [hs, hb, map_ratCast]
  refine hilbertProductFormula_of_mem_adjoin a b hs hN.ne' ?_
  -- `s` lies in `K(μ_N)` read as a field over `ℚ`.
  exact Multiquadratic.mem_of_sq_eq_ratCast (F := (adjoin K _).restrictScalars ℚ) hN hζ
    (subset_adjoin K {x : SeparableClosure K | x ^ N = 1} hζ.pow_eq_one) dvd_rfl hsq

/-- **Hilbert reciprocity over `ℚ`.** For `a, b ∈ ℚˣ`, the Hilbert invariants of `a` and `b` at all
the primes and at the real place sum to zero. -/
theorem hilbertProductFormula_rat (a b : ℚˣ) :
    (∑ v ∈ finiteHilbertSupport ℚ a b, finiteHilbertInvariantAt ℚ v a b) +
        ∑ w : InfinitePlace ℚ, infiniteHilbertInvariantAt ℚ w a b = 0 :=
  hilbertProductFormula_of_coe_eq_ratCast a b (Rat.cast_id _).symm

end TauCeti.ClassFieldTheory
