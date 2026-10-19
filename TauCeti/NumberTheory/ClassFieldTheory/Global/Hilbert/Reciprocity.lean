/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Hilbert.Invariant
public import TauCeti.NumberTheory.ClassFieldTheory.Global.InvariantSum
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.Kummer.Cyclic
import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Compositum
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SecondInequality
import TauCeti.NumberTheory.ClassFieldTheory.Local.CyclicClass

/-!
# Hilbert reciprocity

Let `K` be a number field and `a, b ∈ Kˣ`. Hilbert's reciprocity law says that the local Hilbert
invariants of `a` and `b` at all the places of `K` sum to zero (`hilbertProductFormula`). In its
cohomological form it is the statement that the local invariants of the Brauer class `(a) ∪ (b)`,
the cup product of the Kummer classes of `a` and `b`, sum to zero: by
`finiteInvAt_kummerBrauerClass` and `infiniteInvAt_kummerBrauerClass` these local invariants are
the Hilbert invariants read in `ℚ/ℤ` (`sumLocalInv_brLocalization_kummerBrauerClass`). The local
invariants of every Brauer class of `K` sum to zero once `H¹` of the idele-class formation
vanishes on every layer (`sumLocalInv_brLocalization_eq_zero_of_subsingleton_h1_globalFormation`),
and that vanishing is the companion of the second fundamental inequality
(`subsingleton_h1_globalFormation`).

The file also proves the vanishing of the sum of the local invariants of the Kummer-cup class
`(a) ∪ (b)` of exponent `n` directly from the cyclotomic product formula, whenever an `n`-th root
`s` of `b` lies in a cyclotomic extension of `K`
(`sumLocalInv_brLocalization_kummerBrauerClass_eq_zero_of_mem_adjoin`). The class `(a) ∪ (b)` is
split by the cyclic Kummer extension `K(s)/K`: it is minus the inflation of the cyclic class of `a`
(`kummerBrauerClass_eq_neg_relBrInfl_cyclicClass`). If `K(s)` lies in `K(μ_m)`, the sum of the
local invariants of every class split by `K(s)` vanishes
(`sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_adjoin_nth_roots`), by the product formula
for the local Artin symbols of the cyclotomic extensions.

## Main results

* `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_kummerBrauerClass`: the sum of the local
  invariants of the quadratic Kummer-cup class is the sum of the Hilbert invariants, read in
  `ℚ/ℤ`.
* `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_kummerBrauerClass_eq_zero_of_mem_adjoin`:
  the local invariants of `(a) ∪ (b)` sum to zero when an `n`-th root of `b` lies in a cyclotomic
  extension.
* `TauCeti.ClassFieldTheory.hilbertProductFormula`: Hilbert reciprocity over every number field.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Example 8.2, Lemmas 8.4 and 8.5, and
  Theorem 8.1.
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

/-- **Hilbert reciprocity.** For `a, b ∈ Kˣ`, the Hilbert invariants of `a` and `b` at all the
finite and infinite places of the number field `K` sum to zero. -/
theorem hilbertProductFormula (a b : Kˣ) :
    (∑ v ∈ finiteHilbertSupport K a b, finiteHilbertInvariantAt K v a b) +
        ∑ w : InfinitePlace K, infiniteHilbertInvariantAt K w a b = 0 :=
  ZMod.toRatAddCircle_injective 2 <| by
    rw [← sumLocalInv_brLocalization_kummerBrauerClass, map_zero,
      sumLocalInv_brLocalization_eq_zero_of_subsingleton_h1_globalFormation K
        fun _ _ _ _ _ ↦ subsingleton_h1_globalFormation _]

end TauCeti.ClassFieldTheory
