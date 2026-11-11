/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monomial
public import TauCeti.AlgebraicTopology.Singular.Triple.Finrank
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import TauCeti.Algebra.Homology.EulerCharacteristic.MorseInequalities

/-!
# Milnor's inequalities along a filtration of a space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, and let `V` be
a module over a division ring `k`. For `a ≤ b`, compare the relative singular homology of the pair
`(X b, X a)` with that of the steps `(X (q + 1), X q)`, `a ≤ q < b`. Write
`bᵢ = dim Hᵢ(X b, X a; V)` and `cᵢ = ∑_{a ≤ q < b} dim Hᵢ(X (q + 1), X q; V)`. Then:

* **weak inequalities**: if the homology of the steps is finite-dimensional in degree `n`, so is
  `Hₙ(X b, X a)`, and `bₙ ≤ cₙ`
  (`Monotone.finite_singularHomology_ofInclusion_of_forall_mem_Ico` and
  `Monotone.finrank_singularHomology_ofInclusion_le_sum`);
* **strong inequalities**: if the homology of the steps is finite-dimensional in degrees `≤ n`,
  then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`
  (`Monotone.sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_le`);
* **Euler's equality**: if moreover `Hₙ₊₁` of every step vanishes, then
  `∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = ∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ`
  (`Monotone.sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_eq`);
* **the polynomial identity**: under the same hypotheses,
  `∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with natural number
  coefficients, the coefficient of `tⁱ` being the gap in the `i`-th strong inequality for
  `i < n` and zero for `i ≥ n`
  (`Monotone.exists_sum_range_monomial_singularHomology_ofInclusion_eq_add_mul`);
* **the lacunary principle**: if no two consecutive `cᵢ` are both nonzero, then `bᵢ = cᵢ` for
  every `i` (`Monotone.finrank_singularHomology_ofInclusion_eq_sum_of_eq_zero_or`).

The proof is Milnor's. The long exact sequence of the triple `(X (q + 1), X q, X a)` makes
dimensions and alternating sums subadditive
(`TauCeti.TopTriple.finrank_singularHomology_totalPair_le` and
`TauCeti.TopTriple.sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_le`), and the
signed sums additive in degree `n` when `Hₙ₊₁(X (q + 1), X q)` vanishes; induction on `b` adds
one step at a time. The polynomial identity and the lacunary principle are the numerical
consequences `TauCeti.exists_sum_range_monomial_eq_add_mul` and
`TauCeti.eq_of_forall_sum_range_neg_one_pow_mul_le` of these.

Applied to the sublevels `X q = {f ≤ a q}` of a function `f` cut at an increasing sequence of
values `a q`, these are the Morse inequalities, with `cᵢ` collecting the contributions of the
bands `f⁻¹[a q, a (q + 1)]`. For a Morse function a band containing one critical value has the
relative homology of one `i`-cell for each critical point of index `i` in it. For a Morse–Bott
function it has that of the negative disc bundles of its critical submanifolds, by Bott's
theorem; with these contributions the statements above are the Morse–Bott inequalities.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

noncomputable section

open CategoryTheory Limits Module
open Polynomial (monomial)
open scoped Polynomial

universe w

variable {Y : TopCat.{w}} {X : ℤ → Set Y} (hX : Monotone X) {k : Type*} [DivisionRing k]
  (V : ModuleCat.{w} k)

namespace TauCeti

/-- The triple `(X (b + 1), X b, X a)` of a filtration, for `a ≤ b`. Its inner, outer and total
pairs are, by definition of `TopTriple.ofInclusions`, the pairs `TopPair.ofInclusion` of
`X a ⊆ X b`, `X b ⊆ X (b + 1)` and `X a ⊆ X (b + 1)`; the proofs below pass finiteness and
dimensions between the two descriptions. -/
private abbrev stepTriple {a b : ℤ} (hab : a ≤ b) : TopTriple.{w} :=
  TopTriple.ofInclusions (hX hab) (hX (lt_add_one b).le)

end TauCeti

namespace Monotone

open TauCeti

/-- **Finiteness along a filtration.** If the steps `(X (q + 1), X q)`, `a ≤ q < b`, have
finite-dimensional relative homology in degree `n`, so does `(X b, X a)`. -/
theorem finite_singularHomology_ofInclusion_of_forall_mem_Ico {a b : ℤ} (hab : a ≤ b) (n : ℕ)
    (h : ∀ q ∈ Finset.Ico a b, Module.Finite k
      ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V n : ModuleCat k)) :
    Module.Finite k ((TopPair.ofInclusion (hX hab)).singularHomology V n : ModuleCat k) := by
  induction b, hab using Int.leInduction with
  | base =>
    have := ModuleCat.isZero_iff_subsingleton.1
      (TopPair.isZero_singularHomology_ofInclusion_self V (X a) n)
    infer_instance
  | succ b hab ih =>
    have : Module.Finite k ((TopTriple.innerPair.obj (stepTriple hX hab)).singularHomology V n :
        ModuleCat k) := ih fun q hq ↦ h q (Finset.Ico_subset_Ico_right (lt_add_one b).le hq)
    have : Module.Finite k ((TopTriple.outerPair.obj (stepTriple hX hab)).singularHomology V n :
        ModuleCat k) := h b (Finset.mem_Ico.2 ⟨hab, lt_add_one b⟩)
    exact (stepTriple hX hab).finite_singularHomology_totalPair V n

/-- **The weak inequalities along a filtration.** If the steps `(X (q + 1), X q)`, `a ≤ q < b`,
have finite-dimensional relative homology in degree `n`, the dimension of `Hₙ(X b, X a)` is at
most the sum of the dimensions of the `Hₙ(X (q + 1), X q)`. -/
theorem finrank_singularHomology_ofInclusion_le_sum {a b : ℤ} (hab : a ≤ b) (n : ℕ)
    (h : ∀ q ∈ Finset.Ico a b, Module.Finite k
      ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V n : ModuleCat k)) :
    finrank k ((TopPair.ofInclusion (hX hab)).singularHomology V n : ModuleCat k) ≤
      ∑ q ∈ Finset.Ico a b,
        finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V n :
          ModuleCat k) := by
  induction b, hab using Int.leInduction with
  | base =>
    have := ModuleCat.isZero_iff_subsingleton.1
      (TopPair.isZero_singularHomology_ofInclusion_self V (X a) n)
    simp [finrank_zero_of_subsingleton]
  | succ b hab ih =>
    have h' : ∀ q ∈ Finset.Ico a b, Module.Finite k
        ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V n : ModuleCat k) :=
      fun q hq ↦ h q (Finset.Ico_subset_Ico_right (lt_add_one b).le hq)
    have : Module.Finite k ((TopTriple.innerPair.obj (stepTriple hX hab)).singularHomology V n :
        ModuleCat k) := hX.finite_singularHomology_ofInclusion_of_forall_mem_Ico V hab n h'
    have : Module.Finite k ((TopTriple.outerPair.obj (stepTriple hX hab)).singularHomology V n :
        ModuleCat k) := h b (Finset.mem_Ico.2 ⟨hab, lt_add_one b⟩)
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hab]
    exact ((stepTriple hX hab).finrank_singularHomology_totalPair_le V n).trans
      (Nat.add_le_add_right (ih h') _)

/-- **The strong inequalities along a filtration.** If the steps `(X (q + 1), X q)`, `a ≤ q < b`,
have finite-dimensional relative homology in degrees `≤ n`, then the alternating sum
`dim Hₙ(X b, X a) - dim Hₙ₋₁(X b, X a) + ⋯ ± dim H₀(X b, X a)` is at most the corresponding
alternating sum of the summed dimensions `∑_q dim Hᵢ(X (q + 1), X q)`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_le {a b : ℤ}
    (hab : a ≤ b) (n : ℕ) (h : ∀ q ∈ Finset.Ico a b, ∀ i ≤ n, Module.Finite k
      ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i : ModuleCat k)) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k ((TopPair.ofInclusion (hX hab)).singularHomology V i : ModuleCat k) ≤
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * ∑ q ∈ Finset.Ico a b,
        (finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i :
          ModuleCat k) : ℤ) := by
  induction b, hab using Int.leInduction with
  | base =>
    have (i : ℕ) := ModuleCat.isZero_iff_subsingleton.1
      (TopPair.isZero_singularHomology_ofInclusion_self V (X a) i)
    simp [finrank_zero_of_subsingleton]
  | succ b hab ih =>
    have h' : ∀ q ∈ Finset.Ico a b, ∀ i ≤ n, Module.Finite k
        ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i : ModuleCat k) :=
      fun q hq ↦ h q (Finset.Ico_subset_Ico_right (lt_add_one b).le hq)
    refine ((stepTriple hX hab).sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_le
      V n (fun i hi ↦ hX.finite_singularHomology_ofInclusion_of_forall_mem_Ico V hab i
        fun q hq ↦ h' q hq i hi) (h b (Finset.mem_Ico.2 ⟨hab, lt_add_one b⟩))).trans ?_
    simp only [← Finset.sum_Ico_add_eq_sum_Ico_add_one hab, mul_add, Finset.sum_add_distrib]
    exact add_le_add_left (ih h') _

/-- **Euler's equality along a filtration.** If the steps `(X (q + 1), X q)`, `a ≤ q < b`, have
finite-dimensional relative homology in degrees `≤ n` and vanishing homology in degree `n + 1`,
then `∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(X b, X a) = ∑ᵢ₌₀ⁿ (-1)ⁱ ∑_q dim Hᵢ(X (q + 1), X q)`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_eq {a b : ℤ}
    (hab : a ≤ b) {n : ℕ} (h : ∀ q ∈ Finset.Ico a b, ∀ i ≤ n, Module.Finite k
      ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i : ModuleCat k))
    (hn : ∀ q ∈ Finset.Ico a b,
      IsZero ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V (n + 1))) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k ((TopPair.ofInclusion (hX hab)).singularHomology V i : ModuleCat k) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ∑ q ∈ Finset.Ico a b,
        (finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i :
          ModuleCat k) : ℤ) := by
  induction b, hab using Int.leInduction with
  | base =>
    have (i : ℕ) := ModuleCat.isZero_iff_subsingleton.1
      (TopPair.isZero_singularHomology_ofInclusion_self V (X a) i)
    simp [finrank_zero_of_subsingleton]
  | succ b hab ih =>
    have hsub : Finset.Ico a b ⊆ Finset.Ico a (b + 1) :=
      Finset.Ico_subset_Ico_right (lt_add_one b).le
    have hb : b ∈ Finset.Ico a (b + 1) := Finset.mem_Ico.2 ⟨hab, lt_add_one b⟩
    refine ((stepTriple hX hab).sum_range_neg_one_pow_mul_finrank_singularHomology_totalPair_eq V
      n (fun i hi ↦ hX.finite_singularHomology_ofInclusion_of_forall_mem_Ico V hab i
        fun q hq ↦ h q (hsub hq) i hi) (h b hb) (hn b hb)).trans ?_
    simp only [← Finset.sum_Ico_add_eq_sum_Ico_add_one hab, mul_add, Finset.sum_add_distrib]
    exact congrArg (· + _) (ih (fun q hq ↦ h q (hsub hq)) fun q hq ↦ hn q (hsub hq))

/-- **The Morse polynomial identity along a filtration.** Let the steps `(X (q + 1), X q)`,
`a ≤ q < b`, have finite-dimensional relative homology in degrees `≤ n` and vanishing homology
in degree `n + 1`. Write `bᵢ = dim Hᵢ(X b, X a)` and `cᵢ = ∑_q dim Hᵢ(X (q + 1), X q)`. Then
`∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with natural number coefficients
whose coefficient of `tⁱ` is, for `i < n`, the gap `(cᵢ - cᵢ₋₁ + ⋯ ± c₀) - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)`
in the `i`-th strong inequality, and is zero for `i ≥ n`. -/
theorem exists_sum_range_monomial_singularHomology_ofInclusion_eq_add_mul {a b : ℤ}
    (hab : a ≤ b) {n : ℕ} (h : ∀ q ∈ Finset.Ico a b, ∀ i ≤ n, Module.Finite k
      ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i : ModuleCat k))
    (hn : ∀ q ∈ Finset.Ico a b,
      IsZero ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V (n + 1))) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i (∑ q ∈ Finset.Ico a b,
        finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i :
          ModuleCat k)) =
        ∑ i ∈ Finset.range (n + 1),
          monomial i (finrank k ((TopPair.ofInclusion (hX hab)).singularHomology V i :
            ModuleCat k)) + (1 + Polynomial.X) * Q ∧
      (∀ i < n, (Q.coeff i : ℤ) =
        ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) * ∑ q ∈ Finset.Ico a b,
          (finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V j :
            ModuleCat k) : ℤ) -
        ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
          finrank k ((TopPair.ofInclusion (hX hab)).singularHomology V j : ModuleCat k)) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 := by
  obtain ⟨Q, hQ, hcoeff, hzero⟩ := TauCeti.exists_sum_range_monomial_eq_add_mul
    (b := fun i ↦ finrank k ((TopPair.ofInclusion (hX hab)).singularHomology V i : ModuleCat k))
    (c := fun i ↦ ∑ q ∈ Finset.Ico a b,
      finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i :
        ModuleCat k)) (n := n)
    (fun m hm ↦ by
      simpa only [Nat.cast_sum] using
        hX.sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_le V hab m
          fun q hq i hi ↦ h q hq i (hi.trans hm.le))
    (by
      simpa only [Nat.cast_sum] using
        hX.sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_eq V hab h hn)
  refine ⟨Q, hQ, fun i hi ↦ ?_, hzero⟩
  simpa only [Nat.cast_sum] using hcoeff i hi

/-- **The lacunary principle along a filtration.** Let the steps `(X (q + 1), X q)`,
`a ≤ q < b`, have finite-dimensional relative homology in every degree, and write
`cᵢ = ∑_q dim Hᵢ(X (q + 1), X q)`. If no two consecutive `cᵢ` are both nonzero, then
`dim Hₙ(X b, X a) = cₙ` for every `n`. -/
theorem finrank_singularHomology_ofInclusion_eq_sum_of_eq_zero_or {a b : ℤ} (hab : a ≤ b)
    (h : ∀ q ∈ Finset.Ico a b, ∀ i, Module.Finite k
      ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i : ModuleCat k))
    (hc : ∀ i, ∑ q ∈ Finset.Ico a b,
        finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i :
          ModuleCat k) = 0 ∨
      ∑ q ∈ Finset.Ico a b,
        finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V (i + 1) :
          ModuleCat k) = 0) (n : ℕ) :
    finrank k ((TopPair.ofInclusion (hX hab)).singularHomology V n : ModuleCat k) =
      ∑ q ∈ Finset.Ico a b,
        finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V n :
          ModuleCat k) :=
  congrFun (TauCeti.eq_of_forall_sum_range_neg_one_pow_mul_le
    (b := fun i ↦ finrank k ((TopPair.ofInclusion (hX hab)).singularHomology V i : ModuleCat k))
    (c := fun i ↦ ∑ q ∈ Finset.Ico a b,
      finrank k ((TopPair.ofInclusion (hX (lt_add_one q).le)).singularHomology V i :
        ModuleCat k))
    (fun m ↦ by
      simpa only [Nat.cast_sum] using
        hX.sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_le V hab m
          fun q hq i _ ↦ h q hq i) hc) n

end Monotone
