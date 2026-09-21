/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.DirectingMap
public import TauCeti.Probability.Exchangeability.RandomMeasure.Block.Basic

/-!
# Compatibility of directing laws for finite block marginals

An invariant random probability measure on sequence space gives, for every positive block width,
an exchangeable process of finite block marginals. Applying de Finetti separately at each width
produces directing measures which a priori appear unrelated. This file proves that they are
compatible under restriction from a large block to each of its smaller consecutive subblocks.

For positive `m` and `q`, `blockRestriction m q r` restricts a block of width `q * m` to its
`r`-th subblock of width `m`. The corresponding map on the measurable codes of probability
measures is `codedBlockRestriction m q r`. The arithmetic identity relating the two blockings
then lets directing-measure uniqueness show that every pair of witnesses chosen at widths `m`
and `q * m` commutes almost surely with this restriction.

This is the projective compatibility needed to assemble the fixed-width conditional
factorizations into a single cell-level representation of an invariant random path law.

## Main results

* `MeasureTheory.ProbabilityMeasure.blockMarginals_map_blockRestriction` identifies restriction of
  a large block marginal with the corresponding smaller block marginal;
* `TauCeti.Probability.ConditionallyIIDWith.ae_map_codedBlockMarginals_eq` couples arbitrary
  directing measures chosen at two compatible block widths;
* `TauCeti.Probability.exists_compatible_directing_codedBlockMarginals_of_invariant` supplies
  compatible witnesses for an invariant random path measure.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats ordinary exchangeable
sequences rather than invariant random measures.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

open TauCeti.MeasureTheory

variable {α : Type*}

/-- Restrict a block of width `q * m` to its `r`-th consecutive subblock of width `m`. -/
def blockRestriction (m q : ℕ) (r : Fin q)
    (x : Fin (q * m) → α) : Fin m → α :=
  fun j => x (finProdFinEquiv (r, j))

/-- Evaluation of a consecutive subblock restriction. -/
@[simp]
theorem blockRestriction_apply (m q : ℕ) (r : Fin q)
    (x : Fin (q * m) → α) (j : Fin m) :
    blockRestriction m q r x j = x (finProdFinEquiv (r, j)) :=
  (rfl)

variable [MeasurableSpace α]

/-- Restriction to a consecutive subblock is measurable. -/
theorem measurable_blockRestriction (m q : ℕ) (r : Fin q) :
    Measurable (blockRestriction (α := α) m q r) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- Restricting the `i`-th block of width `q * m` to its `r`-th width-`m` subblock gives the
`(i * q + r)`-th block of width `m`. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.blockMarginals_map_blockRestriction
    (P : ProbabilityMeasure (ℕ → α))
    (m q : ℕ) [NeZero m] [NeZero q] (r : Fin q) (i : ℕ) :
    (P.blockMarginals (q * m) i).map (blockRestriction m q r) =
      P.blockMarginals m (i * q + r.val) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.blockMarginals_apply]
  rw [Measure.map_map]
  · congr 1
    funext x j
    simp only [Function.comp_apply, blockRestriction_apply, Nat.divModEquiv_symm_apply,
      finProdFinEquiv_apply_val]
    congr 1
    ring
  · exact measurable_blockRestriction m q r
  · exact Measurable.of_eval fun j => measurable_pi_apply _

/-- Restriction of probability-measure codes induced by restriction to a consecutive subblock. -/
def codedBlockRestriction (m q : ℕ) (r : Fin q)
    [MeasurableSpace.CountablyGenerated (Fin (q * m) → α)]
    [MeasurableSpace.CountablyGenerated (Fin m → α)] :
    (ProbabilityMeasureCodeIndex (Fin (q * m) → α) → ℝ≥0∞) →
      (ProbabilityMeasureCodeIndex (Fin m → α) → ℝ≥0∞) :=
  probabilityMeasureCodeMap (blockRestriction m q r) (measurable_blockRestriction m q r)

/-- Restriction of probability-measure codes is measurable. -/
theorem measurable_codedBlockRestriction (m q : ℕ) (r : Fin q)
    [MeasurableSpace.CountablyGenerated (Fin (q * m) → α)]
    [MeasurableSpace.CountablyGenerated (Fin m → α)] :
    Measurable (codedBlockRestriction (α := α) m q r) :=
  measurable_probabilityMeasureCodeMap _ _

/-- Restricting the code of a probability measure gives the code of its pushforward under block
restriction. -/
@[simp]
theorem codedBlockRestriction_probabilityMeasureCode (m q : ℕ)
    (r : Fin q) [MeasurableSpace.CountablyGenerated (Fin (q * m) → α)]
    [MeasurableSpace.CountablyGenerated (Fin m → α)]
    (P : ProbabilityMeasure (Fin (q * m) → α)) :
    codedBlockRestriction m q r (probabilityMeasureCode P) =
      probabilityMeasureCode (P.map (blockRestriction m q r)) :=
  probabilityMeasureCodeMap_apply _ _ _

/-- **Directing measures for compatible block widths commute almost surely with restriction.**

Suppose the coded block-marginal processes of widths `q * m` and `m`, formed from the same random
path measure `P`, have directing measures `ν` and `ξ`. Restricting a large block to its `r`-th
small subblock turns coordinate `i` into small-block coordinate `i * q + r`. This is an injective
selection, so conditional-i.i.d. uniqueness identifies `ξ` almost surely with the pushforward of
`ν` under `codedBlockRestriction m q r`.

The probability hypothesis on `μ` is the one required for almost-sure uniqueness of directing
measures. -/
theorem ConditionallyIIDWith.ae_map_codedBlockMarginals_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {P : Ω → ProbabilityMeasure (ℕ → α)} (m q : ℕ) [NeZero m] [NeZero q]
    [MeasurableSpace.CountablyGenerated (Fin (q * m) → α)]
    [MeasurableSpace.CountablyGenerated (Fin m → α)]
    {ν : Ω → ProbabilityMeasure
      (ProbabilityMeasureCodeIndex (Fin (q * m) → α) → ℝ≥0∞)}
    {ξ : Ω → ProbabilityMeasure
      (ProbabilityMeasureCodeIndex (Fin m → α) → ℝ≥0∞)}
    (hν : ConditionallyIIDWith μ
      (fun i ω => (P ω).codedBlockMarginals (q * m) i) ν)
    (hξ : ConditionallyIIDWith μ
      (fun i ω => (P ω).codedBlockMarginals m i) ξ)
    (r : Fin q) :
    (fun ω => (ν ω).map (codedBlockRestriction m q r)) =ᵐ[μ] ξ := by
  have hselect : Function.Injective (fun i : ℕ => i * q + r.val) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_neZero q) (Nat.add_right_cancel hij)
  refine hν.ae_map_directing_eq_of_comp_injective
    (hξ.comp_injective hselect) (measurable_codedBlockRestriction m q r)
      Function.injective_id fun i => Filter.Eventually.of_forall fun ω => ?_
  simp only [id_eq, ProbabilityMeasure.codedBlockMarginals_apply,
    codedBlockRestriction_probabilityMeasureCode]
  rw [ProbabilityMeasure.blockMarginals_map_blockRestriction]

/-- **An invariant random path measure has compatible directing measures at two block widths.**

The witnesses at widths `q * m` and `m` may be chosen so that, on one set of full measure, every
one of the `q` consecutive width-`m` restrictions of the large directing measure equals the small
directing measure. The same small directing measure appears for every subblock because the
width-`m` block process is conditionally i.i.d. -/
theorem exists_compatible_directing_codedBlockMarginals_of_invariant
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsProbabilityMeasure π]
    (m q : ℕ) [NeZero m] [NeZero q]
    [MeasurableSpace.CountablyGenerated (Fin (q * m) → α)]
    [MeasurableSpace.CountablyGenerated (Fin m → α)]
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (permReindex τ)) = π) :
    ∃ ν : ProbabilityMeasure (ℕ → α) → ProbabilityMeasure
        (ProbabilityMeasureCodeIndex (Fin (q * m) → α) → ℝ≥0∞),
      ∃ ξ : ProbabilityMeasure (ℕ → α) → ProbabilityMeasure
          (ProbabilityMeasureCodeIndex (Fin m → α) → ℝ≥0∞),
        ConditionallyIIDWith π (fun i P => P.codedBlockMarginals (q * m) i) ν ∧
        ConditionallyIIDWith π (fun i P => P.codedBlockMarginals m i) ξ ∧
        ∀ᵐ P ∂π, ∀ r : Fin q,
          (ν P).map (codedBlockRestriction m q r) = ξ P := by
  obtain ⟨ν, hν⟩ :=
    (conditionallyIID_codedBlockMarginals_of_invariant π (q * m) hπ).exists_directing
  obtain ⟨ξ, hξ⟩ :=
    (conditionallyIID_codedBlockMarginals_of_invariant π m hπ).exists_directing
  refine ⟨ν, ξ, hν, hξ, ae_all_iff.2 fun r => ?_⟩
  exact hν.ae_map_codedBlockMarginals_eq m q hξ r

end Probability

end TauCeti

end

end
