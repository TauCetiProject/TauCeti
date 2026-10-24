/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Array
public import TauCeti.Probability.Independence.Map

/-!
# Rectangular blocks of array processes

`arrayBlock X e f` selects the entries of a two-index process along arbitrary index maps
`e` and `f`. `arrayBlockPair` retains each selected entry together with its transpose, which
allows oriented data to be read without discarding the reverse orientation.

This file supplies coordinate equations, entrywise almost-everywhere measurability, and
measurability of the corresponding read-offs from array path space. No injectivity or symmetry
is required; exchangeability of selected blocks is developed separately in
`TauCeti.Probability.Exchangeability.Arrays.Block.Basic`.

For a law on array path space, independence of the restrictions to two finite rectangular blocks
transports along any reindexing of the two axes that preserves the law, to the blocks over the
relabelled index sets (`indepFun_restrict_map_of_map_pairReindex_eq`). Exchangeable array laws
are the main source of such reindexings.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* D. Aldous, *Representations for partially exchangeable arrays of random variables*, Journal of
  Multivariate Analysis 11 (1981), 581–598.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α Ω : Type*}

/-! ## Blocks of an array -/

/-- The rectangular block of the array `X` along the index maps `e` and `f`: its `(i, j)`-entry is
the `(e i, f j)`-entry of `X`. -/
def arrayBlock (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) : ℕ × ℕ → Ω → α :=
  fun p ↦ X (e p.1, f p.2)

@[simp]
theorem arrayBlock_apply (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) (p : ℕ × ℕ) :
    arrayBlock X e f p = X (e p.1, f p.2) :=
  (rfl)

/-- The rectangular block of `X` along `e` and `f`, read together with its transpose: its
`(i, j)`-entry is the pair of the `(e i, f j)`-entry and the `(f j, e i)`-entry of `X`. -/
def arrayBlockPair (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) : ℕ × ℕ → Ω → α × α :=
  fun p ω ↦ (X (e p.1, f p.2) ω, X (f p.2, e p.1) ω)

@[simp]
theorem arrayBlockPair_apply (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) (p : ℕ × ℕ) (ω : Ω) :
    arrayBlockPair X e f p ω = (X (e p.1, f p.2) ω, X (f p.2, e p.1) ω) :=
  (rfl)

/-! ## Finite blocks under relabelling -/

/-- Reindexing the restriction of an array to the finite block `I₁ ×ˢ I₂` along permutations of
the two axes, giving a function on the block over the relabelled index sets. -/
private def finsetBlockReindex (σ τ : Equiv.Perm ℕ) (I₁ I₂ : Finset ℕ)
    (y : (I₁ ×ˢ I₂ : Finset (ℕ × ℕ)) → α) :
    (I₁.map σ.toEmbedding ×ˢ I₂.map τ.toEmbedding : Finset (ℕ × ℕ)) → α :=
  fun p ↦ y ⟨(σ.symm p.1.1, τ.symm p.1.2), by
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 p.2
    exact Finset.mem_product.2 ⟨Finset.mem_map_equiv.1 h₁, Finset.mem_map_equiv.1 h₂⟩⟩

/-- The block over the relabelled index sets is read off the reindexed array. -/
private theorem restrict_map_product_eq (σ τ : Equiv.Perm ℕ) (I₁ I₂ : Finset ℕ) :
    (fun x : ℕ × ℕ → α ↦ (I₁.map σ.toEmbedding ×ˢ I₂.map τ.toEmbedding).restrict x) =
      finsetBlockReindex σ τ I₁ I₂ ∘ (fun x : ℕ × ℕ → α ↦ (I₁ ×ˢ I₂).restrict x) ∘
        pairReindex σ τ := by
  funext x ⟨⟨a, b⟩, hab⟩
  simp [Finset.restrict, finsetBlockReindex, pairReindex_apply]

variable [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ × ℕ → Ω → α} {e f : ℕ → ℕ}

/-- Entrywise measurability passes to a block: the `p`-entry of `arrayBlock X e f` is the
`(e p.1, f p.2)`-entry of `X`. -/
theorem aemeasurable_arrayBlock (hX : ∀ p, AEMeasurable (X p) μ) (p : ℕ × ℕ) :
    AEMeasurable (arrayBlock X e f p) μ := by
  simpa only [arrayBlock_apply] using hX (e p.1, f p.2)

/-- Entrywise measurability passes to a block read together with its transpose: the `p`-entry of
`arrayBlockPair X e f` pairs two entries of `X`. -/
theorem aemeasurable_arrayBlockPair (hX : ∀ p, AEMeasurable (X p) μ) (p : ℕ × ℕ) :
    AEMeasurable (arrayBlockPair X e f p) μ := by
  have hread : arrayBlockPair X e f p =
      fun ω ↦ (X (e p.1, f p.2) ω, X (f p.2, e p.1) ω) :=
    funext fun ω ↦ arrayBlockPair_apply X e f p ω
  rw [hread]
  exact (hX (e p.1, f p.2)).prodMk (hX (f p.2, e p.1))

/-- Reading a block off an array's sample path is measurable. -/
theorem measurable_blockReadOff (e f : ℕ → ℕ) :
    Measurable fun x : ℕ × ℕ → α ↦ fun p : ℕ × ℕ ↦ x (e p.1, f p.2) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- Reading a block together with its transpose off an array's sample path is measurable. -/
theorem measurable_blockPairReadOff (e f : ℕ → ℕ) :
    Measurable fun x : ℕ × ℕ → α ↦ fun p : ℕ × ℕ ↦ (x (e p.1, f p.2), x (f p.2, e p.1)) :=
  Measurable.of_eval fun _ ↦ (measurable_pi_apply _).prodMk (measurable_pi_apply _)

/-! ## Independence of finite blocks under relabelling -/

private theorem measurable_finsetBlockReindex (σ τ : Equiv.Perm ℕ) (I₁ I₂ : Finset ℕ) :
    Measurable (finsetBlockReindex (α := α) σ τ I₁ I₂) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- Block independence transports along a reindexing of the two axes preserving the law: the
blocks `I₁ ×ˢ I₂`, `J₁ ×ˢ J₂` independent under `ρ` give the blocks over `σ '' I₁ ×ˢ τ '' I₂`
and `σ '' J₁ ×ˢ τ '' J₂` independent. -/
theorem indepFun_restrict_map_of_map_pairReindex_eq {ρ : Measure (ℕ × ℕ → α)}
    (σ τ : Equiv.Perm ℕ) (hρ : ρ.map (pairReindex σ τ) = ρ) {I₁ I₂ J₁ J₂ : Finset ℕ}
    (h : IndepFun (fun x : ℕ × ℕ → α ↦ (I₁ ×ˢ I₂).restrict x)
      (fun x : ℕ × ℕ → α ↦ (J₁ ×ˢ J₂).restrict x) ρ) :
    IndepFun (fun x : ℕ × ℕ → α ↦ (I₁.map σ.toEmbedding ×ˢ I₂.map τ.toEmbedding).restrict x)
      (fun x : ℕ × ℕ → α ↦ (J₁.map σ.toEmbedding ×ˢ J₂.map τ.toEmbedding).restrict x) ρ := by
  rw [restrict_map_product_eq, restrict_map_product_eq]
  refine IndepFun.comp ?_ (measurable_finsetBlockReindex σ τ I₁ I₂)
    (measurable_finsetBlockReindex σ τ J₁ J₂)
  rw [← indepFun_map_iff_comp (measurable_pairReindex σ τ) (Finset.measurable_restrict _)
    (Finset.measurable_restrict _), hρ]
  exact h

end Probability

end TauCeti
