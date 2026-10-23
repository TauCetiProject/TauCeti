/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.PathLaw.Basic

/-!
# Basic exchangeability definitions

This file defines the symmetry notions of a process `X : ℕ → Ω → α` in terms of its
finite-dimensional and path laws (`blockLaw`, `prefixLaw`, `pathLaw`, from
`TauCeti.Probability.Process.PathLaw.Basic`):

* `ExchangeableAt μ X n` — the law of the first `n` coordinates is invariant under every
  permutation of `Fin n`;
* `Exchangeable μ X` — finite exchangeability at every length;
* `FullyExchangeable μ X` — the path law is invariant under every permutation of `ℕ`;
* `Contractable μ X` — finite-dimensional laws are invariant under strictly increasing finite
  subsequences (spreadability).

The definitions are intentionally hypothesis-light; measurability hypotheses enter only in lemmas
that compose `Measure.map`s. They are adapted from the `cameronfreer/exchangeability` sources
pinned at `e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Finite exchangeability at `n`: the first `n` coordinates have permutation-invariant law. -/
@[expose]
def ExchangeableAt (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    blockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n

/-- Finite exchangeability at every length. -/
@[expose]
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n, ExchangeableAt μ X n

/-- Full exchangeability: the path law is invariant under every permutation of `ℕ`. -/
@[expose]
def FullyExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ π : Equiv.Perm ℕ, μ.map (fun ω i => X (π i) ω) = pathLaw μ X

/-- Contractability, or spreadability: finite-dimensional laws are invariant under strictly
increasing finite subsequences. -/
@[expose]
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k → blockLaw μ X k = prefixLaw μ X m

theorem Exchangeable.exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : Exchangeable μ X) (n : ℕ) : ExchangeableAt μ X n :=
  h n

theorem ExchangeableAt.permute {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (h : ExchangeableAt μ X n) (σ : Equiv.Perm (Fin n)) :
    blockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n :=
  h σ

/-- Under finite exchangeability at `n`, rearranging a path leaves its probability unchanged. -/
theorem ExchangeableAt.prefixLaw_singleton_comp [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ} (h : ExchangeableAt μ X n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (w : Fin n → α)
    (σ : Equiv.Perm (Fin n)) :
    prefixLaw μ X n {w ∘ σ} = prefixLaw μ X n {w} := by
  have hmeas : Measurable fun x : Fin n → α => fun i => x (σ⁻¹ i) :=
    Measurable.of_eval fun i => measurable_pi_apply (σ⁻¹ i)
  have hmap : (prefixLaw μ X n).map (fun x : Fin n → α => fun i => x (σ⁻¹ i)) =
      prefixLaw μ X n := by
    conv_lhs => rw [prefixLaw_def]
    rw [map_blockLaw_reindex μ (fun i : Fin n => i.val) (fun i => σ⁻¹ i) hX]
    exact h σ⁻¹
  conv_rhs => rw [← hmap]
  rw [Measure.map_apply hmeas (measurableSet_singleton w)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Function.comp_apply]
  refine ⟨fun hx j => ?_, fun hx i => ?_⟩
  · simpa using hx (σ⁻¹ j)
  · simpa using hx (σ i)

theorem FullyExchangeable.permute {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) (π : Equiv.Perm ℕ) :
    μ.map (fun ω i => X (π i) ω) = pathLaw μ X :=
  h π

end Probability

end TauCeti
