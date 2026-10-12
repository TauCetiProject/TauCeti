/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.RowCoding
import TauCeti.MeasureTheory.Measure.MixtureInjective

/-!
# The canonical row-coding law of a separately exchangeable array

The first-stage representation of a separately exchangeable array draws a random law `P` on
column paths, then independently draws one uniform variable for each row and samples that row
from `P`. The resulting array law is `rowCodingArrayLaw`.

The law is canonical: its image under currying is the de Finetti barycenter of the law of `P`.
Consequently, two finite laws on random path measures give the same array law exactly when they
are equal. In particular, the mixing law in the row-coding representation of a separately
exchangeable array is unique.

This first-stage canonicality identifies the invariant random path law independently of a
chosen directing measure, for its resolution into column and cell noise.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
arrays.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- Separate exchangeability of an array is equivalent to representing its law by a
column-invariant row-coding array law. -/
theorem separatelyExchangeable_iff_exists_rowCodingArrayLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ × ℕ → Ω → α} (hX : ∀ p, AEMeasurable (X p) μ) :
    SeparatelyExchangeable μ X ↔
      ∃ π : ProbabilityMeasure (ProbabilityMeasure (ℕ → α)),
        (∀ τ : Equiv.Perm ℕ,
          (π : Measure (ProbabilityMeasure (ℕ → α))).map
            (fun P ↦ P.map (fun x : ℕ → α ↦ fun k ↦ x (τ k))) = π) ∧
          μ.map (fun ω p ↦ X p ω) = rowCodingArrayLaw π := by
  simpa only [rowCodingArrayLaw_def] using
    separatelyExchangeable_iff_exists_coding (α := α) hX

/-- A column-invariant mixing law gives a separately exchangeable row-coding array law. -/
theorem separatelyExchangeable_rowCodingArrayLaw
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsProbabilityMeasure π]
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P ↦ P.map (fun x : ℕ → α ↦ fun k ↦ x (τ k))) = π) :
    SeparatelyExchangeable (rowCodingArrayLaw π) (fun p x ↦ x p) := by
  apply (separatelyExchangeable_iff_exists_rowCodingArrayLaw
    (μ := rowCodingArrayLaw π) (X := fun p x ↦ x p)
    (fun p ↦ (measurable_pi_apply p).aemeasurable)).2
  exact ⟨⟨π, inferInstance⟩, hπ, by simp⟩

/-- Currying the canonical row-coding array law gives the de Finetti barycenter of its mixing
law. This identifies the parameter law from the array law. -/
@[simp]
theorem map_curry_rowCodingArrayLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    (rowCodingArrayLaw π).map (MeasurableEquiv.curry ℕ ℕ α) = deFinettiBarycenter π := by
  rw [rowCodingArrayLaw_eq_map_snd, map_snd_arrayRowCodingLaw,
    Measure.map_map (MeasurableEquiv.measurable _) measurable_uncurry]
  have h : (MeasurableEquiv.curry ℕ ℕ α) ∘ Function.uncurry = id := by
    funext x
    rfl
  rw [h, Measure.map_id]

/-- The row-coding array law determines every finite mixing law on path measures. -/
theorem eq_of_rowCodingArrayLaw_eq {π₁ π₂ : Measure (ProbabilityMeasure (ℕ → α))}
    [IsFiniteMeasure π₁]
    (h : rowCodingArrayLaw π₁ = rowCodingArrayLaw π₂) : π₁ = π₂ := by
  apply TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq
  have h' := congrArg (fun ρ : Measure (ℕ × ℕ → α) ↦
    ρ.map (MeasurableEquiv.curry ℕ ℕ α)) h
  simpa only [map_curry_rowCodingArrayLaw, deFinettiBarycenter_def] using h'

/-- Equality of finite mixing laws is equivalent to equality of their row-coding array laws. -/
@[simp]
theorem rowCodingArrayLaw_inj {π₁ π₂ : Measure (ProbabilityMeasure (ℕ → α))}
    [IsFiniteMeasure π₁] :
    rowCodingArrayLaw π₁ = rowCodingArrayLaw π₂ ↔ π₁ = π₂ :=
  ⟨eq_of_rowCodingArrayLaw_eq, fun h ↦ congrArg rowCodingArrayLaw h⟩

/-- **Canonical row-coding representation.** A separately exchangeable array has a unique law on
path measures which is invariant under column reindexing and whose row-coding array law is the
array law. -/
theorem SeparatelyExchangeable.existsUnique_rowCodingArrayLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ × ℕ → Ω → α} (h : SeparatelyExchangeable μ X)
    (hX : ∀ p, AEMeasurable (X p) μ) :
    ∃! π : ProbabilityMeasure (ProbabilityMeasure (ℕ → α)),
      (∀ τ : Equiv.Perm ℕ,
        (π : Measure (ProbabilityMeasure (ℕ → α))).map
          (fun P ↦ P.map (fun x : ℕ → α ↦ fun k ↦ x (τ k))) = π) ∧
        μ.map (fun ω p ↦ X p ω) = rowCodingArrayLaw π := by
  obtain ⟨π, hπ, hlaw⟩ := h.exists_arrayLaw_eq_map_unitIntervalCoding hX
  refine ⟨π, ⟨hπ, ?_⟩, ?_⟩
  · rw [rowCodingArrayLaw_def]
    exact hlaw
  · intro π' hπ'
    apply ProbabilityMeasure.toMeasure_injective
    apply eq_of_rowCodingArrayLaw_eq
    exact hπ'.2.symm.trans (by
      rw [rowCodingArrayLaw_def]
      exact hlaw)

end TauCeti.Probability
