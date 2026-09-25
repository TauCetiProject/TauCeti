/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Coding
import TauCeti.MeasureTheory.Measure.MixtureInjective

/-!
# The canonical row-coding law of a separately exchangeable array

The first-stage representation of a separately exchangeable array draws a random law `P` on
column paths, then independently draws one uniform variable for each row and samples that row
from `P`. This file names the resulting array law `rowCodingArrayLaw`.

The law is canonical: its image under currying is the de Finetti barycenter of the law of `P`.
Consequently, two finite laws on random path measures give the same array law exactly when they
are equal. In particular, the mixing law in the row-coding representation of a separately
exchangeable array is unique.

This is the first-stage canonicality needed by the Aldous--Hoover representation. The remaining
step is to resolve the invariant random path law into column and cell noise.

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

/-- The array law obtained by drawing a random path measure with law `π`, then using independent
uniform variables to sample one row from that path measure at each row index. -/
def rowCodingArrayLaw (π : Measure (ProbabilityMeasure (ℕ → α))) : Measure (ℕ × ℕ → α) :=
  (π.prod (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval))).map
    fun q p ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2

/-- The defining pushforward expression for `rowCodingArrayLaw`. -/
theorem rowCodingArrayLaw_def (π : Measure (ProbabilityMeasure (ℕ → α))) :
    rowCodingArrayLaw π =
      (π.prod (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval))).map
        fun q p ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2 := by
  rw [rowCodingArrayLaw]

/-- A probability law of random path measures gives a probability row-coding array law. -/
instance instIsProbabilityMeasureRowCodingArrayLaw
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (rowCodingArrayLaw π) := by
  rw [rowCodingArrayLaw_def]
  infer_instance

/-- Currying the canonical row-coding array law gives the de Finetti barycenter of its mixing
law. This identifies the parameter law from the array law. -/
@[simp]
theorem map_curry_rowCodingArrayLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    (rowCodingArrayLaw π).map (MeasurableEquiv.curry ℕ ℕ α) = deFinettiBarycenter π := by
  have hcode : Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) ↦
      fun p : ℕ × ℕ ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2 :=
    Measurable.of_eval fun p ↦ measurable_unitIntervalCoding_entry p
  rw [rowCodingArrayLaw_def, Measure.map_map (MeasurableEquiv.measurable _) hcode]
  convert map_prod_unitIntervalCoding_eq_deFinettiBarycenter (α := ℕ → α) π using 1
  apply congrArg (fun f : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) → ℕ → ℕ → α ↦
    (π.prod (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval))).map f)
  funext q i j
  rfl

/-- The row-coding array law determines every finite mixing law on path measures. -/
theorem rowCodingArrayLaw_injective {π₁ π₂ : Measure (ProbabilityMeasure (ℕ → α))}
    [IsFiniteMeasure π₁] [IsFiniteMeasure π₂]
    (h : rowCodingArrayLaw π₁ = rowCodingArrayLaw π₂) : π₁ = π₂ := by
  apply TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq
  have h' := congrArg (fun ρ : Measure (ℕ × ℕ → α) ↦
    ρ.map (MeasurableEquiv.curry ℕ ℕ α)) h
  simpa only [map_curry_rowCodingArrayLaw, deFinettiBarycenter_def] using h'

/-- Equality of finite mixing laws is equivalent to equality of their row-coding array laws. -/
theorem rowCodingArrayLaw_eq_iff {π₁ π₂ : Measure (ProbabilityMeasure (ℕ → α))}
    [IsFiniteMeasure π₁] [IsFiniteMeasure π₂] :
    rowCodingArrayLaw π₁ = rowCodingArrayLaw π₂ ↔ π₁ = π₂ :=
  ⟨rowCodingArrayLaw_injective, fun h ↦ congrArg rowCodingArrayLaw h⟩

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
    apply rowCodingArrayLaw_injective
    exact hπ'.2.symm.trans (by
      rw [rowCodingArrayLaw_def]
      exact hlaw)

end TauCeti.Probability
