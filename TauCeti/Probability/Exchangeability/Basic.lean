import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Basic laws of stochastic processes

This file starts the exchangeability library with the law-level wrappers used by the
Layer 0 roadmap: the law of a whole sequence, its finite-dimensional marginals, and the
projection to the first `n` coordinates.

The main finite-dimensional uniqueness theorem is not reproved here.  The final lemma
`pathLaw_eq_iff_forall_finiteDimensionalLaw_eq` is only a Tau Ceti naming wrapper around
Mathlib's `ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq`.
-/

open MeasureTheory

noncomputable section

namespace TauCeti

namespace Probability

namespace Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω}
  {X Y : ℕ → Ω → α}

/-- The sample path associated to a sequence of random variables. -/
def pathMap (X : ℕ → Ω → α) (ω : Ω) : ℕ → α :=
  fun i => X i ω

/-- The law of the whole sequence as a measure on path space. -/
def pathLaw (μ : Measure Ω) (X : ℕ → Ω → α) : Measure (ℕ → α) :=
  μ.map (pathMap X)

/-- The finite-dimensional marginal over a finite set of indices. -/
def finiteDimensionalLaw (μ : Measure Ω) (X : ℕ → Ω → α) (I : Finset ℕ) : Measure (I → α) :=
  μ.map (fun ω => I.restrict (pathMap X ω))

/-- Projection from path space to the coordinates indexed by a finite set. -/
def finiteDimensionalProj (α : Type*) [MeasurableSpace α] (I : Finset ℕ) (x : ℕ → α) :
    I → α :=
  I.restrict x

/-- Projection from path space to the first `n` coordinates. -/
def prefixProj (α : Type*) (n : ℕ) (x : ℕ → α) : Fin n → α :=
  fun i => x i.val

/-- The law of the first `n` coordinates of a sequence. -/
def prefixLaw (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Measure (Fin n → α) :=
  μ.map (fun ω => prefixProj α n (pathMap X ω))

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma pathMap_apply (X : ℕ → Ω → α) (ω : Ω) (i : ℕ) : pathMap X ω i = X i ω :=
  rfl

@[simp]
lemma finiteDimensionalProj_apply (I : Finset ℕ) (x : ℕ → α) (i : I) :
    finiteDimensionalProj α I x i = x i :=
  rfl

omit [MeasurableSpace α] in
@[simp]
lemma prefixProj_apply (n : ℕ) (x : ℕ → α) (i : Fin n) :
    prefixProj α n x i = x i.val :=
  rfl

/-- Measurability of the sample-path map, from coordinatewise measurability. -/
lemma measurable_pathMap (hX : ∀ i, Measurable (X i)) : Measurable (pathMap X) :=
  measurable_pi_iff.mpr hX

/-- Almost-everywhere measurability of the sample-path map, from coordinatewise
almost-everywhere measurability. -/
lemma aemeasurable_pathMap (hX : ∀ i, AEMeasurable (X i) μ) :
    AEMeasurable (pathMap X) μ :=
  aemeasurable_pi_lambda _ hX

/-- Measurability of a finite-dimensional projection on path space. -/
lemma measurable_finiteDimensionalProj (I : Finset ℕ) :
    Measurable (finiteDimensionalProj α I) :=
  Finset.measurable_restrict I

/-- Measurability of the prefix projection on path space. -/
lemma measurable_prefixProj (n : ℕ) : Measurable (prefixProj α n) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply i.val

/-- The finite-dimensional law is the image of the path law under the corresponding
finite-dimensional projection. -/
lemma finiteDimensionalLaw_eq_map_pathLaw (hX : ∀ i, Measurable (X i)) (I : Finset ℕ) :
    finiteDimensionalLaw μ X I = (pathLaw μ X).map (finiteDimensionalProj α I) := by
  rw [finiteDimensionalLaw, pathLaw, Measure.map_map (measurable_finiteDimensionalProj I)
    (measurable_pathMap hX)]
  rfl

/-- The prefix law is the image of the path law under `prefixProj`. -/
lemma prefixLaw_eq_map_pathLaw (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    prefixLaw μ X n = (pathLaw μ X).map (prefixProj α n) := by
  rw [prefixLaw, pathLaw, Measure.map_map (measurable_prefixProj n) (measurable_pathMap hX)]
  rfl

/-- The first-coordinate prefix marginal is the law of `X 0`, up to the unique coordinate of
`Fin 1`. -/
lemma prefixLaw_one (μ : Measure Ω) (X : ℕ → Ω → α) :
    prefixLaw μ X 1 = μ.map (fun ω : Ω => fun _ : Fin 1 => X 0 ω) := by
  refine Measure.map_congr (Filter.Eventually.of_forall fun ω => ?_)
  funext i
  fin_cases i
  rfl

/-- Reindexing paths before taking a finite-dimensional projection is the same as taking the
corresponding finite-dimensional law of the reindexed sequence. -/
lemma finiteDimensionalLaw_reindex (f : ℕ → ℕ) (I : Finset ℕ) :
    finiteDimensionalLaw μ (fun i ω => X (f i) ω) I =
      μ.map (fun ω => fun i : I => X (f i) ω) :=
  rfl

/-- The finite-dimensional law over `I` can be read directly from the path law. -/
lemma pathLaw_map_finiteDimensionalProj (hX : ∀ i, Measurable (X i)) (I : Finset ℕ) :
    (pathLaw μ X).map (finiteDimensionalProj α I) = finiteDimensionalLaw μ X I :=
  (finiteDimensionalLaw_eq_map_pathLaw hX I).symm

/-- The prefix law can be read directly from the path law. -/
lemma pathLaw_map_prefixProj (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    (pathLaw μ X).map (prefixProj α n) = prefixLaw μ X n :=
  (prefixLaw_eq_map_pathLaw hX n).symm

/-- Equality of path laws is equivalent to equality of all finite-dimensional laws.

This is the Tau Ceti wrapper around Mathlib's finite-dimensional-law uniqueness theorem. -/
lemma pathLaw_eq_iff_forall_finiteDimensionalLaw_eq [IsFiniteMeasure μ]
    (hX : AEMeasurable (pathMap X) μ) (hY : AEMeasurable (pathMap Y) μ) :
    pathLaw μ X = pathLaw μ Y ↔
      ∀ I : Finset ℕ, finiteDimensionalLaw μ X I = finiteDimensionalLaw μ Y I := by
  exact ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq hX hY

/-- Coordinatewise almost-sure equality gives equal finite-dimensional laws. -/
lemma finiteDimensionalLaw_eq_of_forall_ae_eq (h : ∀ i, X i =ᵐ[μ] Y i) (I : Finset ℕ) :
    finiteDimensionalLaw μ X I = finiteDimensionalLaw μ Y I :=
  ProbabilityTheory.map_restrict_eq_of_forall_ae_eq h I

/-- Coordinatewise almost-sure equality gives equal path laws for finite measures. -/
lemma pathLaw_eq_of_forall_ae_eq [IsFiniteMeasure μ]
    (hX : AEMeasurable (pathMap X) μ) (hY : AEMeasurable (pathMap Y) μ)
    (h : ∀ i, X i =ᵐ[μ] Y i) :
    pathLaw μ X = pathLaw μ Y :=
  ProbabilityTheory.map_eq_of_forall_ae_eq hX hY h

end Exchangeability

end Probability

end TauCeti

end
