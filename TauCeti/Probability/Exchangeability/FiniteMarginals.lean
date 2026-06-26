module

public import TauCeti.Probability.Exchangeability.Basic
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Finite-dimensional marginal uniqueness

Two finite measures on path space `ℕ → α` that agree on every finite prefix marginal
(`prefixProj α n`, the projection to the first `n` coordinates) are equal. This is the Layer 0
finite-marginal uniqueness milestone of `TauCetiRoadmap/Exchangeability`: a thin ℕ-prefix wrapper
over Mathlib's projective-limit machinery (`IsProjectiveLimit.unique`), not new measure theory.

`measure_eq_of_prefixProj_map_eq` is the main API (marginals as `Measure.map` equalities);
`measure_eq_of_prefixProj_setwise` is the setwise form matching the roadmap target. The same
finite-measure statements apply directly to probability measures, since `IsProbabilityMeasure`
provides `IsFiniteMeasure`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **Finite-marginal uniqueness.** Two finite measures on `ℕ → α` that have the same law under
every finite prefix projection `prefixProj α n` are equal. -/
theorem measure_eq_of_prefixProj_map_eq {μ ν : Measure (ℕ → α)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (prefixProj α n) = ν.map (prefixProj α n)) : μ = ν := by
  -- The two `Finset ℕ`-restriction families agree: a finite index set `I` sits inside the
  -- prefix `{0, …, n-1}` for `n = I.sup id + 1`, so its restriction factors through `prefixProj`.
  have key : ∀ I : Finset ℕ, μ.map I.restrict = ν.map I.restrict := by
    intro I
    obtain ⟨n, hn⟩ : ∃ n, ∀ i ∈ I, i < n :=
      ⟨I.sup id + 1, fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩
    let g : (Fin n → α) → ((i : I) → α) := fun y i => y ⟨i.1, hn i.1 i.2⟩
    have hg : Measurable g := measurable_pi_lambda _ fun i => measurable_pi_apply _
    have hcomp : (Finset.restrict I : (ℕ → α) → ((i : I) → α)) = g ∘ prefixProj α n := by
      funext x i; rfl
    calc μ.map I.restrict
        = μ.map (g ∘ prefixProj α n) := by rw [hcomp]
      _ = (μ.map (prefixProj α n)).map g := (Measure.map_map hg (measurable_prefixProj n)).symm
      _ = (ν.map (prefixProj α n)).map g := by rw [h n]
      _ = ν.map (g ∘ prefixProj α n) := Measure.map_map hg (measurable_prefixProj n)
      _ = ν.map I.restrict := by rw [hcomp]
  -- `μ` and `ν` are both projective limits of the family `I ↦ μ.map I.restrict`.
  exact IsProjectiveLimit.unique (P := fun I => μ.map I.restrict)
    (fun I => rfl) (fun I => (key I).symm)

/-- **Finite-marginal uniqueness, setwise form** (matching the roadmap target): two finite measures
on `ℕ → α` agreeing on every measurable prefix-cylinder are equal. -/
theorem measure_eq_of_prefixProj_setwise {μ ν : Measure (ℕ → α)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (n : ℕ) (S : Set (Fin n → α)), MeasurableSet S →
      μ.map (prefixProj α n) S = ν.map (prefixProj α n) S) : μ = ν :=
  measure_eq_of_prefixProj_map_eq fun n => Measure.ext fun S hS => h n S hS

end Probability

end TauCeti
