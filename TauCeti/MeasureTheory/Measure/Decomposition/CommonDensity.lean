/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Densities of finitely many signed differences against a common measure

Let `λ` be a measure and let `ν₁ i`, `ν₂ i` be finitely many pairs of measures on a σ-compact
topological space, all finite on compact sets. The sum `ρ = λ + ∑ i, (ν₁ i + ν₂ i)` is finite on
compact sets and dominates all of them, so each signed difference `ν₁ i - ν₂ i` has a real density
`dν₁ i/dρ - dν₂ i/dρ` with respect to `ρ`, integrable on compact sets
(`MeasureTheory.Measure.exists_common_density_sub`).

This is how a vector-valued functional, given componentwise as differences of measures, is
represented by a single vector-valued density against one measure `ρ` which also dominates a
prescribed variation measure `λ`. Its pointwise norm is then compared with the density of `λ`
with respect to `ρ`, as in a polar decomposition.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §1.8 (the Riesz representation theorem for vector-valued functionals).
-/

public section

namespace MeasureTheory.Measure

/-- **Common densities.** For a measure `λ` and finitely many pairs of measures `ν₁ i`, `ν₂ i`, all
finite on compact sets of a σ-compact space, there is a measure `ρ`, finite on compact sets and
dominating `λ`, with respect to which each signed difference `ν₁ i - ν₂ i` has a measurable density
`f i`, integrable on compact sets: `∫ ψ dν₁ i - ∫ ψ dν₂ i = ∫ f i ψ dρ` for every `ψ` integrable
for `ν₁ i` and `ν₂ i`. -/
theorem exists_common_density_sub {X ι : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] [Finite ι] (lam : Measure X) [IsFiniteMeasureOnCompacts lam]
    (ν₁ ν₂ : ι → Measure X)
    [∀ i, IsFiniteMeasureOnCompacts (ν₁ i)] [∀ i, IsFiniteMeasureOnCompacts (ν₂ i)] :
    ∃ ρ : Measure X, IsFiniteMeasureOnCompacts ρ ∧ lam ≪ ρ ∧ ∃ f : ι → X → ℝ,
      (∀ i, Measurable (f i)) ∧ (∀ i K, IsCompact K → IntegrableOn (f i) K ρ) ∧
      ∀ i (ψ : X → ℝ), Integrable ψ (ν₁ i) → Integrable ψ (ν₂ i) →
        Integrable (fun x => f i x * ψ x) ρ ∧
          ∫ x, f i x * ψ x ∂ρ = ∫ x, ψ x ∂ν₁ i - ∫ x, ψ x ∂ν₂ i := by
  have := Fintype.ofFinite ι
  set ρ : Measure X := lam + ∑ i, (ν₁ i + ν₂ i) with hρ
  have hρc : IsFiniteMeasureOnCompacts ρ := ⟨fun K hK => by
    simp only [hρ, FunLike.coe_add, FunLike.coe_sum, Pi.add_apply, Finset.sum_apply]
    exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, ENNReal.sum_lt_top.2 fun i _ =>
      ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩⟩
  -- Each `ν₁ i` and `ν₂ i` is dominated by `ρ`.
  have hac {i} {ν : Measure X} (hν : ν = ν₁ i ∨ ν = ν₂ i) : ν ≪ ρ := fun s hs => by
    simp only [hρ, FunLike.coe_add, FunLike.coe_sum, Pi.add_apply, Finset.sum_apply,
      add_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at hs
    rcases hν with rfl | rfl
    exacts [(hs.2 i).1, (hs.2 i).2]
  have hint {i} {ν : Measure X} (hν : ν = ν₁ i ∨ ν = ν₂ i) {K : Set X} (hK : IsCompact K) :
      IntegrableOn (fun x => (ν.rnDeriv ρ x).toReal) K ρ := by
    have : IsFiniteMeasureOnCompacts ν := by rcases hν with rfl | rfl <;> infer_instance
    exact Measure.integrableOn_toReal_rnDeriv hK.measure_lt_top.ne
  refine ⟨ρ, hρc, Measure.AbsolutelyContinuous.rfl.add_right _,
    fun i x => ((ν₁ i).rnDeriv ρ x).toReal - ((ν₂ i).rnDeriv ρ x).toReal,
    fun i => (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
      (Measure.measurable_rnDeriv _ _).ennreal_toReal,
    fun i K hK => (hint (Or.inl rfl) hK).sub (hint (Or.inr rfl) hK), fun i ψ h₁ h₂ => ?_⟩
  have h₁' := (integrable_toReal_rnDeriv_mul_iff (hac (i := i) (Or.inl rfl))).2 h₁
  have h₂' := (integrable_toReal_rnDeriv_mul_iff (hac (i := i) (Or.inr rfl))).2 h₂
  simp only [sub_mul]
  refine ⟨h₁'.sub h₂', ?_⟩
  rw [integral_sub h₁' h₂', integral_toReal_rnDeriv_mul (hac (Or.inl rfl)),
    integral_toReal_rnDeriv_mul (hac (Or.inr rfl))]

end MeasureTheory.Measure
