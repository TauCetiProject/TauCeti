/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Finite-basis reconstruction in `Lᵖ`

An `Lᵖ` function with finite-dimensional target is the sum of its scalar coordinate functions
multiplied by the basis vectors. This transports `Module.Basis.sum_repr` through
`ContinuousLinearMap.compLpL` and permits coordinatewise arguments about vector-valued operators.
The same decomposition bounds the `Lᵖ` seminorm of a function by those of its coordinates.
-/

public section

namespace TauCeti

open MeasureTheory

variable {α 𝕜 F ι : Type*} [MeasurableSpace α]
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] [Fintype ι]
  {p : ENNReal} [Fact (1 ≤ p)] {μ : Measure α}

/-- Reconstruct an `Lᵖ` function from its coordinates in a finite basis. -/
theorem eq_sum_basis_compLpL (b : Module.Basis ι 𝕜 F) (f : Lp F p μ) :
    f = ∑ i, (ContinuousLinearMap.toSpanSingleton 𝕜 (b i)).compLpL p μ
      ((b.coord i).toContinuousLinearMap.compLpL p μ f) := by
  classical
  apply Lp.ext
  have hcoord : ∀ i, (ContinuousLinearMap.toSpanSingleton 𝕜 (b i)).compLpL p μ
      ((b.coord i).toContinuousLinearMap.compLpL p μ f) =ᵐ[μ]
        fun x ↦ (b.coord i) (f x) • b i := fun i ↦ by
    filter_upwards [(ContinuousLinearMap.toSpanSingleton 𝕜 (b i)).coeFn_compLpL
      ((b.coord i).toContinuousLinearMap.compLpL p μ f),
      (b.coord i).toContinuousLinearMap.coeFn_compLpL f] with x hvec hscalar
    simp only [hvec, hscalar, ContinuousLinearMap.toSpanSingleton_apply,
      LinearMap.coe_toContinuousLinearMap']
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
    (ContinuousLinearMap.toSpanSingleton 𝕜 (b i)).compLpL p μ
      ((b.coord i).toContinuousLinearMap.compLpL p μ f)),
    ae_all_iff.mpr hcoord] with x hsum hcoords
  simpa only [hsum, hcoords, Module.Basis.coord_apply] using (b.sum_repr (f x)).symm

/-- The `Lᵖ` seminorm of a function with values in a space with a finite basis is controlled
by the `Lᵖ` seminorms of its coordinates. -/
theorem eLpNorm_le_sum_enorm_mul_eLpNorm_coord (b : Module.Basis ι 𝕜 F)
    {g : α → F} (hg : AEStronglyMeasurable g μ) :
    eLpNorm g p μ ≤ ∑ i, ‖b i‖ₑ * eLpNorm (fun x ↦ b.coord i (g x)) p μ := by
  have hsum : g = ∑ i, fun x ↦ b.coord i (g x) • b i := by
    funext x
    rw [Finset.sum_apply]
    exact (b.sum_repr (g x)).symm
  calc
    eLpNorm g p μ ≤ ∑ i, eLpNorm (fun x ↦ b.coord i (g x) • b i) p μ := by
      conv_lhs => rw [hsum]
      exact eLpNorm_sum_le Fact.out
    _ ≤ ∑ i, ‖b i‖ₑ * eLpNorm (fun x ↦ b.coord i (g x)) p μ := by
      refine Finset.sum_le_sum fun i _ ↦ eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ ?_
        (Filter.Eventually.of_forall fun x ↦ ?_)
      · exact ((b.coord i).continuous_of_finiteDimensional.comp_aestronglyMeasurable
          hg).smul_const (b i)
      · rw [enorm_smul, mul_comm]

end TauCeti
