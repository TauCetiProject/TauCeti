/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.Pi

/-!
# Finite-basis reconstruction in `Lᵖ`

An `Lᵖ` function with finite-dimensional target is the sum of its scalar coordinate functions
multiplied by the basis vectors. This transports `Module.Basis.sum_repr` through
`ContinuousLinearMap.compLpL` and permits coordinatewise arguments about vector-valued operators.
The same decomposition bounds the `Lᵖ` seminorm of a function by those of its coordinates.
Consequently, an operator into `Lᵖ` with finite-dimensional target is compact as soon as each of
its scalar projections is compact
(`TauCeti.isCompactOperator_of_forall_isCompactOperator_compLpL_comp`).
-/

public section

open MeasureTheory

variable {α 𝕜 F ι : Type*} [MeasurableSpace α]
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] [Fintype ι]
  {p : ENNReal} [Fact (1 ≤ p)] {μ : Measure α}

namespace TauCeti

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

variable (𝕜) in
/-- A map into `Lᵖ` with finite-dimensional target is a compact operator as soon as its
composition with every scalar projection `ℓ.compLpL p μ` is. Neither linearity nor continuity
of `T` is needed. The scalar field `𝕜` of the functionals `ℓ` is not determined by `T`: any
complete nontrivially normed field over which `F` is a finite-dimensional normed space works. -/
theorem isCompactOperator_of_forall_isCompactOperator_compLpL_comp
    {Y : Type*} [Zero Y] [TopologicalSpace Y] {T : Y → Lp F p μ}
    (h : ∀ ℓ : F →L[𝕜] 𝕜, IsCompactOperator (ℓ.compLpL p μ ∘ T)) :
    IsCompactOperator T := by
  let b := Module.finBasis 𝕜 F
  -- Near `0`, the coordinate projections of `T` lie in a compact set `K`; `T` itself is recovered
  -- from them by the continuous reconstruction map of `eq_sum_basis_compLpL`.
  obtain ⟨K, hK, hKT⟩ := IsCompactOperator.pi fun i ↦ h (b.coord i).toContinuousLinearMap
  refine ⟨(fun v ↦ ∑ i, (ContinuousLinearMap.toSpanSingleton 𝕜 (b i)).compLpL p μ (v i)) '' K,
    hK.image (by fun_prop), Filter.mem_of_superset hKT fun y hy ↦ ⟨_, hy, ?_⟩⟩
  exact (eq_sum_basis_compLpL b (T y)).symm

end TauCeti

namespace Module.Basis

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
      · rw [eNorm_smul, mul_comm]

end Module.Basis
