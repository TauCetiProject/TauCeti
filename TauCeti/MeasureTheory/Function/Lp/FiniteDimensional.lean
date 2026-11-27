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
The same decomposition bounds the `Lᵖ` seminorm of a function by those of its coordinates, and that
of a field of functionals by those of its values on the basis vectors
(`Module.Basis.eLpNorm_le_sum_enorm_mul_eLpNorm_apply`). A function agrees almost everywhere with
the sum assembled from almost-everywhere representatives of its coordinates
(`Module.Basis.ae_eq_sum_smul_of_coord_ae_eq`).
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

/-- The `Lᵖ` seminorm of a field of functionals on a space with a finite basis `b` is controlled
by the `Lᵖ` seminorms of its values on the basis vectors, weighted by the norms of the coordinate
functionals of `b`: these are the coordinates of the field in the dual basis. -/
theorem eLpNorm_le_sum_enorm_mul_eLpNorm_apply (b : Module.Basis ι 𝕜 F)
    {g : α → F →L[𝕜] 𝕜} (hg : AEStronglyMeasurable g μ) :
    eLpNorm g p μ ≤
      ∑ i, ‖(b.coord i).toContinuousLinearMap‖ₑ * eLpNorm (fun x ↦ g x (b i)) p μ := by
  classical
  -- The dual basis of `b`, as continuous functionals.
  let κ : Module.Basis ι 𝕜 (F →L[𝕜] 𝕜) := b.dualBasis.map LinearMap.toContinuousLinearMap
  have hcoord (i : ι) (f : F →L[𝕜] 𝕜) : κ.coord i f = f (b i) := by
    simp [κ, Module.Basis.coord_apply, Module.Basis.map_repr, Module.Basis.dualBasis_repr]
  simpa [κ, hcoord] using κ.eLpNorm_le_sum_enorm_mul_eLpNorm_coord hg

/-- The `Lᵖ` norm of a field of functionals on a space with a finite basis `b` is at most a
constant, the sum of the norms of the coordinate functionals of `b`, times the sum of the `Lᵖ`
norms of its values on the basis vectors. When the field is not in `Lᵖ` the left side is `0`. -/
theorem toReal_eLpNorm_le_mul_sum_toReal_eLpNorm_apply (b : Module.Basis ι 𝕜 F)
    {g : α → F →L[𝕜] 𝕜} (hg : AEStronglyMeasurable g μ) :
    (eLpNorm g p μ).toReal ≤ (∑ i, ‖(b.coord i).toContinuousLinearMap‖) *
      ∑ i, (eLpNorm (fun x ↦ g x (b i)) p μ).toReal := by
  by_cases htop : eLpNorm g p μ = ⊤
  · rw [htop, ENNReal.toReal_top]
    exact mul_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)
      (Finset.sum_nonneg fun i _ ↦ ENNReal.toReal_nonneg)
  have hg' : MemLp g p μ := lt_top_iff_ne_top.2 htop
  have hfin (i : ι) : ‖(b.coord i).toContinuousLinearMap‖ₑ *
      eLpNorm (fun x ↦ g x (b i)) p μ ≠ ⊤ :=
    ENNReal.mul_ne_top eNorm_ne_top
      (hg'.continuousLinearMap_comp (ContinuousLinearMap.apply 𝕜 𝕜 (b i))).eLpNorm_ne_top
  refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ ↦ hfin i)
    (b.eLpNorm_le_sum_enorm_mul_eLpNorm_apply hg)).trans ?_
  rw [ENNReal.toReal_sum fun i _ ↦ hfin i, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [ENNReal.toReal_mul, toReal_eNorm]
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ ↦ norm_nonneg
    (b.coord i).toContinuousLinearMap) (Finset.mem_univ i)) ENNReal.toReal_nonneg

/-- **Reassembling a map from representatives of its coordinates.** If each coordinate
`z ↦ b.coord l (u z)` of `u` in a finite basis `b` agrees `μ`-almost everywhere with `g l`, then
`u` agrees `μ`-almost everywhere with `z ↦ ∑ₗ g l z • b l`. -/
theorem ae_eq_sum_smul_of_coord_ae_eq {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (b : Module.Basis ι R M) {u : α → M} {g : ι → α → R}
    (h : ∀ l, (fun z => b.coord l (u z)) =ᵐ[μ] g l) :
    u =ᵐ[μ] fun z => ∑ l, g l z • b l := by
  filter_upwards [ae_all_iff.2 h] with z hz
  simp only [← hz, Module.Basis.coord_apply, b.sum_repr]

end Module.Basis
