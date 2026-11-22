/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.NumberTheory.Padics.Distribution.Topology
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Topology

/-!
# The topological Amice isomorphism

The Amice bijection identifies the projective-limit topology of locally analytic distributions
with the Gauss topology of series on the open unit disc. The two topologies are compared by
`S_h(Aμ) ≤ D_h(μ) ≤ p S_{h+1}(Aμ)`, where `D_h` is the norm on the dual of the analytic stage
and `S_h` is the Gauss norm at `p ^ (-1 / ((p - 1) p^h))`. These radii tend to one, so they
detect the full open-disc topology, not merely coefficientwise convergence.

`amiceTransformContinuousLinearEquiv` bundles the Amice map as a continuous `K`-linear
equivalence. No strong-dual identification or single Banach norm is asserted here.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010),
  Théorème II.2.2, using the estimates of Théorème I.4.7.
-/

public section

open Filter Topology

namespace TauCeti.LocallyAnalyticDistribution

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K]
  [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra ℚ_[p] K]

/-- The Amice transform is continuous from the stage-dual topology to the open-disc Gauss
topology. -/
@[continuity, fun_prop]
theorem continuous_amiceTransformEquiv :
    Continuous (amiceTransformEquiv (p := p) (K := K)) := by
  rw [continuous_iff_continuousAt]
  intro ν
  rw [ContinuousAt]
  refine (PowerSeries.OnOpenDisc.tendsto_iff_of_tendsto
    (ρ := fun h ↦ ⟨amiceRadius p h, amiceRadius_pos h, amiceRadius_lt_one h⟩)
    tendsto_amiceRadius).mpr fun h ↦ ?_
  let r : Set.Ioo (0 : ℝ) 1 :=
    ⟨amiceRadius p h, amiceRadius_pos _, amiceRadius_lt_one _⟩
  let : Fact (0 < (r : ℝ)) := ⟨r.property.1⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hstage := (tendsto_iff_stageSeminorm_sub (f := id) (μ := ν)).mp tendsto_id h
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun μ ↦ ?_) hstage
  rw [← map_sub, PowerSeries.norm_eq_gaussNorm, PowerSeries.OnOpenDisc.coe_restrict]
  simpa only [AddSubgroupClass.coe_sub, coe_amiceTransformEquiv,
    map_sub (amiceTransform (p := p) (K := K)), id_eq] using
    gaussNorm_amiceRadius_le_stageSeminorm (μ - ν) h

/-- The inverse Amice map is continuous from the open-disc Gauss topology to the stage-dual
topology. -/
@[continuity, fun_prop]
theorem continuous_amiceTransformEquiv_symm :
    Continuous (amiceTransformEquiv (p := p) (K := K)).symm := by
  rw [continuous_iff_continuousAt]
  intro G
  rw [ContinuousAt, tendsto_iff_stageSeminorm_sub]
  intro h
  let r : Set.Ioo (0 : ℝ) 1 :=
    ⟨amiceRadius p (h + 1), amiceRadius_pos _, amiceRadius_lt_one _⟩
  let : Fact (0 < (r : ℝ)) := ⟨r.property.1⟩
  have hnorm : Tendsto
      (fun F : PowerSeries.OnOpenDisc.subring K 1 ↦
        (p : ℝ) * ‖PowerSeries.OnOpenDisc.restrict r F - PowerSeries.OnOpenDisc.restrict r G‖)
      (𝓝 G) (𝓝 0) := by
    have hc := (PowerSeries.OnOpenDisc.uniformContinuous_restrict (R := K) r).continuous
    simpa only [Pi.sub_apply, sub_self, norm_zero, mul_zero] using
      ((hc.sub (continuous_const (y := PowerSeries.OnOpenDisc.restrict r G))).norm.const_mul
        (p : ℝ)).tendsto G
  refine squeeze_zero (fun F ↦ apply_nonneg (stageSeminorm (p := p) (K := K) h) _)
    (fun F ↦ ?_) hnorm
  have hsub : amiceTransform ((amiceTransformEquiv (p := p) (K := K)).symm F -
      (amiceTransformEquiv (p := p) (K := K)).symm G) =
      (F : PowerSeries K) - (G : PowerSeries K) := by
    simp only [map_sub (amiceTransform (p := p) (K := K)),
      ← coe_amiceTransformEquiv, LinearEquiv.apply_symm_apply]
  convert stageSeminorm_le_mul_gaussNorm_amiceRadius_succ
    ((amiceTransformEquiv (p := p) (K := K)).symm F - amiceTransformEquiv.symm G) h using 1
  rw [← map_sub, PowerSeries.norm_eq_gaussNorm, PowerSeries.OnOpenDisc.coe_restrict, hsub]
  rfl

/-- Amice's topological isomorphism: the projective limit of the analytic-stage duals is the
space of series on the open unit disc with all its smaller-radius Gauss norms. -/
noncomputable def amiceTransformContinuousLinearEquiv :
    LocallyAnalyticDistribution p K ≃L[K] PowerSeries.OnOpenDisc.subring K 1 where
  toLinearEquiv := amiceTransformEquiv
  continuous_toFun := continuous_amiceTransformEquiv
  continuous_invFun := continuous_amiceTransformEquiv_symm

/-- The topological Amice map is the algebraic Amice map on each distribution. -/
@[simp]
theorem amiceTransformContinuousLinearEquiv_apply (μ : LocallyAnalyticDistribution p K) :
    amiceTransformContinuousLinearEquiv μ = amiceTransformEquiv μ :=
  (rfl)

/-- The inverse topological Amice map agrees with the inverse algebraic Amice map. -/
@[simp]
theorem amiceTransformContinuousLinearEquiv_symm_apply
    (F : PowerSeries.OnOpenDisc.subring K 1) :
    (amiceTransformContinuousLinearEquiv (p := p)).symm F =
      (amiceTransformEquiv (p := p)).symm F :=
  (rfl)

end TauCeti.LocallyAnalyticDistribution
