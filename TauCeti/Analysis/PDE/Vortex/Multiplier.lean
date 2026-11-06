/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplication

/-!
# Smooth multipliers on Sobolev vortex fields

The field equations, the deformation complex and the gauge action on the affine space
`A_m^k = (a_m, α_m) + H^k(ℂ; iT*ℂ ⊕ ℂ)` of framed degree-`m` vortex fields multiply the
`H^k` direction by the reference pair `(a_m, α_m)`. These coefficients do not decay: the
reference section has unit modulus and the reference connection decays only like `1 / |z|`
outside a disc. They are nevertheless smooth with bounded derivatives of every order
(`TauCeti.Vortex.exists_norm_iteratedFDeriv_referenceSection_le`,
`TauCeti.Vortex.exists_norm_iteratedFDeriv_referenceConnection_le`).

This file proves that a pointwise real-linear map `M z` on field values whose coefficients are
smooth, of temperate growth, with derivatives of order at most `k` bounded, preserves the space
`sobolevFields k` of `H^k` fields for every natural number `k`
(`TauCeti.Vortex.clm_apply_mem_sobolevFields`). Every term of the field equations that is linear
in the `H^k` direction with a coefficient built from the reference pair has this form, for
instance complex multiplication of the section part by `α_m`, or the action of `a_m` on it.

The proof reduces to the scalar statement for real `H^k` functions,
`TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul_of_norm_iteratedFDeriv_le`,
applied to the matrix coefficients of `M z` in the standard basis.

## Main results

* `TauCeti.Vortex.clm_apply_mem_sobolevFields`: `z ↦ M z (y z)` lies in `sobolevFields k` for
  `y ∈ sobolevFields k`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution

namespace TauCeti.Vortex

/-- **Smooth multipliers on Sobolev fields.** For a natural number `k`, a pointwise real-linear
map `M z` on field values, of temperate growth in `z` and with derivatives of order at most `k`
bounded, maps `H^k` fields to `H^k` fields. -/
theorem clm_apply_mem_sobolevFields {k : ℕ}
    {M : ℂ → EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)}
    (hM : M.HasTemperateGrowth) (hbd : ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n M z‖ ≤ C)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) :
    (fun z ↦ M z (y z)) ∈ sobolevFields k := by
  refine mem_sobolevFields.2 fun i ↦ ?_
  -- The matrix coefficient `c j z = (M z eⱼ)ᵢ` is a smooth multiplier.
  let L (j : Fin 4) : (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace.single j 1))
  have hc (j : Fin 4) : (fun z ↦ L j (M z)).HasTemperateGrowth :=
    (L j).hasTemperateGrowth.comp hM
  have hcbd (j : Fin 4) : ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ L j (M z)) z‖ ≤ C :=
    (L j).exists_norm_iteratedFDeriv_comp_left_le (hM.1.of_le (mod_cast le_top)) hbd
  -- Multiply each coordinate of `y` by its coefficient and sum.
  have hv (j : Fin 4) : ∃ u : Lp ℝ 2 (volume : Measure ℂ), u ∈ realSobolevSubmodule ℂ k 2 ∧
      u =ᵐ[volume] fun z ↦ L j (M z) * y z j := by
    obtain ⟨u, hu, hS⟩ := mem_sobolevFields.1 hy j
    obtain ⟨v, hvS, hv⟩ := exists_mem_realSobolevSubmodule_ae_eq_mul_of_norm_iteratedFDeriv_le
      (by norm_num) (by norm_num) (hc j) (hcbd j) (mem_realSobolevSubmodule.2 hS)
    refine ⟨v, hvS, ?_⟩
    filter_upwards [hv, hu] with z h₁ h₂
    rw [h₁, h₂]
  choose v hvS hv using hv
  refine ⟨∑ j, v j, ?_, mem_realSobolevSubmodule.1 (Submodule.sum_mem _ fun j _ ↦ hvS j)⟩
  filter_upwards [Lp.coeFn_finsetSum Finset.univ v, ae_all_iff.2 hv] with z h₁ h₂
  rw [h₁, Finset.sum_apply]
  simp only [h₂]
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr (y z)]
  simp [L, map_sum, mul_comm]

end TauCeti.Vortex
