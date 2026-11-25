/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Complex.Wirtinger.Similarity.Transported
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.Local.Multiplication

/-!
# A Sobolev family of frames transports the complex structure

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open and `2 < p < ∞`, and let
`Φ : ℂ → V ≃L[ℝ] V` be a family of real-linear automorphisms which, together with its inverse, is
continuous on `Ω`, and which has a weak derivative `DΦ ∈ Lᵖ_loc(Ω)`. Put `J = Φ i Φ⁻¹`
(`TauCeti.transportedComplexStructure`) and

`C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹`, with `∂_s Φ = DΦ · 1` and `∂_t Φ = DΦ · I`

(`TauCeti.weakTransportedCoeff`). Then `C` is locally `Lᵖ`
(`TauCeti.memLpLoc_weakTransportedCoeff`), and every `ξ = Φ σ` with `σ` holomorphic is a weak
solution of `∂_s ξ + J ∂_t ξ + C ξ = 0`
(`TauCeti.isWeakLinearCauchyRiemannOn_transportedComplexStructure`). This is the converse of the
similarity principle for weak solutions: every factorization it produces, with a `W^{1,p}` frame
`Φ`, solves an equation of the kind it treats, so its conclusion cannot be improved to a constant
or holomorphic `Φ`. It extends the classical case of
`TauCeti.Analysis.Complex.Wirtinger.Similarity.Transported`, where `Φ` is `C¹` and `C` is
continuous, to Sobolev frames; for a `C¹` family `weakTransportedCoeff` with `DΦ = fderiv` is
`TauCeti.transportedCoeff`.

## Main declarations

* `TauCeti.weakTransportedCoeff`: the coefficient `C = -(DΦ · 1 + J (DΦ · I)) Φ⁻¹`.
* `TauCeti.memLpLoc_weakTransportedCoeff`: `C ∈ Lᵖ_loc`.
* `TauCeti.isWeakLinearCauchyRiemannOn_transportedComplexStructure`: `Φ σ` is a weak solution.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (Theorem 2.3.5, the Carleman similarity principle).
-/

public noncomputable section

open Complex ContinuousLinearMap MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The coefficient `C = -(DΦ · 1 + J (DΦ · I)) Φ⁻¹`, for a family `Φ` of real-linear automorphisms
with a derivative field `DΦ` and `J = Φ i Φ⁻¹`. -/
def weakTransportedCoeff (Φ : ℂ → V ≃L[ℝ] V) (DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (z : ℂ) :
    V →L[ℝ] V :=
  -((DΦ z 1 + transportedComplexStructure Φ z ∘L DΦ z I) ∘L ((Φ z).symm : V →L[ℝ] V))

variable {Φ : ℂ → V ≃L[ℝ] V} {DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}

/-- `C v = -(DΦ · 1 (Φ⁻¹ v) + J (DΦ · I (Φ⁻¹ v)))`. -/
theorem weakTransportedCoeff_apply (z : ℂ) (v : V) :
    weakTransportedCoeff Φ DΦ z v =
      -(DΦ z 1 ((Φ z).symm v) + transportedComplexStructure Φ z (DΦ z I ((Φ z).symm v))) := by
  simp [weakTransportedCoeff]

/-- For the classical derivative, `weakTransportedCoeff` is `TauCeti.transportedCoeff`. -/
theorem weakTransportedCoeff_fderiv :
    weakTransportedCoeff Φ (fun z ↦ fderiv ℝ (fun w ↦ (Φ w : V →L[ℝ] V)) z) =
      transportedCoeff Φ := by
  funext z
  ext v
  simp [weakTransportedCoeff_apply, transportedCoeff_apply]

/-- For a family `Φ` continuous on `Ω` with inverse continuous on `Ω` and a locally `Lᵖ`
derivative field `DΦ`, the coefficient `C = -(DΦ · 1 + J (DΦ · I)) Φ⁻¹` is locally `Lᵖ`. -/
theorem memLpLoc_weakTransportedCoeff {p : ℝ≥0∞} {Ω : Set ℂ}
    (hΦ : ContinuousOn (fun w ↦ (Φ w : V →L[ℝ] V)) Ω)
    (hΨ : ContinuousOn (fun w ↦ ((Φ w).symm : V →L[ℝ] V)) Ω) (hDΦ : MemLpLoc p Ω DΦ) :
    MemLpLoc p Ω (weakTransportedCoeff Φ DΦ) := by
  have hJ : ContinuousOn (transportedComplexStructure Φ) Ω :=
    (hΦ.clm_comp ((continuousOn_const (c := I • ContinuousLinearMap.id ℝ V)).clm_comp hΨ)).congr
      fun z _ ↦ by ext v; simp [transportedComplexStructure_apply]
  have h1 := hDΦ.clm_comp (apply ℝ (V →L[ℝ] V) 1)
  have hI := (hDΦ.clm_comp (apply ℝ (V →L[ℝ] V) I)).continuousOn_clm_comp hJ
  exact ((h1.add hI).clm_comp_continuousOn hΨ).neg

variable [FiniteDimensional ℂ V]

/-- **A Sobolev frame transports the complex structure.** Let `2 < p < ∞`, and let `Φ` be a family
of real-linear automorphisms of a finite-dimensional complex normed space, continuous on an open
set `Ω` together with its inverse, with weak derivative `DΦ ∈ Lᵖ_loc(Ω)`. For `J = Φ i Φ⁻¹` and
`C = -(DΦ · 1 + J (DΦ · I)) Φ⁻¹`, every `ξ = Φ σ` with `σ` holomorphic on `Ω` is a weak solution
of `∂_s ξ + J ∂_t ξ + C ξ = 0` on `Ω`. -/
theorem isWeakLinearCauchyRiemannOn_transportedComplexStructure {p : ℝ≥0} (hp : 2 < p)
    {Ω : Opens ℂ} (hΦ : ContinuousOn (fun w ↦ (Φ w : V →L[ℝ] V)) Ω)
    (hDΦ : HasWeakFDerivOn volume Ω (fun w ↦ (Φ w : V →L[ℝ] V)) DΦ) (hDΦp : MemLpLoc p Ω DΦ)
    {σ : ℂ → V} (hσ : DifferentiableOn ℂ σ Ω) :
    IsWeakLinearCauchyRiemannOn p (Ω : Set ℂ) (transportedComplexStructure Φ)
      (weakTransportedCoeff Φ DΦ) (fun z ↦ Φ z (σ z)) := by
  have hσ1 : ContDiffOn ℝ 1 σ Ω :=
    (hσ.contDiffOn Ω.isOpen).restrict_scalars ℝ
  have hDσ : ContinuousOn (fderiv ℝ σ) Ω := hσ1.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  have hp1 : 1 < p := one_lt_two.trans hp
  -- the weak Leibniz rule for `Φ σ`
  set B := ContinuousLinearMap.id ℝ (V →L[ℝ] V)
  have hD := hDΦ.bilin_of_memLpLoc B hp hp1 le_rfl hΦ.memLpLoc hDΦp
    (hσ1.hasWeakFDerivOn_fderiv (μ := volume)) hσ1.continuousOn.memLpLoc hDσ.memLpLoc
  have h1 : MemLpLoc p Ω (fun z ↦ B.precompL ℂ (DΦ z) (σ z)) :=
    (hDΦp.clm_comp (B.precompL ℂ)).clm_apply_continuousOn hσ1.continuousOn
  have h2 : MemLpLoc p Ω (fun z ↦ B.precompR ℂ (Φ z : V →L[ℝ] V) (fderiv ℝ σ z)) :=
    (((B.precompR ℂ).continuous.comp_continuousOn hΦ).clm_apply hDσ).memLpLoc
  refine isWeakLinearCauchyRiemannOn_iff_of_isOpen.2 ⟨hΦ.clm_apply hσ1.continuousOn,
    (hΦ.clm_apply hσ1.continuousOn).memLpLoc, _, hD, h1.add h2, ?_⟩
  · refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 (.of_forall fun z hz ↦ ?_)
    have hI : fderiv ℝ σ z I = I • fderiv ℝ σ z 1 := by
      rw [(hσ.differentiableAt (Ω.isOpen.mem_nhds hz)).fderiv_restrictScalars ℝ,
        ContinuousLinearMap.coe_restrictScalars', ← map_smul, smul_eq_mul, mul_one]
    simp only [B, add_apply, precompL_apply, precompR_apply, ContinuousLinearMap.id_apply,
      compL_apply, comp_apply, hI, weakTransportedCoeff_apply, transportedComplexStructure_apply,
      map_add, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      smul_smul, I_mul_I, neg_smul, one_smul, map_neg]
    abel

end TauCeti
