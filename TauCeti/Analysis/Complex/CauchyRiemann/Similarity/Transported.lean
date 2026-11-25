/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Complex.Wirtinger.Similarity.Transported
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder

/-!
# A Sobolev family of frames transports the complex structure

Let `V` be a complex Banach space and `Ω ⊆ ℂ` open, and let `Φ : ℂ → V ≃L[ℝ] V` be a family of
real-linear automorphisms which is continuous on `Ω` and has a weak derivative `DΦ ∈ Lᵖ_loc(Ω)`.
Put `J = Φ i Φ⁻¹` (`TauCeti.transportedComplexStructure`) and

`C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹`, with `∂_s Φ = DΦ · 1` and `∂_t Φ = DΦ · I`

(`TauCeti.transportedCoeff Φ DΦ`). Then `C` is locally `Lᵖ` when `Φ⁻¹` is also continuous on `Ω`
(`TauCeti.memLpLoc_transportedCoeff_of_memLpLoc`), and for `p ≥ 2` every `ξ = Φ σ` with `σ`
holomorphic is a weak solution of `∂_s ξ + J ∂_t ξ + C ξ = 0`
(`TauCeti.isWeakLinearCauchyRiemannOn_transportedComplexStructure`). This extends the classical
case of `TauCeti.Analysis.Complex.Wirtinger.Similarity.Transported`, where `Φ` is `C¹`,
`DΦ = fderiv` and `C` is continuous, to Sobolev frames; both proofs rest on the pointwise identity
`TauCeti.add_transportedComplexStructure_add_transportedCoeff_eq_zero`.

## Main declarations

* `TauCeti.memLpLoc_transportedCoeff_of_memLpLoc`: `C ∈ Lᵖ_loc` for `DΦ ∈ Lᵖ_loc`.
* `TauCeti.isWeakLinearCauchyRiemannOn_transportedComplexStructure`: `Φ σ` is a weak solution.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (Theorem 2.3.5, the Carleman similarity principle).
-/

public noncomputable section

open Complex ContinuousLinearMap MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {Φ : ℂ → V ≃L[ℝ] V}
  {DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}

/-- For a family `Φ` continuous on `Ω` with inverse continuous on `Ω` and a locally `Lᵖ`
derivative field `DΦ`, the coefficient `C = -(DΦ · 1 + J (DΦ · I)) Φ⁻¹` is locally `Lᵖ`. -/
theorem memLpLoc_transportedCoeff_of_memLpLoc {p : ℝ≥0∞} {Ω : Set ℂ}
    (hΦ : ContinuousOn (fun w ↦ (Φ w : V →L[ℝ] V)) Ω)
    (hΨ : ContinuousOn (fun w ↦ ((Φ w).symm : V →L[ℝ] V)) Ω) (hDΦ : MemLpLoc p Ω DΦ) :
    MemLpLoc p Ω (transportedCoeff Φ DΦ) := by
  have hJ := continuousOn_transportedComplexStructure hΦ hΨ
  have h1 := hDΦ.clm_comp (apply ℝ (V →L[ℝ] V) 1)
  have hI := (hDΦ.clm_comp (apply ℝ (V →L[ℝ] V) I)).continuousOn_clm_comp hJ
  convert ((h1.add hI).clm_comp_continuousOn hΨ).neg using 1
  funext z
  ext v
  simp [transportedCoeff_apply]

variable [CompleteSpace V]

/-- **A Sobolev frame transports the complex structure.** Let `2 ≤ p ≤ ∞`, and let `Φ` be a
family of real-linear automorphisms of a complex Banach space, continuous on an open set `Ω`,
with weak derivative `DΦ ∈ Lᵖ_loc(Ω)`. For `J = Φ i Φ⁻¹` and
`C = -(DΦ · 1 + J (DΦ · I)) Φ⁻¹`, every `ξ = Φ σ` with `σ` holomorphic on `Ω` is a weak solution
of `∂_s ξ + J ∂_t ξ + C ξ = 0` on `Ω`. -/
theorem isWeakLinearCauchyRiemannOn_transportedComplexStructure {p : ℝ≥0∞} (hp : 2 ≤ p)
    {Ω : Opens ℂ} (hΦ : ContinuousOn (fun w ↦ (Φ w : V →L[ℝ] V)) Ω)
    (hDΦ : HasWeakFDerivOn volume Ω (fun w ↦ (Φ w : V →L[ℝ] V)) DΦ) (hDΦp : MemLpLoc p Ω DΦ)
    {σ : ℂ → V} (hσ : DifferentiableOn ℂ σ Ω) :
    IsWeakLinearCauchyRiemannOn p (Ω : Set ℂ) (transportedComplexStructure Φ)
      (transportedCoeff Φ DΦ) (fun z ↦ Φ z (σ z)) := by
  have hσ1 : ContDiffOn ℝ 1 σ Ω :=
    (hσ.contDiffOn Ω.isOpen).restrict_scalars ℝ
  have hDσ : ContinuousOn (fderiv ℝ σ) Ω := hσ1.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  -- the weak Leibniz rule for `Φ σ`, with every factor locally `L²`
  have h2p : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ ≤ 1 := ENNReal.inv_two_add_inv_two.le
  have hD : HasWeakFDerivOn volume Ω (fun z ↦ Φ z (σ z))
      (fun z ↦ (DΦ z).flip (σ z) + (Φ z : V →L[ℝ] V) ∘L fderiv ℝ σ z) := by
    convert hDΦ.bilin_of_memLp (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) ENNReal.ofNat_ne_top
      ENNReal.ofNat_ne_top ENNReal.ofNat_ne_top ENNReal.ofNat_ne_top h2p h2p h2p
      (hσ1.hasWeakFDerivOn_fderiv (μ := volume))
      (fun K hK hKΩ ↦ memLpLoc_iff.1 hΦ.memLpLoc K hKΩ hK)
      (fun K hK hKΩ ↦ memLpLoc_iff.1 (hDΦp.mono_exponent hp) K hKΩ hK)
      (fun K hK hKΩ ↦ memLpLoc_iff.1 hσ1.continuousOn.memLpLoc K hKΩ hK)
      (fun K hK hKΩ ↦ memLpLoc_iff.1 hDσ.memLpLoc K hKΩ hK) using 1
    · simp only [ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe]
    · funext z
      ext1 v
      simp
  have h1 : MemLpLoc p Ω (fun z ↦ (DΦ z).flip (σ z)) := by
    convert (hDΦp.clm_comp ((ContinuousLinearMap.id ℝ (V →L[ℝ] V)).precompL ℂ))
      |>.clm_apply_continuousOn hσ1.continuousOn using 1
    funext z
    ext1 v
    simp
  have h2 : MemLpLoc p Ω (fun z ↦ (Φ z : V →L[ℝ] V) ∘L fderiv ℝ σ z) :=
    (hΦ.clm_comp hDσ).memLpLoc
  refine isWeakLinearCauchyRiemannOn_iff_of_isOpen.2 ⟨hΦ.clm_apply hσ1.continuousOn,
    (hΦ.clm_apply hσ1.continuousOn).memLpLoc, _, hD, h1.add h2, ?_⟩
  · refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 (.of_forall fun z hz ↦ ?_)
    simpa only [add_apply, flip_apply, comp_apply, ContinuousLinearEquiv.coe_coe] using
      add_transportedComplexStructure_add_transportedCoeff_eq_zero z (σ z)
        (differentiableAt_complex_iff_differentiableAt_real.1
          (hσ.differentiableAt (Ω.isOpen.mem_nhds hz))).2

end TauCeti
