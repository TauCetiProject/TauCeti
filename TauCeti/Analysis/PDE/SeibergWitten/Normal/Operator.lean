/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Flat.Operator
public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic
public import TauCeti.Analysis.PDE.SeibergWitten.Normal.Frame
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed

/-!
# Normal intertwining for the gauge-fixed flat Seiberg–Witten operator

On an abstract oriented four-dimensional real inner product space `V` with almost complex structure
`J`, an adapted orthonormal frame `e` splits `V` into tangential and normal complex planes via
`normalCoord e : V → ℂ`. Pulling back `x` gives the canonical-line background
`(normalConnection e x, normalModelSpinor e u₀ x 0)`.

To reduce the linearized four-dimensional Seiberg–Witten problem along the normal plane to the
plane-vortex model, we relate `normalDomainEquiv` pointwise to `(normalModelConnection e y (-η),
normalModelSpinor e u₀ y (-η))` (`normalDomainEquiv_apply_normalCoord`) and prove
(`gaugeFixedFlatOperator_normalPerturbation`) that at any background `x`, the eight-real-component
linearized gauge-fixed operator `gaugeFixedFlatOperator` intertwines normal perturbations from
`(y, η)` with `normalTargetEquiv (L_x y, L_x* η)`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open CliffordAlgebra Complex Module exteriorPower
open scoped RealInnerProductSpace InnerProductSpace

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

attribute [local instance] finiteDimensional_of_finrank_four

/-! ### Exact eight-component normal intertwining theorem -/

section NormalIntertwining

section FrameHypotheses

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
  (hu₀₁ : ‖u₀‖ = 1)
include hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁

/-- Pointwise evaluation of `normalDomainEquiv` on `(y ∘ normalCoord e, η ∘ normalCoord e)`
recovers `(normalModelConnection e y (-η) p, normalModelSpinor e u₀ y (-η) p)`. -/
theorem normalDomainEquiv_apply_normalCoord (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (p : V) :
    normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (y (normalCoord e p), η (normalCoord e p)) =
      (normalModelConnection e y (-η) p, normalModelSpinor e u₀ y (-η) p) := by
  rw [normalDomainEquiv_apply]
  refine Prod.ext (normalFrameForm_eq_of_apply (by simp) (by simp) (by simp) (by simp)) ?_
  simp [normalFrameSpinor_def, normalModelSpinor_apply, Vortex.sectionValue_apply, sub_eq_add_neg]
  module

/-- **Eight-real-component normal intertwining theorem**: for any plane field `x : ℂ → ℝ⁴` (with no
PDE hypothesis on `x`), `gaugeFixedFlatOperator` at the pulled-back background
`(normalConnection e x, normalModelSpinor e u₀ x 0)` applied to the normal perturbation pulled back
from `(y, η)` equals `normalTargetEquiv (L_x y, L_x* η)` at `normalCoord e p`. -/
theorem gaugeFixedFlatOperator_normalPerturbation (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {y η : ℂ → EuclideanSpace ℝ (Fin 4)} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p))
    (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    gaugeFixedFlatOperator o ρ e hkl (normalConnection e x) (normalModelSpinor e u₀ x 0)
        (normalModelConnection e y (-η)) (normalModelSpinor e u₀ y (-η)) p =
      normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (Vortex.gaugeFixedOperator x y (normalCoord e p),
          Vortex.gaugeFixedAdjoint x η (normalCoord e p)) := by
  let z := normalCoord e p
  have hη' : DifferentiableAt ℝ (-η) z := hη.neg
  have hadj : Vortex.gaugeFixedAdjoint x (-η) z = -Vortex.gaugeFixedAdjoint x η z := by
    simpa only [neg_one_smul] using Vortex.gaugeFixedAdjoint_smul x η (-1) z
  have hω_sd := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  rw [normalTargetEquiv_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [gaugeFixedFlatOperator_apply]
    simpa [z] using flatDeformationGauge_normalModel hQ h₀ h₂₃ hρ hu₀ x hu₀₁ hy hη'
  · dsimp only
    set c := (gaugeFixedFlatOperator o ρ e hkl (normalConnection e x) (normalModelSpinor e u₀ x 0)
      (normalModelConnection e y (-η)) (normalModelSpinor e u₀ y (-η)) p).2.1
    have hc_sd : o.hodgeStar hkl (c : ⋀[ℝ]^2 V) = c :=
      o.hodgeStar_coe_of_mem_eigenspace_one hkl c
    have hinner {j : Fin 4}
        {σ : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1}
        (hσ : σ = o.selfDualWedge hkl (e 0) (e j)) :
        ⟪σ, c⟫ = ⟪flatDeformationCurvature o ρ hkl (normalModelConnection e y (-η))
            (normalModelSpinor e u₀ x 0) (normalModelSpinor e u₀ y (-η)) p,
          ιMulti ℝ 2 ![e 0, e j]⟫ := by
      rw [hσ, Submodule.coe_inner, o.inner_selfDualWedge_left_of_hodgeStar_eq_self hkl hc_sd,
        coe_gaugeFixedFlatOperator_snd_fst, real_inner_smul_right,
        real_inner_comm (ιMulti ℝ 2 ![e 0, e j]), ← mul_assoc, mul_div_assoc',
        Real.mul_self_sqrt zero_le_two]
      ring
    have hc0 : ⟪J.kahlerSelfDual o hkl hω_sd, c⟫ = Vortex.gaugeFixedOperator x y z 1 := by
      rw [hinner (AlmostComplexStructure.kahlerSelfDual_eq_selfDualWedge he h₀ h₂₃ hω_sd),
        inner_flatDeformationCurvature_normalModel_zero_one hQ hkl he h₀ h₂₃ hρ hu₀ x hu₀₁ hy hη']
    have hc1 : ⟪AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he, c⟫ =
        Vortex.gaugeFixedAdjoint x η z 0 := by
      rw [hinner AlmostComplexStructure.antiInvariantSelfDual₁_eq_selfDualWedge,
        inner_flatDeformationCurvature_normalModel_zero_two hQ hkl he h₀ h₂₃ hρ hu₀ x hu₀₁ hy hη',
        hadj, PiLp.neg_apply, neg_neg]
    have hc2 : ⟪AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he, c⟫ =
        Vortex.gaugeFixedAdjoint x η z 1 := by
      rw [hinner AlmostComplexStructure.antiInvariantSelfDual₂_eq_selfDualWedge,
        inner_flatDeformationCurvature_normalModel_zero_three hQ hkl he h₀ h₂₃ hρ hu₀ x hu₀₁ hy hη',
        hadj, PiLp.neg_apply, neg_neg]
    rw [AlmostComplexStructure.eq_inner_kahlerSelfDual_add_antiInvariantSelfDual
      (e := e) (he := he) (h₀ := h₀) (h₂ := h₂₃) hω_sd c, hc0, hc1, hc2,
      normalFrameSelfDual_def]
  · rw [gaugeFixedFlatOperator_apply, normalFrameNegSpinor_def]
    apply Subtype.ext
    have hdir := flatDeformationDirac_normalModel hQ h₀ h₂₃ hu₀ x hy hη'
    rw [normalModelConnection_zero_right] at hdir
    dsimp only
    rw [hdir]
    simp only [Submodule.coe_sub, Submodule.coe_smul, coe_halfSpinCliffordMul_apply_apply,
      LinearEquiv.coe_ofEq_apply, hadj, PiLp.neg_apply, ofReal_neg, z]
    module

end FrameHypotheses
end NormalIntertwining
end TauCeti.SeibergWitten
